/*-------------------------------------------------------------------------
 *
 * reindex.c
 *	  Implementation of regular expression index for  PostgreSQL.
 *
 * NOTES
 *
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 * Portions Copyright (c) 2013, Giannis Mouchakis gmouchakis@gmail.com
 * Portions Copyright (c) 2013, N.C.S.R. "Demokritos"
 *
 * IDENTIFICATION
 *	  src/backend/access/reindex/reindex.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/nbtree.h"
#include "access/relscan.h"
#include "catalog/index.h"
#include "commands/vacuum.h"
#include "storage/indexfsm.h"
#include "storage/ipc.h"
#include "storage/lmgr.h"
#include "storage/smgr.h"
#include "tcop/tcopprot.h"
#include "utils/memutils.h"

#include <regex.h>
#include <string.h>
//#include <time.h>
//#include "commands/tablecmds.h"
#include "tcop/pquery.h"
#include "tcop/dest.h"
#include "tcop/utility.h"
#include "pgstat.h"
#include "utils/probes.h"
#include "parser/analyze.h"
#include "miscadmin.h"
#include "access/printtup.h"
#include "executor/spi.h"

//#include "/home/giannis/project/pgsql/src/backend/tcop/postgres.c"

ItemPointerData http_array[10000000];
int http_array_size = 0;
const char* http_regex = "^http";
static regex_t* http_regex_ptr = NULL;

ItemPointerData httpa_array[1000000];
int httpa_array_size = 0;
const char* httpa_regex = "^httpa";
static regex_t* httpa_regex_ptr = NULL;
//int httpa_current_position = 0;
//bool httpa_have_checked = false;


ItemPointerData httpb_array[1000];
int httpb_array_size = 0;
const char* httpb_regex = "^httpb";
static regex_t* httpb_regex_ptr = NULL;
//int httpb_current_position = 0;
//bool httpb_have_checked = false;

const char* begin_regex_str = "re:";
const size_t begin_regex_str_length = 3;

int current_position = 0;
bool have_checked = false;
int current_matched_regex = -1;
int current_array_size = 0;
ItemPointerData *current_regex_array = NULL;

ItemPointerData itemPointerData;

int proc = 0;

int dead = 0;

/* Working state for btbuild and its callback */
typedef struct
{
	bool		isUnique;
	bool		haveDead;
	Relation	heapRel;
	BTSpool    *spool;

	/*
	 * spool2 is needed only when the index is an unique index. Dead tuples
	 * are put into spool2 instead of spool in order to avoid uniqueness
	 * check.
	 */
	BTSpool    *spool2;
	double		indtuples;
} BTBuildState;

/* Working state needed by btvacuumpage */
typedef struct
{
	IndexVacuumInfo *info;
	IndexBulkDeleteResult *stats;
	IndexBulkDeleteCallback callback;
	void	   *callback_state;
	BTCycleId	cycleid;
	BlockNumber lastBlockVacuumed;		/* last blkno reached by Vacuum scan */
	BlockNumber lastUsedPage;	/* blkno of last non-recyclable page */
	BlockNumber totFreePages;	/* true total # of free pages */
	MemoryContext pagedelcontext;
} BTVacState;


static void btbuildCallback(Relation index,
				HeapTuple htup,
				Datum *values,
				bool *isnull,
				bool tupleIsAlive,
				void *state);
static void btvacuumscan(IndexVacuumInfo *info, IndexBulkDeleteResult *stats,
			 IndexBulkDeleteCallback callback, void *callback_state,
			 BTCycleId cycleid);
static void btvacuumpage(BTVacState *vstate, BlockNumber blkno,
			 BlockNumber orig_blkno);


/*
 *	btbuild() -- build a new btree index.
 */
Datum
btbuild(PG_FUNCTION_ARGS)
{
	Relation	heap = (Relation) PG_GETARG_POINTER(0);
	Relation	index = (Relation) PG_GETARG_POINTER(1);
	IndexInfo  *indexInfo = (IndexInfo *) PG_GETARG_POINTER(2);
	IndexBuildResult *result;
	double		reltuples;
	BTBuildState buildstate;

	buildstate.isUnique = indexInfo->ii_Unique;
	buildstate.haveDead = false;
	buildstate.heapRel = heap;
	buildstate.spool = NULL;
	buildstate.spool2 = NULL;
	buildstate.indtuples = 0;

#ifdef BTREE_BUILD_STATS
	if (log_btree_build_stats)
		ResetUsage();
#endif   /* BTREE_BUILD_STATS */

	/*
	 * We expect to be called exactly once for any index relation. If that's
	 * not the case, big trouble's what we have.
	 */
	if (RelationGetNumberOfBlocks(index) != 0)
		elog(ERROR, "index \"%s\" already contains data",
			 RelationGetRelationName(index));

	buildstate.spool = _bt_spoolinit(index, indexInfo->ii_Unique, false);

	/*
	 * If building a unique index, put dead tuples in a second spool to keep
	 * them out of the uniqueness check.
	 */
	if (indexInfo->ii_Unique)
		buildstate.spool2 = _bt_spoolinit(index, false, true);

	/* do the heap scan */
	reltuples = IndexBuildHeapScan(heap, index, indexInfo, true,
								   btbuildCallback, (void *) &buildstate);

	/* okay, all heap tuples are indexed */
	if (buildstate.spool2 && !buildstate.haveDead)
	{
		/* spool2 turns out to be unnecessary */
		_bt_spooldestroy(buildstate.spool2);
		buildstate.spool2 = NULL;
	}

	/*
	 * Finish the build by (1) completing the sort of the spool file, (2)
	 * inserting the sorted tuples into btree pages and (3) building the upper
	 * levels.
	 */
	_bt_leafbuild(buildstate.spool, buildstate.spool2);
	_bt_spooldestroy(buildstate.spool);
	if (buildstate.spool2)
		_bt_spooldestroy(buildstate.spool2);

#ifdef BTREE_BUILD_STATS
	if (log_btree_build_stats)
	{
		ShowUsage("BTREE BUILD STATS");
		ResetUsage();
	}
#endif   /* BTREE_BUILD_STATS */

	/*
	 * If we are reindexing a pre-existing index, it is critical to send out a
	 * relcache invalidation SI message to ensure all backends re-read the
	 * index metapage.	We expect that the caller will ensure that happens
	 * (typically as a side effect of updating index stats, but it must happen
	 * even if the stats don't change!)
	 */

	/*
	 * Return statistics
	 */
	result = (IndexBuildResult *) palloc(sizeof(IndexBuildResult));

	result->heap_tuples = reltuples;
	result->index_tuples = buildstate.indtuples;

	/*elog(INFO, "reltuples=%f", reltuples);
	elog(INFO, "index_tuples=%f", buildstate.indtuples);
	elog(INFO, "http_array_size=%d", http_array_size);
	elog(INFO, "httpa_array_size=%d", httpa_array_size);
	elog(INFO, "httpb_array_size=%d", httpb_array_size);
	elog(INFO, "dead=%d", dead);*/

	//test create table
	//int is_my_index = strcmp("f_str_idx", index->rd_rel->relname.data);
	int is_my_index = strcmp("magic_index", index->rd_rel->relname.data);
	if(is_my_index == 0) {

		//char *query_string = "create table test_semagrow(str text);";
		//exec_simple_query2(query_string);

		/*elog(LOG, "SPI_connect()=%d", SPI_connect());
		elog(LOG, "create magic_index_table=%d", SPI_execute("create table magic_index_table(offset_nubmer integer, block_number integer);", false, 0));
		elog(LOG, "SPI_finish()=%d", SPI_finish());*/
		SPI_connect();
		SPI_execute("create table magic_index_table(offset_number integer, block_number integer);", false, 0);
		SPI_finish();

	}

	PG_RETURN_POINTER(result);
}

/*
 * Per-tuple callback from IndexBuildHeapScan
 */
static void
btbuildCallback(Relation index,
				HeapTuple htup,
				Datum *values,
				bool *isnull,
				bool tupleIsAlive,
				void *state)
{
	BTBuildState *buildstate = (BTBuildState *) state;
	IndexTuple	itup;

	/* form an index tuple and point it at the heap tuple */
	itup = index_form_tuple(RelationGetDescr(index), values, isnull);
	itup->t_tid = htup->t_self;

	/*
	 * insert the index tuple into the appropriate spool file for subsequent
	 * processing
	 */
	if (tupleIsAlive || buildstate->spool2 == NULL)
	{
		_bt_spool(itup, buildstate->spool);
		r_i_insert(index, values, &(htup->t_self));
	}
	else
	{
		/* dead tuples are put into spool2 */
		buildstate->haveDead = true;
		_bt_spool(itup, buildstate->spool2);
		dead++;
		elog(INFO, "dead");
	}

	buildstate->indtuples += 1;

	pfree(itup);
}

/*
 *	btbuildempty() -- build an empty btree index in the initialization fork
 */
Datum
btbuildempty(PG_FUNCTION_ARGS)
{
	Relation	index = (Relation) PG_GETARG_POINTER(0);
	Page		metapage;

	/* Construct metapage. */
	metapage = (Page) palloc(BLCKSZ);
	_bt_initmetapage(metapage, P_NONE, 0);

	/* Write the page.	If archiving/streaming, XLOG it. */
	smgrwrite(index->rd_smgr, INIT_FORKNUM, BTREE_METAPAGE,
			  (char *) metapage, true);
	if (XLogIsNeeded())
		log_newpage(&index->rd_smgr->smgr_rnode.node, INIT_FORKNUM,
					BTREE_METAPAGE, metapage);

	/*
	 * An immediate sync is require even if we xlog'd the page, because the
	 * write did not go through shared_buffers and therefore a concurrent
	 * checkpoint may have move the redo pointer past our xlog record.
	 */
	smgrimmedsync(index->rd_smgr, INIT_FORKNUM);

	PG_RETURN_VOID();
}


void
exec_simple_query2(const char *query_string)
{
	CommandDest dest = whereToSendOutput;
	MemoryContext oldcontext;
	List	   *parsetree_list;
	ListCell   *parsetree_item;
	bool		save_log_statement_stats = log_statement_stats;
	bool		was_logged = false;
	bool		isTopLevel;
	char		msec_str[32];


	/*
	 * Report query to various monitoring facilities.
	 */
	debug_query_string = query_string;

	pgstat_report_activity(STATE_RUNNING, query_string);

	TRACE_POSTGRESQL_QUERY_START(query_string);

	/*
	 * We use save_log_statement_stats so ShowUsage doesn't report incorrect
	 * results because ResetUsage wasn't called.
	 */
	if (save_log_statement_stats)
		ResetUsage();

	/*
	 * Start up a transaction command.	All queries generated by the
	 * query_string will be in this same command block, *unless* we find a
	 * BEGIN/COMMIT/ABORT statement; we have to force a new xact command after
	 * one of those, else bad things will happen in xact.c. (Note that this
	 * will normally change current memory context.)
	 */
	//start_xact_command();

	/*
	 * Zap any pre-existing unnamed statement.	(While not strictly necessary,
	 * it seems best to define simple-Query mode as if it used the unnamed
	 * statement and portal; this ensures we recover any storage used by prior
	 * unnamed operations.)
	 */
	//drop_unnamed_stmt();

	/*
	 * Switch to appropriate context for constructing parsetrees.
	 */
	oldcontext = MemoryContextSwitchTo(MessageContext);

	/*
	 * Do basic parsing of the query or queries (this should be safe even if
	 * we are in aborted transaction state!)
	 */
	parsetree_list = pg_parse_query(query_string);
/*
	 Log immediately if dictated by log_statement
	if (check_log_statement(parsetree_list))
	{
		ereport(LOG,
				(errmsg("statement: %s", query_string),
				 errhidestmt(true),
				 errdetail_execute(parsetree_list)));
		was_logged = true;
	}*/

	/*
	 * Switch back to transaction context to enter the loop.
	 */
	MemoryContextSwitchTo(oldcontext);

	/*
	 * We'll tell PortalRun it's a top-level command iff there's exactly one
	 * raw parsetree.  If more than one, it's effectively a transaction block
	 * and we want PreventTransactionChain to reject unsafe commands. (Note:
	 * we're assuming that query rewrite cannot add commands that are
	 * significant to PreventTransactionChain.)
	 */
	isTopLevel = (list_length(parsetree_list) == 1);

	/*
	 * Run through the raw parsetree(s) and process each one.
	 */
	foreach(parsetree_item, parsetree_list)
	{
		Node	   *parsetree = (Node *) lfirst(parsetree_item);
		//bool		snapshot_set = false;
		const char *commandTag;
		char		completionTag[COMPLETION_TAG_BUFSIZE];
		List	   *querytree_list,
				   *plantree_list;
		Portal		portal;
		DestReceiver *receiver;
		int16		format;

		/*
		 * Get the command name for use in status display (it also becomes the
		 * default completion tag, down inside PortalRun).	Set ps_status and
		 * do any special start-of-SQL-command processing needed by the
		 * destination.
		 */
		commandTag = CreateCommandTag(parsetree);

		//set_ps_display(commandTag, false);

		BeginCommand(commandTag, dest);

		/*
		 * If we are in an aborted transaction, reject all commands except
		 * COMMIT/ABORT.  It is important that this test occur before we try
		 * to do parse analysis, rewrite, or planning, since all those phases
		 * try to do database accesses, which may fail in abort state. (It
		 * might be safe to allow some additional utility commands in this
		 * state, but not many...)
		 */
		/*if (IsAbortedTransactionBlockState() &&
			!IsTransactionExitStmt(parsetree))
			ereport(ERROR,
					(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
					 errmsg("current transaction is aborted, "
						  "commands ignored until end of transaction block"),
					 errdetail_abort()));
*/
		/* Make sure we are in a transaction command */
		//start_xact_command();

		/* If we got a cancel signal in parsing or prior command, quit */
		//CHECK_FOR_INTERRUPTS();

		/*
		 * Set up a snapshot if parse analysis/planning will need one.
		 */
		/*if (analyze_requires_snapshot(parsetree))
		{
			PushActiveSnapshot(GetTransactionSnapshot());
			snapshot_set = true;
		}*/

		/*
		 * OK to analyze, rewrite, and plan this query.
		 *
		 * Switch to appropriate context for constructing querytrees (again,
		 * these must outlive the execution context).
		 */
		oldcontext = MemoryContextSwitchTo(MessageContext);

		querytree_list = pg_analyze_and_rewrite(parsetree, query_string,
												NULL, 0);

		plantree_list = pg_plan_queries(querytree_list, 0, NULL);

		/* Done with the snapshot used for parsing/planning */
		/*if (snapshot_set)
			PopActiveSnapshot();
*/
		/* If we got a cancel signal in analysis or planning, quit */
		CHECK_FOR_INTERRUPTS();

		/*
		 * Create unnamed portal to run the query or queries in. If there
		 * already is one, silently drop it.
		 */
		portal = CreatePortal("semagrow_portal", true, true);
		/* Don't display the portal in pg_cursors */
		portal->visible = false;

		/*
		 * We don't have to copy anything into the portal, because everything
		 * we are passing here is in MessageContext, which will outlive the
		 * portal anyway.
		 */
		PortalDefineQuery(portal,
						  NULL,
						  query_string,
						  commandTag,
						  plantree_list,
						  NULL);

		/*
		 * Start the portal.  No parameters here.
		 */
		PortalStart(portal, NULL, 0, InvalidSnapshot);

		/*
		 * Select the appropriate output format: text unless we are doing a
		 * FETCH from a binary cursor.	(Pretty grotty to have to do this here
		 * --- but it avoids grottiness in other places.  Ah, the joys of
		 * backward compatibility...)
		 */
		format = 0;				/* TEXT is default */
		if (IsA(parsetree, FetchStmt))
		{
			FetchStmt  *stmt = (FetchStmt *) parsetree;

			if (!stmt->ismove)
			{
				Portal		fportal = GetPortalByName(stmt->portalname);

				if (PortalIsValid(fportal) &&
					(fportal->cursorOptions & CURSOR_OPT_BINARY))
					format = 1; /* BINARY */
			}
		}
		PortalSetResultFormat(portal, 1, &format);

		/*
		 * Now we can create the destination receiver object.
		 */
		receiver = CreateDestReceiver(dest);
		if (dest == DestRemote)
			SetRemoteDestReceiverParams(receiver, portal);

		/*
		 * Switch back to transaction context for execution.
		 */
		MemoryContextSwitchTo(oldcontext);

		/*
		 * Run the portal to completion, and then drop it (and the receiver).
		 */
		(void) PortalRun(portal,
						 FETCH_ALL,
						 isTopLevel,
						 receiver,
						 receiver,
						 completionTag);

		(*receiver->rDestroy) (receiver);

		PortalDrop(portal, false);

		if (IsA(parsetree, TransactionStmt))
		{
			/*
			 * If this was a transaction control statement, commit it. We will
			 * start a new xact command for the next command (if any).
			 */
			//finish_xact_command();
		}
		else if (lnext(parsetree_item) == NULL)
		{
			/*
			 * If this is the last parsetree of the query string, close down
			 * transaction statement before reporting command-complete.  This
			 * is so that any end-of-transaction errors are reported before
			 * the command-complete message is issued, to avoid confusing
			 * clients who will expect either a command-complete message or an
			 * error, not one and then the other.  But for compatibility with
			 * historical Postgres behavior, we do not force a transaction
			 * boundary between queries appearing in a single query string.
			 */
			//finish_xact_command();
		}
		else
		{
			/*
			 * We need a CommandCounterIncrement after every query, except
			 * those that start or end a transaction block.
			 */
			//CommandCounterIncrement();
		}

		/*
		 * Tell client that we're done with this query.  Note we emit exactly
		 * one EndCommand report for each raw parsetree, thus one for each SQL
		 * command the client sent, regardless of rewriting. (But a command
		 * aborted by error will not send an EndCommand report at all.)
		 */
		EndCommand(completionTag, dest);
	}							/* end loop over parsetrees */

	/*
	 * Close down transaction statement, if one is open.
	 */
	//finish_xact_command();

	/*
	 * If there were no parsetrees, return EmptyQueryResponse message.
	 */
	if (!parsetree_list)
		NullCommand(dest);

	/*
	 * Emit duration logging if appropriate.
	 */
	/*switch (check_log_duration(msec_str, was_logged))
	{
		case 1:
			ereport(LOG,
					(errmsg("duration: %s ms", msec_str),
					 errhidestmt(true)));
			break;
		case 2:
			ereport(LOG,
					(errmsg("duration: %s ms  statement: %s",
							msec_str, query_string),
					 errhidestmt(true),
					 errdetail_execute(parsetree_list)));
			break;
	}

	if (save_log_statement_stats)
		ShowUsage("QUERY STATISTICS");
*/
	TRACE_POSTGRESQL_QUERY_DONE(query_string);

	debug_query_string = NULL;
}

/*
 *	r_i_insert() -- insert tuple pointer in my array if it matches my regex.
 */
void
r_i_insert(Relation index, Datum *values, ItemPointer ht_ctid)
{
	//int is_my_index = strcmp("b_str_idx", index->rd_rel->relname.data);
	int is_my_index = strcmp("magic_index", index->rd_rel->relname.data);
	if(is_my_index == 0) {//if index name is b_str_idx
		char *textptr;
		text *str = DatumGetTextP(*values);
		int32 i;
		int32 size;

		size = VARSIZE(str) - VARHDRSZ;
		textptr = malloc(size); //TODO: use palloc?
		//elog(INFO, "size=%d", size);
		for (i = 0; i < size; i++) {
			textptr[i] = str->vl_dat[i];
			//elog(INFO, "%c", str->vl_dat[i]);
			//elog(INFO, "%c", VARDATA(str)[i]);
		}
		textptr[size] = '\0';
		//elog(INFO, "final string is %s", textptr);

		// regex_t regex;
		int reti;
		// char msgbuf[100];

		if (http_regex_ptr == NULL ) {
			http_regex_ptr = malloc(sizeof(regex_t));
			/* Compile regular expression */
			reti = regcomp(http_regex_ptr, http_regex, 0);
			//if( reti ){ fprintf(stderr, "Could not compile regex\n"); exit(1); }
		}
		/* Execute regular expression */
		reti = regexec(http_regex_ptr, textptr, 0, NULL, 0);
		if (!reti) {
			//http_array[http_array_size] = *ht_ctid;
			//http_array_size++;
			//elog(LOG, "SPI_connect()=%d", SPI_connect());
			SPI_connect();
			BlockNumber ip_blkid = ItemPointerGetBlockNumber(ht_ctid);
			OffsetNumber ip_posid = ItemPointerGetOffsetNumber(ht_ctid);
			//char *query = "insert into magic_index_table(offset_number, block_number) values (? ,?);";
			SPI_connect();
			char *fmt = "insert into magic_index_table(offset_number, block_number) values (%u, %u);";
			size_t buf_len = strlen(fmt) + 12;//2^32 = 4G < 10^10, 2^16 = 64K < 10^5, 15 + 1 (null termination) - 4 (2 x %u) = 12
			char *query = palloc(buf_len);
			size_t n = snprintf(query, buf_len, fmt, ip_posid, ip_blkid);
			//elog(LOG, query);
			if (n > buf_len) {
				pfree(query);
				query = palloc(n + 1);
				snprintf(query, buf_len, fmt, ip_posid, ip_blkid);
				elog(WARNING, "n=%d, buf_len=%d, fmt=%d", n, buf_len, strlen(fmt));
			}
			SPI_execute(query, false, 0);
			SPI_finish();
			pfree(query);
			//elog(LOG, "value matches to regex. inserted. http_array_size=%d", http_array_size);
		}
		/* else if( reti == REG_NOMATCH ){
		 	 puts("No match");
		 }
		 else{
		 	 regerror(reti, &regex, msgbuf, sizeof(msgbuf));
		 	 fprintf(stderr, "Regex match failed: %s\n", msgbuf);
		 	 exit(1);
		 }*/
		if (httpa_regex_ptr == NULL ) {
			httpa_regex_ptr = malloc(sizeof(regex_t));
			/* Compile regular expression */
			reti = regcomp(httpa_regex_ptr, httpa_regex, 0);
		}
		reti = regexec(httpa_regex_ptr, textptr, 0, NULL, 0);
		if (!reti) {
			httpa_array[httpa_array_size] = *ht_ctid;
			httpa_array_size++;
			//elog(INFO, "value matches to regex. inserted");
		} else {
			if (httpb_regex_ptr == NULL ) {
				httpb_regex_ptr = malloc(sizeof(regex_t));
				/* Compile regular expression */
				reti = regcomp(httpb_regex_ptr, httpb_regex, 0);
			}
			reti = regexec(httpb_regex_ptr, textptr, 0, NULL, 0);
			if (!reti) {
				httpb_array[httpb_array_size] = *ht_ctid;
				httpb_array_size++;
				//elog(INFO, "value matches to regex. inserted");
			}
		}

		/* Free compiled regular expression if you want to use the regex_t again */
		//regfree(&regex);
		free(textptr);//TODO: use pfree?

		//memcpy(dst,str->vl_dat,size); dst[len] = '\0';
	}
}

/*
 * returns -1 if no match, 0 if matches to ^http, 1 if matches to ^httpa and 2 matches to ^httpb
 */
int
r_i_matches(IndexScanDesc scan)
{
	//bool result = false;
	int result = -1;

	/*time_t start,end;
	double dif;
	time (&start);*/
	//elog(INFO, "scan->indexRelation->rd_id = %d", scan->indexRelation->rd_id);
	//if (scan->indexRelation->rd_id==41192){
	//int is_my_index = strcmp("b_str_idx", scan->indexRelation->rd_rel->relname.data);
	int is_my_index = strcmp("magic_index", scan->indexRelation->rd_rel->relname.data);
	if(is_my_index == 0) {
		//elog(LOG, "eimai sto magic. http_array_size=%d", http_array_size);
		char *textptr;
		//elog(INFO, "scanKey %s", DatumGetTextP(scan->keyData->sk_argument));
		text *str = DatumGetTextP(scan->keyData->sk_argument);
		int32 i;
		int32 size;

		size = VARSIZE(str) - VARHDRSZ;
		textptr = malloc(size);
		//elog(INFO, "size=%d", size);
		for (i = 0; i < size; i++) {
			textptr[i] = str->vl_dat[i];
			//elog(INFO, "%c", str->vl_dat[i]);
			//elog(INFO, "%c", VARDATA(str)[i]);
		}
		textptr[size] = '\0';
		//elog(INFO, "final string is %s", textptr);

		//code bellow to be removed after sesame tests!
		int result_regex = strcmp("http", textptr + begin_regex_str_length);
		if (result_regex == 0) {
			//elog(LOG, "tairiazei sto regex");
			result = 0;
		}

/*commented bellow to test with sesame.
		int result_begin = strncmp(begin_regex_str, textptr, begin_regex_str_length);
		if(result_begin == 0) {
			int result_regex = strcmp(http_regex, textptr + begin_regex_str_length);
			if (result_regex == 0) {
				result = 0;
				//elog(INFO, "key matches to regex %s. returning my values.", my_regex);
				time (&end);
				dif = difftime (end,start);
				elog(INFO, "My index took %f seconds to run.", dif );
				elog(INFO, "nentries=%d", tbm->nentries);
				elog(INFO, "maxentries=%d", tbm->maxentries);
				elog(INFO, "npages=%d", tbm->npages);
				elog(INFO, "nchunks=%d", tbm->nchunks);
				elog(INFO, "iterating=%d", tbm->iterating);

			}
			result_regex = strcmp(httpa_regex, textptr + begin_regex_str_length);
			if (result_regex == 0) {
				result = 1;
			} else {
				result_regex = strcmp(httpb_regex, textptr + begin_regex_str_length);
				if (result_regex == 0) {
					result = 2;
				}
			}

		}*/
		free(textptr);
	}

	return result;
}

bool
r_i_gettuple(IndexScanDesc scan)
{
	//elog(LOG, "r_i_gettuple");

	bool res;

	if (current_position < current_array_size) {
		//elog(LOG, "current_position=%d", current_position);
		scan->xs_ctup.t_self = current_regex_array[current_position];
		current_position++;
		res = true;
	} else {
		//elog(LOG, "false!");
		res = false;
		current_position = 0;
		have_checked = false;
		current_regex_array = NULL;
		current_array_size = 0;
		current_matched_regex = -1;
	}

	return res;
}


bool
r_i_gettuple_disk(IndexScanDesc scan)
{
	//elog(LOG, "r_i_gettuple");

	bool res;
	//elog(LOG, "current_array_size");
	if (current_position < current_array_size) {
		//elog(LOG, "current_position=%d", current_position);
		//scan->xs_ctup.t_self = current_regex_array[current_position];
		elog(DEBUG5, "begin");
		TupleDesc tupdesc = SPI_tuptable->tupdesc;
		SPITupleTable *tuptable = SPI_tuptable;
		elog(DEBUG5, "reached 1");
		HeapTuple tuple = tuptable->vals[current_position];
		elog(DEBUG5, "reached 2");
		bool isnull;
		OffsetNumber ip_posid =  DatumGetUInt16(SPI_getbinval(tuple, tupdesc, 1, &isnull));
		elog(DEBUG5, "reached 3");
		BlockNumber ip_blkid = DatumGetUInt32(SPI_getbinval(tuple, tupdesc, 2, &isnull));
		elog(DEBUG5, "reached 5");
		elog(DEBUG5, "ip_blkid=%u", ip_blkid);
		elog(DEBUG5, "ip_posid=%u", ip_posid);
		ItemPointerSet(&itemPointerData, ip_blkid, ip_posid);
		elog(DEBUG5, "ItemPointerIsValid(itemPointer)=%d", ItemPointerIsValid(&itemPointerData));
		elog(DEBUG5, "reached 6");
		scan->xs_ctup.t_self = itemPointerData;
		elog(DEBUG5, "reached 7");
		current_position++;
		elog(DEBUG5, "reached 8");
		res = true;
		elog(DEBUG5, "reached 9");
	} else {
		//elog(LOG, "false!");
		res = false;
		current_position = 0;
		have_checked = false;
		current_regex_array = NULL;
		current_array_size = 0;
		current_matched_regex = -1;
		proc = 0;
		SPI_finish();
	}

	return res;
}


/*int r_i_get_index_tuples();

int
r_i_get_index_tuples()
{
    char *command;
    int ret;
    int proc;

     Convert given text object to a C string
    command = text_to_cstring("SELECT * from magic_index_table;");

    SPI_connect();

    ret = SPI_execute(command, true, 0);

    proc = SPI_processed;

     * If some rows were fetched, print them via elog(INFO).

    if (ret > 0 && SPI_tuptable != NULL)
    {
        TupleDesc tupdesc = SPI_tuptable->tupdesc;
        SPITupleTable *tuptable = SPI_tuptable;
        char buf[8192];
        int i, j;

        for (j = 0; j < proc; j++)
        {
            HeapTuple tuple = tuptable->vals[j];

            for (i = 1, buf[0] = 0; i <= tupdesc->natts; i++)
                snprintf(buf + strlen (buf), sizeof(buf) - strlen(buf), " %s%s",
                        SPI_getvalue(tuple, tupdesc, i),
                        (i == tupdesc->natts) ? " " : " |");
            elog(INFO, "EXECQ: %s", buf);
        }
    }

    SPI_finish();
    pfree(command);

    return (proc);
}*/

/*
 *	btinsert() -- insert an index tuple into a btree.
 *
 *		Descend the tree recursively, find the appropriate location for our
 *		new tuple, and put it there.
 */
Datum
btinsert(PG_FUNCTION_ARGS)
{
	Relation	rel = (Relation) PG_GETARG_POINTER(0);
	Datum	   *values = (Datum *) PG_GETARG_POINTER(1);
	bool	   *isnull = (bool *) PG_GETARG_POINTER(2);
	ItemPointer ht_ctid = (ItemPointer) PG_GETARG_POINTER(3);
	Relation	heapRel = (Relation) PG_GETARG_POINTER(4);
	IndexUniqueCheck checkUnique = (IndexUniqueCheck) PG_GETARG_INT32(5);
	bool		result;
	IndexTuple	itup;

	r_i_insert(rel, values, ht_ctid);

	/* generate an index tuple */
	itup = index_form_tuple(RelationGetDescr(rel), values, isnull);
	itup->t_tid = *ht_ctid;

	result = _bt_doinsert(rel, itup, checkUnique, heapRel);

	pfree(itup);

	PG_RETURN_BOOL(result);
}

/*
 *	btgettuple() -- Get the next tuple in the scan.
 */
Datum
btgettuple(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	ScanDirection dir = (ScanDirection) PG_GETARG_INT32(1);
	BTScanOpaque so = (BTScanOpaque) scan->opaque;
	bool		res;

	/* btree indexes are never lossy */
	scan->xs_recheck = false;

	//elog(LOG, "btgettuple");
	/*if (r_i_matches(scan)) {
		PG_RETURN_BOOL(r_i_gettuple(scan));
	}*/


	if (have_checked) {
		//elog(LOG, "have_checked=true");
		PG_RETURN_BOOL(r_i_gettuple_disk(scan));
	} else {
		//elog(LOG, "have_checked=false");
		current_matched_regex = r_i_matches(scan);
		if (current_matched_regex != -1) {
			if (current_matched_regex == 0) {
				//elog(LOG, "current_matched_regex == 0");
				//char *command;
				current_regex_array = http_array;
				//command = text_to_cstring("SELECT * from magic_index_table;");
			    SPI_connect();
			    SPI_execute("SELECT * from magic_index_table;", true, 0);
			    //pfree(command);
				//current_array_size = http_array_size;
				current_array_size = SPI_processed;
				//elog(LOG, "current_array_size=%d", current_array_size);
			} else if (current_matched_regex == 1) {
				current_regex_array = httpa_array;
				current_array_size = httpa_array_size;
			} else if (current_matched_regex == 2) {
				current_regex_array = httpb_array;
				current_array_size = httpb_array_size;
			}
			have_checked = true;
			PG_RETURN_BOOL(r_i_gettuple_disk(scan));
		}
	}

	/*
	 * If we have any array keys, initialize them during first call for a
	 * scan.  We can't do this in btrescan because we don't know the scan
	 * direction at that time.
	 */
	if (so->numArrayKeys && !BTScanPosIsValid(so->currPos))
	{
		/* punt if we have any unsatisfiable array keys */
		if (so->numArrayKeys < 0)
			PG_RETURN_BOOL(false);

		_bt_start_array_keys(scan, dir);
	}

	/* This loop handles advancing to the next array elements, if any */
	do
	{
		/*
		 * If we've already initialized this scan, we can just advance it in
		 * the appropriate direction.  If we haven't done so yet, we call
		 * _bt_first() to get the first item in the scan.
		 */
		if (!BTScanPosIsValid(so->currPos))
			res = _bt_first(scan, dir);
		else
		{
			/*
			 * Check to see if we should kill the previously-fetched tuple.
			 */
			if (scan->kill_prior_tuple)
			{
				/*
				 * Yes, remember it for later. (We'll deal with all such
				 * tuples at once right before leaving the index page.)  The
				 * test for numKilled overrun is not just paranoia: if the
				 * caller reverses direction in the indexscan then the same
				 * item might get entered multiple times. It's not worth
				 * trying to optimize that, so we don't detect it, but instead
				 * just forget any excess entries.
				 */
				if (so->killedItems == NULL)
					so->killedItems = (int *)
						palloc(MaxIndexTuplesPerPage * sizeof(int));
				if (so->numKilled < MaxIndexTuplesPerPage)
					so->killedItems[so->numKilled++] = so->currPos.itemIndex;
			}

			/*
			 * Now continue the scan.
			 */
			res = _bt_next(scan, dir);
		}

		/* If we have a tuple, return it ... */
		if (res)
			break;
		/* ... otherwise see if we have more array keys to deal with */
	} while (so->numArrayKeys && _bt_advance_array_keys(scan, dir));

	PG_RETURN_BOOL(res);
}

/*
 * btgetbitmap() -- gets all matching tuples, and adds them to a bitmap
 */
Datum
btgetbitmap(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	TIDBitmap  *tbm = (TIDBitmap *) PG_GETARG_POINTER(1);
	BTScanOpaque so = (BTScanOpaque) scan->opaque;
	int64		ntids = 0;
	ItemPointer heapTid;

	int matched_regex = r_i_matches(scan);
	/*if (matched_regex != 0) {

	}*/
	if (matched_regex == 0) {
		int x;
		for (x = 0; x < http_array_size; x++) {
			tbm_add_tuples(tbm, &http_array[x], 1, false );
			ntids++;
		}
		PG_RETURN_INT64(ntids);
	} else if (matched_regex == 1) {
		int x;
		for (x = 0; x < httpa_array_size; x++) {
			tbm_add_tuples(tbm, &httpa_array[x], 1, false );
			ntids++;
		}
		PG_RETURN_INT64(ntids);
	} else if (matched_regex == 2) {
		int x;
		for (x = 0; x < httpb_array_size; x++) {
			tbm_add_tuples(tbm, &httpb_array[x], 1, false );
			ntids++;
		}
		PG_RETURN_INT64(ntids);
	}

	/*
	 * If we have any array keys, initialize them.
	 */
	if (so->numArrayKeys)
	{
		/* punt if we have any unsatisfiable array keys */
		if (so->numArrayKeys < 0)
			PG_RETURN_INT64(ntids);

		_bt_start_array_keys(scan, ForwardScanDirection);
	}

	/* This loop handles advancing to the next array elements, if any */
	do
	{
		/* Fetch the first page & tuple */
		if (_bt_first(scan, ForwardScanDirection))
		{
			/* Save tuple ID, and continue scanning */
			heapTid = &scan->xs_ctup.t_self;
			tbm_add_tuples(tbm, heapTid, 1, false);
			ntids++;

			for (;;)
			{
				/*
				 * Advance to next tuple within page.  This is the same as the
				 * easy case in _bt_next().
				 */
				if (++so->currPos.itemIndex > so->currPos.lastItem)
				{
					/* let _bt_next do the heavy lifting */
					if (!_bt_next(scan, ForwardScanDirection))
						break;
				}

				/* Save tuple ID, and continue scanning */
				heapTid = &so->currPos.items[so->currPos.itemIndex].heapTid;
				tbm_add_tuples(tbm, heapTid, 1, false);
				ntids++;
			}
		}
		/* Now see if we have more array keys to deal with */
	} while (so->numArrayKeys && _bt_advance_array_keys(scan, ForwardScanDirection));

	/*if (scan->indexRelation->rd_id==16391){
		tbm_add_tuples(tbm, ItemPointerArray[0], 1, false);
		ntids++;
	}*/

	/*time (&end);
	dif = difftime (end,start);
	elog(INFO, "Default index took %f seconds to run.", dif );*/

	PG_RETURN_INT64(ntids);
}

/*
 *	btbeginscan() -- start a scan on a btree index
 */
Datum
btbeginscan(PG_FUNCTION_ARGS)
{
	Relation	rel = (Relation) PG_GETARG_POINTER(0);
	int			nkeys = PG_GETARG_INT32(1);
	int			norderbys = PG_GETARG_INT32(2);
	IndexScanDesc scan;
	BTScanOpaque so;

	/* no order by operators allowed */
	Assert(norderbys == 0);

	/* get the scan */
	scan = RelationGetIndexScan(rel, nkeys, norderbys);

	/* allocate private workspace */
	so = (BTScanOpaque) palloc(sizeof(BTScanOpaqueData));
	so->currPos.buf = so->markPos.buf = InvalidBuffer;
	if (scan->numberOfKeys > 0)
		so->keyData = (ScanKey) palloc(scan->numberOfKeys * sizeof(ScanKeyData));
	else
		so->keyData = NULL;

	so->arrayKeyData = NULL;	/* assume no array keys for now */
	so->numArrayKeys = 0;
	so->arrayKeys = NULL;
	so->arrayContext = NULL;

	so->killedItems = NULL;		/* until needed */
	so->numKilled = 0;

	/*
	 * We don't know yet whether the scan will be index-only, so we do not
	 * allocate the tuple workspace arrays until btrescan.	However, we set up
	 * scan->xs_itupdesc whether we'll need it or not, since that's so cheap.
	 */
	so->currTuples = so->markTuples = NULL;
	so->currPos.nextTupleOffset = 0;
	so->markPos.nextTupleOffset = 0;

	scan->xs_itupdesc = RelationGetDescr(rel);

	scan->opaque = so;

	PG_RETURN_POINTER(scan);
}

/*
 *	btrescan() -- rescan an index relation
 */
Datum
btrescan(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	ScanKey		scankey = (ScanKey) PG_GETARG_POINTER(1);

	/* remaining arguments are ignored */
	BTScanOpaque so = (BTScanOpaque) scan->opaque;

	/* we aren't holding any read locks, but gotta drop the pins */
	if (BTScanPosIsValid(so->currPos))
	{
		/* Before leaving current page, deal with any killed items */
		if (so->numKilled > 0)
			_bt_killitems(scan, false);
		ReleaseBuffer(so->currPos.buf);
		so->currPos.buf = InvalidBuffer;
	}

	if (BTScanPosIsValid(so->markPos))
	{
		ReleaseBuffer(so->markPos.buf);
		so->markPos.buf = InvalidBuffer;
	}
	so->markItemIndex = -1;

	/*
	 * Allocate tuple workspace arrays, if needed for an index-only scan and
	 * not already done in a previous rescan call.	To save on palloc
	 * overhead, both workspaces are allocated as one palloc block; only this
	 * function and btendscan know that.
	 *
	 * NOTE: this data structure also makes it safe to return data from a
	 * "name" column, even though btree name_ops uses an underlying storage
	 * datatype of cstring.  The risk there is that "name" is supposed to be
	 * padded to NAMEDATALEN, but the actual index tuple is probably shorter.
	 * However, since we only return data out of tuples sitting in the
	 * currTuples array, a fetch of NAMEDATALEN bytes can at worst pull some
	 * data out of the markTuples array --- running off the end of memory for
	 * a SIGSEGV is not possible.  Yeah, this is ugly as sin, but it beats
	 * adding special-case treatment for name_ops elsewhere.
	 */
	if (scan->xs_want_itup && so->currTuples == NULL)
	{
		so->currTuples = (char *) palloc(BLCKSZ * 2);
		so->markTuples = so->currTuples + BLCKSZ;
	}

	/*
	 * Reset the scan keys. Note that keys ordering stuff moved to _bt_first.
	 * - vadim 05/05/97
	 */
	if (scankey && scan->numberOfKeys > 0)
		memmove(scan->keyData,
				scankey,
				scan->numberOfKeys * sizeof(ScanKeyData));
	so->numberOfKeys = 0;		/* until _bt_preprocess_keys sets it */

	/* If any keys are SK_SEARCHARRAY type, set up array-key info */
	_bt_preprocess_array_keys(scan);

	PG_RETURN_VOID();
}

/*
 *	btendscan() -- close down a scan
 */
Datum
btendscan(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BTScanOpaque so = (BTScanOpaque) scan->opaque;

	/* we aren't holding any read locks, but gotta drop the pins */
	if (BTScanPosIsValid(so->currPos))
	{
		/* Before leaving current page, deal with any killed items */
		if (so->numKilled > 0)
			_bt_killitems(scan, false);
		ReleaseBuffer(so->currPos.buf);
		so->currPos.buf = InvalidBuffer;
	}

	if (BTScanPosIsValid(so->markPos))
	{
		ReleaseBuffer(so->markPos.buf);
		so->markPos.buf = InvalidBuffer;
	}
	so->markItemIndex = -1;

	/* Release storage */
	if (so->keyData != NULL)
		pfree(so->keyData);
	/* so->arrayKeyData and so->arrayKeys are in arrayContext */
	if (so->arrayContext != NULL)
		MemoryContextDelete(so->arrayContext);
	if (so->killedItems != NULL)
		pfree(so->killedItems);
	if (so->currTuples != NULL)
		pfree(so->currTuples);
	/* so->markTuples should not be pfree'd, see btrescan */
	pfree(so);

	PG_RETURN_VOID();
}

/*
 *	btmarkpos() -- save current scan position
 */
Datum
btmarkpos(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BTScanOpaque so = (BTScanOpaque) scan->opaque;

	/* we aren't holding any read locks, but gotta drop the pin */
	if (BTScanPosIsValid(so->markPos))
	{
		ReleaseBuffer(so->markPos.buf);
		so->markPos.buf = InvalidBuffer;
	}

	/*
	 * Just record the current itemIndex.  If we later step to next page
	 * before releasing the marked position, _bt_steppage makes a full copy of
	 * the currPos struct in markPos.  If (as often happens) the mark is moved
	 * before we leave the page, we don't have to do that work.
	 */
	if (BTScanPosIsValid(so->currPos))
		so->markItemIndex = so->currPos.itemIndex;
	else
		so->markItemIndex = -1;

	/* Also record the current positions of any array keys */
	if (so->numArrayKeys)
		_bt_mark_array_keys(scan);

	PG_RETURN_VOID();
}

/*
 *	btrestrpos() -- restore scan to last saved position
 */
Datum
btrestrpos(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BTScanOpaque so = (BTScanOpaque) scan->opaque;

	/* Restore the marked positions of any array keys */
	if (so->numArrayKeys)
		_bt_restore_array_keys(scan);

	if (so->markItemIndex >= 0)
	{
		/*
		 * The mark position is on the same page we are currently on. Just
		 * restore the itemIndex.
		 */
		so->currPos.itemIndex = so->markItemIndex;
	}
	else
	{
		/* we aren't holding any read locks, but gotta drop the pin */
		if (BTScanPosIsValid(so->currPos))
		{
			/* Before leaving current page, deal with any killed items */
			if (so->numKilled > 0 &&
				so->currPos.buf != so->markPos.buf)
				_bt_killitems(scan, false);
			ReleaseBuffer(so->currPos.buf);
			so->currPos.buf = InvalidBuffer;
		}

		if (BTScanPosIsValid(so->markPos))
		{
			/* bump pin on mark buffer for assignment to current buffer */
			IncrBufferRefCount(so->markPos.buf);
			memcpy(&so->currPos, &so->markPos,
				   offsetof(BTScanPosData, items[1]) +
				   so->markPos.lastItem * sizeof(BTScanPosItem));
			if (so->currTuples)
				memcpy(so->currTuples, so->markTuples,
					   so->markPos.nextTupleOffset);
		}
	}

	PG_RETURN_VOID();
}

/*
 * Bulk deletion of all index entries pointing to a set of heap tuples.
 * The set of target tuples is specified via a callback routine that tells
 * whether any given heap tuple (identified by ItemPointer) is being deleted.
 *
 * Result: a palloc'd struct containing statistical info for VACUUM displays.
 */
Datum
btbulkdelete(PG_FUNCTION_ARGS)
{
	IndexVacuumInfo *info = (IndexVacuumInfo *) PG_GETARG_POINTER(0);
	IndexBulkDeleteResult *volatile stats = (IndexBulkDeleteResult *) PG_GETARG_POINTER(1);
	IndexBulkDeleteCallback callback = (IndexBulkDeleteCallback) PG_GETARG_POINTER(2);
	void	   *callback_state = (void *) PG_GETARG_POINTER(3);
	Relation	rel = info->index;
	BTCycleId	cycleid;

	/* allocate stats if first time through, else re-use existing struct */
	if (stats == NULL)
		stats = (IndexBulkDeleteResult *) palloc0(sizeof(IndexBulkDeleteResult));

	/* Establish the vacuum cycle ID to use for this scan */
	/* The ENSURE stuff ensures we clean up shared memory on failure */
	PG_ENSURE_ERROR_CLEANUP(_bt_end_vacuum_callback, PointerGetDatum(rel));
	{
		cycleid = _bt_start_vacuum(rel);

		btvacuumscan(info, stats, callback, callback_state, cycleid);
	}
	PG_END_ENSURE_ERROR_CLEANUP(_bt_end_vacuum_callback, PointerGetDatum(rel));
	_bt_end_vacuum(rel);

	PG_RETURN_POINTER(stats);
}

/*
 * Post-VACUUM cleanup.
 *
 * Result: a palloc'd struct containing statistical info for VACUUM displays.
 */
Datum
btvacuumcleanup(PG_FUNCTION_ARGS)
{
	IndexVacuumInfo *info = (IndexVacuumInfo *) PG_GETARG_POINTER(0);
	IndexBulkDeleteResult *stats = (IndexBulkDeleteResult *) PG_GETARG_POINTER(1);

	/* No-op in ANALYZE ONLY mode */
	if (info->analyze_only)
		PG_RETURN_POINTER(stats);

	/*
	 * If btbulkdelete was called, we need not do anything, just return the
	 * stats from the latest btbulkdelete call.  If it wasn't called, we must
	 * still do a pass over the index, to recycle any newly-recyclable pages
	 * and to obtain index statistics.
	 *
	 * Since we aren't going to actually delete any leaf items, there's no
	 * need to go through all the vacuum-cycle-ID pushups.
	 */
	if (stats == NULL)
	{
		stats = (IndexBulkDeleteResult *) palloc0(sizeof(IndexBulkDeleteResult));
		btvacuumscan(info, stats, NULL, NULL, 0);
	}

	/* Finally, vacuum the FSM */
	IndexFreeSpaceMapVacuum(info->index);

	/*
	 * It's quite possible for us to be fooled by concurrent page splits into
	 * double-counting some index tuples, so disbelieve any total that exceeds
	 * the underlying heap's count ... if we know that accurately.  Otherwise
	 * this might just make matters worse.
	 */
	if (!info->estimated_count)
	{
		if (stats->num_index_tuples > info->num_heap_tuples)
			stats->num_index_tuples = info->num_heap_tuples;
	}

	PG_RETURN_POINTER(stats);
}

/*
 * btvacuumscan --- scan the index for VACUUMing purposes
 *
 * This combines the functions of looking for leaf tuples that are deletable
 * according to the vacuum callback, looking for empty pages that can be
 * deleted, and looking for old deleted pages that can be recycled.  Both
 * btbulkdelete and btvacuumcleanup invoke this (the latter only if no
 * btbulkdelete call occurred).
 *
 * The caller is responsible for initially allocating/zeroing a stats struct
 * and for obtaining a vacuum cycle ID if necessary.
 */
static void
btvacuumscan(IndexVacuumInfo *info, IndexBulkDeleteResult *stats,
			 IndexBulkDeleteCallback callback, void *callback_state,
			 BTCycleId cycleid)
{
	Relation	rel = info->index;
	BTVacState	vstate;
	BlockNumber num_pages;
	BlockNumber blkno;
	bool		needLock;

	/*
	 * Reset counts that will be incremented during the scan; needed in case
	 * of multiple scans during a single VACUUM command
	 */
	stats->estimated_count = false;
	stats->num_index_tuples = 0;
	stats->pages_deleted = 0;

	/* Set up info to pass down to btvacuumpage */
	vstate.info = info;
	vstate.stats = stats;
	vstate.callback = callback;
	vstate.callback_state = callback_state;
	vstate.cycleid = cycleid;
	vstate.lastBlockVacuumed = BTREE_METAPAGE;	/* Initialise at first block */
	vstate.lastUsedPage = BTREE_METAPAGE;
	vstate.totFreePages = 0;

	/* Create a temporary memory context to run _bt_pagedel in */
	vstate.pagedelcontext = AllocSetContextCreate(CurrentMemoryContext,
												  "_bt_pagedel",
												  ALLOCSET_DEFAULT_MINSIZE,
												  ALLOCSET_DEFAULT_INITSIZE,
												  ALLOCSET_DEFAULT_MAXSIZE);

	/*
	 * The outer loop iterates over all index pages except the metapage, in
	 * physical order (we hope the kernel will cooperate in providing
	 * read-ahead for speed).  It is critical that we visit all leaf pages,
	 * including ones added after we start the scan, else we might fail to
	 * delete some deletable tuples.  Hence, we must repeatedly check the
	 * relation length.  We must acquire the relation-extension lock while
	 * doing so to avoid a race condition: if someone else is extending the
	 * relation, there is a window where bufmgr/smgr have created a new
	 * all-zero page but it hasn't yet been write-locked by _bt_getbuf(). If
	 * we manage to scan such a page here, we'll improperly assume it can be
	 * recycled.  Taking the lock synchronizes things enough to prevent a
	 * problem: either num_pages won't include the new page, or _bt_getbuf
	 * already has write lock on the buffer and it will be fully initialized
	 * before we can examine it.  (See also vacuumlazy.c, which has the same
	 * issue.)	Also, we need not worry if a page is added immediately after
	 * we look; the page splitting code already has write-lock on the left
	 * page before it adds a right page, so we must already have processed any
	 * tuples due to be moved into such a page.
	 *
	 * We can skip locking for new or temp relations, however, since no one
	 * else could be accessing them.
	 */
	needLock = !RELATION_IS_LOCAL(rel);

	blkno = BTREE_METAPAGE + 1;
	for (;;)
	{
		/* Get the current relation length */
		if (needLock)
			LockRelationForExtension(rel, ExclusiveLock);
		num_pages = RelationGetNumberOfBlocks(rel);
		if (needLock)
			UnlockRelationForExtension(rel, ExclusiveLock);

		/* Quit if we've scanned the whole relation */
		if (blkno >= num_pages)
			break;
		/* Iterate over pages, then loop back to recheck length */
		for (; blkno < num_pages; blkno++)
		{
			btvacuumpage(&vstate, blkno, blkno);
		}
	}

	/*
	 * InHotStandby we need to scan right up to the end of the index for
	 * correct locking, so we may need to write a WAL record for the final
	 * block in the index if it was not vacuumed. It's possible that VACUUMing
	 * has actually removed zeroed pages at the end of the index so we need to
	 * take care to issue the record for last actual block and not for the
	 * last block that was scanned. Ignore empty indexes.
	 */
	if (XLogStandbyInfoActive() &&
		num_pages > 1 && vstate.lastBlockVacuumed < (num_pages - 1))
	{
		Buffer		buf;

		/*
		 * We can't use _bt_getbuf() here because it always applies
		 * _bt_checkpage(), which will barf on an all-zero page. We want to
		 * recycle all-zero pages, not fail.  Also, we want to use a
		 * nondefault buffer access strategy.
		 */
		buf = ReadBufferExtended(rel, MAIN_FORKNUM, num_pages - 1, RBM_NORMAL,
								 info->strategy);
		LockBufferForCleanup(buf);
		_bt_delitems_vacuum(rel, buf, NULL, 0, vstate.lastBlockVacuumed);
		_bt_relbuf(rel, buf);
	}

	MemoryContextDelete(vstate.pagedelcontext);

	/* update statistics */
	stats->num_pages = num_pages;
	stats->pages_free = vstate.totFreePages;
}

/*
 * btvacuumpage --- VACUUM one page
 *
 * This processes a single page for btvacuumscan().  In some cases we
 * must go back and re-examine previously-scanned pages; this routine
 * recurses when necessary to handle that case.
 *
 * blkno is the page to process.  orig_blkno is the highest block number
 * reached by the outer btvacuumscan loop (the same as blkno, unless we
 * are recursing to re-examine a previous page).
 */
static void
btvacuumpage(BTVacState *vstate, BlockNumber blkno, BlockNumber orig_blkno)
{
	IndexVacuumInfo *info = vstate->info;
	IndexBulkDeleteResult *stats = vstate->stats;
	IndexBulkDeleteCallback callback = vstate->callback;
	void	   *callback_state = vstate->callback_state;
	Relation	rel = info->index;
	bool		delete_now;
	BlockNumber recurse_to;
	Buffer		buf;
	Page		page;
	BTPageOpaque opaque;

restart:
	delete_now = false;
	recurse_to = P_NONE;

	/* call vacuum_delay_point while not holding any buffer lock */
	vacuum_delay_point();

	/*
	 * We can't use _bt_getbuf() here because it always applies
	 * _bt_checkpage(), which will barf on an all-zero page. We want to
	 * recycle all-zero pages, not fail.  Also, we want to use a nondefault
	 * buffer access strategy.
	 */
	buf = ReadBufferExtended(rel, MAIN_FORKNUM, blkno, RBM_NORMAL,
							 info->strategy);
	LockBuffer(buf, BT_READ);
	page = BufferGetPage(buf);
	opaque = (BTPageOpaque) PageGetSpecialPointer(page);
	if (!PageIsNew(page))
		_bt_checkpage(rel, buf);

	/*
	 * If we are recursing, the only case we want to do anything with is a
	 * live leaf page having the current vacuum cycle ID.  Any other state
	 * implies we already saw the page (eg, deleted it as being empty).
	 */
	if (blkno != orig_blkno)
	{
		if (_bt_page_recyclable(page) ||
			P_IGNORE(opaque) ||
			!P_ISLEAF(opaque) ||
			opaque->btpo_cycleid != vstate->cycleid)
		{
			_bt_relbuf(rel, buf);
			return;
		}
	}

	/* If the page is in use, update lastUsedPage */
	if (!_bt_page_recyclable(page) && vstate->lastUsedPage < blkno)
		vstate->lastUsedPage = blkno;

	/* Page is valid, see what to do with it */
	if (_bt_page_recyclable(page))
	{
		/* Okay to recycle this page */
		RecordFreeIndexPage(rel, blkno);
		vstate->totFreePages++;
		stats->pages_deleted++;
	}
	else if (P_ISDELETED(opaque))
	{
		/* Already deleted, but can't recycle yet */
		stats->pages_deleted++;
	}
	else if (P_ISHALFDEAD(opaque))
	{
		/* Half-dead, try to delete */
		delete_now = true;
	}
	else if (P_ISLEAF(opaque))
	{
		OffsetNumber deletable[MaxOffsetNumber];
		int			ndeletable;
		OffsetNumber offnum,
					minoff,
					maxoff;

		/*
		 * Trade in the initial read lock for a super-exclusive write lock on
		 * this page.  We must get such a lock on every leaf page over the
		 * course of the vacuum scan, whether or not it actually contains any
		 * deletable tuples --- see nbtree/README.
		 */
		LockBuffer(buf, BUFFER_LOCK_UNLOCK);
		LockBufferForCleanup(buf);

		/*
		 * Check whether we need to recurse back to earlier pages.	What we
		 * are concerned about is a page split that happened since we started
		 * the vacuum scan.  If the split moved some tuples to a lower page
		 * then we might have missed 'em.  If so, set up for tail recursion.
		 * (Must do this before possibly clearing btpo_cycleid below!)
		 */
		if (vstate->cycleid != 0 &&
			opaque->btpo_cycleid == vstate->cycleid &&
			!(opaque->btpo_flags & BTP_SPLIT_END) &&
			!P_RIGHTMOST(opaque) &&
			opaque->btpo_next < orig_blkno)
			recurse_to = opaque->btpo_next;

		/*
		 * Scan over all items to see which ones need deleted according to the
		 * callback function.
		 */
		ndeletable = 0;
		minoff = P_FIRSTDATAKEY(opaque);
		maxoff = PageGetMaxOffsetNumber(page);
		if (callback)
		{
			for (offnum = minoff;
				 offnum <= maxoff;
				 offnum = OffsetNumberNext(offnum))
			{
				IndexTuple	itup;
				ItemPointer htup;

				itup = (IndexTuple) PageGetItem(page,
												PageGetItemId(page, offnum));
				htup = &(itup->t_tid);

				/*
				 * During Hot Standby we currently assume that
				 * XLOG_BTREE_VACUUM records do not produce conflicts. That is
				 * only true as long as the callback function depends only
				 * upon whether the index tuple refers to heap tuples removed
				 * in the initial heap scan. When vacuum starts it derives a
				 * value of OldestXmin. Backends taking later snapshots could
				 * have a RecentGlobalXmin with a later xid than the vacuum's
				 * OldestXmin, so it is possible that row versions deleted
				 * after OldestXmin could be marked as killed by other
				 * backends. The callback function *could* look at the index
				 * tuple state in isolation and decide to delete the index
				 * tuple, though currently it does not. If it ever did, we
				 * would need to reconsider whether XLOG_BTREE_VACUUM records
				 * should cause conflicts. If they did cause conflicts they
				 * would be fairly harsh conflicts, since we haven't yet
				 * worked out a way to pass a useful value for
				 * latestRemovedXid on the XLOG_BTREE_VACUUM records. This
				 * applies to *any* type of index that marks index tuples as
				 * killed.
				 */
				if (callback(htup, callback_state))
					deletable[ndeletable++] = offnum;
			}
		}

		/*
		 * Apply any needed deletes.  We issue just one _bt_delitems_vacuum()
		 * call per page, so as to minimize WAL traffic.
		 */
		if (ndeletable > 0)
		{
			BlockNumber lastBlockVacuumed = BufferGetBlockNumber(buf);

			_bt_delitems_vacuum(rel, buf, deletable, ndeletable,
								vstate->lastBlockVacuumed);

			/*
			 * Keep track of the block number of the lastBlockVacuumed, so we
			 * can scan those blocks as well during WAL replay. This then
			 * provides concurrency protection and allows btrees to be used
			 * while in recovery.
			 */
			if (lastBlockVacuumed > vstate->lastBlockVacuumed)
				vstate->lastBlockVacuumed = lastBlockVacuumed;

			stats->tuples_removed += ndeletable;
			/* must recompute maxoff */
			maxoff = PageGetMaxOffsetNumber(page);
		}
		else
		{
			/*
			 * If the page has been split during this vacuum cycle, it seems
			 * worth expending a write to clear btpo_cycleid even if we don't
			 * have any deletions to do.  (If we do, _bt_delitems_vacuum takes
			 * care of this.)  This ensures we won't process the page again.
			 *
			 * We treat this like a hint-bit update because there's no need to
			 * WAL-log it.
			 */
			if (vstate->cycleid != 0 &&
				opaque->btpo_cycleid == vstate->cycleid)
			{
				opaque->btpo_cycleid = 0;
				SetBufferCommitInfoNeedsSave(buf);
			}
		}

		/*
		 * If it's now empty, try to delete; else count the live tuples. We
		 * don't delete when recursing, though, to avoid putting entries into
		 * freePages out-of-order (doesn't seem worth any extra code to handle
		 * the case).
		 */
		if (minoff > maxoff)
			delete_now = (blkno == orig_blkno);
		else
			stats->num_index_tuples += maxoff - minoff + 1;
	}

	if (delete_now)
	{
		MemoryContext oldcontext;
		int			ndel;

		/* Run pagedel in a temp context to avoid memory leakage */
		MemoryContextReset(vstate->pagedelcontext);
		oldcontext = MemoryContextSwitchTo(vstate->pagedelcontext);

		ndel = _bt_pagedel(rel, buf, NULL);

		/* count only this page, else may double-count parent */
		if (ndel)
			stats->pages_deleted++;

		MemoryContextSwitchTo(oldcontext);
		/* pagedel released buffer, so we shouldn't */
	}
	else
		_bt_relbuf(rel, buf);

	/*
	 * This is really tail recursion, but if the compiler is too stupid to
	 * optimize it as such, we'd eat an uncomfortably large amount of stack
	 * space per recursion level (due to the deletable[] array). A failure is
	 * improbable since the number of levels isn't likely to be large ... but
	 * just in case, let's hand-optimize into a loop.
	 */
	if (recurse_to != P_NONE)
	{
		blkno = recurse_to;
		goto restart;
	}
}

/*
 *	btcanreturn() -- Check whether btree indexes support index-only scans.
 *
 * btrees always do, so this is trivial.
 */
Datum
btcanreturn(PG_FUNCTION_ARGS)
{
	PG_RETURN_BOOL(true);
}
