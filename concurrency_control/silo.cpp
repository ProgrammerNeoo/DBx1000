#include "txn.h"
#include "row.h"
#include "row_silo.h"

#if CC_ALG == SILO

RC
txn_man::validate_silo()
{
	RC rc = RCOK;
	
	// Get the read set and the write set.
	int write_set[wr_cnt];
	int cur_wr_idx = 0;
	int read_set[row_cnt - wr_cnt];
	int cur_rd_idx = 0;
	for (int rid = 0; rid < row_cnt; rid ++) {
		if (accesses[rid]->type == WR)
			write_set[cur_wr_idx ++] = rid;
		else 
			read_set[cur_rd_idx ++] = rid;
	}

	// Bubble sort the write set in primary key order.
	for (int i = wr_cnt - 1; i >= 1; i--) {
		for (int j = 0; j < i; j++) {
			if (accesses[ write_set[j] ]->orig_row->get_primary_key() > 
				accesses[ write_set[j + 1] ]->orig_row->get_primary_key())
			{
				int tmp = write_set[j];
				write_set[j] = write_set[j+1];
				write_set[j+1] = tmp;
			}
		}
	}

	int num_locks = 0;
	ts_t max_tid = 0;
	bool done = false;
	if (_pre_abort) {
		// Early abort a transaction if any tuple in the read set or the write set has
		// been modified by other transactions.
		// Why check the write set?
		for (int i = 0; i < wr_cnt; i++) {
			row_t * row = accesses[ write_set[i] ]->orig_row;
			if (row->manager->get_tid() != accesses[write_set[i]]->tid) {
				rc = Abort;
				goto final;
			}	
		}	
		for (int i = 0; i < row_cnt - wr_cnt; i ++) {
			Access * access = accesses[ read_set[i] ];
			if (access->orig_row->manager->get_tid() != accesses[read_set[i]]->tid) {
				rc = Abort;
				goto final;
			}
		}
	}

	// Lock all rows in the write set.
	if (_validation_no_wait) {
		// Transactions are not allowed to wait for locks. Whenever a transaction encounters
		// a row that is locked by other transactions, it release all locks and performs an
		// early abort check. This is deployed to avoid lock thrashing.
		while (!done) {
			num_locks = 0;
			for (int i = 0; i < wr_cnt; i++) {
				row_t * row = accesses[ write_set[i] ]->orig_row;
				if (!row->manager->try_lock())
					break;
				row->manager->assert_lock();
				num_locks ++;
				if (row->manager->get_tid() != accesses[write_set[i]]->tid)
				{
					rc = Abort;
					goto final;
				}
			}
			if (num_locks == wr_cnt)
				done = true;
			else {
				for (int i = 0; i < num_locks; i++)
					accesses[ write_set[i] ]->orig_row->manager->release();
				if (_pre_abort) {
					num_locks = 0;
					for (int i = 0; i < wr_cnt; i++) {
						row_t * row = accesses[ write_set[i] ]->orig_row;
						if (row->manager->get_tid() != accesses[write_set[i]]->tid) {
							rc = Abort;
							goto final;
						}	
					}	
					for (int i = 0; i < row_cnt - wr_cnt; i ++) {
						Access * access = accesses[ read_set[i] ];
						if (access->orig_row->manager->get_tid() != accesses[read_set[i]]->tid) {
							rc = Abort;
							goto final;
						}
					}
				}
                PAUSE
			}
		}
	} else {
		// Transactions wait when the required row is currently locked by other transactions.
		for (int i = 0; i < wr_cnt; i++) {
			row_t * row = accesses[ write_set[i] ]->orig_row;
			row->manager->lock();
			num_locks++;
			if (row->manager->get_tid() != accesses[write_set[i]]->tid) {
				rc = Abort;
				goto final;
			}
		}
	}

	// Validate rows in the read set.
	// For repeatable_read, no need to validate the read set.
	for (int i = 0; i < row_cnt - wr_cnt; i ++) {
		Access * access = accesses[ read_set[i] ];
		bool success = access->orig_row->manager->validate(access->tid, false);
		if (!success) {
			rc = Abort;
			goto final;
		}
		if (access->tid > max_tid)
			max_tid = access->tid;
	}

	// Validate rows in the write set.
	for (int i = 0; i < wr_cnt; i ++) {
		Access * access = accesses[ write_set[i] ];
		bool success = access->orig_row->manager->validate(access->tid, true);
		if (!success) {
			rc = Abort;
			goto final;
		}
		if (access->tid > max_tid)
			max_tid = access->tid;
	}

	// _cur_tid is the tid of the last transaction of the thread. If max_tid is bigger
	// than _cur_tid, _cur_tid needs to be advanced. Otherwise, just increment _cur_tid
	// to distinguish it from the last transaction.
	if (max_tid > _cur_tid)
		_cur_tid = max_tid + 1;
	else 
		_cur_tid ++;

final:
	if (rc == Abort) {
		for (int i = 0; i < num_locks; i++) 
			accesses[ write_set[i] ]->orig_row->manager->release();
		cleanup(rc);
	} else {
		for (int i = 0; i < wr_cnt; i++) {
			Access * access = accesses[ write_set[i] ];
			access->orig_row->manager->write( access->data, _cur_tid );
			accesses[ write_set[i] ]->orig_row->manager->release();
		}
		cleanup(rc);
	}
	return rc;
}
#endif
