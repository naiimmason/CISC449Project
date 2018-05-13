/*@ requires \valid(accnum_arr+(0..n-1));
  @ requires \valid(accrec_arr+(0..r-1));
  @ ensures \valid(\result);
  @ ensures \result->account_number >= 1000000;
  @ ensures \result->active == 0;
  @ ensures \valid(\result->prev_account_number);
  @ ensures \valid(\result->next_account_number);
  @*/
struct AccountRecord start_system(struct AccountNumber* accnum_arr, struct AccountRecord* accrec_arr, int n, int r){
	//accounts = malloc(sizeof(*accounts)*record_space);
	//root_account_number = malloc(sizeof(struct AccountNumber*));

	accounts = AccountRecord[n][r];
	root_account_number = accrec_arr[r];
	root_account_number->account_number = 1000000;
	root_account_number->active = 0;
	root_account_number->prev_account_number = NULL;
	root_account_number->next_account_number = NULL;
	open_account_number = root_account_number;

	return accounts;
}