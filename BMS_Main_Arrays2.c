#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#define num_accounts 25

// A data structure to dynamically and in O(1) time manage unique 7 digit account numbers with efficient recovery from deleted accounts
// Based on a linked list implementation
struct AccountNumber {
	long account_number;
	int active;
	struct AccountNumber* next_account_number;
	struct AccountNumber* prev_account_number;
};

struct AccountRecord {
	char* name;
	double balance;
	long account_number;
};

// Set of global variables that make up the model of the BMS. Can be pseudo-encapsulated by a struct, but it would
// require either creating a global struct, or passing the same struct pointer to every function, this is a simpler
// solution, but understandably not best practice
long record_space = 1;
long records = 0;
double account_balances = 0;
struct AccountRecord **accounts;
struct AccountNumber *root_account_number;
struct AccountNumber *open_account_number;

// reachability in linked lists
/*@ inductive reachable{A}(struct AccountNumber *root, struct AccountNumber *to) {
 	 @ case empty{A}: \forall struct AccountNumber *l; reachable(l,l) ;
 	 @ case non_empty{A}: \forall struct AccountNumber *l1,*l2;
 	 @ \valid (l1) && reachable(l1->next_account_number,l2) ==> reachable(l1,l2) ;
 	 @ }
 */

/*@ requires reachable(an,\null);
  @ assigns { an->active | struct AccountNumber *an ; reachable(an, an->next_account_number) } ;
  @*/
void incr_numbers(struct AccountNumber *an) {
	while (an) { an->account_number; an = an->next_account_number; }
}

// @ requires reachable(ar,\null);
// @
void incr_records(struct AccountRecord *ar) {
	//while (ar) { ar->account_number; ar = ar->account_number->next_account_number; }
}
//   @ assigns { q->active | struct AccountRecord *q ; reachable(p,q) } ;



// Engine for the AccountNumber struct which manages the creation, deletion, and assignment of unique
// account numbers used to access each account owner's account information
/*@ requires \true;
  @ ensures \result > 0;
  @ ensures \result == open_account_number->account_number;
  @*/
long assign_account_number(){
	long account_number = open_account_number->account_number;
	struct AccountNumber *current = open_account_number;
	current->active = 1;

	/*@ loop invariant current != NULL;
	  @ loop assigns open_account_number;
	  @*/
	while(current != NULL){
		if(current->active == 0){
			open_account_number = current;
		}else if(current->next_account_number == NULL){
			struct AccountNumber* new_account_number = malloc(sizeof(*new_account_number));
			new_account_number->account_number = current->account_number+1;
			new_account_number->active = 0;
			current->next_account_number = new_account_number;
			new_account_number->prev_account_number = current;
			new_account_number->next_account_number = NULL;
			open_account_number = new_account_number;
		}
		current = current->next_account_number;
	}

	return account_number;
}

// Deactivates an account number from a closed account, and waits to assign it to a newly opened account
/*@ requires _account_number > 0;
  @*/
void remove_account_number(long _account_number){
	struct AccountNumber* current = root_account_number;
	//ADD loop invariant with isReachable
	/*@ loop assigns current, current->account_number, current->active;
	 */
	while(current != NULL){
		if(current->account_number == _account_number){
			current->active = 0;
			open_account_number = current;
			break;
		}
		current = current->next_account_number;
		//comment @ assert \pre(current->account_number) != \Here(current->account_number);
	}
}
/*@ requires \true;
  @ assigns accounts;
  @*/
void expand_accounts(){
	record_space = (record_space+1)*2;

	struct AccountRecord **new_accounts = malloc(sizeof(*new_accounts)*record_space);

	/*@ loop invariant 0<=i<=records;
	  @ loop assigns i, new_accounts[i];
	  @*/
	for(int i = 0; i < records; i++)
		new_accounts[i] = accounts[i];

	free(accounts);

	accounts = new_accounts;
}

void open_account(char* _name, double opening_balance){
	struct AccountRecord* new_record = malloc(sizeof(*new_record));
	new_record->name = _name;
	new_record->balance = opening_balance;
	new_record->account_number = assign_account_number();

	accounts[records] = new_record;

	records++;
	account_balances+=opening_balance;

	if(records == record_space)
		expand_accounts();
}

/*@ requires i> 0;
  @*/
void push_back(int i){
  /*@ loop invariant 0<=j<=records;
    @ loop assigns accounts[j-i];
    @*/
	for(int j = i; j < records; j++){
		accounts[j-1] = accounts[j];
	}
}

// Finds the account associated with the account number and deletes its information as well
// as subtracting the account balance out of the total bank balance. Time is a slower O(n)
// due to the intitial search for the correct account number. Pointer is also freed to prevent
// memory leaks
int close_account(long _account_number){
	int i;
	int found = 0;
	/*@ loop invariant 0<=records<=i;
	  @ loop assigns accounts[i]->account_number;
	  @*/
	for(i = 0; i < records; i++){
		if(accounts[i]->account_number == _account_number){
			account_balances-=accounts[i]->balance;
			remove_account_number(accounts[i]->account_number);
			free(accounts[i]);
			push_back(i+1);
			records--;
			accounts[records] = NULL;
			found = 1;
			break;
		}
	}

	return found;
}

// Finds the account number of the account owner with the specified name, case sensitive.
// If the system doesn't contain a person with the specified name, it will return -1
long find_account_number(char* _name){
	for(int i = 0; i < records; i++){
		if(accounts[i]->name == _name)
			return accounts[i]->account_number;
	}
	return -1;
}

// Deposits the specified amount into correct account. Returns a 0 if the account
// number doesn't exist or the information doesn't match so money isn't wrongfully
// deposited. Returns a 1 if the transaction was successful
/*@ requires \valid(_name);
  @ requires _account_number > 0;
  @ requires deposit > 0;
  @ ensures 0<= \result <= 1;
  @*/
int deposit(char* _name, long _account_number, double deposit){
  /*@ loop invariant 0<=i<=records;
    @ loop assigns accounts[i]->balance, account_balances;
    @*/
	for(int i = 0; i < records; i++){
		if(accounts[i]->account_number == _account_number && accounts[i]->name == _name){
			accounts[i]->balance+=deposit;
			account_balances+=deposit;
			return 1;
		}
	}
	return 0;
}

// Finds the correct account and validates the withdrawal. If it is accepted, it withdraws the amount
// from the account's balance as well as the bank's total balance. If the account isn't found, the
// account information doesn't match, or the withdraw will overdraft the account, it'll return a 0,
// otherwise it'll return 1 for a successful transaction
/*@ requires \valid(_name);
  @ requires _account_number > 0 && withdrawal > 0;
  @*/
int withdrawal(char* _name, long _account_number, double withdrawal){
	/*@ loop invariant 0<=i<=records;
	  @ loop assigns i, account_balances;
	  @ loop variant records-i;
	  @*/
	for(int i = 0; i < records; i++){
		if(accounts[i]->account_number == _account_number && accounts[i]->name == _name && accounts[i]->balance > withdrawal){
			accounts[i]->balance-=withdrawal;
			account_balances-=withdrawal;
			return 1;
		}
	}
	return 0;
}

// Tries to withdraw the amount from the sender. If successful, it attempts to deposit it in the receiver account.
// If this doesn't work, the money is deposited back into the sender's account. A 0 is returned if the withdraw
// or the deposit fail for any of the reasons already mentioned above, otherwise it'll return a 1
/*@ requires \valid(sender_name) && \valid(receiver_name);
  @*/
int transfer_from_to(char* sender_name, long sender_account_number, char* receiver_name, long receiver_account_number, double transfer_amount){
	int withdraw_approved = withdrawal(sender_name, sender_account_number, transfer_amount);
	int deposit_approved = 0;

	if(withdraw_approved == 1)
		deposit_approved = deposit(receiver_name, receiver_account_number, transfer_amount);

	if(withdraw_approved == 1 && deposit_approved == 0)
		deposit(sender_name, sender_account_number, transfer_amount);

	return deposit_approved;
}

// Returns the global variable counting the total number of accounts or the size
// of the linked list
/*@ requires \true;
  @ assigns \nothing;
  @ ensures \result >= 0;
  @*/
long total_accounts(){
	return records;
}

// Returns the global variable keeping track of the total balance of all the accounts
/*@ requires \true;
  @ assigns \nothing;
  @ ensures \result >= 0;
  @*/
double total_balance(){
	return account_balances;
}

//Given an interest rate and an amount of time, updates the account balance to reflect the new rate over time
//Interest is calculated yearly (ie. 5% yearly for 1 year)
/*@ requires 0<= interest <= 1;
  @ requires 0<time;
  @*/
void add_interest(long _account_number, double interest, int time){
	/*@ loop invariant 0<=i<=records;
	  @ loop assigns accounts[i]->balance;
	  @ loop variant records-i;
	  @*/
	for(int i=0; i<records; i++){
		if(accounts[i]->account_number == _account_number){
			accounts[i]->balance = (accounts[i]->balance) * (1+interest*time);
		}
	}
}
//	  @ loop invariant \forall int j; 0<=j<i => accounts[j]->account_number != _account_number;
//	  @ loop invariant \forall int k; 0<=k<i => \Pre(accounts[k]->balance) == \Here(at(accounts[k]->balance));

int main(int argc, const char * argv[]) {
	start_system();

	open_account("Tom", 1000);
	open_account("Tommy", 50);
	open_account("Tam", 826);
	open_account("Tammy", 3);

	assert(find_account_number("Tammy") == 1000003);
	assert(total_accounts() == 4);
	assert(close_account(find_account_number("Tommy")) == 1);
	assert(find_account_number("Tommy") == -1);
	assert(total_accounts() == 3);
	assert(withdrawal("Tom", find_account_number("Tom"), 200) == 1);
	assert(total_balance() == (1000+826+3-200));
	assert(transfer_from_to("Tom", find_account_number("Tom"), "Tammy", find_account_number("Tammy"), 9000.50) == 0);
	assert(transfer_from_to("Tom", find_account_number("Tom"), "Tammy", find_account_number("Tammy"), 300) == 1);

	return 0;
}
