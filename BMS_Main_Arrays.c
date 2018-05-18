#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct _AccountRecord {
    char* name;
    double balance;
    long account_number;
} AccountRecord;

// Set of global variables that make up the model of the BMS. Can be pseudo-encapsulated by a struct, but it would
// require either creating a global struct, or passing the same struct pointer to every function, this is a simpler
// solution, but understandably not best practice
long record_space = 0;
long records = 0;
double account_balances = 0;
long open_account_number = 1000000;
AccountRecord *accounts;

/*@ 
  predicate 
    Unchanged_Balance{K,L}(AccountRecord* a, integer m, integer n) =
      \forall integer l; m <= l < n ==> \at(a[l].balance,K) == \at(a[l].balance,L);

  predicate
    Equal_Values{K}(AccountRecord* a, AccountRecord* b, integer m, integer n) =
      \forall integer l; m <= l < n ==> \at(a[l],K) == \at(b[l],K);

  predicate
    Account_Exists(AccountRecord* a, integer m, integer n, long _account_number, char* _name) =
      \exists integer k; m<=k<n && (a[k].account_number == _account_number && a[k].name == _name);

  predicate
    Account_Name_Exists(AccountRecord* a, integer m, integer n, char* _name) =
      \exists integer k; m<=k<n && (a[k].name == _name);

  predicate
    Account_Number_Exists(AccountRecord* a, integer m, integer n, long _account_number) =
      \exists integer k; m<=k<n && (a[k].account_number == _account_number);

  predicate
    Account_Does_Not_Exist(AccountRecord *a, integer m, integer n, long _account_number, char* _name) =
      \forall integer k; m<=k<n ==> (a[k].account_number != _account_number || a[k].name != _name);

  predicate
    Account_Name_Does_Not_Exist(AccountRecord *a, integer m, integer n, char* _name) =
      \forall integer k; m<=k<n ==> (a[k].name != _name);
  
  predicate
    Account_Number_Does_Not_Exist(AccountRecord *a, integer m, integer n, long _account_number) =
      \forall integer k; m<=k<n ==> (a[k].account_number != _account_number);
*/

/*@ requires \true;
  @ behavior accounts_null:
  @   assumes accounts != NULL;
  @   requires \valid(accounts);
  @ behavior accounts_not_null:
  @   assumes accounts == NULL;
  @   requires \valid(accounts);
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void expand_accounts(){
  record_space = (record_space+1)*2;
  //@ assert record_space == 2*(record_space+1);

    AccountRecord *account_array = malloc(sizeof(account_array)*record_space);

    /*@ loop invariant 0<=i<=records;
      @ loop invariant equal_vals: Equal_Values{Here}(accounts, account_array, 0, i);
      @ loop invariant equal_vals2: Equal_Values{Here}(account_array, accounts, 0, i);
      @ loop assigns i;
      @ loop variant records-i;
      @*/
    //loop invariant equal: EqualRanges{Pre, Here}(account_array, i, accounts);
    //loop invariant equal: EqualRanges{Pre, Here}(accounts, i, account_array);
    //loop invariant unchanged: {Pre, Here}(account_array, i, n);
    //loop invariant unchanged: {Pre, Here}(accounts, i, n);
    for(int i = 0; i < records; i++){
        account_array[i] = accounts[i];
    }
    
    /*@ loop invariant records<=i<=record_space;
      @ loop invariant \forall integer k; records<=k<i ==> account_array[k].name == "";
      @ loop invariant \forall integer k; records<=k<i ==> account_array[k].balance == 0;
      @ loop invariant \forall integer k; records<=k<i ==> account_array[k].account_number == 0;
      @ loop assigns i, account_array[i];
      @ loop variant record_space-i;
      @*/
    for(long i = records; i < record_space; i++){
        AccountRecord prim_account = {"", 0, 0};
        account_array[i] = prim_account;
    }
    
    if(accounts != NULL)
        free(accounts);
    
    accounts = account_array;
    //@ assert accounts == account_array;
}

/*@ requires \valid(_name);
  @ requires opening_balance >= 0;
  @ ensures \at(open_account_number, Here) > \at(open_account_number, Old);
  @ ensures \at(records, Here) > \at(records, Old);
  @ ensures \at(account_balances, Here) == \at(account_balances, Pre) + opening_balance; 
  @*/
void open_account(char* _name, double opening_balance){
    if(records == record_space)
        expand_accounts();

    accounts[records].name = _name;
    accounts[records].balance = opening_balance;
    accounts[records].account_number = open_account_number;

    open_account_number++;
    records++;
    account_balances+=opening_balance;
    //@ assert open_account_number == open_account_number + 1;
    //@ assert open_account_number == 1000000 + records;
    //@ assert records == records + 1;
    //@ assert account_balances == account_balances + opening_balance;
}

/*@ requires i>=0;
  @ assigns \nothing;
  @ ensures \forall integer k; i<=k<records ==> \at(accounts[k], Here) == \at(accounts[k+1], Pre);
  @*/
void push_back(int i){
  /*@ loop invariant i<=j<=records;
    @ loop invariant \forall integer k; i<=k<j ==> \at(accounts[k], Here) == \at(accounts[k+1], Pre); 
    @ loop assigns j;
    @ loop variant records-j;
    @*/
    for(int j = i; j < records; j++){
        accounts[j-1] = accounts[j];
    }
}

// Finds the account associated with the account number and deletes its information as well
// as subtracting the account balance out of the total bank balance. Time is a slower O(n)
// due to the intital search for the correct account number. Pointer is also freed to prevent
// memory leaks

/*@ requires _account_number >= 0;
  @ behavior not_found:
  @  assumes Account_Number_Does_Not_Exist(accounts, 0, records, _account_number);
  @  ensures \at(account_balances, Here) == \at(account_balances, Pre);
  @  ensures \at(records, Here) == \at(records, Pre);
  @  ensures \result == 0;
  @ behavior found:
  @  assumes Account_Number_Exists(accounts, 0, records, _account_number);
  @  ensures \at(account_balances, Here) < \at(account_balances, Pre);
  @  ensures \at(records, Here) < \at(records, Pre);
  @  ensures \result == 1;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int close_account(long _account_number){
    int i;
    int found = 0;

    /*@ loop invariant 0<=i<=records;
      @ loop invariant Account_Number_Does_Not_Exist(accounts, 0, i, _account_number);
      @ loop assigns i, found, records, account_balances;
      @ loop variant records-i;
      @*/
    for(int i = 0; i < records; i++){
        if(accounts[i].account_number == _account_number){
            account_balances-=accounts[i].balance;
            push_back(i+1);
            records--;
            found = 1;
	    //@ assert account_balances == account_balances - accounts[i].balance;
	    //@ assert records == records-1;
        }
    }
    return found;
}

// Finds the account number of the account owner with the specified name, case sensitive.
// If the system doesn't contain a person with the specified name, it will return -1

/*@ requires \valid(_name);
  @ behavior account_number_found:
  @  assumes Account_Name_Exists(accounts, 0, records, _name);
  @  ensures \result > -1;
  @ behavior account_number_not_found:
  @  assumes Account_Name_Does_Not_Exist(accounts, 0, records, _name);
  @  ensures \result == -1;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
long find_account_number(char* _name){
  /*@ loop invariant 0<=i<=records;
    @ loop assigns i;
    @ loop variant records-i;
    @*/
    for(int i = 0; i < records; i++){
        if(accounts[i].name == _name)
            return accounts[i].account_number;
    }
    return -1;
}

// Deposits the specified amount into correct account. Returns a 0 if the account
// number doesn't exist or the information doesn't match so money isn't wrongfully
// deposited. Returns a 1 if the transaction was successful

/*@ requires \valid(_name);
  @ requires _account_number > 0 && deposit > 0;
  @ behavior error_condition:
  @  assumes Account_Does_Not_Exist(accounts, 0, records, _account_number, _name);
  @  ensures Unchanged_Balance{Pre, Here}(accounts, 0, records);
  @  ensures \result == 0;
  @ behavior successful:
  @  assumes Account_Exists(accounts, 0, records, _account_number, _name);
  @  ensures \exists integer i; \at(accounts[i].balance, Pre) < \at(accounts[i].balance, Here);
  @  ensures \result == 1;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int deposit(char* _name, long _account_number, double deposit){
  /*@ loop invariant 0<=i<=records;
    @ loop invariant \forall integer j; 0<=j<i ==> accounts[j].account_number != _account_number || accounts[j].name != _name;
    @ loop assigns i, account_balances;
    @*/
    for(int i = 0; i < records; i++){
        if(accounts[i].account_number == _account_number && accounts[i].name == _name){
            accounts[i].balance+=deposit;
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
  @ behavior error_condition_withdrawal:
  @   assumes Account_Does_Not_Exist(accounts, 0, records, _account_number, _name);
  @   ensures \result == 0;
  @ behavior successful:
  @   assumes Account_Exists(accounts, 0, records, _account_number, _name);
  @   ensures \result == 1;
  @*/
int withdrawal(char* _name, long _account_number, double withdrawal){
  /*@ loop invariant 0<=i<=records;
    @ loop assigns i, account_balances;
    @ loop variant records-i;
    @*/
    for(int i = 0; i < records; i++){
        if(accounts[i].account_number == _account_number && accounts[i].name == _name && accounts[i].balance >= withdrawal){
            accounts[i].balance-=withdrawal;
            account_balances-=withdrawal;
            return 1;
        }
    }
    return 0;
}
//TODO loop invariant that checks that balance >= withdrawal

// Tries to withdraw the amount from the sender. If successful, it attempts to deposit it in the receiver account.
// If this doesn't work, the money is deposited back into the sender's account. A 0 is returned if the withdraw
// or the deposit fail for any of the reasons already mentioned above, otherwise it'll return a 1

/* work in progress
 * @ behavior withdrawal_fail:
 * @ assumes 
 * @ behavior deposit_fail:
 * @ behavior withdrawal_success:
 * @ behavior deposit_success:
 * @ complete behaviors;
 */
/*@ requires \valid(sender_name) && \valid(receiver_name);
  @ requires sender_account_number > 0 && receiver_account_number > 0 && transfer_amount > 0;
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
  @ behavior account_found:
  @   assumes Account_Number_Exists(accounts, 0, records, _account_number);
  @   ensures \exists integer k; \at(accounts[k].balance, Here) != \at(accounts[k].balance, Pre);
  @   ensures \exists integer k; accounts[k].balance == accounts[k].balance * (1+interest*time);
  @ behavior account_not_found:
  @   assumes Account_Number_Does_Not_Exist(accounts, 0, records, _account_number);
  @   ensures Unchanged_Balance{Pre, Here}(accounts, 0, records);
  @*/
void add_interest(long _account_number, double interest, int time){
	/*@ loop invariant 0<=i<=records;
	  @ loop invariant Account_Number_Does_Not_Exist(accounts, 0, i, _account_number);
	  @ loop invariant Unchanged_Balance{Pre,Here}(accounts, 0, i);
	  @ loop assigns i;
	  @ loop variant records-i;
	  @*/
	for(int i=0; i<records; i++){
		if(accounts[i].account_number == _account_number){
			accounts[i].balance = (accounts[i].balance) * (1+interest*time);
			break;
		}
	}
}

int main(int argc, const char * argv[]) {
    open_account("Tom", 1000.0);
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
