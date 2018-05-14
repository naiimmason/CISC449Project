#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

struct AccountRecord {
    char* name;
    double balance;
    long account_number;
};

// Set of global variables that make up the model of the BMS. Can be pseudo-encapsulated by a struct, but it would
// require either creating a global struct, or passing the same struct pointer to every function, this is a simpler
// solution, but understandably not best practice
long record_space = 0;
long records = 0;
double account_balances = 0;
long open_account_number = 1000000;
struct AccountRecord *accounts;

void expand_accounts(){
    record_space = (record_space+1)*2;
    
    struct AccountRecord *account_array = malloc(sizeof(account_array)*record_space);
    
    for(long i = 0; i < records; i++){
        account_array[i] = accounts[i];
    }
    
    for(long i = records; i < record_space; i++){
        struct AccountRecord prim_account = {"", 0, 0};
        account_array[i] = prim_account;
    }
    
    if(accounts != NULL)
        free(accounts);
    
    accounts = account_array;
}

void open_account(char* _name, double opening_balance){
    if(records == record_space)
        expand_accounts();
    
    accounts[records].name = _name;
    accounts[records].balance = opening_balance;
    accounts[records].account_number = open_account_number;

    open_account_number++;
    records++;
    account_balances+=opening_balance;
}

void push_back(int i){
    for(int j = i; j < records; j++){
        accounts[j-1] = accounts[j];
    }
}

// Finds the account associated with the account number and deletes its information as well
// as subtracting the account balance out of the total bank balance. Time is a slower O(n)
// due to the intital search for the correct account number. Pointer is also freed to prevent
// memory leaks
int close_account(long _account_number){
    int i;
    int found = 0;
    
    for(i = 0; i < records; i++){
        if(accounts[i].account_number == _account_number){
            account_balances-=accounts[i].balance;
            push_back(i+1);
            records--;
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
        if(accounts[i].name == _name)
            return accounts[i].account_number;
    }
    return -1;
}

// Deposits the specified amount into correct account. Returns a 0 if the account
// number doesn't exist or the information doesn't match so money isn't wrongfully
// deposited. Returns a 1 if the transaction was successful
int deposit(char* _name, long _account_number, double deposit){
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
int withdrawal(char* _name, long _account_number, double withdrawal){
    for(int i = 0; i < records; i++){
        if(accounts[i].account_number == _account_number && accounts[i].name == _name && accounts[i].balance > withdrawal){
            accounts[i].balance-=withdrawal;
            account_balances-=withdrawal;
            return 1;
        }
    }
    return 0;
}

// Tries to withdraw the amount from the sender. If successful, it attempts to deposit it in the receiver account.
// If this doesn't work, the money is deposited back into the sender's account. A 0 is returned if the withdraw
// or the deposit fail for any of the reasons already mentioned above, otherwise it'll return a 1
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
long total_accounts(){
    return records;
}

// Returns the global variable keeping track of the total balance of all the accounts
double total_balance(){
    return account_balances;
}

// Still working on this
void add_interest(long _account_number, double interest, int time, int period){
    
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