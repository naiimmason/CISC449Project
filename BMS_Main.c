#include <stdio.h>
#include <stdlib.h>
#include <time.h>

// A data structure to dynamically and in O(1) time manage unique 7 digit account numbers with efficient recovery from deleted accounts
// Based on a linked list implementation
struct AccountNumber {
    long account_number;
    int active;
    struct AccountNumber* next_account_number;
    struct AccountNumber* prev_account_number;
};

// Accounts could be stored in an array, but used linked lists because it makes memory management easier
// as arrays have to be resized once their pre-set limit is reached. Linked lists allow for O(1) insert and
// delete, but O(n) for search. An array could get better performance there with a binary search, but I'm not
// sure the resizing is worth it
struct AccountRecord {
    char* name;
    double balance;
    long account_number;
    struct AccountRecord* next_record;
    struct AccountRecord* prev_record;
};

// Set of global variables that make up the model of the BMS. Can be pseudo-encapsulated by a struct, but it would
// require either creating a global struct, or passing the same struct pointer to every function, this is a simpler
// solution, but understandably not best practice
long records;
double account_balances;
struct AccountRecord* root_record;
struct AccountNumber* root_account_number;
struct AccountNumber* open_account_number;

// Initializes the variables of the BMS to allow us to begin manipulating account data
void start_system(){
    records = 0;
    account_balances = 0;
    root_record = NULL;
    root_account_number = malloc(sizeof(struct AccountNumber*));
    root_account_number->account_number = 1000000;
    root_account_number->active = 0;
    root_account_number->prev_account_number = NULL;
    root_account_number->next_account_number = NULL;
    open_account_number = root_account_number;
}

// Engine for the AccountNumber struct which manages the creation, deletion, and assignment of unique
// account numbers used to access each account owner's account information
long assign_account_number(){
    long account_number = open_account_number->account_number;
    struct AccountNumber* current = open_account_number;
    current->active = 1;
    
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

// Inactivates an account number from a closed account, and waits to assign it to a newly opened account
void remove_account_number(long _account_number){
    struct AccountNumber* current = root_account_number;
    
    while(current != NULL){
        if(current->account_number == _account_number){
            current->active = 0;
            open_account_number = current;
            break;
        }
        current = current->next_account_number;
    }
}

// Creates a new record with the account owner's name and their opening balance
// Places the new record at the beginning of the linked list and slides everything else down
// in O(1)
void open_account(char* _name, double opening_balance){
    struct AccountRecord* new_record = malloc(sizeof(*new_record));
    new_record->name = _name;
    new_record->balance = opening_balance;
    new_record->prev_record = NULL;
    new_record->account_number = assign_account_number();
    
    records++;
    account_balances+=opening_balance;
    
    if(root_record == NULL){
        new_record->next_record = NULL;
    }else{
        new_record->next_record = root_record;
        root_record->prev_record = new_record;
    }
    root_record = new_record;
}

// Finds the account associated with the account number and deletes its information as well
// as subtracting the account balance out of the total bank balance. Time is a slower O(n)
// due to the intital search for the correct account number. Pointer is also freed to prevent
// memory leaks
void close_account(long _account_number){
    struct AccountRecord* record = root_record;
    
    while(record != NULL){
        if(record->account_number == _account_number)
            break;
        record = record->next_record;
    }
    
    if(record != NULL){
        records--;
        account_balances-=record->balance;
        remove_account_number(record->account_number);
        
        if(record->prev_record == NULL && record->next_record == NULL){
            root_record = NULL;
        }else if(record->prev_record == NULL){
            root_record = record->next_record;
            record->next_record->prev_record = NULL;
        }else if(record->next_record == NULL){
            record->prev_record->next_record = NULL;
        }else{
            record->prev_record->next_record = record->next_record;
            record->next_record->prev_record = record->prev_record;
        }
    }
    
    free(record);
}

// Finds the account number of the account owner with the specified name, case sensitive.
// If the system doesn't contain a person with the specified name, it will return -1
long find_account_number(char* _name){
    struct AccountRecord* record = root_record;
    
    while(record != NULL){
        if(record->name == _name)
            return record->account_number;
        record = record->next_record;
    }
    
    return -1;
}

// Deposits the specified amount into correct account. Returns a 0 if the account
// number doesn't exist or the information doesn't match so money isn't wrongfully
// deposited. Returns a 1 if the transaction was successful
int deposit(char* _name, long _account_number, double deposit){
    struct AccountRecord* record = root_record;
    int found = 0;
    
    while(record != NULL){
        if(record->account_number == _account_number && record->name == _name){
            record->balance+=deposit;
            account_balances+=deposit;
            found = 1;
            break;
        }
        record = record->next_record;
    }
    
    return found;
}

// Finds the correct account and validates the withdrawal. If it is accepted, it withdraws the amount
// from the account's balance as well as the bank's total balance. If the account isn't found, the
// account information doesn't match, or the withdraw will overdraft the account, it'll return a 0,
// otherwise it'll return 1 for a successful transaction
int withdrawal(char* _name, long _account_number, double withdrawal){
    struct AccountRecord* record = root_record;
    int withdraw_approved = 0;
    
    while(record != NULL){
        if(record->account_number == _account_number && record->name == _name && record->balance > withdrawal){
            record->balance-=withdrawal;
            account_balances-=withdrawal;
            withdraw_approved = 1;
            break;
        }
        record = record->next_record;
    }
    
    return withdraw_approved;
}

// Tries to withdraw the amount from the sender. If successful, it attempts to deposit it in the receiver account.
// If this doesn't work, the money is deposited back into the sender's account. A 0 is returned if the withdraw
// or the deposit fail for any of the reasons already mentioned above, otherwise it'll return a 1
int transfer(char* sender_name, long sender_account_number, char* receiver_name, long receiver_account_number, double transfer_amount){
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
    start_system();
    
    open_account("Tom", 1000);
    open_account("Tommy", 50);
    open_account("Tam", 826);
    open_account("Tammy", 3);
    
    printf("%ld \n", find_account_number("Tommy"));
    
    close_account(find_account_number("Tommy"));
    
    transfer("Tom", find_account_number("Tom"), "Tammy", find_account_number("Tammy"), 9000.50);
    
    printf("%ld \n", find_account_number("Tommy"));
    
    printf("Hello, World!\n");
    return 0;
}