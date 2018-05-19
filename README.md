# CISC449Project
Mini-Project for CISC449
Naiim Mason and Monica Mooney

1. Project: Bank Management System

2. Structure:
For this project we utilized the following structs:
   AccountRecord

And the following functions:
    void expand_accounts();
    void open_account(char* _name, double opening_balance);
    void push_back(int i);
    void close_account(long _account_number);
    long find_account_number(char* _name);
    int deposit(char* _name, long _account_number, double deposit)
    int withdrawal(char* _name, long _account_number, double withdrawal)
    int transfer_from_to(char* sender_name, long sender_account_number, char* receiver_name, long receiver_account_number, double transfer_amount);
    long total_accounts();
    double total_balance();
    void add_interest(long _account_number, double interest, int time);

More documentation for each of these functions is included in our comments in BMS_Main_Arrays.c

3. Execution:
Any aspect of this project can be compiled with our included Makefile (make, make test, make verify)

4. Testing:
All of our testing of this project can be tested within our main function.
Calling "make test" will make the a.out file to execute the main tests. 

5. Specifications:
We employed the use of several predicates and Frama-C to verify our project.
To view our verifications "make verify"

6. Proved:
We were able to successfully prove 69/82 of our goals.

For each function we were able to successfully verify:
    pre-conditions, post-conditions, and assignments

Within loops in these functions we verified:
       loop invariants, loop variants, any loop assignments and other loop actions.

7. Did Not Prove:
We were not able to prove details of functions involving allocation/deallocation (malloc and free) 
We also ran into 2 specific timeout errors (add_interest loop invariant l1 and push_back loop assigns (part2)):
  With further review we believe that both of these errors have been resolved but frama-c has not recognized that

