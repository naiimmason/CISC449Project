/*
 * bank.c
 *
 *  Created on: May 4, 2018
 *      Author: Naiim and Monica
 */

#include "bank.h"

typedef struct{
	int account_num;
	char owner_name[];
	double balance;
	double interest_val;
}Account;



typedef struct{
	Account bank_accounts[];
}Bank;

int createAccountNumber(){
	//generate an account number between 0-1000
	int randnum = rand() % (1000 + 1 - 0);
	return randnum;
}

void newAccount(char name[], double init_balance){
	Account *newAccount = malloc(sizeof(Account));
	newAccount->account_num = createAccountNumber();
	newAccount->owner_name = name;
	newAccount->balance = init_balance;
	newAccount->interest_val = 0;
}
