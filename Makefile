
INC = -I/Logic -I.

FC = frama-c -wp -cpp-command 'gcc -C -E $(INC)' -cpp-frama-c-compliant \
     -wp-skip-fct main -kernel-msg-key pp
CC = cc $(INC)
NAME = BMS_Main_Arrays

verify: $(NAME).c
	$(FC) $(NAME).c

test: $(NAME).c
	$(CC) $(NAME).c
	./a.out

p : p.c
	$(FC) p.c
