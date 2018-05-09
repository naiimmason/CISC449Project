
#FC=frama-c -wp -cpp-command 'gcc -C -E -I.. -I.' -cpp-frama-c-compliant
FC=frama-c-gui -wp -cpp-command 'gcc -C -E -I.. -I.' -cpp-frama-c-compliant

CountLogic : CountLogic.h
	$(FC) CountLogic.h

CountLemmas: CountLemmas.h CountLogic.h CountSectionLemmas.h
	$(FC) CountLemmas.h



LessThanComparable : LessThanComparable.h
	$(FC) LessThanComparable.h

LessAndOtherRelations: LessAndOtherRelations.h
	$(FC) LessAndOtherRelations.h

ShiftLemmas: ShiftLemmas.h
	$(FC) ShiftLemmas.h
