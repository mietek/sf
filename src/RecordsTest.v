Require Import Records.
Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be " B]
end.

Ltac check_exists A :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => idtac "Is present."; idtac "Check type:" T
end.
End Check.

Require Import Records.
Import Check.

Require Import Maps.
Require Import Imp.
Require Import Smallstep.
Require Import Stlc.
Module TestSTLCExtendedRecords.
Import STLCExtendedRecords.
Module TestFirstTry.
Import FirstTry.
End TestFirstTry.
Goal True.
idtac "Entering exercise examples (standard): 2 points".
Abort.
Import STLCExtendedRecords.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_example_2".
check_type @STLCExtendedRecords.typing_example_2 (empty |-(tapp(tabs a(TRCons i1(TArrow A A)(TRCons i2(TArrow B B)TRNil))(tproj(tvar a)i2))(trcons i1(tabs a A(tvar a))(trcons i2(tabs a B(tvar a))trnil)))\in(TArrow B B)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_example_2.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample".
check_type @STLCExtendedRecords.typing_nonexample (~ exists T, (update empty a(TRCons i2(TArrow A A)TRNil))|-(trcons i1(tabs a B(tvar a))(tvar a))\in T).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample_2".
check_type @STLCExtendedRecords.typing_nonexample_2 (forall y, ~ exists T, (update empty y A)|-(tapp(tabs a(TRCons i1 A TRNil)(tproj(tvar a)i1))(trcons i1(tvar y)(trcons i2(tvar y)trnil)))\in T).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
Goal True.
idtac " ".

idtac "Exiting exercise (examples)".
idtac " ".
Abort.

End TestSTLCExtendedRecords.
Goal True.
idtac "Max points - regular: 2".
idtac "Max points - advanced: 2".
Abort.
