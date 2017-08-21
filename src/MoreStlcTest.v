Require Import MoreStlc.
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

Require Import MoreStlc.
Import Check.

Require Import Maps.
Require Import Types.
Require Import Smallstep.
Require Import Stlc.
Goal True.
idtac "Entering exercise STLC_extensions (standard): 5 points".
idtac " ".
Abort.

Module TestSTLCExtended.
Import STLCExtended.
Module TestExamples.
Import Examples.
Module TestNumtest.
Import Numtest.
End TestNumtest.
Module TestProdtest.
Import Prodtest.
End TestProdtest.
Module TestLetTest.
Import LetTest.
End TestLetTest.
Module TestSumtest1.
Import Sumtest1.
End TestSumtest1.
Module TestSumtest2.
Import Sumtest2.
End TestSumtest2.
Module TestListTest.
Import ListTest.
End TestListTest.
Module TestFixTest1.
Import FixTest1.
End TestFixTest1.
Module TestFixTest2.
Import FixTest2.
End TestFixTest2.
Module TestFixTest3.
Import FixTest3.
End TestFixTest3.
Module TestFixTest4.
Import FixTest4.
End TestFixTest4.
End TestExamples.
End TestSTLCExtended.
Goal True.
idtac "Exiting exercise (STLC_extensions)".
idtac " ".

idtac "Max points - regular: 5".
idtac "Max points - advanced: 5".
Abort.
