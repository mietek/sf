Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Ltac verif_stack_free_hint1 :=
match goal with
|- semax ?D (PROPx _ (LOCALx ?Q (SEPx ?R)))
            (Ssequence
                 (Scall _ (Evar ?free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
                 (Etempvar ?i _ :: _)) _) _ =>
  match Q with context [temp i ?q] =>
   match R with context [data_at _ ?t _ q] =>
       unify ((glob_specs D) ! free) (Some library.free_spec');
       idtac "When doing forward_call through this call to" free
  "you need to supply a WITH-witness of type (type*val*globals) and you need to supply a proof that"
   q "<>nullval.  Look in your SEP clauses for 'data_at _" t "_" q"', which will be useful for both."
"Regarding the proof, assert_PROP(...) will make use of the fact that data_at cannot be a nullval."
"Regarding the witness, you should look at the funspec declared for" free
"to see what will be needed; look in Verif_stack.v at free_spec_example."
"But in particular, for the type, you can use the second argument of the data_at, that is," t
".";
  match goal with a : globals |- _ =>
    idtac "Regarding the 'globals', you have" a ": globals above the line."
   end
  end end
end.

Ltac verif_stack_malloc_hint1_aux D R c :=
  match c with
  | Ssequence ?c1 _ => verif_stack_malloc_hint1_aux D R c1
  | Scall _ (Evar ?malloc
                 (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
                (cons (Esizeof ?t _) nil) =>
      match R with context [mem_mgr ?gv] =>
          idtac "try  'forward_call (" t "," gv ")'"
     end
  end.

Ltac verif_stack_malloc_hint1 :=
match goal with |- semax ?D (PROPx _ (LOCALx _ (SEPx ?R))) ?c _ =>
     verif_stack_malloc_hint1_aux D R c
end.

Ltac vc_special_hint :=
  first
    [ verif_stack_free_hint1
    | verif_stack_malloc_hint1
    ];
  idtac "THAT WAS NOT A STANDARD VST HINT, IT IS SPECIAL FOR THE VC VOLUME OF SOFTWARE FOUNDATIONS."
  "STANDARD VST HINTS WOULD BE AS FOLLOWS:
".

Ltac hint_special ::=  try vc_special_hint.

(* 2020-09-18 15:39 *)
