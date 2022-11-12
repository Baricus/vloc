Require Import Vloc.Lib.theory.

Require Import Vloc.CCode.ret_one.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.



(* I shouldn't have to do this, I think *)
Definition refines_heap_lang e A : funspec := refines  (gName := theory.gName) (nspace:= theory.nspace) e A.

Definition ret_one : iexp := Val (LitV (heap_lang.LitInt 1%Z)).
(*NOTE: diff between ectxi language and ectx language?*)
Definition fspec := DECLARE _returns_one refines_heap_lang ret_one 
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z))&&emp)%logic.
Definition Gprog : funspecs := [fspec].

Lemma one: semax_body Vprog Gprog f_returns_one fspec.
Proof.
  unfold fspec, refines_heap_lang, refines.
  start_function.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
  unfold ret_one.
  simpl.
  cancel.
Qed.
  

Definition ret_one_plus : iexp := BinOp PlusOp (Val (LitV (heap_lang.LitInt 1%Z))) (Val (LitV (heap_lang.LitInt 0%Z))).

Lemma one_plus_zero : semax_body Vprog Gprog f_returns_one (DECLARE _returns_one refines_heap_lang ret_one_plus
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic).
Proof.
  unfold fspec, refines_heap_lang, refines.
  start_function.
  unfold ret_one_plus.
  step_pure_r ctx.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
  apply derives_refl.
Qed.

Definition ret_one_min_plus : iexp := BinOp PlusOp 
  (BinOp MinusOp (Val (LitV (heap_lang.LitInt 1%Z)))  (Val (LitV (heap_lang.LitInt 1%Z))))
  (Val (LitV (heap_lang.LitInt 0%Z))).

Lemma one_plus_zero' : semax_body Vprog Gprog f_returns_one (DECLARE _returns_one refines_heap_lang ret_one_min_plus
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic).
Proof.
  unfold fspec, refines_heap_lang, refines.
  start_function.
  Fail step_pure_r ctx.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
Admitted.
