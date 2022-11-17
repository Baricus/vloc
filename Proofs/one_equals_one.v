Require Import Vloc.Lib.theory.

Require Import Vloc.CCode.ret_one.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

#[local] Instance one_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

Definition refines f2 A : funspec :=
  WITH gv: globals, ctx: ref_id
  PRE [ (* types of function parameters *) ]
    PROP()
    PARAMS((* NOTE: how to handle parameters *))
    GLOBALS((* do we need anything to correlate globals and Context? Hopefully not *))
    SEP(refines_right ctx f2)
  POST [ tint ] (* NOTE: type!!! A map of iris types to vst types? *)
    EX v' : ival, EX v : val,
    PROP()
    RETURN(v)
    SEP(refines_right ctx (ectxi_language.of_val v') * A v v').


(* I shouldn't have to do this, I think *)

Definition ret_one : iexp := Val (LitV (heap_lang.LitInt 1%Z)).
(*NOTE: diff between ectxi language and ectx language?*)
Definition fspec := DECLARE _returns_one refines ret_one 
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z))&&emp)%logic.
Definition Gprog : funspecs := [fspec].

Lemma one: semax_body Vprog Gprog f_returns_one fspec.
Proof.
  unfold fspec, refines, refines.
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

Lemma one_plus_zero : semax_body Vprog Gprog f_returns_one (DECLARE _returns_one refines ret_one_plus
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic).
Proof.
  unfold fspec, refines, refines.
  start_function.
  step_pure_r ctx.
  forward.
  Exists (LitV (heap_lang.LitInt 1%Z)).
  Exists (Vint (Int.repr 1)).
  entailer!; eauto.
  apply derives_refl.
Qed.

Definition ret_one_min_plus : iexp := BinOp PlusOp 
  (BinOp MinusOp (Val (LitV (heap_lang.LitInt 1%Z)))  (Val (LitV (heap_lang.LitInt (-1)%Z))))
  (Val (LitV (heap_lang.LitInt (-1)%Z))).

Lemma one_plus_zero' : semax_body Vprog Gprog f_returns_one (DECLARE _returns_one refines ret_one_min_plus
  (fun vVST vHL => !! (exists n : Z, vVST = Vint (Int.repr n) /\ vHL = LitV (heap_lang.LitInt n%Z)) && emp)%logic).
Proof.
  unfold fspec, refines, refines.
  start_function.
  Fail step_pure_r ctx.
  unfold ret_one_min_plus.
  step_pure_r ctx.
  step_pure_r ctx.
  forward.

  (* fun with seeing evars to see if this is nicer *)
  evar (a : ival).
  Exists a.
  evar (b : val).
  Exists b.
  entailer!.
  - split; eauto.
    subst b; auto.
  - subst a; apply derives_refl.
Qed.
