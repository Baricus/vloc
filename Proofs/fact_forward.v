(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

(* used for our modulus *)
Import compcert.lib.Integers.
Import proofmode notation.

Definition factI : heap_lang.val :=
  rec: "factI" "n" :=
    if: "n" < #1 then #1 else ("n" * "factI" ("n" - #1)) `rem` #(Int.modulus)
    .

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.fact.

#[local] Instance fact_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Definition nat_relate vVST vHL :=
  ((exists (n : Z), (n >= 0)%Z /\ ((vVST = Vint (Int.repr n))%Z) /\ vHL = LitV (heap_lang.LitInt n%Z))).

Lemma nat_relate_n n :
  (n >= 0)%Z -> nat_relate (Vint (Int.repr n)) (LitV (heap_lang.LitInt n%Z)).
Proof.
  exists n; repeat split; auto.
Qed.

(* for simplicity, we're ignoring out of bounds errors here *)
Fixpoint fact n : nat :=
  match n with
  | O => 1
  | S (n') => n * (fact n')
  end.

(* here, the refines we had before won't work... *)
Definition fspec :=
  DECLARE _factorial
  WITH gv: globals, ctx: ref_id, n : int
  PRE [ tuint ]
    PROP()
    PARAMS(Vint n)
    GLOBALS()
    SEP(refines_right ctx (App (Val iris.factI) (Val (LitV (LitInt (Int.unsigned n))))))
  POST [ tuint ] 
    EX v' : ival, EX v : val,
    PROP(nat_relate v v')
    RETURN(v)
    SEP((refines_right ctx (ectxi_language.of_val v'))).

Definition Gprog : funspecs := [fspec].

Lemma fact_lemma : semax_body Vprog Gprog f_factorial fspec.
Proof.
  start_function. 
  evar (e : iexp).
  forward_if (
    PROP((Int.unsigned n >= 1)%Z) 
    LOCAL(temp _n (Vint n)) 
    SEP(refines_right ctx e)).
       (*(BinOp RemOp*)
          (*(BinOp MultOp (Val (LitV (LitInt (Int.unsigned n))))*)
             (*(App*)
                (*(Val*)
                   (*(RecV "factI" "n"*)
                      (*(If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))*)
                         (*(Val (LitV (LitInt 1)))*)
                         (*(BinOp RemOp*)
                            (*(BinOp MultOp (Var "n")*)
                               (*(App (Var "factI")*)
                                  (*(BinOp MinusOp (Var "n")*)
                                     (*(Val (LitV (LitInt 1))))))*)
                            (*(Val (LitV (LitInt Int.modulus)))))))*)
                (*(BinOp MinusOp (Val (LitV (LitInt (Int.unsigned n))))*)
                   (*(Val (LitV (LitInt 1))))))*)
          (*(Val (LitV (LitInt Int.modulus)))))*)
  (*).*)
  (* n is zero or less *)
  {
    (* step hl to right form *)
    do 4 step_pure_r ctx.
    forward.
    simpl.
    replace (Z.pos (1 * 1)) with (Z.pos 1) by lia.
    Exists (LitV (heap_lang.LitInt 1%Z)).
    Exists (Vint (Int.repr 1)).
    entailer!.
    apply nat_relate_n.
    lia.
  }
  {
    (* step hl through 1 cycle *)
    do 4 step_pure_r ctx.
    forward.
    unfold iris.factI.
    unfold e.
    entailer!.
    apply derives_refl.
  }
  subst e.
  Intros.
  step_pure_r ctx.
  evar (e : list ectx_item).
  forward_call (gv, add_to_ctx ctx e, (Int.sub n Int.one)); try lia.
  {
    subst e.
    unfold iris.factI.
    (* adding existentials here messes with fill_app *)
    replace (BinOp _ _ _) with (
    fill ([BinOpRCtx MultOp (Val (LitV (LitInt (Int.unsigned n)))); BinOpLCtx RemOp ((LitV (LitInt Int.modulus)))])
    (App
         (Val
            (RecV "factI" "n"
               (If (BinOp LtOp (Var "n") (Val (LitV (LitInt 1))))
                  (Val (LitV (LitInt 1)))
                  (BinOp RemOp
                     (BinOp MultOp (Var "n")
                        (App (Var "factI")
                           (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1))))))
                     (Val (LitV (LitInt Int.modulus)))))))
                     (Val (LitV (LitInt (Int.unsigned n - 1)))))
    ) by by rewrite ? fill_app.
    rewrite refines_right_add_ctx.
    rewrite Int.unsigned_sub_borrow.
    rewrite ? Int.unsigned_repr; try rep_lia.
    unfold Int.sub_borrow; simpl.
    rewrite if_false.
    {
      rewrite ? Int.unsigned_repr; [ |rep_lia].
      rewrite Z.add_0_r.
      ecancel.
    }
      apply Z.compare_ge_iff.
      rewrite ? Int.unsigned_repr; rep_lia.
    }
  (* extract recursive value *)
  Intros ret.
  destruct ret as [iret vret]; simpl; simpl in H0. 
  rewrite <- refines_right_add_ctx; simpl.
  unfold nat_relate in H0.
  destruct H0 as [rn [HrnPos [Hvst Hiris]]]; subst.
  (* step both programs to completion *)
  do 2 step_pure_r ctx.
  forward.
  (* prove equivalence *)
  Exists (LitV (LitInt ((Int.unsigned n * rn) `rem` Int.modulus))).
  Exists (Vint (Int.mul n (Int.repr rn))).
  simpl.
  entailer!.
  exists ((Int.unsigned n * rn) `rem` Int.modulus)%Z.
  assert (0 <= (Int.unsigned n * rn) `rem` Int.modulus < Int.modulus)%Z. 
  { apply Z.rem_bound_pos_pos; try rep_lia. }
  split; try lia.
  split; auto.
  (* prove that the remainder does nothing here *)
  rewrite Z.rem_mod_nonneg; try lia.
  rewrite <- (Int.repr_unsigned n).
  rewrite mul_repr.
  rewrite <- Int.unsigned_repr_eq.
  rewrite ! Int.repr_unsigned.
  reflexivity.
Qed.
