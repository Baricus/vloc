Require Import Vloc.Lib.theory.


Require Import Vloc.CCode.ret_one.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

#[local] Instance one_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.


(*Definition refines f2 A : funspec :=*)
  (*WITH gv: globals, ctx: ref_id*)
  (*PRE [ [> types of function parameters <] ]*)
    (*PROP()*)
    (*PARAMS([> NOTE: how to handle parameters <])*)
    (*GLOBALS([> do we need anything to correlate globals and Context? Hopefully not <])*)
    (*SEP(refines_right ctx f2)*)
  (*POST [ tint ] [> NOTE: type!!! A map of iris types to vst types? <]*)
    (*EX v' : ival, EX v : val,*)
    (*PROP()*)
    (*RETURN(v)*)
    (*SEP(refines_right ctx (ectxi_language.of_val v') * A v v').*)

Definition ret_false : iexp := (λ: "bool", if: "bool" then (#false) else (#true))%Ei.

Definition A v i := !!((i = (#false)) <-> (v = Vint (Int.repr 1))).

Definition fspec := 
  DECLARE _returns_one
  GIVEN ( )
  PRE []
  (fun '(_) => (
   (* Prop Params Globals Sep Rhs *)
          [],
          [],
          [],
          [],
          inl (ret_false (#true))))

  POST [ tint ]
  A(A)
  .

Definition Gprog : funspecs := [fspec].

Lemma one: semax_body Vprog Gprog f_returns_one fspec.
Proof.
  start_refines ().
  unfold ret_false.
  SPR_recc; SPR_beta.
  SPR_if_true.
  forward.
  Exists (Vint (Int.repr 1)).
  Exists (#false).
  iIntros "RR"; iFrame.
  iPureIntro.
  split; split; auto.
Qed.


(* now we use this to prove the spec we want *)
Definition true_spec :=
  DECLARE _returns_one
  WITH gv: globals
  PRE []
    PROP()
    PARAMS()
    GLOBALS()
    SEP()
  POST [ tint ]
    EX v : val,
    PROP()
    RETURN(v)
    SEP(!!(v = Vint (Int.repr 1))).

Context `{!heapGS Σ}.

(*Context {cs: compspecs}.*)

(*Context `{refines_ctx}.*)

Lemma related: 
      forall r : ref_id,
        {{{ True }}} (ret_false (#true)) {{{v, RET v; ⌜v = (#false)⌝ }}}
      → funspec_sub (snd fspec) (snd true_spec).
Proof.
  intros rid.
  intros HheapSpec.
  apply prove_funspec_sub.
  split; auto.
  intros Lts Params Gargs.
  iIntros "[%HargTyps Precondition]".
  iModIntro.
  iExists (nil).
  iExists ((), rid). (* No idea how to fill this in *)
  iExists (emp)%logic. (* also no idea here; what mpred would I want? *)
  iVST.
  entailer!.
  {
    iIntros (env Hve).
    unfold ve_of in Hve; destruct env; subst; simpl.
    Intros vres.
    Intros ires.
    iIntros "Hpre".
    iExists vres.
    rewrite PROP_LOCAL_SEP_cons.
    iDestruct "Hpre" as "[[%HA Rrefines] Rret]".
    destruct HA as [Hi Hv].

    (* TODO: show that the heaplang program proves that ires = #false *)


    destruct (eq_dec vres (Vint (Int.repr 1))).

    rewrite lift0C_prop.
    rewrite lift_prop_unfold.
    iVST.
    rewrite prop_sepcon.
    iIntros "[% Hpre]".
    rewrite H.
    unfold A.
        

  }


Lemma sub_route: 
      {{{ True }}} (ret_false (#true)) {{{v, RET v; ⌜v = (#false)⌝ }}}
    → semax_body Vprog Gprog f_returns_one fspec 
    → funspec_sub (snd fspec) (snd true_spec)
    → semax_body Vprog Gprog f_returns_one true_spec.
Proof.
  intros Hheap Hrefines Hsub.
  simpl in Hsub.


iLemma two: semax_body Vprog Gprog f_returns_one fspec 
    → {{{ True }}} (ret_false (#true)) {{{v, RET v; ⌜v = (#false)⌝ }}}
    → semax_body Vprog Gprog f_returns_one true_spec.
Proof.
  intros H Hheap.
  simpl.
  do 2 (split; auto).
  intros.
  unfold semax_body in H; simpl in H; repeat destruct H as [_ H].
  specialize (H Espec [] ((), (RefId 0 []))); simpl in H.
