(* workaround for not having notation *)
(*From iris.heap_lang Require proofmode notation.*)
(*Require compcert.lib.Integers.*)
(*Module iris.*)

(*[> used for our modulus <]*)
(*Import compcert.lib.Integers.*)
(*Import proofmode notation.*)

(*Definition rev_internal : val := *)
  (*[> NOTE: there is a difference between λ: and rec:  besides notation! Recursion! <]*)
  (*rec: "rev_internal" "prev" "cur" :=*)
    (*match: "cur" with*)
      (*[> return the new head of the list, the end <]*)
      (*NONE        => "prev"*)
      (*[> turn rest to previous and return <]*)
    (*| SOME "node" => *)
        (*let: "elem" := Fst !"node" in*)
        (*let: "rest" := Snd !"node" in*)
        (*"node" <- ("elem", "prev");;*)
        (*"rev_internal" (SOME "node") "rest" *)
    (*end.*)

(*[> NOTE: "rev_internal" (quotes) does not work, but rev_internal does <]*)
(*Definition iRev : val := λ: "list", (rev_internal NONE "list").*)

(*End iris.*)

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.rev.

(* NOTE: don't need a module! *)
Definition rev_internal : heap_lang.val := 
  (* NOTE: there is a difference between λ: and rec:  besides notation! Recursion! *)
  (rec: "rev_internal" "prev" "cur" :=
    match: "cur" with
      (* return the new head of the list, the end *)
      NONE        => "prev"
      (* turn rest to previous and return *)
    | SOME "node" => 
        let: "elem" := Fst (!"node") in
        let: "rest" := Snd (!"node") in
        "node" <- ("elem", "prev");;
        "rev_internal" (SOME "node") "rest" 
    end%Ei).

(* NOTE: "rev_internal" (quotes) does not work, but rev_internal does *)
Definition iRev : heap_lang.val := λ: "list", (rev_internal NONE "list").

#[local] Instance prog_ctx : refines_ctx := { gName := 1; nspace := nroot .@ "test"}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*
   We'll need a way to compare VST lists and iris lists.
   We could do something direct, but it's probably easier
   to just say that they both equal the same Coq level list.

   For simplicity, let's stick to integers. 
*)

(* first a VST list *)
Definition node_t := Tstruct _node noattr.

Fixpoint Vlist (sigma: list Z) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
    (* NOTE: should malloc_token be here? -> Probably!  It makes sense here. *)
    data_at Ews node_t (Vint (Int.repr h),y) p  *  malloc_token Ews node_t p * Vlist hs y
 | nil => 
    ⌜ (p = nullval) ⌝  (* NOTE: I used to have an emp here; why? -> Allows binding logic to empty memory *)
 end.

(* now an iris list *)
(* NOTE: should these be notations? *)
Definition iLit x := (LitV x).
Definition iUnit  := (LitUnit).
Definition iInt x := iLit (LitInt x).
Definition iPair l r := (PairV l r).

(* NOTE: we don't want an iris heap here directly, we want our simulated one. *)
Fixpoint Ilist (sigma : list Z) v : mpred :=
  match sigma with
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iLit (LitLoc p)) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => ⌜ (v = InjLV (LitV LitUnit)) ⌝
  end.

(* and we can compare them *)
Definition EquivList σ V I : mpred
  := (Ilist σ I * Vlist σ V)%logic.


(* so I can stop seeing so many App constructors *)
Notation "a <AP> b" := (App a b) (at level 21, left associativity, only parsing).

(*Notation "'RR' a b" := (refines_right a b) (at level 20, only printing).*)

(*NOTE: gather_SEP really runs let i := fresh "i" in freeze i := L; thaw i. for any input L *)


Lemma Equiv_null_l σ Ival :
  EquivList σ nullval Ival |-- EquivList [] nullval Ival.
Proof.
  destruct σ; auto.
  (*NOTE: how to do in one step? *) iIntros "[Ri Rv]".
  iDestruct "Rv" as (y) "[[Rnull Rtok] Rrest]".
  fold Vlist.
  iDestruct (field_at_ptr_neq_null with "Rnull") as "%Hcontra".
  exfalso.
  apply Hcontra.
  apply ptr_eq_nullval.
Qed.

Lemma Equiv_null_r σ Vval :
  EquivList σ Vval (InjLV (iLit iUnit)) |-- (EquivList [] Vval (InjLV (iLit iUnit))).
Proof.
  destruct σ; auto.
  iIntros "[Ril Rvl]".
  iDestruct "Ril" as (p) "[%Hcontra RUselessButICantDrop]".
  discriminate.
Qed.

Lemma Equiv_empty Vval Ival :
  EquivList [] Vval Ival |-- (!! (Vval = nullval) && !! (Ival = (InjLV (iLit (iUnit)))) && EquivList [] Vval Ival).
Proof.
  iIntros "[%Ri %Rv]".
  auto.
Qed.

(* for the non-empty cases *)
Lemma Equiv_not_null σ Vval Ival :
  (Vval ≠ nullval \/ Ival ≠ (InjLV (iLit iUnit))) ->
  EquivList σ Vval Ival |-- EX (s : Z), EX (σ' : list Z), (EquivList (s :: σ') Vval Ival).
Proof.
  (* exhaustive check of all the cases *)
  intros H; destruct H as [HV | HI]; destruct σ as [| s σ'].
  {
    iIntros "[_ %Contra]".
    contradiction.
  }
  2:{
    iIntros "[%Contra _]".
    contradiction.
  }
  1,2:
    iIntros "R";
    iExists s;
    iExists σ';
    iFrame.
Qed.

Lemma Equiv_pop s σ' Vval Ival:
  EquivList (s :: σ') Vval Ival |-- 
      (EX Vval', EX Ival', EX p, (
      (!! (Ival = InjRV (iLit (LitLoc p)) /\ Vval ≠ nullval) && (data_at Ews node_t (Vint (Int.repr s),Vval') Vval * malloc_token Ews node_t Vval) * p |-> (iPair (iInt s) Ival') *
      EquivList σ' Vval' Ival'))).
Proof.
  iIntros  "[RI RV]".
  simpl.
  iDestruct "RI" as (p Hip Ival') "(RIpts & Ri')".
  iDestruct "RV" as (Vval') "[[Rvdata Rvmal] Rv']".
  iExists Vval'.
  iExists Ival'.
  iExists p.
  iSplitR "Ri' Rv'".
  2: iFrame.
  iSplitR "RIpts"; auto.
  iSplit; last iFrame.
  iSplit; auto.
  iPoseProof (field_at_ptr_neq_null with "Rvdata") as "%H".
  iPureIntro.
  intro Hcontra.
  subst Vval.
  assert (ptr_eq nullval nullval = true); auto.
  apply ptr_eq_True.
  apply mapsto_memory_block.is_pointer_or_null_nullval.
  destruct H.
  rewrite H0.
  auto.
Qed.

Lemma EquivList_push v v' i i' l s σ:
  ((i = InjRV (iLit (LitLoc l))) /\ (v ≠ nullval)) -> (EquivList σ v' i' * data_at Ews node_t (Vint (Int.repr s), v') v * malloc_token Ews node_t v * l |-> (iPair (iInt s) i')) |-- EquivList (s :: σ) v i.
Proof.
  iIntros (Hnnull) "[[[[Ri Rv] Rdata] Rmalloc] Rpts]".
  destruct Hnnull as [Hi Hv].
  unfold EquivList.
  iSplitL "Rpts Ri".
  - iExists l; fold Ilist.
    iSplitR; auto.
    iExists i'.
    iFrame.
  - iExists v'; fold Vlist.
    iFrame.
Qed.
  
Lemma EquivList_local_facts:
  forall sigma v i,
   EquivList sigma v i |--
       !! (is_pointer_or_null v /\ (v=nullval <-> sigma=nil) /\ (i=(InjLV (#())) <-> sigma=nil)).
Proof.
  iIntros (σ v i) "EqList".
  destruct σ.
  - iDestruct "EqList" as "[%Ilist %Vlist]".
    subst v; subst i.
    iPureIntro.
    split; first apply mapsto_memory_block.is_pointer_or_null_nullval.
    split; split; auto.
  - iDestruct (Equiv_pop with "EqList") as (v' i' p) "[[[[%Hi %Hv] [Hdata Hmalloc]] ptsTo] EqList']".
    subst i.
    iDestruct (data_at_valid_ptr with "Hdata") as "Hvalid"; auto.
    { rewrite sizeof_Tstruct. simpl; lia. } (* NOTE: This is a weird goal.  Why does it come up? *)
    iSplitL.
    { destruct v; auto. }
    iPureIntro; split; split; intro; try contradiction; try list_solve.
Qed.
#[export] Hint Resolve EquivList_local_facts : saturate_local.

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival, Lcur: list Z, Lprev: list Z
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur ;
            refines_right ctx ((of_val rev_internal) <AP> (Val Iprev) <AP> (Val Icur)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).

(* the equivalent wrappers *)
Definition rev_list_spec :=
  DECLARE _rev_list
    WITH gv: globals, ctx: ref_id, Vhead: val, Ihead: ival, σ: list Z
    PRE [ tptr node_t ]
      PROP()
      PARAMS(Vhead)
      GLOBALS()
      SEP(EquivList σ Vhead Ihead ;
            refines_right ctx ((of_val iRev) <AP> (Val Ihead)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec
  ]).

Lemma rev_internal_lemma : semax_body Vprog Gprog f_rev_list_internal rev_list_internal_spec.
Proof.
  start_function.
  unfold rev_internal.
  (* NOTE: this works! *)
  (*viewshift_SEP' (refines_right _ _) (EquivList Vprev Iprev).*)
  SPR_beta.
  fold rev_internal. (* do remember to fold this! *)
  SPR_recc; SPR_beta.
  (* either cur is null or not *)
  destruct (eq_dec Vcur nullval); subst.
  {
    (* if it is null, then the iris one is too *)
    sep_apply Equiv_null_l; sep_apply Equiv_empty.
    (* NOTE: why do I need this here? It can't pull the emp's apart right otherwise? *)
    autorewrite with norm.
    Intros.
    rename H into HIcurNull.
    rewrite HIcurNull. (* cannot subst for some reason *)
    unfold iLit, iUnit.

    (* Step iris to ending *)
    SPR_inl.
    SPR_recc.
    SPR_beta.

    (* We cannot get past this if statement in this case *)
    forward_if (
      PROP (False)
      LOCAL()
      SEP()
    ).
    {
      forward.
      iIntros "[[ReqNull RrefR] ReqPrev]".
      iExists Vprev.
      iExists Iprev.
      iExists Lprev.
      iFrame.
      auto.
    }
    {
      (* Null != Null *)
      contradiction.
    }
  }
  {
    (* If it's not null, then... *)

    (* NOTE: To get rid of the %Ei tag *)
    (*Open Scope iris_expr_scope.*)

    (* we have an element in BOTH lists *)
    sep_apply (Equiv_not_null Lcur); [left; auto|].
    Intros c Lcur'; clear Lcur.
    sep_apply (Equiv_pop c Lcur').
    Intros Vcur' Icur' IlocCur.
    rename H into HIlocCur; rewrite ! HIlocCur.

    (* and we can reduce the right hand side! *)
    SPR_inr.
    SPR_recc; SPR_beta.

    (* including loads *)
    SPR_load IlocCur.
    SPR_fst.
    SPR_recc.
    SPR_beta.
    SPR_load IlocCur.
    SPR_snd.
    SPR_recc.
    SPR_beta.

    SPR_pairc. (* I hate this :( (also I needed the underscores again) *)
    unfold iPair.
    SPR_store IlocCur (#c, Iprev)%V. (* NOTE: how to get rid of the %V here? *)

    (* now we step *)
    SPR_recc; SPR_beta.

    (* run the right side to the same point now *)

    (* This if statement cannot be entered *)
    forward_if.
    { contradiction. }

    forward.
    forward.



    (* rebuild our list *)
    viewshift_SEP' (IlocCur |-> _) (data_at _ _ _ _) (malloc_token _ _ _) (EquivList Lprev _ _) 
        (EquivList (c :: Lprev) Vcur Icur).
    {
      entailer!.
      iIntros "[[[Rpt Rdta] Rmlc] Reqt]".
      iModIntro.
      iApply EquivList_push; auto.
      iFrame.
    }

    (* Almost forgot this step! *)
    SPR_injrc.

    forward_call (gv, ctx, Vcur, Vcur', Icur, Icur', Lcur', (c :: Lprev)).
    { 
      rewrite HIlocCur. 
      cancel.
    }

    Intros ret.
    destruct ret as [p lret]; destruct p as [vret iret].
    forward.

    Exists vret.
    Exists iret.
    Exists lret.
    entailer!.
  }
Qed.

