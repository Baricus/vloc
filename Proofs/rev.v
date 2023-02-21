(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

(* used for our modulus *)
Import compcert.lib.Integers.
Import proofmode notation.

Definition rev_internal : val := 
  (* NOTE: there is a difference between λ: and rec:  besides notation! Recursion! *)
  rec: "rev_internal" "prev" "cur" :=
    match: "cur" with
      (* return the new head of the list, the end *)
      NONE        => "prev"
      (* turn rest to previous and return *)
    | SOME "node" => 
        let: "elem" := Fst !"node" in
        let: "rest" := Snd !"node" in
        "node" <- ("elem", "prev");;
        "rev_internal" (SOME "node") "rest" 
    end.

(* NOTE: "rev_internal" (quotes) does not work, but rev_internal does *)
Definition iRev : val := λ: "list", (rev_internal NONE "list").

End iris.

Require Import Vloc.Lib.theory.
Require Import Vloc.CCode.rev.


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
     (!! (p = nullval) && emp)%logic  (* NOTE: I used to have an emp here; why? -> Allows binding logic to empty memory *)
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
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iInt x) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => (!! (v = InjLV (LitV LitUnit)) && emp)%logic
  end.

(* and we can compare them *)
Definition EquivList σ V I : mpred
  := (Ilist σ I * Vlist σ V)%logic.


(* so I can stop seeing so many App constructors *)
Notation "a <AP> b" := (App a b) (at level 21, left associativity).

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival, Lcur: list Z, Lprev: list Z
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur ;
            refines_right ctx ((of_val iris.rev_internal) <AP> (Val Iprev) <AP> (Val Icur)))
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
            refines_right ctx ((of_val iris.iRev) <AP> (Val Ihead)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList σ' Vres Ires ; (refines_right ctx (ectxi_language.of_val Ires))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec
  ]).

(*Notation "'RR' a b" := (refines_right a b) (at level 20, only printing).*)

(*NOTE: trying out making a nicer viewshift_SEP *)
Tactic Notation "viewshift_SEP'" uconstr(L) constr(L') :=
  let i := fresh "i" in freeze i := L; thaw i; viewshift_SEP 0 L'.

(*NOTE: gather_SEP really runs let i := fresh "i" in freeze i := L; thaw i. for any input L *)


Lemma Equiv_null_l σ Ival :
  EquivList σ nullval Ival |-- EquivList [] nullval Ival.
Proof.
  destruct σ; auto.
  (*NOTE: how to do in one step? *)
  iIntros "[Ri Rv]".
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
  EquivList [] Vval Ival |-- EquivList [] Vval Ival * (!! (Vval = nullval) && emp) * (!! (Ival = (InjLV (iLit (iUnit)))) && emp).
Proof.
  iIntros "[[%Ri _] [%Rv _]]".
  auto.
Qed.


Lemma rev_internal_lemma : semax_body Vprog Gprog f_rev_list_internal rev_list_internal_spec.
Proof.
  start_function.
  unfold iris.rev_internal.
  (* NOTE: this works! *)
  (*viewshift_SEP' (refines_right _ _) (EquivList Vprev Iprev).*)
  SPR_beta.
  SPR_recc.
  SPR_beta.
  (* either cur is null or not *)
  destruct (eq_dec Vcur nullval); subst.
  {
    (* if it is null, then the iris one is too *)
    sep_apply Equiv_null_l.
    sep_apply Equiv_empty.
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

    evar (e : iexp).
    (* We cannot get past this if statement in this case *)
    forward_if (
      PROP (False)
      LOCAL (temp _prev Vprev; temp _cur nullval)
      SEP (refines_right ctx e; EquivList Lprev Vprev Iprev; EquivList [] nullval (InjLV (LitV LitUnit)))
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
  }

  ).
