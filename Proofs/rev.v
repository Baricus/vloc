(* workaround for not having notation *)
From iris.heap_lang Require proofmode notation.
Require compcert.lib.Integers.
Module iris.

(* used for our modulus *)
Import compcert.lib.Integers.
Import proofmode notation.

Definition rev_internal : expr := 
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
     ⌜ (p = nullval) ⌝ (* NOTE: I used to have an emp here; why? *)
 end.

(* now an iris list *)
(* NOTE: should these be notations? *)
Definition iLit x := (LitV x).
Definition iUnit  := (LitUnit).
Definition iInt x := iLit (LitInt x).
Definition iPair l r := (PairV l r).

(* NOTE: we don't want an iris heap here directly, we want our simulated one. *)
Fixpoint Ilist (sigma : list Z) v :=
  match sigma with
  | x :: xs => ∃ (p : loc), ⌜ v = InjRV (iInt x) ⌝ ∗ ∃ (v' : ival), p |-> (iPair (iInt x) v') ∗ Ilist xs v'
  | [] => ⌜ v = InjLV (LitV LitUnit) ⌝
  end.

(* and we can compare them *)
Definition EquivList V I
  := ∃ σ, Ilist σ I ∗ Vlist σ V.


(* so I can stop seeing so many App constructors *)
Notation "a <AP> b" := (App a b) (at level 20).

(* The main program we want to verify *)
Definition rev_list_internal_spec :=
  DECLARE _rev_list_internal
    WITH gv: globals, ctx: ref_id, Vprev: val, Vcur: val, Iprev: ival, Icur: ival
    PRE [ tptr node_t, tptr node_t ]
      PROP()
      PARAMS(Vprev; Vcur)
      GLOBALS()
      SEP(EquivList Vprev Iprev ∗ EquivList Vcur Icur ∗ 
            refines_right ctx (iris.rev_internal <AP> (Val Iprev) <AP> (Val Icur)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival, EX σ': list Z,
      PROP()
      RETURN(Vres)
      SEP(EquivList Vres Ires ∗ (refines_right ctx (ectxi_language.of_val Ires))).

(* the equivalent wrappers *)
Definition rev_list_spec :=
  DECLARE _rev_list
    WITH gv: globals, ctx: ref_id, Vhead: val, Ihead: ival
    PRE [ tptr node_t ]
      PROP()
      PARAMS(Vhead)
      GLOBALS()
      SEP(EquivList Vhead Ihead ∗
            refines_right ctx (iris.rev_internal <AP> (Val Ihead)))
    POST [ tptr node_t ]
      EX Vres: val, EX Ires: ival,
      PROP()
      RETURN(Vres)
      SEP(EquivList Vres Ires ∗ (refines_right ctx (ectxi_language.of_val Ires))).


Definition Gprog : funspecs := ltac:(with_library prog [ 
    rev_list_internal_spec ;
    rev_list_spec
  ]).
