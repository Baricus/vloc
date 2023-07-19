From Vloc Require Import theory.

From VST Require Import floyd.proofauto.

(* Two different approaches we could take:
    - syntactical relation between predicates 
    - semantic relationship between C and HeapLang 
 *)

(* Third approach:
    - use A as the relationship directly
 *)


Context `{!heapGS Σ}.

Context {cs: compspecs}.

Context `{refines_ctx}.

Context `{NatDed Prop}.

Axiom syn_relate : iProp Σ -> mpred -> Prop.

Inductive syn_relate' (I : iProp Σ) (M : mpred) : Prop :=
  | synRel_Int: forall (x : heap_lang.val) z, I = ⌜ x = LitV (LitInt z) ⌝ -> M = !!(TT) -> syn_relate' I M.

(*
Definition refines_semax varspecs funspecs func ident argTs retT with_type (P : with_type -> argsEnviron -> mpred) (rhs : sum iexp ref_id) (A : val -> ival -> mpred) :=
  semax_body (C:=cs) varspecs funspecs func
  (
    ident, 
    refines argTs retT with_type P rhs A
  ).
*)

Require Import CCode.rev.
Require Import Proofs.rev.

(*Unset Printing Notations.*)
Definition test_spec := 
  DECLARE _rev_list_internal
  GIVEN (val * val * heap_lang.val * heap_lang.val * list Z * list Z)
  PRE [tptr node_t ; tptr node_t]
  (fun '(Vprev, Vcur, Iprev, Icur, Lcur, Lprev, _) => (
   (* Prop Params Globals Sep Rhs *)
          [],
          [Vprev; Vcur],
          [],
          [EquivList Lprev Vprev Iprev ; EquivList Lcur Vcur Icur],
          inl (of_val rev_internal Iprev Icur)))

  POST [tptr node_t]
  A(fun v i => EX σ, EquivList σ v i)
  .

(*Definition refines_def (E : coPset)*)
  (*(e : expr) (e'k : rhs_t) (A : lrel Σ) : iProp Σ :=*)
  (*(∀ j : ref_id,*)
  (*match e'k with*)
    (*[> if it is an expression, it refines it to the right <]*)
  (*| inl e' => refines_right j e'*)
      (*[> if it is not, so it is a reference #, they are equal (pure fact) <]*)
  (*| inr k  => ⌜j = k⌝*)
  (*end -∗*)
 (*|={E,⊤}=> WP e {{ v, ∃ v', refines_right j (of_val v') ∗ A v v' }})%I.*)

(*Definition semax_body*)
   (*(V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=*)
(*match spec with (_, mk_funspec fsig cc A P Q _ _) =>*)
  (*fst fsig = map snd (fst (fn_funsig f)) /\*)
  (*snd fsig = snd (fn_funsig f) /\*)
(*forall Espec ts (x:dependent_type_functor_rec ts A mpred),*)
  (*semax Espec (func_tycontext f V G nil)*)
      (*(fun rho => close_precondition (map fst f.(fn_params)) (P ts x) rho * stackframe_of f rho)*)
       (*f.(fn_body)*)
      (*(frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))*)
(*end.*)

(*Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=*)
  (*(NDmk_funspec (pair (cons u .. (cons v nil) ..) tz) cc_default tx*)
     (*(fun x => P) (fun x => Q)) : funspec_scope (default interpretation)*)

(* Currently:
    - P' Q' need to be replaced with propL, etc as in final clause
    - Can I have syn_relate be tied to a function on the argsEnviron as the PROP()LOCAL()SEP()?
*)
Lemma syn_relate_sound 
  varspecs funspecs func ident argTs retT with_type
  (P : iProp Σ) e v (Q : ival -> iProp Σ) (P' : mpred) (Q' : with_type -> environ -> mpred) pieces 
  (A : val -> ival -> mpred):
  (* relationship between structures *)
  (* First one requires us to translate the precondition *)
  forall wth_vals aE,
  let '(propL, paramsL, globalsL, sepL, _) := pieces wth_vals
  in
  syn_relate P ((PROPx (propL) (PARAMSx (paramsL) (GLOBALSx (globalsL) (SEPx sepL)))) aE) →
  (* Second one just ensures that the heaplang Q is translated directly to a VST Q' *)
  (* NOTE: what should emp be?  We don't want a precondition but can we assume no memory? *)
  ( forall Vret Iret environ, 
    (emp |-- A Vret Iret) 
  → (eval_var ret_temp retT environ) = Vret
  → syn_relate (Q Iret) (Q' wth_vals environ) 
  ) →
  (* HeapLang triple *)
  {{{ P }}} e {{{ RET v; Q v }}} →
  (* Refinement triple *)
  semax_body varspecs funspecs func (ident, refines argTs retT with_type pieces A) →

  (* VST triple *)
  (*semax compspecs Espec Δ *)
  semax_body varspecs funspecs func (
    ident,
    (* x => WITH clauses, y => environment (args/return) *)
    NDmk_funspec (argTs, retT) cc_default with_type (fun wth_vals =>
    let '(propL, paramsL, globalsL, sepL, _) := pieces wth_vals
    in
      PROPx (propL) (PARAMSx (paramsL) (GLOBALSx (globalsL) (SEPx sepL))))
 (Q') 
  )
  .
Proof.
  intros;
  destruct pieces;
  destruct p as [p MPreds];
  destruct p as [p Globals];
  destruct p as [Props Vals];
  intros HSynP HSynQ Hheapspec Hrefinesspec.
