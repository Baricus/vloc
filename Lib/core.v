Require Export iris.program_logic.language.
Require Export iris.program_logic.ectxi_language.

Require Export iris.bi.lib.atomic.
From iris.heap_lang Require Export lang derived_laws metatheory.
From iris.heap_lang Require Export proofmode.
Require Export stdpp.list.

From VST.veric Require Export rmaps compcert_rmaps.

Require Export VST.veric.bi.

Require Export VST.floyd.library.
Require Export VST.zlist.sublist.
Require Export Program.Equality.
From iris.algebra Require Export excl gmap.
Require Export VST.floyd.proofauto.
Require Export VST.concurrency.invariants.
(*Separate import needed!*)
Require Export VST.concurrency.ghosts.
Require Export VST.concurrency.ghostsI.
Require Export VST.concurrency.fupd.

Require Export VST.floyd.library.

(* Taken from theories/logic/proofmode/spec_tactics!!! *)
(** Tactics for updating the specification program. *)
From iris.proofmode Require Export
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.


Section refinement.

(* declare context; a name for the state, the location type, and the ectxi language *)
Class refines_ctx := { gName : own.gname; nspace : namespace }.
Context `{ref_ctx: refines_ctx}.

(*define shorthand *)
Definition ival := heap_lang.val.
Definition iexp := heap_lang.expr.

(* the tpool is a map of numbers to expressions.  The "exclusive_PCM" is for ownership; 
   it mirrors the vloc Excl *)
Definition tpool_ghost := (gmap_ghost (K:=nat) (A:=(exclusive_PCM iexp))).
(* the heap is another map, of locations (essentially just nats?) to a share of ownership of a value *)
Definition heap_ghost := (gmap_ghost (K:=loc) (A:=(@pos_PCM (discrete_PCM (option ival))))). (*(@pos_PCM (discrete_PCM (option ival)))).*)
(* The whole ghost state is just the combination of both the tpool and heap ghost states *)
Definition spec_ghost := prod_PCM tpool_ghost heap_ghost.

(*The reference has no share, so we can't combine it*)
Definition InvGhost (map : @G spec_ghost) := @ghost_reference spec_ghost map gName.
(* NOTE: S is "some share" which may not be enough later!  It works for now *)
Definition UsrGhost (map : @G spec_ghost) := ∃ s, (!!(s ≠ emptyshare) * (@ghost_part spec_ghost s map gName))%logic.

(* NOTE: G is the type of any ghost state; which is by default opaque
    one way to show the actual type is below *)
(*Compute @G spec_ghost.*)

(* to_tpool
    converts a list of expressions to a thread pool,
    a map of thread indexes to their expressions 
*)
Definition to_tpool (exps : list iexp) : @G tpool_ghost
  := Some <$> (map_seq 0 exps).

(* tpool_lookup 
    to_tpool doesn't discard elements; for lookup's purpose it's just an extra Some
*)
Lemma tpool_lookup tp j : to_tpool tp !! j = Some <$> tp !! j.
Proof.
  unfold to_tpool. rewrite lookup_fmap.
  by rewrite lookup_map_seq_0.
Qed.

(* tpool_lookup_Some
    to_tpool doesn't add elements so the original tp and the tpool must agree
*)
Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Some (Some e) → tp !! j = Some e.
Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.

(* Borrowed from spec_ra *)

(* NOTE: G is horrible.  It's the type of the ghost state, but it's opaque by default!
   Below is one way to see the actual type that G is. *)
(*Compute @G tpool_ghost.*)

(* to_tpool_insert
    Inserting elements into the original tp is the same as inserting the elements
    wrapped in "Some" to the tpool

    This lets us "pull out" and "push in" updates as needed across to_tpool
*)
Lemma to_tpool_insert tp (j:nat) (e:iexp) :
  (j < length tp)%nat →
  to_tpool (<[j:=e]> tp) = <[j:=Some e]> (to_tpool tp).
Proof.
  intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
  - by rewrite tpool_lookup lookup_insert list_lookup_insert.
  - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
    by rewrite tpool_lookup.
Qed.
(* various other versions of insertion with tpool *)
Lemma to_tpool_insert' tp (j:nat) (e:iexp) :
  is_Some (to_tpool tp !! j) →
  to_tpool (<[j:=e]> tp) = <[j:=Some e]> (to_tpool tp).
Proof.
  rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
Qed.
Lemma to_tpool_snoc tp e :
  to_tpool (tp ++ [e]) = <[length tp:=Some e]>(to_tpool tp).
Proof.
  intros. apply: map_eq=> i.
  destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
  - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
  - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
  - rewrite lookup_insert_ne; last lia.
    rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
       change (ofe_car exprO) with expr; lia.
Qed.

(* to_heap
    Converts the standard heap_lang heap to the heap_ghost type.  
    This is largely just a reformatting to fit the form
*)
Definition to_heap (heap : gmap loc (option ival)) : @G heap_ghost :=
  fmap (λ v, (Some (fullshare, v))) heap.

(* to_heap_insert
    Inserting elements into the original heap is the same as inserting
    the "modified" element after to_heap.

    like to_tpool_insert, this lets us pull insertion across to_heap
*)
Lemma to_heap_insert σ l v:
  to_heap (heap (state_upd_heap <[l:=Some v]> σ)) = <[l := Some (fullshare, Some v)]> (to_heap (heap σ)).
Proof.
  unfold to_heap.
  rewrite fmap_insert.
  auto.
Qed.

(* assert that we have a value in the heap *)
(* heapS_mapsto
    An assertion that there is a value v in the heap at location l 
*)
Definition heapS_mapsto (s : share) (l : loc) (v: ival) : mpred :=
  UsrGhost (to_tpool [], {[ l := Some (s, (Some v)) ]} ).

Definition spec_inv (c : cfg (heap_lang)) : mpred := 
    EX exp_list : list iexp, EX σ,
    (* tp is a list of expressions! σ is the state *)
    ⌜rtc erased_step c (exp_list, σ)⌝ &&
      (* take the left side of the ghost share *)
    @InvGhost ((to_tpool exp_list), to_heap (heap σ)).

Definition spec_ctx : mpred := 
  (EX ρ, inv nspace (spec_inv ρ)). 

(*Define our own singleton map and turn it to a VST map for the non-invariant side *)
(* tpool_mapsto
    an assertion that the expression e is thread j's (numbered as nat's) 
*)
Definition tpool_mapsto (j : nat) (e : iexp) : mpred := 
  UsrGhost ({[j := Some e]}, to_heap gmap_empty).

(* ref_id
    A context and associated thread identifier
*)
Record ref_id : Set := RefId { tp_id : nat;  tp_ctx : list ectx_item }.

Definition add_to_ctx id (ctx : list ectx_item) : ref_id :=
  RefId (tp_id id) (ctx ++ tp_ctx id).

Definition refines_right (r : ref_id) (e : iexp) : mpred := 
  (spec_ctx * tpool_mapsto (tp_id r) (fill (tp_ctx r) e))%logic.

(* refines_right_add_ctx
    Filling is the same as adding something to the "forall K context" 
*)
Lemma refines_right_add_ctx ref K e :
  (refines_right ref (fill K e) = refines_right (add_to_ctx ref K) e).
Proof.
  unfold add_to_ctx, refines_right; simpl.
  rewrite fill_app.
  auto.
Qed.

(* A VST triple for a refinement *)
Definition refines argTs retT with_type (pieces : with_type -> (_ * _ * _ * _ * _)) (A : val -> ival -> mpred) :=
  NDmk_funspec (argTs, retT) cc_default (with_type * ref_id)
    (fun '(wth_vals, ctx) =>
      let '(propL, paramsL, globalsL, sepL, rhs) := pieces wth_vals
      in
      (PROPx (propL) (PARAMSx (paramsL) (GLOBALSx (globalsL) (SEPx
      (cons 
        (match rhs with
         | inl e' => refines_right ctx e'
         | inr k => !! (ctx = k) && emp
         end
        )%logic 
        (sepL) )
      ))))
    ) 
    (fun '(_, ctx) =>
      EX Vres, EX Ires, 
      PROP()
      RETURN(Vres)
      SEP(((A Vres Ires) * (refines_right ctx (of_val Ires))))
    )
  .

(* NOTE: some possible better notations for later *)
Notation "({ x , .. , y })" := (pair x .. (pair y tt) ..).

Notation "( 'tuplef' n1 .. nn  => body )" :=
  (fun tuple =>
    (*match tuple with (pair tuple u) =>*)
    (*(fun (_ : unit) =>*)
      match tuple with (pair tuple tail) =>
        (fun nn =>
          ..
            match tuple with (pair tuple tail) =>
              (fun n1 => body) tail
            end
          ..
        ) tail
      (*end) u*)
    end)
  (at level 200, n1 closed binder, nn closed binder).

(*
Check (( tuplef a b c d => a + b + c + d)) : _ -> nat.

Compute ((tuplef a b c d => a + b + c + d) ((), 1, 2, 3, 4)).
 *)

End refinement.

(* hints have to go here since they don't export otherwise *)
#[export] Hint Resolve tpool_lookup_Some : core.

(* so do notations? *)
(* TODO: better notation *)
#[export] Notation "a |-> b"   := (heapS_mapsto fullshare a b) (at level 20).
#[export] Notation "a { s }-> b" := (heapS_mapsto s a b) (at level 20).

(* TODO: figure out if this is actually exported? My bet is ... no *)
#[export] Notation "a |=> b" := (tpool_mapsto a b) (at level 20).

#[export] Notation "'GIVEN' ( g1 * .. * gn ) 'PRE' [ t ; .. ; t' ] pieces 'POST' [ rtyp ] 'A' ( a )" :=  (
  refines (cons t .. (cons t' nil) ..) rtyp
  (prod g1 .. (prod gn ()) ..)
  pieces
  a
  ) (only parsing).

