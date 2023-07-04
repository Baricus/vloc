From Vloc Require Import core pure heap util heaplang_notation.

(* Tactics for starting refinement proofs *)
#[export] Ltac start_refines_unwrap :=
  match goal with
  | |- semax_body _ _ _ ?spec => unfold spec
  end;
  unfold refines;
  leaf_function;
   lazymatch goal with
   | |- semax_body ?V ?G ?F ?spec =>
         check_normalized F; function_body_unsupported_features F;
          (let s := fresh "spec" in
           pose (s := spec); hnf in s; cbn zeta in s;
            repeat
             lazymatch goal with
             | s:=(_, NDmk_funspec _ _ _ _ _):_ |- _ => fail
             | s:=(_, mk_funspec _ _ _ _ _ _ _):_ |- _ => fail
             | s:=(_, ?a _ _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _):_ |- _ => unfold a in s
             | s:=(_, ?a):_ |- _ => unfold a in s
             end;
            lazymatch goal with
            | s:=(_, WITH _ : globals PRE [ ] main_pre _ _ _ POST [tint] _):_
              |- _ => idtac
            | s:=?spec':_ |- _ => check_canonical_funspec spec'
            end; change (semax_body V G F s); subst s; 
            unfold NDmk_funspec')
   end;
   (let DependedTypeList := fresh "DependedTypeList" in
    unfold NDmk_funspec;
     match goal with
     | |- semax_body _ _ _ (_, mk_funspec _ _ _ ?Pre _ _ _) =>
           split3; [ check_parameter_types' | check_return_type |  ];
            match Pre with
            | λ _, convertPre _ _ (λ i, _) =>
                intros Espec DependedTypeList i
            | λ _ x, match _ with
                     | (a, b) => _
                     end => intros Espec DependedTypeList [a b]
            | λ _ i, _ => intros Espec DependedTypeList i
            end; simpl fn_body; simpl fn_params; simpl fn_return
     end;
     try
      match goal with
      | |- semax _ (λ rho, (?A rho * ?B rho)%logic) _ _ =>
            change (λ rho, (?A rho * ?B rho)%logic) with (A * B)%logic
      end; simpl _functor in *; simpl dependent_type_functor_rec; clear
     DependedTypeList; rewrite_old_main_pre).

#[export] Ltac start_refines_unfold wth_vals :=
    try
      match goal with
      | |- context[let 'pair a b := wth_vals in _] => destruct wth_vals as [a b]; start_refines_unfold a
      end.

#[export] Ltac start_refines_reduce :=
     repeat
      match goal with
      | |- semax _ (match ?p with
                    | (a, b) => _
                    end * _)%logic _ _ => destruct p as [a b]
      | |-
        semax _
          (close_precondition _ match ?p with
                                | (a, b) => _
                                end * _)%logic _ _ => 
        destruct p as [a b]
      | |-
        semax _
          (close_precondition _ (match ?p with
                                | (a, b) => _
                                end * _) * _)%logic _ _ => 
        destruct p as [a b]
      | |- semax _ (match ?p with
                    | (a, b) => _
                    end eq_refl * _)%logic _ _ => 
        destruct p as [a b]
      | |-
        semax _
          (close_precondition _ (match ?p with
                                 | (a, b) => _
                                 end eq_refl) * _)%logic _ _ =>
            destruct p as [a b]
      | |-
        semax _
          (close_precondition _
             (λ ae,
                !! (length ae.2 = ?A) &&
                ?B (make_args ?C ae.2 (mkEnviron ae.1 _ _))) * _)%logic _ _
        =>
            match B with
            | match ?p with
              | (a, b) => _
              end => destruct p as [a b]
            end
      end; try start_func_convert_precondition.

#[export] Ltac start_refines wth_vals :=
    start_refines_unwrap;
    start_refines_unfold wth_vals;
    start_refines_reduce;
    start_function2;
    start_function3.
      


(* Tactics for stepping functions *)
#[local] Ltac try_pures e' := first [
     apply pure_injrc 
   | apply pure_injlc 
   | apply pure_unop 
   | apply pure_binop 
   | apply pure_fst 
   | apply pure_snd 
   | apply pure_pairc 

   (* needed to ensure we can properly infer the true and false cases for some reason *)
   | match goal with
     | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
         subst e'; first [apply pure_if_false | apply pure_if_true]
     end
   (*| apply pure_if_true*)
   (*| apply pure_if_false*)
   | apply pure_case_inr 
   | apply pure_case_inl 
   (* Removes the goal created by pure_beta? *)
   | apply pure_beta; apply AsRecV_recv
   | apply pure_eqop
       (* since we're reshaping, this shouldn't be needed *)
   (*| apply pure_exec_fill *)
       (*I shouldn't need this one, I think?*)
   (*| apply pure_exec*)
   | apply (pure_recc _) (* allows inferrence? *)
   (* TODO: figure out how to actually fail with this *)
   | fail "Could not find a pure step to take (no pure_ tactic found)"
  ].

(* NOTE: this is obsolete; does not contain fixes for instruction level version *)
#[export] Ltac step_pure_r ctx :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try contradiction; try lia; 
        clear Hcond
    (* otherwise, try to step to the next instruction *)
    | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          viewshift_SEP 0 (refines_right ctx (fill K e'));
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            [try_pures e' | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.


(* useful to have tactics that step a specific way *)
#[local] Ltac step_pure_r_instr tactic :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try contradiction; try lia; 
        clear Hcond
    (* anything else we carry on *)
    | |- ?anything => idtac (* do nothing tactic *)
    end;
    (* try to step to the next instruction *)
  lazymatch goal with
    | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          viewshift_SEP' (refines_right ctx _) (refines_right ctx (fill K e'));
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            [tactic e' | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.


#[export] Ltac SPR_injrc    := step_pure_r_instr  ltac:(fun _ => apply (pure_injrc _)).
#[export] Ltac SPR_injlc    := step_pure_r_instr  ltac:(fun _ => apply (pure_injlc _)).
#[export] Ltac SPR_unop     := step_pure_r_instr  ltac:(fun _ => apply pure_unop).
#[export] Ltac SPR_binop    := step_pure_r_instr  ltac:(fun _ => apply pure_binop).
#[export] Ltac SPR_fst      := step_pure_r_instr  ltac:(fun _ => apply (pure_fst _ _)).
#[export] Ltac SPR_snd      := step_pure_r_instr  ltac:(fun _ => apply (pure_snd _ _)).
#[export] Ltac SPR_pairc   := step_pure_r_instr  ltac:(fun _ => apply (pure_pairc _ _)).

(* NOTE: If requires that we know the branch we're going down in order to work *)
#[export] Ltac SPR_if_true  := step_pure_r_instr  ltac:(fun e' =>
  match goal with
  | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
      subst e'; apply pure_if_true
  end).
#[export] Ltac SPR_if_false  := step_pure_r_instr  ltac:(fun e' =>
  match goal with
  | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
      subst e'; apply pure_if_false
  end).

#[export] Ltac SPR_inr      := step_pure_r_instr  ltac:(fun _ => apply (pure_case_inr _ _ _)).
#[export] Ltac SPR_inl      := step_pure_r_instr  ltac:(fun _ => apply (pure_case_inl _ _ _)).

#[export] Ltac SPR_beta     := step_pure_r_instr  ltac:(fun _ => apply pure_beta; apply AsRecV_recv).
#[export] Ltac SPR_eqop     := step_pure_r_instr  ltac:(fun _ => apply pure_eqop).

#[export] Ltac SPR_recc     := step_pure_r_instr  ltac:(fun _ => apply (pure_recc _)).


(* tactics for heap actions *)
#[export] Ltac SPR_load l := 
  match goal with
  | |- context[heapS_mapsto ?sh l ?v] =>
    match goal with
      | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          viewshift_SEP' (refines_right ctx _) (l |-> _) (refines_right ctx (fill K (Val v)) * (l |-> v))%logic;
          first (
            go_lower;
            simple eapply (ref_right_load _ ctx K l sh _); first auto
          );
          simpl;
          (* Needed to transform resulting A * B into the proper list form *)
          Intros
          )
      | |- ?anything => fail 999 "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
    end
  | |- ?anything => fail "Could not find a value that the given location maps to; are you sure this is a location?"
  end.

#[export] Ltac SPR_store l vnew := 
      match goal with
      | |- context[heapS_mapsto ?sh l ?vcur] =>
          match goal with
          | |- context[refines_right ?ctx ?expr] => 
              reshape_expr expr ltac:(fun K e => 
              replace expr with (fill K e) by (by rewrite ? fill_app);
              viewshift_SEP' (refines_right ctx _) (l |-> vcur) (refines_right ctx (fill K (Val (LitV LitUnit))) * (l |-> vnew%V))%logic;
                  first (
                  go_lower;
                  simple eapply (ref_right_store _ ctx K l _ vcur%V vnew%V);
                  [try apply into_val | auto]
                  );
                  simpl;
                  (* Needed to transform resulting A * B into the proper list form *)
                  Intros
              )
          | |- ?anything => fail 999 "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
          end
      | |- ?anything => fail "Could not find a value that the given location maps to; are you sure this is a location?"
      end.

#[export] Ltac SPR_alloc := 
          match goal with
          | |- context[refines_right ?ctx ?expr] => 
                reshape_expr expr ltac:(fun K e =>
                  match e with 
                  (* This needs to be allocating a value; so we match on "ref" (Val v) *)
                  | context[(ref (Val ?v)%V)%Ei] =>
                      replace expr with (fill K e) by (by rewrite ? fill_app);
                      viewshift_SEP' (refines_right ctx _) (EX l, (refines_right ctx (fill K (Val (LitV (LitLoc l))))) * (l |-> v));
                      first (
                        go_lower;
                        simple eapply ref_right_alloc; [try apply into_val | auto]
                      );
                      simpl
                  end
              )
          | |- ?anything => fail 999 "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
          end.
