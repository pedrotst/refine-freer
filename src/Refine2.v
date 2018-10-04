Require Export Imp.
Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.omega.Omega
  Coq.Lists.List.

Require Export
  Eff
  Comp
  Choice.

Import ListNotations.

Generalizable All Variables.

Require Import
  Hask.Control.Monad
  RWS.

Definition nonDet_list : Eff [Choice] (list nat) :=
  (l <- send (Pick (fun (l: list nat) => (length l) >= 10));
     pure l).

Definition det_list: Eff [Choice] _ :=
     (pure (repeat 10 11)).

Definition denotes_choice {effs v}: Eff (Choice :: effs) v -> Eff effs v -> Prop :=
    handleRelayP
      (fun x s => match s with
               | Pure x' =>  x = x'
               | Impure u k => False
               end)
      (fun A '(Pick p) a => p a).

Definition refines {a effs} (e1 e2: Eff (Choice::effs) a) :=
  denotes_choice e2 ~> denotes_choice e1.

Lemma reduce_nonDet: 
  denotes_choice nonDet_list (pure (repeat 10 11)).
Proof.
  intros.
  simpl.
  econstructor; [| econstructor; eauto]; simpl; eauto.
Qed.

Lemma nonEffect_Denotes: forall v (l: v),
    denotes_choice (pure[Eff [Choice]] l) (pure l).
Proof.
  econstructor; simpl; eauto.
Qed.

Lemma refines_detList_nonDetList:
    refines nonDet_list det_list.
Proof.
  intros t H.
  inversion H; subst.
  destruct t; [|intuition]; subst; eauto.
  apply reduce_nonDet.
Qed.

Fixpoint denote_aexp `{Member (State state) effs}
         (a:aexp): Eff effs nat :=
  match a with
  | ANum n => pure n
  | AId x => (st <- send Get;
              pure (st x))
  | APlus a1 a2 | AMinus a1 a2 | AMult a1 a2
                                 => denote_aexp a1 ;; denote_aexp a2
  end.

Fixpoint denote_bexp `{Member (State state) effs}
         (b:bexp): Eff ([State state]++effs) bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 | BLe a1 a2 => (x1 <- (denote_aexp a1) ;
                               x2 <- (denote_aexp a2) ;
                               pure (beq_nat x1 x2))
  | BAnd b1 b2 => (x1 <- (denote_bexp b1);
                    x2 <- (denote_bexp b2);
                    pure (andb x1 x2))
  | BNot b' => (b'' <- denote_bexp b';
                 pure (negb b''))
  end.

Fixpoint denote_imp `{Member (State state) effs}
         (c: com): Eff ([State state]++effs) state :=
  match c with
  | SKIP => (st <- send Get; pure st)
  | CAss x ax => (a <- denote_aexp ax;
                   st <- send Get;
                   pure (t_update st x a))
  | IFB b THEN c1 ELSE c2 FI => b' <- denote_bexp b;
                                 if (b':bool)
                                 then denote_imp c1
                                 else  denote_imp c2
  | c1 ;;; c2 => denote_imp c1 ;; denote_imp c2
  | WHILE b DO c' END => st <- send Get; pure st
  end.

Inductive NDaexp: Type :=
| Daexp : aexp -> NDaexp
| NDnum : (Choice nat) -> NDaexp.

Inductive NDbexp : Type :=
| NDBool: (Choice bool) -> NDbexp
| NBTrue : NDbexp
| NBFalse : NDbexp
| NBEq : NDaexp -> NDaexp -> NDbexp
| NBLe : NDaexp -> NDaexp -> NDbexp
| NBNot : NDbexp -> NDbexp
| NBAnd : NDbexp -> NDbexp -> NDbexp.

Inductive NDcom : Type :=
| NDCSkip : NDcom
| NDCAss : string -> NDaexp -> NDcom
| NDCSeq : NDcom -> NDcom -> NDcom
| NDCIf : NDbexp -> NDcom -> NDcom -> NDcom
| NDCWhile : NDbexp -> NDcom -> NDcom.


Definition Fuel: Type -> Type := State nat.

Definition step_fuel `{Member Fuel effs} `(f: a -> Eff effs v) (x: a) (default: v):
  (Eff effs v) :=
  fuel <- send Get;
     (match fuel with
      | O => pure default
      | S n' => send (Put n');; f x
      end).

Fixpoint denote_NDaexp `{Member Choice effs} `{Member (State state) effs} `{Member Fuel effs}
         (na: NDaexp): Eff effs nat :=
  match na with
  | Daexp a => denote_aexp a
  | NDnum (Pick p) => n <- send (Pick (fun (x: nat) => p x));
              pure n
  end.

Fixpoint denote_NDbexp `{Member Choice effs} `{Member (State state) effs} `{Member Fuel effs}
         (nb:NDbexp): Eff effs bool :=
  match nb with
  | NDBool (Pick p) => b <- send (Pick (fun (b: bool) => p b));
                        pure b
  | NBTrue => pure true
  | NBFalse => pure false
  | NBEq a1 a2 => (x1 <- (denote_NDaexp a1) ;
                    x2 <- (denote_NDaexp a2) ;
                    pure (beq_nat x1 x2))
  | NBLe a1 a2 => (x1 <- (denote_NDaexp a1) ;
                    x2 <- (denote_NDaexp a2) ;
                    pure (leb x1 x2))
  | NBAnd b1 b2 => (x1 <- (denote_NDbexp b1);
                    x2 <- (denote_NDbexp b2);
                    pure (andb x1 x2))
  | NBNot b' => (b'' <- denote_NDbexp b';
                 pure (negb b''))
  end.

Fixpoint denote_NDimp `{Member Choice effs} `{Member (State state) effs} `{Member Fuel effs}
         (nc: NDcom): Eff effs unit :=
  match nc with
  | NDCSkip => pure tt
  | NDCAss x ax => (a <- denote_NDaexp ax;
                   st <- send Get;
                   send (Put (t_update st x a));;
                   pure tt)

  | NDCIf b c1 c2 => b' <- denote_NDbexp b;
                            if (b':bool)
                            then denote_NDimp c1
                            else  denote_NDimp c2
  | NDCSeq c1 c2 => denote_NDimp c1 ;; denote_NDimp c2
  | NDCWhile b c' => fuel' <- send Get;
                      (fix run_fuel n :=
                         b' <- denote_NDbexp b;
                         if (b': bool)
                         then match n with
                              | O => pure tt
                              | S n => denote_NDimp c';;
                                        run_fuel n
                              end
                         else pure tt) fuel'
  end.

Definition effect_swap `(e: Eff ([eff1; eff2]++effs) v) : Eff ([eff2; eff1]++effs) v.
Proof.
  unfold Eff in *.
  induction e.
  - constructor; auto.
  - inversion f; subst.
    -- constructor 2 with x; auto.
       constructor 2; eauto.
       constructor 1; eauto.
    -- inversion X0; subst.
       --- constructor 2 with x; auto.
           constructor; auto.
       --- constructor 2 with x; auto.
           repeat constructor 2.
           auto.
Defined.

Notation "⇄ x" := (effect_swap x) (at level 50).
Notation "⟦ c ⟧" := (@denote_NDimp [Choice; State state; Fuel] _ _ _ c) (at level 40).

Definition plusNDet :=
  ⟦ NDCAss "X" (NDnum (Pick (fun x => x <= 2))) ⟧.

Definition plusDet :=
  ⟦ NDCAss "X" (Daexp (ANum 2)) ⟧.

Lemma refines_plus:
  refines plusNDet plusDet.
Proof.
  unfold refines.
  intros.
  cbn in *.
  destruct x; simpl.
  -- inversion H.
  -- simpl in *.
     constructor 2 with 2; eauto.
Qed.

Definition nonDet_assign:=
  send (Put 1);; ⟦ NDCWhile (NDBool (Pick (fun b => b = true))) (NDCAss "X" (Daexp (ANum 3))) ⟧.

Definition det_assign:=
  send (Put 1);; ⟦ NDCWhile NBTrue (NDCAss "X" (Daexp (ANum 3))) ⟧.

Inductive Fix {dom cod} : Type -> Type:=
   | call : forall (x:dom), Fix (cod x).

Ltac clean_existTs := repeat match goal with
     | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
     end; subst.

Lemma refines_assign:
  refines nonDet_assign det_assign.
Proof.
  intros.
  intro.
  simpl.
  induction x; intro.
  -- inversion H.
  -- unfold det_assign in *.
     simpl in *.
     unfold denotes_choice in *.
     inversion H0; subst.
     clean_existTs.
     clear H2.
     simpl in *.
     inversion H0.
     clean_existTs.
Admitted.

(* Sept 13th meeting
 * 1 V Denotes polimorphic on the rest of the effects
 * 2 V Choice to aexp
 * 3 V State in denote
 * 4 V Write an Imp program with choice and show that you can refine to another without
 * 5 - Formulate Heap operations in the Algebraic Effects
 * 6 - Semantics of while with the Comp monad
 *     -- look at the delay effect 
 *     -- use fuel
 *     -- encode the idea of fuel as an effect
 *        -> show that any action in the presence of fuel terminates
 *)

(* Sept 20th meeting
 * 1 - Change denote_choice to use Handlerelayp (Fix refinement)
       -- This way we look at each node equally
   2 - Denote
     a) Fuel
     b) Fix Monad / Delay (They are different things, though)
     c) 
*)
(* Sept 27th meeting
 * Fix dom cod : Type -> Type: =
   | call : forall (x:dom), Fix (cod x) -- or something like that
 *
 * Imp with a heap
 *   -> 
 * Implement Imp with a Compcert heap as an effect
 * Implement Imp with a Raw memory (I assume this is from Fiat) as an effect
 *   -> Need to import those libs to here
 * Define a (stateful) homomophism between the two
 * 
*)