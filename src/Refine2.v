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

Fixpoint denotes_choice' `(s1: Eff (Choice :: effs) v) (s2: Eff [] v): Prop :=
  match s2 with
  | Impure u k => False_rect _ (Union_empty _ u)
  | Pure a2 =>
    match s1 with
    | Pure a1 => a1 = a2
    | Impure u1 k =>
      match decomp u1 with
      | inl (Pick p) => exists a, denotes_choice' (k a) s2 /\ p a
      | inr u' => exists a, denotes_choice' (k a) s2
      end
    end
  end.

Fixpoint denotes_choice `(s1: Eff (Choice :: effs) v) (s2: Eff effs v): Prop :=
  match s2 with
  | Impure u k => exists a, denotes_choice s1 (k a) /\ ~ In Choice effs
  | Pure a2 => denotes_choice' s1 (Pure a2)
  end.

Fixpoint denotes_comp' `(s1: Eff (Comp :: effs) v): Eff [] v -> Prop :=
  fun s2 => match s2 with
  | Impure u _ => False_rect _ (Union_empty _ u)
  | Pure a2 =>
    match s1 with
    | Pure a1 => a1 = a2
    | Impure u1 k =>
      match decomp u1 with
      | inl p => exists a, denotes_comp' (k a) s2 /\ p a
      | inr u' => exists a, denotes_comp' (k a) s2
      end
    end
  end.

Fixpoint denotes_comp `(s1: Eff (Comp :: effs) v) (s2: Eff effs v): Prop :=
  match s2 with
  | Impure u k => exists a, denotes_comp s1 (k a) /\ ~ In Comp effs
  | Pure a2 => denotes_comp' s1 (Pure a2)
  end.

(*
Fixpoint denotes_state `(s1 s2: Eff ((State x) :: effs) v): Prop :=
  match s1, s2 with
  | Pure a1, Pure a2 => a1 = a2
  | Impure u1 k1, Impure u2 k2 =>
    match decomp u1, decomp u2 with
      | inl p1, inl p2 => exists a1 a2, denotes_state (k1 a1) (k2 a2) /\ p1 = p2
      | inr u1', inr u2' => exists a1 a2, denotes_state (k1 a1) (k2 a2)
      | _, _ => False
      end
  | _, _ => False 
  end.
*)


Lemma reduce_nonDet: 
  denotes_choice nonDet_list (pure (repeat 10 11)).
Proof.
  intros.
  simpl.
  eexists.
  split; eauto; simpl; eauto.
Qed.

Lemma nonEffect_Denotes: forall v effs (l: v),
    @denotes_choice effs _ (pure l) (pure l).
Proof.
  reflexivity.
Qed.

Lemma nonEffect_pure: forall v x (l: v),
    @denotes_choice nil _ (pure l) x -> x = (pure l).
Proof.
  destruct x; intros; simpl in *.
  - subst.
    reflexivity.
  - inversion u.    
Qed.

Lemma pure_nonEffect: forall v (l: v) x,
    x = (pure l) -> @denotes_choice nil _ (pure l) x.
Proof.
  intros; subst.
  reflexivity.
Qed.

(* e1 refines e2 if forall t \in [| e2 |] -> t \in [| e1 |] *)
Definition refines {v} {effs} e1 e2 := forall t, @denotes_choice v effs e2 t -> @denotes_choice v effs e1 t.

Lemma refines_detList_nonDetList:
    refines nonDet_list det_list.
Proof.
  intros t H.
  apply nonEffect_pure in H.
  subst.
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


(*
Polymorphic Inductive Fuel {a: Type} (t: a -> a): a -> Type :=
| Consume : forall (v: a), Fuel t (t v).
*)
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
  | NBEq a1 a2 | NBLe a1 a2 => (x1 <- (denote_NDaexp a1) ;
                               x2 <- (denote_NDaexp a2) ;
                               pure (beq_nat x1 x2))
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

(* e1 refines e2 if forall t \in [| e2 |] -> t \in [| e1 |] *)
Definition refines_imp {v} {effs} e1 e2 := forall t, @denotes_choice v effs e2 t -> @denotes_choice v effs e1 t.



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
  induction t; simpl.
  -- exists 2; eauto.
  -- simpl in *.
     destruct H.
     exists x0.
     destruct H.
     split; auto.
Qed.
Definition nonDet_assign:=
  ⟦ NDCWhile (NDBool (Pick (fun b => b = true))) (NDCAss "X" (Daexp (ANum 3))) ⟧.

Definition det_assign:=
  ⟦ NDCWhile NBTrue (NDCAss "X" (Daexp (ANum 2))) ⟧.

Lemma refines_assign:
  refines nonDet_assign det_assign.
Proof.
  unfold refines.
  intros.
  induction t.
  -- destruct H.
     simpl in *; eauto.
     induction x.
     --- simpl in *.
         exists 0; simpl.
         exists true; split; eauto.
     --- simpl in *.
         apply IHx.
         destruct H.
         destruct H.
         auto.
  -- simpl in *.
     destruct H.
     destruct H.
     eexists.
     split; eauto.
Qed.

(* 1 V Denotes polimorphic on the rest of the effects
   2 V Choice to aexp
   3 V State in denote
   4 V Write an Imp program with choice and show that you can refine to another without
   5 - Formulate Heap operations in the Algebraic Effects
   6 - Semantics of while with the Comp monad
       -- look at the delay effect 
       -- use fuel
       -- encode the idea of fuel as an effect
          -> show that any action in the presence of fuel terminates
*)