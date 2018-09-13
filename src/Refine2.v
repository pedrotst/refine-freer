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

Program Fixpoint denotes_choice {v} (s1: Eff [Choice] v) (s2: Eff [] v): Prop :=
  match s2 with
  | Impure u _ => False_rect _ (Union_empty _ u)
  | Pure a2 =>
    match s1 with
    | Pure a1 => a1 = a2
    | Impure u1 k =>
      match extract u1 with
      | Pick p => exists a, denotes_choice (k a) s2 /\ p a
      end
    end
  end.


Program Fixpoint denotes {v} (s1: Eff [Comp] v): Eff [] v -> Prop :=
  fun s2 => match s2 with
  | Impure u _ => False_rect _ (Union_empty _ u)
  | Pure a2 =>
    match s1 with
    | Pure a1 => a1 = a2
    | Impure u1 k =>
      match extract u1 with
      | p => exists a, denotes (k a) s2 /\ p a
      end
    end
  end.

Lemma reduce_nonDet: 
  denotes_choice nonDet_list (pure (repeat 10 11)).
Proof.
  intros.
  remember (repeat 10 11) as l.
  simpl.
  exists l.
  subst; split; simpl; auto.
Qed.

Lemma nonEffect_Denotes: forall v (l: v),
    denotes_choice (pure l) (pure l).
Proof.
  reflexivity.
Qed.

Lemma nonEffect_pure: forall v (l: v) x,
    denotes_choice (pure l) x -> x = (pure l).
Proof.
  intros.
  simpl in *.
  destruct x eqn:Heq in *; subst; auto.
  inversion u.
Qed.

Lemma pure_nonEffect: forall v (l: v) x,
    x = (pure l) -> denotes_choice (pure l) x.
Proof.
  intros.
  simpl in *.
  destruct x eqn:Heq in *; subst; auto.
  inversion H; auto.
  inversion u.
Qed.

(* e1 refines e2 if forall t \in [| e2 |] -> t \in [| e1 |] *)
Definition refines {v} e1 e2 := forall t, @denotes_choice v e2 t -> @denotes_choice v e1 t.

Lemma refines_detList_nonDetList:
    refines nonDet_list det_list.
Proof.
  intros t H.
  apply nonEffect_pure in H.
  subst.
  apply reduce_nonDet.
Qed.

Fixpoint pack_aexp (st: state) (a:aexp): Eff [Comp] nat :=
  match a with
  | ANum n => pure n
  | AId x => Impure (@UThis _ Comp _ (fun n => st x = n))
                   (fun n => pure n)
  | APlus a1 a2 | AMinus a1 a2 | AMult a1 a2
                                 => pack_aexp st a1 ;; pack_aexp st a2
  end.

Fixpoint pack_bexp (st: state) (b:bexp): Eff [Comp] bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 | BLe a1 a2 => (x1 <- (pack_aexp st a1) ;
                               x2 <- (pack_aexp st a2) ;
                               pure (beq_nat x1 x2))
  | BAnd b1 b2 => (x1 <- pack_bexp st b1;
                    x2 <- pack_bexp st b2;
                    pure (andb x1 x2))
  | BNot b' => (b'' <- pack_bexp st b';
                 pure (negb b''))
  end.

Fixpoint pack_imp (st: state) (c: com): Eff [Comp] state :=
  match c with
  | SKIP => pure st
  | CAss x ax => (a <- pack_aexp st ax;
                   pure (t_update st x a))
  | IFB b THEN c1 ELSE c2 FI => (b' <- pack_bexp st b;
                                  c1' <- pack_imp st c1;
                                  c2' <- pack_imp st c2;
                                  pure (if b' then c1' else c2'))
  | c1 ;;; c2 => pack_imp st c1 ;; pack_imp st c2
  | WHILE b DO c' END => pure st
  end.

