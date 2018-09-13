Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Sets.Ensembles
  Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Comp (A : Type) := A -> Prop.

Instance Comp_Functor : Functor Comp :=
  {
    (* fmap: forall a b, (a -> b) -> (Comp a) -> b -> Prop *)
    fmap := fun (a b: Type) (ma: a -> b) (fa: a -> Prop) (xb: b) => exists (xa: a), ma xa = xb /\ fa xa

  }.
Program Instance Comp_Applicative : Applicative Comp :=
  {
    pure := fun A (a: A) (a': A) => a = a';
    ap := fun A B (f: (A -> B) -> Prop) (g: A -> Prop) (b: B) => exists a (fa_b: A -> B),
              fa_b a = b /\ g a /\ f fa_b
  }.

Program Instance Comp_Alternative : Alternative Comp :=
  {
    empty := fun _ _ => False;
    choose := fun X (f1: X -> Prop) (f2: X -> Prop) x => f1 x \/ f2 x
  }.

Program Instance Comp_Monad : Monad Comp :=
  {
    join := fun A (f: (A -> Prop) -> Prop) a => exists f', f' a /\ f f'
  }.

Module CompLaws.

Import MonadLaws.

Require Import FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Ltac shatter :=
  unfold comp, id in *;
  repeat
    match goal with
    | [ H : _ = _           |- _               ] => subst
    | [ H : and _ _         |- _               ] => destruct H
    | [ H : exists _ : _, _ |- _               ] => destruct H
    | [                     |- exists _ : _, _ ] => eexists
    | [                     |- and _ _         ] => split
    end;
  simpl in *.

Ltac simplify_comp :=
  repeat let x := fresh "x" in extensionality x;
  try (apply prop_ext; split; intros);
  repeat (simpl; shatter; try constructor; eauto).

Local Obligation Tactic := simpl; intros; simplify_comp.

Program Instance Comp_FunctorLaws     : FunctorLaws Comp.
Program Instance Comp_ApplicativeLaws : ApplicativeLaws Comp.
Program Instance Comp_MonadLaws       : MonadLaws Comp.

End CompLaws.

Definition comp `(f : A -> Prop) : Comp A := f.

Definition computes_to {A : Type} (ca : Comp A) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v) (at level 40).

(*

  fmap := fun A B f (x : Comp A) b => exists a : A, x a /\ f a = b
  pure := fun _ x a => x = a;
  ap   := fun A B mf mx r => exists f x, mf f /\ mx x /\ f x = r

  empty  := fun A _ => False;
  choose := fun A x y s => x s \/ y s (* jww (2016-01-28): right? *)

  join := fun A m r => exists t : Comp A, t r /\ m t
*)