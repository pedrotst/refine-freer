Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Maps.

Require Export
  Eff
  Comp
  Choice.


Require Import
  Hask.Control.Monad
  RWS.

Generalizable All Variables.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ALoad: aexp -> aexp.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CStore : aexp -> aexp -> com.

Inductive Heap {addr value: Type}: Type -> Type :=
| Read : addr -> Heap value (* Takes an addrs and return a value *)
| Write : addr -> value -> Heap unit. 

Arguments Heap _ _ _ : clear implicits.

Definition Locals := Heap string nat.
Definition HeapCanon := Heap nat nat.

Fixpoint denote_aexp `{Member HeapCanon effs} `{Member Locals effs}
         (a:aexp): Eff effs nat :=
  match a with
  | ANum n => pure n
  | AId x => send (Read x)
  | APlus a1 a2 => (l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l+r))
  | AMinus a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l-r)
  | AMult a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l*r)
  | ALoad e => a <- denote_aexp e ; send (Read a)
  end.


Fixpoint denote_bexp `{Member HeapCanon effs} `{Member Locals effs}
         (b:bexp): Eff effs bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l =? r))
  | BLe a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l <=? r))
  | BAnd b1 b2 => (l <- (denote_bexp b1); r <- (denote_bexp b2); pure (l && r))
  | BNot b' => (r <- denote_bexp b'; pure (negb r))
  end.

Definition Heap_func `(H: Heap addr val t): val -> (addr * t):=
  match H with
  | Read x => fun v => (x, v)
  | Write x v => fun _ => (x, tt)
  end.

Axiom str_to_num: string -> nat.

Fixpoint denote_imp `{Member HeapCanon effs} `{Member Locals effs}
         (c: com): Eff effs unit :=
  match c with
  | CSkip => pure tt
  | CAss x ax => (a <- denote_aexp ax;
                   t <- send (Write (str_to_num x) a);
                   pure tt)
  | CIf b c1 c2 => b' <- denote_bexp b;
                          if (b':bool)
                          then denote_imp c1
                          else  denote_imp c2
  | CSeq c1 c2 => denote_imp c1 ;; denote_imp c2
  | CStore aaddr aval => adr <- denote_aexp aaddr;
                          val <- denote_aexp aval;
                          t <- send (Write adr val);
                          pure tt
  end.



(* The basic idea here now is to fold these two heaps into a single one via some mapping
 * i.e. A function of the following type:
 * `forall t, Eff (Heap nat nat :+: Locals) t ->
              map nat nat ->
              Eff StackOverflow (map nat nat * t)`
 * Write Effect handler for heap -> work as a finite map.
 * `forall t, Heap k v t -> (map k v) -> (map k v * t)` (edited)
 * forall t, Heap k v t -> State (map k v) t
 *)