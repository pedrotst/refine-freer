Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Require Export
  Eff
  Comp
  Choice.

Require Import
  Hask.Control.Monad
  RWS.

Generalizable All Variables.

(* We start by defining our Imp language
 * We leave While out because we don't have a Fix effect yet
 * And we add two new constructs to this language
 * ALoad, loads a value from the Heap
 * And CStore takes an address and a value to be stored
 *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp 
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ALoad: aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CStore : aexp -> aexp -> com.

(* Some nice, usual, notations... *)
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.
Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

(* Now we define our Heap as an effect
 * It takes an address and a value as input
 * And returns the value read, or unit for the write
 * In the future we can add some StackOverflow effect to know when
 * we are trying to access something out of bounds.
 *)
Inductive Heap {addr value: Type}: Type -> Type :=
| Read : addr -> Heap value (* Takes an addrs and return a value *)
| Write : addr -> value -> Heap unit. 

Arguments Heap _ _ _ : clear implicits.

(* Instead of using State effect to store the value of the local variables
 * we use the Heap itself
 *)
Definition Locals: Type -> Type := Heap string nat.

(* We also need another Heap for all the stores *)
Definition HeapCanon: Type -> Type := Heap nat nat.

(* The denotation functions follows straightfoward with these two heaps as effects
 * TODO: add other effects
 *)
Fixpoint denote_aexp {effs} (a:aexp): Eff ([Locals; HeapCanon]++effs) nat :=
  match a with
  | ANum n => pure n
  | AId x => send (Read x)
  | APlus a1 a2 => (l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l+r))
  | AMinus a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l-r)
  | AMult a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l*r)
  | ALoad e => a <- denote_aexp e ; send (Read a)
  end.

Fixpoint denote_bexp {effs} (b:bexp): Eff ([Locals; HeapCanon]++effs) bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l =? r))
  | BLe a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l <=? r))
  | BAnd b1 b2 => (l <- (denote_bexp b1); r <- (denote_bexp b2); pure (l && r))
  | BNot b' => (r <- denote_bexp b'; pure (negb r))
  end.

Fixpoint denote_imp {effs} (c: com): Eff ([Locals; HeapCanon]++effs) unit :=
  match c with
  | CSkip => pure tt
  | CAss x ax => (a <- denote_aexp ax;
                   send (Write x a);;
                   pure tt)
  | CIf b c1 c2 => b' <- denote_bexp b;
                          if (b':bool)
                          then denote_imp c1
                          else  denote_imp c2
  | CSeq c1 c2 => denote_imp c1 ;; denote_imp c2
  | CStore aaddr aval => addr <- denote_aexp aaddr;
                          val <- denote_aexp aval;
                          send (Write addr val);;
                          pure tt
  end.

(* It would be nice if we can collapse these two heaps in only one
 * We choose to erase the Locals Heap, since nat is a more natural key then string
 *)
Fixpoint string_to_asciiList (s: string): list ascii :=
  match s with
  | EmptyString => []
  | String x xs => x :: string_to_asciiList xs
  end.

(* As a first approach we chose the trivial hash function of multiplying all the
 * ascii values of the string together *)
Definition hash_string (s: string): nat :=
  fold_right (fun c n => n * nat_of_ascii c) 1 (string_to_asciiList s).

Eval compute in (hash_string "0").
Eval compute in (hash_string "1").
Eval compute in (hash_string "01").
(* It works! *)

(* Now we write the handler responsible to translate Locals to Effs with Heapcanon *)
Definition handler `{Member HeapCanon effs}: Locals ~> Eff effs :=
  fun `(H: Locals a) =>
    match H with
    | Read addr => c <- send (Read (hash_string addr)); pure c
    | Write addr val => send (Write (hash_string addr) val);; pure tt
    end.

(* With this we have everything we need to fuse the Locals heap into the HeapCanon *)
Definition heap_fusion {effs}
  : Eff (Locals::(HeapCanon::effs)) unit -> Eff (HeapCanon :: effs) unit:=
  @interpret _ _ handler unit.

(* Here is an example of this in action *)
Definition foo: com := ("X" ::= ANum 3;;; "Y" ::= 4;;; CStore 0 (4+1) ;;; CStore 1 (4+2);;;
                                             "Z" ::= ALoad 0;;; SKIP).

Notation "⟦ c ⟧" := (@denote_imp nil c) (at level 40).

Definition foo_denote := ⟦ foo ⟧.

Eval compute in (foo_denote).
Eval compute in (heap_fusion foo_denote).