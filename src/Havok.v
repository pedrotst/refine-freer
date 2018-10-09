Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.omega.Omega
  Coq.Lists.List
  Coq.Strings.String.

Require Import Maps.

Require Export
  Eff
  Comp
  Choice.

Import ListNotations.

Generalizable All Variables.

Require Import
  Hask.Control.Monad
  RWS.

(* The idea of the Havok operation is that it will receive
 * a predicate over a memory and work upon that *)

Inductive aexp: Type :=
  ANum : nat -> aexp
  | NDNum : (Choice nat) -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ARand : aexp.

Inductive bexp : Type :=
  BTrue : bexp
  | BFalse : bexp
  | NDBool: (Choice bool) -> bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Definition state := total_map nat.

Inductive com : Type :=
  CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CHavok: (Choice state) -> com.


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


Fixpoint denote_aexp `{Member Choice effs} `{Member (State state) effs} (a : aexp)
  : Eff effs nat :=
  match a with
  | ANum n => pure n
  | NDNum (Pick p) => n <- send (Pick (fun (x: nat) => p x)); pure n
  | AId x => (st <- send Get; pure (st x))
  | APlus a1 a2 => lhs <- (denote_aexp a1); rhs <- (denote_aexp a2); pure (lhs + rhs)
  | AMinus a1 a2  => lhs <- (denote_aexp a1); rhs <- (denote_aexp a2); pure (lhs - rhs)
  | AMult a1 a2 => lhs <- (denote_aexp a1); rhs <- (denote_aexp a2); pure (lhs * rhs)
  | ARand => n <- send (Pick (fun _ => True)); pure n
  end.

Fixpoint denote_bexp `{Member Choice effs} `{Member (State state) effs} (b : bexp)
  : Eff effs bool :=
  match b with
  | BTrue       => pure true
  | BFalse      => pure false
  | NDBool (Pick p) => b <- send (Pick (fun (b: bool) => p b)); pure b
  | BEq a1 a2   =>  lhs <- (denote_aexp a1); rhs <- (denote_aexp a2); pure (beq_nat lhs rhs)
  | BLe a1 a2   => lhs <- (denote_aexp a1); rhs <- (denote_aexp a2); pure (leb lhs rhs)
  | BAnd b1 b2  => lhs <- (denote_bexp b1); rhs <- (denote_bexp b2); pure (andb lhs rhs)
  | BNot b'     => (denote_bexp b') >>= pure
  end.

Fixpoint denote_com `{Member Choice effs} `{Member (State state) effs} (c : com)
  : Eff effs unit :=
  match c with
    | CSkip => pure tt
    | CAss x a1 => (a <- denote_aexp a1;
                    st <- send Get;
                    send (Put (t_update st x a));;
                         pure tt)
    | CSeq a1 a2 => denote_com a1 ;; denote_com a2
    | CIf b cI cE => b' <- denote_bexp b;
                      if (b':bool)
                      then denote_com cI
                      else denote_com cE
    | CHavok (Pick p) => (s <- send (Pick (fun (s': state) => p s'));
                          send (Put s);;
                          pure tt)
  end.