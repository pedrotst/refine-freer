Require Import Imp.
Require Import Maps.
(* Require Import SfLib. for [admit] *)

(* Extensional: Enumeration *)
(* Seen this style of definition before... *)
Definition Set' (A : Type) := list A.

(* Intensional: Characteristic 'Function' *)
Definition Bool_Set (A : Type) := A -> bool.

(* Definition evens' : Bool_Set nat := evenb. *)

Definition In_b {A} (a : A) (e : Bool_Set A) : Prop :=
  e a = true.

Definition Same_Set' {A} (e1 e2 : Bool_Set A) : Prop :=
  forall x, e1 x = e2 x.

(* How to define Intersection, Union, Subset ? *)
Definition Union' {A} (e1 e2 : Bool_Set A) : Bool_Set A :=
  fun x => orb (e1 x) (e2 x).

Definition Intersection' {A} (e1 e2 : Bool_Set A)
  : Bool_Set A :=
  fun x => andb (e1 x) (e2 x).

Definition Subset' {A} (e1 e2 : Bool_Set A) : Prop :=
  forall x, In_b e1 x -> In_b e2 x.

(* This embedding means we can always decide membership! *)

  (* Let's use Prop instead! *)

Definition Prop_Set (A : Type) := A -> Prop.

Definition evens : Prop_Set nat :=
  fun n => exists m, n = 2 * m.

Definition In {A} (a : A) (e : Prop_Set A) : Prop :=
  e a.

Notation "x '∈' e" := (In x e) (at level 60).

(*Definition odds : Prop_Set nat := ???.*)

(* Membership doesn't need to be decideable! *)
Definition terminating : Prop_Set com :=
  fun c => forall sigma,
      exists sigma',
        c / sigma \\ sigma'.

Lemma skip_in_terminating :
  SKIP ∈ terminating.
Proof.
  unfold terminating.
  unfold In.
  intros.
  exists sigma.
  constructor.
Qed.

Definition Same_Set {A} (e1 e2 : Prop_Set A) :=
  forall x, x ∈ e1 <-> x ∈ e2.

(* How to define Intersection, Union, Subset ? *)
Definition Union {A} (e1 e2 : Prop_Set A) : Prop_Set A := fun x => x ∈ e1 \/ x ∈ e2.

Definition Intersection {A} (e1 e2 : Prop_Set A)
  : Prop_Set A := fun x => x ∈ e1 /\ x ∈ e2.

Definition Subset {A} (e1 e2 : Prop_Set A) : Prop :=
  forall x, x ∈ e1 -> x ∈ e2.

Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 60).

Lemma Subset_transitive {A}
  : forall (e1 e2 e3 : Prop_Set A),
    e1 ⊆ e2
    -> e2 ⊆ e3
    -> e1 ⊆ e3.
Proof.
  intros e1 e2 e3 ? ? x In_x.
  apply H in In_x.
  apply H0 in In_x.
  apply In_x.
Qed.

Definition AExpDom := Prop_Set (nat * state).
Definition BExpDom := Prop_Set (bool * state).
Definition ComDom := Prop_Set (state * state).

Reserved Notation "'[[' a ']]A'" (at level 40).
Reserved Notation "'[[' b ']]B'" (at level 40).
Reserved Notation "'[[' c ']]'" (at level 40).

Fixpoint denote_A (a : aexp) : AExpDom :=
  fun nst =>
  match a, nst with
  | ANum n, (n', st) =>
    n' = n

  | AId x, (n', st) =>
    n' = st x

  | APlus a1 a2, (n', st) =>

    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A
    /\ (v2, st) ∈ [[ a2 ]]A
    /\ n' = v1 + v2



  | AMinus a1 a2, (n', st) =>
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A
    /\ (v2, st) ∈ [[ a2 ]]A
    /\ n' = v1 - v2
  | AMult a1 a2, (n', st) =>
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A
    /\ (v2, st) ∈ [[ a2 ]]A
    /\ n' = v1 * v2
  end
where "'[[' a ']]A'" := (denote_A a).

Fixpoint denote_B (b : bexp) : BExpDom :=
  fun nst =>
  match b, nst with
  | BTrue, (v, st) =>
    v = true
  | BFalse, (v, st) =>
    v = false
  | BEq a1 a2, (v, st)   =>
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 -> v = true)
    /\ (v1 <> v2 -> v = false)

  | BLe a1 a2, (v, st)   =>
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 <= v2 -> v = true)
    /\ (~ v1 <= v2 -> v = false)

  | BNot b1, (v, st)     =>
    (negb v, st) ∈ [[ b1 ]]B

  | BAnd b1 b2, (v, st)  =>
    exists v1 v2,
    (v1, st) ∈ [[ b1 ]]B /\ (v2, st) ∈ [[ b2 ]]B
    /\ v = (andb v1 v2)
  end
where "'[[' b ']]B'" := (denote_B b).


(* Need a fixpoint operator for sets! *)
Fail Fixpoint Fix' {A} (Gamma : Prop_Set A -> Prop_Set A) : Prop_Set A :=
  Gamma (Fix' Gamma).

Definition Fix {A} (Gamma : Prop_Set A -> Prop_Set A)
  : Prop_Set A :=
  fun a =>
    forall phi, Gamma phi ⊆ phi -> a ∈ phi.

Fixpoint denote_Com (c : com)
  : ComDom :=
  match c with
  | SKIP =>
    fun stst' =>
      let (st, st') := stst' in
      st = st'
  | x ::= a1 =>
    fun stst' =>
      let (st, st') := stst' in
      exists v,
        (v, st) ∈ [[a1]]A
      /\ st' = t_update st x v

  | c1 ;;; c2 =>
    fun stst' =>
      let (st, st') := stst' in
      exists st'',
        (st, st'') ∈ [[c1]] /\
      (st'', st') ∈ [[c2]]

  | IFB b THEN c1 ELSE c2 FI =>
    fun stst' =>
      let (st, st') := stst' in
      ((true, st) ∈ [[b]]B /\ (st, st') ∈ [[c1]])
      \/ ((false, st) ∈ [[b]]B /\ (st, st') ∈ [[c2]])

  | WHILE b DO c END =>
      Fix (fun phi : Prop_Set _ =>
             fun st : state * state =>
               let (st, st') := st in
               ((false, st) ∈ [[b]]B /\ st' = st)
               \/ (exists st'',
                      (true, st) ∈ [[b]]B /\
                      (st, st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi))


  end
where "'[[' c ']]'" := (denote_Com c).

Definition com_eq (c c' : com) : Prop :=
  Same_Set ([[ c ]]) ([[c']]).

Lemma seq_skip_opt :
  forall c,
    com_eq (SKIP;;; c) c.
Proof.
  unfold com_eq. unfold Same_Set. split; intros.
  - destruct x; simpl in H.
    unfold In in H.
    destruct H as [st'' [? ?] ].
    subst.
    unfold In.
    apply H0.
  - destruct x; simpl; unfold In.
    exists s; split.
    reflexivity.
    apply H.
Qed.

Lemma while_monotone :
  forall b c (e1 e2 : Prop_Set (state * state)),
    e1 ⊆ e2 ->
    (fun (st : state * state) =>
       let (st0, st') := st in
       ((false, st0) ∈ [[b]]B /\ st' = st0) \/
       (exists st'' : state,
           (true, st0) ∈ [[b]]B /\ (st0, st'') ∈ [[c]] /\ (st'', st') ∈ e1))
      ⊆
    (fun (st : state * state) =>
       let (st0, st') := st in
       ((false, st0) ∈ [[b]]B /\ st' = st0) \/
       (exists st'' : state,
           (true, st0) ∈ [[b]]B /\ (st0, st'') ∈ [[c]] /\ (st'', st') ∈ e2)).
Proof.
  unfold Subset, In; intros.
  destruct x; destruct H0 as [? | [st'' [? [? ?] ] ] ].
  - left; eassumption.
  - right; eexists; repeat split; try eassumption.
    apply H; assumption.
Qed.

Lemma IF_WHILE_eq :
  forall b c,
    com_eq (IFB b THEN (c;;; WHILE b DO c END) ELSE SKIP FI)
           (WHILE b DO c END).
Proof.
  unfold com_eq, Same_Set; split; intros.
  - destruct x; simpl in H; unfold In in H.
    simpl.
    (* Need to unfold one iteration of the loop, BUT HOW? *)
Abort.

(* Restatement of the definition of Fix: if we wanted to show that *)
(* a is in a set [phi], and we know that a is in [Fix Gamma], it  *)
(* suffices to show that [phi] is *closed* under [Gamma]. *)
Lemma In_Fix {A} (Gamma : Prop_Set A -> Prop_Set A) :
  forall a,
    a ∈ Fix Gamma
    -> forall phi, Gamma phi ⊆ phi -> a ∈ phi.
Proof.
  (* By Definition. *)
  intros; apply H; assumption.
Qed.

(* This unrolls one application of the fixpoint. *)
Lemma Fix_Subset {A} :
  forall Gamma
         (Gamma_monotone :
            forall e1 e2,
              e1 ⊆ e2 -> Gamma e1 ⊆ Gamma e2),
     Gamma (Fix (A := A) Gamma) ⊆ Fix Gamma.
Proof.
  intros Gamma ? a In_a phi Sub_Gamma.
  (* Definition of Fix. *)
  apply Sub_Gamma.
  (* Monotonicity of Gamma. *)
  eapply Gamma_monotone with (e1 := Fix Gamma); try assumption.
  (* Definition of Fix again. *)
  intros a' In_a'.
  apply In_a'; assumption.
Qed.

(* We can also 're-roll' an application of the fixpoint *)
Lemma Fix_is_Fixpoint {A} :
  forall Gamma
         (Gamma_monotone :
            forall e1 e2,
              e1 ⊆ e2 -> Gamma e1 ⊆ Gamma e2),
    @Same_Set A (Gamma (Fix Gamma)) (Fix Gamma).
Proof.
  intros.
  split; intros.
  - apply Fix_Subset; eassumption.
  - eapply In_Fix; try eassumption.
    eapply Gamma_monotone.
    apply Fix_Subset; eassumption.
Qed.

Lemma IF_WHILE_eq :
  forall b c,
    com_eq (IFB b THEN (c;;; WHILE b DO c END) ELSE SKIP FI)
           (WHILE b DO c END).
Proof.
  unfold com_eq, Same_Set; split; intros.
  - destruct x; simpl in H; unfold In in H.
    simpl.
    simpl.
      eapply (proj1 (Fix_is_Fixpoint _ (while_monotone _ _) _));
      unfold In in *; intros.
    (* The denotation of [if] is built from the denotations of each branch *)
    destruct H as [ [Denote_b [st'' [? ? ] ] ] | [Denote_b st_eq] ].
    + right.
      eexists; repeat split; try eassumption.
    + left; subst; split; try eassumption; reflexivity.
  - simpl in H.
    (* Again, unfold one iteration of the loop. *)
    eapply (proj2 (Fix_is_Fixpoint _ (while_monotone _ _) _)) in H.
    (* The denotation of [while] is built from the denotation *)
    (* of the loop body and the denotation of the terminating case. *)
    destruct x; simpl in H; unfold In in H.
    destruct H as [ [? ?] | [st' [Denote_b [? ?] ] ] ].
    + simpl; unfold In.
      right; split; subst; try eassumption; reflexivity.
    + simpl; unfold In; left; repeat split; try eassumption.
      eexists; repeat split; eassumption.
Qed.

Lemma Denotational_A_BigStep_Equivalent :
  forall a st,
    (aeval st a, st) ∈ [[a]]A.
Proof.
  intros;
  induction a; simpl; try solve [constructor]; unfold In;
  eexists _, _; repeat split; try eassumption.
Qed.

Lemma Denotational_B_BigStep_Equivalent :
  forall b st,
    (beval st b, st) ∈ [[b]]B.
Proof.
Admitted.

Lemma BigStep_Denotational_Equivalent :
  forall c st st',
    c / st \\ st' -> (st, st') ∈ [[c]].
Proof.
  intros.
  induction H; simpl; try solve [econstructor]; unfold In.
  - (* E_Ass *)
    eexists; split; try reflexivity.
    rewrite <- H; eapply Denotational_A_BigStep_Equivalent.
  - (* E_Seq *)
    eexists; split; try reflexivity; eassumption.
  - (* E_IfTrue *)
    left; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Equivalent.
  - (* E_IfFalse *)
    right; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Equivalent.
  - (* E_WhileEnd *)
    apply Fix_is_Fixpoint.
    apply while_monotone.
    left.
    split; try reflexivity.
    rewrite <- H; apply Denotational_B_BigStep_Equivalent.
  - (* E_WhileLoop *)
    apply Fix_is_Fixpoint.
    apply while_monotone.
    right.
    eexists; repeat split; try eassumption.
    rewrite <- H; apply Denotational_B_BigStep_Equivalent.
Qed.

Lemma BigStep_A_Denotational_Equivalent :
  forall a st v,
    (v, st) ∈ [[a]]A
    -> v = aeval st a.
Proof.
  induction a; simpl; intros st v H;
    unfold In in H; try eassumption.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
Qed.

Lemma BigStep_B_Denotational_Equivalent :
  forall b st v,
    (v, st) ∈ [[b]]B
    -> v = beval st b.
Proof.
Admitted.

(* Yet another restatement of the definition of Fix; this time as *)
(* the principle of mathematical induction. *)
Lemma Fix_ind {A}
      (P : A -> Prop)
      (Gamma : Prop_Set A -> Prop_Set A)
  : forall a,
    (Gamma P ⊆ P)
    -> a ∈ Fix Gamma
    -> P a.
Proof.
  intros a P_Ind a_In.
  eapply In_Fix; try eassumption.
Qed.

Lemma Denotational_BigStep_Equivalent :
  forall c st st',
    (st, st') ∈ [[c]] -> c / st \\ st'.
Proof.
  induction c; unfold In; simpl; intros st st' denote_c.
  - (* SKIP *)
    subst; econstructor.
  - (* Assignment *)
    destruct denote_c as [v [? ?] ].
    subst; econstructor.
    erewrite BigStep_A_Denotational_Equivalent; try reflexivity; assumption.
  - (* Sequence *)
    destruct denote_c as [v [denote_c1 denote_c2] ].
    subst; econstructor.
    + apply IHc1; eassumption.
    + apply IHc2; eassumption.
  - (* Conditional *)
    destruct denote_c as [ [denote_b denote_c1] | [denote_b denote_c2] ].
    + constructor.
      erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
      apply IHc1; eassumption.
    + apply E_IfFalse.
      erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
      apply IHc2; eassumption.
  - apply Fix_is_Fixpoint in denote_c; try apply while_monotone.
    destruct denote_c as [ [denote_b st_eq]
                         | [st'' [denote_b [denote_c ? ] ] ] ].
    + rewrite st_eq; econstructor.
      erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
    + eapply E_WhileLoop.
      erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
      apply IHc; eassumption.
      change st'' with (fst (st'', st')).
      change st' with (snd (st'', st')) at 2.
      pattern (st'', st').
      (* Hmmmm... we're (almost) back to where we started! *)
      (* Why can't we apply the Inductive Hypothesis? *)
      eapply Fix_ind; try eassumption.
      generalize IHc; clear.
      intros IHc [st'' st']
             [ [denote_b st_eq]
             | [st''0 [denote_b [denote_c ? ] ] ] ].
      * subst; econstructor.
        erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
      * econstructor.
        erewrite BigStep_B_Denotational_Equivalent; try reflexivity; assumption.
        apply IHc; eassumption.
        apply H.
Qed.