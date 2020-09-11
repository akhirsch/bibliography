Require Import Coq.Structures.Orders Coq.Structures.Equalities.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.SetoidList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Program.Wf.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Mergesort.

From Equations Require Import Equations.
Require Import Psatz.
        
(*
  A module describing the properties of locations in 
  choreographies and our process calculus. Locations are
  ordered (with equality the usual leibniz equality.
  
  This is inspired by FullUsualOrderedType. However, 
  we're using a set, not a type. Thus, it's a separate 
  module type, and I give a functor to translate to a 
  FullUsualOrderedType. This functor is useful for FMaps. 
  (However, I might build my own FMap later using BSTs, 
  because that's much better than ordered lists.)
 *)
Module Type Locations.

  Parameter Inline(10) t : Set.

  Parameter Inline(40) lt : t -> t -> Prop.
  Parameter Inline(40) le : t -> t -> Prop.
  Axiom le_lteq : forall x y : t, le x y <-> lt x y \/ x = y.

  Declare Instance eq_equiv : @Equivalence t eq.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.

  Declare Instance lt_strorder : StrictOrder lt.
  Declare Instance lt_compat : Proper (eq ==> eq ==> iff) lt.

  Parameter Inline compare : t -> t -> comparison.
  Axiom cmp_spec : forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
End Locations.


Module LocationNotations (L : Locations).
  Infix "<" := L.lt.
  Notation "x > y" := (y < x) (only parsing).
  Notation "x < y < z" := (x < y /\ y < z) (only parsing).
  Infix "<=" := L.le.
  Notation "x >= y" := (y <= x) (only parsing).
  Notation "x <= y <= z" := (x <= y /\ y <= z) (only parsing).
  Infix "?=" := L.compare (at level 70, no associativity).
End LocationNotations.

Module LocationFacts (L : Locations).
  Include (LocationNotations L).

  Instance le_refl : Reflexive L.le.
  unfold Reflexive. intro x. apply <- L.le_lteq. right; reflexivity.
  Defined.

  Instance le_trans : Transitive L.le.
  unfold Transitive. intros x y z x_le_y y_le_z.
  rewrite L.le_lteq in x_le_y. rewrite L.le_lteq in y_le_z.
  rewrite L.le_lteq.
  destruct x_le_y as [x_lt_y | eq]; subst; auto.
  destruct y_le_z as [y_lt_z | eq]; subst; auto.
  left; transitivity y; auto.
  Defined.

  Theorem lt_irrefl : forall x : L.t, ~ x < x.
  Proof using.
    intro x. assert (complement L.lt x x) as H. reflexivity. unfold complement in H; exact H.
  Qed.

  Theorem lt_to_le : forall x y : L.t, x < y -> x <= y.
  Proof using.
    intros x y H; rewrite L.le_lteq; left; exact H.
  Qed.

  Theorem compare_Eq_to_eq : forall (x y : L.t), x ?= y = Eq -> x = y.
  Proof using.
    intros x y H. remember (L.cmp_spec x y) as c; inversion c; auto.
    assert (Lt = Eq) as r by (transitivity (x ?= y); auto); discriminate r.
    assert (Gt = Eq) as r by (transitivity (x ?= y); auto); discriminate r.
  Qed.

  Theorem compare_Lt_to_lt : forall (x y : L.t), x ?= y = Lt -> x < y.
  Proof using.
    intros x y H. remember (L.cmp_spec x y) as c; inversion c; auto.
    assert (Eq = Lt) as r by (transitivity (x ?= y); auto); discriminate r.
    assert (Gt = Lt) as r by (transitivity (x ?= y); auto); discriminate r.
  Qed.

  Theorem compare_Gt_to_gt : forall (x y : L.t), x ?= y = Gt -> x > y.
  Proof using.
    intros x y H. remember (L.cmp_spec x y) as c; inversion c; auto.
    assert (Eq = Gt) as r by (transitivity (x ?= y); auto); discriminate r.
    assert (Lt = Gt) as r by (transitivity (x ?= y); auto); discriminate r.
  Qed.
  Ltac LocationOrder :=
    repeat match goal with
           | [ H : ?l < ?l |- _ ] => exfalso; apply (lt_irrefl l); exact H
           | [ H : ?l <> ?l |- _ ] => exfalso; apply H; reflexivity; auto
           | [ H : Some _ = None |- _ ] => inversion H
           | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l1 |- _ ] => exfalso; apply (lt_irrefl l1); transitivity l2; [exact H1 | exact H2] 
           | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3, H3 : ?l3 < ?l1 |- _ ] => exfalso; apply (lt_irrefl l1); transitivity l2; [exact H1 | transitivity l3; [exact H2 | exact H3]]
           | [ H1 : ?l1 < ?l2, H2 : ?l2 <= ?l1 |- _ ] => apply L.le_lteq in H2; destruct H2; subst
           | [ |- ?l <= ?l ] => reflexivity
           | [ H : ?l1 < ?l2 |- ?l1 <= ?l2 ] => apply lt_to_le; exact H
           | [ H1 : ?l1 <= ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [exact H1 | exact H2]
           | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3 |- ?l1 <= ?l3 ] => apply lt_to_le; transitivity l2; [exact H1 | exact H2]
           | [ H1 : ?l1 < ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [apply lt_to_le; exact H1 | exact H2]
           | [ H : Some ?l1 = Some ?l2 |- _] => inversion H; subst; clear H
           | [ H : (?l ?= ?l') = Eq |- _ ] => apply compare_Eq_to_eq in H; subst
           | [ H : (?l ?= ?l') = Lt |- _ ] => apply compare_Lt_to_lt in H
           | [ H : (?l ?= ?l') = Gt |- _ ] => apply compare_Gt_to_gt in H
           | [ H : Eq = (?l ?= ?l') |- _ ] => symmetry in H; apply compare_Eq_to_eq in H; subst
           | [ H : Lt = (?l ?= ?l') |- _ ] => symmetry in H; apply compare_Lt_to_lt in H
           | [ H : Gt = (?l ?= ?l') |- _ ] => symmetry in H; apply compare_Gt_to_gt in H
           end; auto.
  Ltac DestructCompare x y :=
    let x_y := fresh x "_" y in
    destruct (x ?= y) eqn:x_y; cbn in *; LocationOrder.

  Definition le_bool : L.t -> L.t -> bool :=
    fun l1 l2 => match L.compare l1 l2 with
              | Gt => false
              | _ => true
              end.
  Notation "l1 <=? l2" := (le_bool l1 l2) (at level 70).
  Theorem le_bool_spec : forall l1 l2 : L.t, l1 <= l2 <-> le_bool l1 l2 = true.
  Proof using.
    unfold le_bool. intros l1 l2. DestructCompare l1 l2; split; intro H; auto.
    reflexivity. apply lt_to_le; auto. LocationOrder. inversion H.
  Qed.
  Theorem le_bool_total : forall l1 l2, l1 <=? l2 = true \/ l2 <=? l1 = true.
  Proof using.
    intros l1 l2; unfold le_bool.
    DestructCompare l1 l2; DestructCompare l2 l1.
  Qed.

End LocationFacts.

Module Type LocationWithNotations.
  Declare Module L : Locations.
  Include L.
  Include (LocationNotations L).
End LocationWithNotations.

Module LocToOrderedType (L : Locations) <: OrderedTypeFull.
  Definition t := L.t.
  Definition eq := @eq t.
  Definition lt := L.lt.
  Definition le := L.le.

  Instance eq_refl : Reflexive eq.
  intro x; reflexivity.
  Defined.

  Instance eq_sym : Symmetric eq.
  intros x y H; unfold eq in *; subst; reflexivity.
  Defined.

  Instance eq_trans : Transitive eq.
  intros x y z H1 H2; unfold eq in *; subst; reflexivity.
  Defined.

  Instance eq_equiv : Equivalence eq :=
    {| Equivalence_Reflexive := eq_refl;
       Equivalence_Symmetric := eq_sym;
       Equivalence_Transitive := eq_trans
    |}.

  Instance lt_strorder : StrictOrder lt := L.lt_strorder.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt := L.lt_compat.

  Definition compare := L.compare.
  Definition compare_spec := L.cmp_spec.
  Definition eq_dec := L.eq_dec.
  Theorem le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    unfold eq. unfold lt. unfold le. unfold t. exact L.le_lteq.
  Defined.
End LocToOrderedType.

Module LocToTotalLeBool' (L : Locations) <: Orders.TotalLeBool'.
  Module LF := LocationFacts L.
  Definition t := L.t.
  Definition leb := LF.le_bool.
  Definition leb_total := LF.le_bool_total.
End LocToTotalLeBool'.

Module Type LocationSorter (L : Locations).
  Parameter sort : list L.t -> list L.t.
  Parameter sort_rev : list L.t -> list L.t.

  Parameter sort_Sorted : forall l : list L.t, StronglySorted L.le (sort l).
  Parameter sort_Perm : forall l : list L.t, Permutation l (sort l).

  Parameter sort_rev_Sorted : forall l : list L.t, StronglySorted (fun a b => L.le b a) (sort_rev l).
  Parameter sort_rev_Perm : forall l : list L.t, Permutation l (sort_rev l).
End LocationSorter.

Module LocationMergeSorter (L : Locations) <: (LocationSorter L).
  Module LF := (LocationFacts L).
  Include (LocationNotations L).

  Module LocToTotalGeBool' <: Orders.TotalLeBool'.
    Definition t := L.t.
    Definition leb := fun l1 l2 => match l1 ?= l2 with
                                | Lt => false
                                | _ => true
                                end.
    Infix ">=?" := leb (at level 70).
    Theorem leb_total : forall l1 l2, l1 >=? l2 = true \/ l2 >=? l1 = true.
    Proof using.
      intros l1 l2. unfold leb. LF.DestructCompare l1 l2; LF.DestructCompare l2 l1.
    Qed.
  End LocToTotalGeBool'.
  Module LocToTotalLeBool' <: Orders.TotalLeBool'.
    Definition t := L.t.
    Definition leb := fun l1 l2 => match l1 ?= l2 with
                                | Gt => false
                                | _ => true
                                end.
    Infix "<=?" := leb (at level 70).
    Theorem leb_total : forall l1 l2, l1 <=? l2 = true \/ l2 <=? l1 = true.
    Proof using.
      intros l1 l2. unfold leb. LF.DestructCompare l1 l2; LF.DestructCompare l2 l1.
    Qed.
  End LocToTotalLeBool'.

  Module SortModule := (Sort LocToTotalLeBool').
  Module SortRevModule := (Sort LocToTotalGeBool').

  Definition sort := SortModule.sort.
  Definition sort_rev := SortRevModule.sort.

  Lemma sort_Sorted : forall l, StronglySorted L.le (sort l).
  Proof using.
    intro l.
    assert (Transitive (fun a b => (is_true (LocToTotalLeBool'.leb a b)))) as H
      by (unfold Transitive; intros x y z; unfold LocToTotalLeBool'.leb;
          LF.DestructCompare x y; LF.DestructCompare y z; LF.DestructCompare x z);
      apply (SortModule.StronglySorted_sort l) in H.
    unfold sort.
    induction (SortModule.sort l); constructor.
    apply IHl0. inversion H; subst; auto.
    inversion H; subst.
    apply Forall_forall; rewrite Forall_forall in H3; intros x i; specialize (H3 x i).
    LF.DestructCompare a x; auto. inversion H3.
  Qed.
  Lemma sort_Perm : forall l, Permutation l (sort l).
  Proof using.
    unfold sort; apply SortModule.Permuted_sort.
  Qed.

  Lemma sort_rev_Sorted : forall l, StronglySorted (fun a b => a >= b) (sort_rev l).
  Proof using.
    unfold sort_rev; intro l.
    assert (Transitive (fun a b => (is_true (LocToTotalGeBool'.leb a b)))) as H
      by (unfold Transitive; intros x y z; unfold LocToTotalGeBool'.leb;
          LF.DestructCompare x y; LF.DestructCompare y z; LF.DestructCompare x z);
      apply (SortRevModule.StronglySorted_sort l) in H.
    induction (SortRevModule.sort l); constructor.
    apply IHl0. inversion H; subst; auto.
    inversion H; subst.
    apply Forall_forall; rewrite Forall_forall in H3; intros x i; specialize (H3 x i).
    LF.DestructCompare a x; auto. inversion H3.
  Qed.

  Lemma sort_rev_Perm : forall l, Permutation l (sort_rev l).
  Proof using.
    unfold sort; apply SortRevModule.Permuted_sort.
  Qed.
End LocationMergeSorter.
