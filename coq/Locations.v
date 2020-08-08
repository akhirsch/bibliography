Require Import Coq.Structures.Orders Coq.Structures.Equalities.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.SetoidList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Program.Wf.
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

(* Maps keyed by locations *)
Module Type LocationMap (L : Locations).
  Include (LocationNotations L).

  Parameter t : Set -> Set.
  Set Implicit Arguments.
  Section Types.
    Variable elt : Set.

    Parameter empty : t elt.
    Parameter is_empty : t elt -> bool.
    Parameter add : L.t -> elt -> t elt -> t elt.
    Parameter find : L.t -> t elt -> option elt.
    Parameter remove : L.t -> t elt -> t elt.
    Parameter mem : L.t -> t elt -> bool.
    Parameter elements : t elt -> list (L.t * elt).
    Parameter cardinal : t elt -> nat.

    Variable elt' elt'' : Set.

    Parameter map : (elt -> elt') -> t elt -> t elt'.
    Parameter mapi : (L.t -> elt -> elt') -> t elt -> t elt'.
    Parameter map2 : (option elt -> option elt' -> option elt'') -> t elt -> t elt' -> t elt''.
    Parameter fold : forall {A : Type}, (L.t -> elt -> A -> A) -> t elt -> A -> A.
    
    Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool. 

    Section spec.

      Variable m m' m'' : t elt.
      Variable x y z : L.t.
      Variable e e' : elt.

      Parameter MapsTo : L.t -> elt -> t elt -> Prop.
      Definition In (k : L.t) (m : t elt) : Prop := exists e : elt, MapsTo k e m.
      Definition Empty m := forall (a : L.t) (e : elt), ~ MapsTo a e m.
      Definition eq_key (p p' : L.t * elt) := fst p = fst p'.
      Definition eq_key_elt (p p' : L.t * elt) := fst p = fst p' /\ snd p = snd p'.
      Definition lt_key (p p' : L.t * elt) := fst p < fst p'.

      Parameter mem_1 : In x m -> mem x m = true.
      Parameter mem_2 : mem x m = true -> In x m.

      Parameter empty_1 : Empty empty.

      Parameter is_empty_1 : Empty m -> is_empty m = true.
      Parameter is_empty_2 : is_empty m = true -> Empty m.

      Parameter add_1 : MapsTo x e (add x e m).
      Parameter add_2 : x <> y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Parameter add_3 : x <> y -> MapsTo y e (add x e' m) -> MapsTo y e m.

      Parameter remove_1 : ~ In x (remove x m).
      Parameter remove_2 : x <> y -> MapsTo y e m -> MapsTo y e (remove x m).
      Parameter remove_3 : x <> y  -> MapsTo y e (remove x m) -> MapsTo y e m.

      Parameter find_1 : MapsTo x e m -> find x m = Some e.
      Parameter find_2 : find x m = Some e -> MapsTo x e m.

      Parameter elements_1 : MapsTo x e m -> InA eq_key_elt (x, e) (elements m).
      Parameter elements_2 : InA eq_key_elt (x, e) (elements m) -> MapsTo x e m.
      Parameter elements_3w : NoDupA eq_key (elements m).
      Parameter elements_3 : sort lt_key (elements m).

      Parameter cardinal_1 : cardinal m = length (elements m).

      Parameter fold_1 : forall (A : Type) (i : A) (f : L.t -> elt -> A -> A),
          fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

      Definition Equal m m' := forall y, find y m = find y m'.
      Definition Equiv (eq_elt : elt -> elt -> Prop) m m' :=
        (forall k, In k m <-> In k m') /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
      Definition Equivb (cmp : elt -> elt -> bool) := Equiv (fun e1 e2 => cmp e1 e2 = true).

      Variable cmp : elt -> elt -> bool.

      Parameter equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Parameter equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
    End spec.
  End Types.

  Parameter map_1 : forall (elt elt' : Set) (m : t elt) (x : L.t) (e : elt)(f : elt -> elt'), MapsTo x e m -> MapsTo x (f e) (map f m).
  Parameter map_2 : forall (elt elt' : Set) (m : t elt) (x : L.t) (f : elt -> elt'), In x (map f m) -> In x m.

  Parameter mapi_1 : forall (elt elt' : Set) (m : t elt) (x : L.t) (e : elt) (f: L.t -> elt -> elt'), MapsTo x e m -> MapsTo x (f x e) (mapi f m).
  Parameter mapi_2 : forall (elt elt' : Set) (m : t elt) (x : L.t) (f : L.t -> elt -> elt'), In x (mapi f m) -> In x m.

  Parameter map2_1 : forall (elt elt' elt'' : Set) (m : t elt) (m' : t elt') (x : L.t) (f : option elt -> option elt' -> option elt''),
      In x m \/ In x m' -> find x (map2 f m m') = f (find x m) (find x m').
  Parameter map2_2 : forall (elt elt' elt'' : Set) (m : t elt) (m' : t elt') (x : L.t) (f : option elt -> option elt' -> option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.

  Hint Immediate mem_2 is_empty_2 map_2 mapi_2 add_3 remove_3 find_2 : lmap.
  Hint Resolve mem_1 is_empty_1 add_1 add_2 remove_1 remove_2 find_1 fold_1 map_1 mapi_1 mapi_2 : lmap.
End LocationMap.

Module TreeLMap (L : Locations) <: (LocationMap L).
  Include (LocationNotations L).
  Include (LocationFacts L).

  Inductive BT (elt : Set) : Set :=
    EmptyBT : BT elt
  | Branch : BT elt -> L.t -> elt -> BT elt -> BT elt.
  Arguments Branch {elt} _ _ _ _.

  Fixpoint forallLocationsInTree {elt : Set} (t : BT elt) (P : L.t -> Prop) : Prop :=
    match t with
    | EmptyBT _ => True
    | Branch lt l e rt =>
      P l /\ forallLocationsInTree lt P /\ forallLocationsInTree rt P          
    end.
  Lemma ChangeOfProperty : forall {elt : Set} (t : BT elt) (P Q : L.t -> Prop),
      forallLocationsInTree t P -> (forall l : L.t, P l -> Q l) -> forallLocationsInTree t Q.
  Proof using .
    intros elt t; induction t as [| t1 IHt1 l e t2 IHt2]; intros P Q fa imp; cbn; auto.
    destruct fa as [Pl H]; destruct H as [fat1 fat2].
    split; [|split]; auto; [apply IHt1 with (P := P) | apply IHt2 with (P := P)]; auto.
  Qed.

  Fixpoint isBST {elt : Set} (t : BT elt) : Prop :=
    match t with
    | EmptyBT _ => True
    | Branch lt l e rt =>
      forallLocationsInTree lt (fun l' => l' < l)
      /\ forallLocationsInTree rt (fun l' => l < l')
      /\ isBST lt
      /\ isBST rt
    end.

  Record BST (elt : Set) : Set :=
    {
    U : BT elt; (* U for Underlying *)
    U_corr : isBST U
    }.
  Arguments U {elt} _.
  Arguments U_corr {elt}.
  Arguments Build_BST {elt} _ _.

  Definition t : Set -> Set := BST.

  Inductive MapsToInBT {elt : Set} : L.t -> elt -> BT elt -> Prop :=
    MapsToHere : forall (l : L.t) (e : elt) (t1 t2 : BT elt), MapsToInBT l e (Branch t1 l e t2)
  | MapsToLeft : forall (l l' : L.t) (e e' : elt) (t1 t2 : BT elt),
      MapsToInBT l e t1 -> MapsToInBT l e (Branch t1 l' e' t2)
  | MapsToRight: forall (l l' : L.t) (e e' : elt) (t1 t2 : BT elt),
      MapsToInBT l e t2 -> MapsToInBT l e (Branch t1 l' e' t2).
  
  Definition MapsTo : forall {elt : Set}, L.t -> elt -> t elt -> Prop := fun elt l e t => MapsToInBT l e (U t).
  Definition InBT {elt : Set} (k : L.t) (m : BT elt) : Prop := exists e : elt, MapsToInBT k e m.
  Definition In {elt : Set} (k : L.t) (m : t elt) : Prop := exists e : elt, MapsTo k e m.
  Definition Empty {elt : Set} m := forall (a : L.t) (e : elt), ~ MapsTo a e m.

  Definition eq_key {elt : Set} (p p' : L.t * elt) := fst p = fst p'.
  Definition eq_key_elt {elt : Set} (p p' : L.t * elt) := fst p = fst p' /\ snd p = snd p'.
  Definition eq_key_equiv_elt {elt : Set} (p1 p2 : L.t * elt) (cmp : elt -> elt -> bool) := fst p1 = fst p2 /\ cmp (snd p1) (snd p2) = true.
  Definition lt_key {elt : Set} (p p' : L.t * elt) := fst p < fst p'.

  Theorem forallLocationsInTree_1 : forall {elt : Set} (t : BT elt) (P : L.t -> Prop) (l : L.t) (el : elt), MapsToInBT l el t -> forallLocationsInTree t P -> P l.
  Proof using.
    intros elt t; induction t as [|t1 IHt1 l' el' t2 IHt2]; intros P l el mt; inversion mt; subst; cbn; intro H; destruct H as [Pl H]; destruct H as [fat1 fat2]; auto.
    apply IHt1 with (el := el); auto.
    apply IHt2 with (el := el); auto.
  Qed.
  Theorem forallLocationsInTree_2 : forall {elt : Set} (t : BT elt) (P : L.t -> Prop), (forall (l : L.t) (el : elt), MapsToInBT l el t -> P l) -> forallLocationsInTree t P.
  Proof using.
    intros elt t; induction t as [|t1 IHt1 l' el' t2 IHt2]; intros P allmap; cbn; auto.
    split; [|split;[apply IHt1 |apply IHt2]].
    - apply allmap with (el := el'); constructor.
    - intros l el mt; apply allmap with (el := el); constructor; auto.
    - intros l el mt; apply allmap with (el := el); constructor; auto; fail.
  Qed.

  Theorem MapsToInBTUnique : forall {elt : Set} (t : BT elt) (l : L.t) (e1 e2 : elt), isBST t -> MapsToInBT l e1 t -> MapsToInBT l e2 t -> e1 = e2.
  Proof using.
    intros elt t l e1 e2 BSTt; revert l e1 e2; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; intros l' e1 e2 mt1 mt2; [inversion mt1|].
    destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2]; specialize (IHt1 BSTt1); specialize (IHt2 BSTt2).
    inversion mt1; subst; inversion mt2; subst; auto.
    - apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto. exfalso; apply lt_irrefl with (x := l); exact H2.
    - apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto. exfalso; apply lt_irrefl with (x := l); exact H2.
    - apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto. exfalso; apply lt_irrefl with (x := l); exact H2.
    - apply IHt1 with (l := l'); auto.
    - apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto.
      apply forallLocationsInTree_1 with (P := fun l' => l < l') in H3; auto.
      exfalso; apply lt_irrefl with (x := l); transitivity l'; auto.
    - apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto. exfalso; apply lt_irrefl with (x := l); exact H2.
    - apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H3; auto.
      apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto.
      exfalso; apply lt_irrefl with (x := l); transitivity l'; auto.
    - apply IHt2 with (l := l'); auto.
  Qed.
  
  Section empty.
    Variable elt : Set.

    Definition empty : t elt := {| U := EmptyBT elt; U_corr := I |}.

    Theorem empty_1 : Empty empty.
    Proof using.
      unfold Empty; unfold empty; unfold MapsTo; cbn.
      intros l el mt; inversion mt.
    Qed.
  End empty.
  Arguments empty {elt}.
  
  Section is_empty.
    Variable elt : Set.
    
    Definition is_empty : t elt -> bool :=
      fun t => match U t with
            | EmptyBT _ => true
            | _ => false
            end.


    Theorem is_empty_1 : forall m : t elt, Empty m -> is_empty m = true.
    Proof using.
      intro m; unfold Empty; unfold is_empty; unfold MapsTo; destruct m as [t BSTt]; cbn; intro empt.
      destruct t as [| t1 l el t2]; [reflexivity | exfalso; apply (empt l el); constructor].
    Qed.
    
    Definition is_empty_2 : forall m : t elt, is_empty m = true -> Empty m.
    Proof using.
      intro m; unfold is_empty; unfold Empty; unfold MapsTo; destruct m as [t BSTt]; cbn; intro ie.
      destruct t as [| t1 l el t2]; [intros l el mt; inversion mt  |discriminate ie].
    Qed.
  End is_empty.
  Arguments is_empty {elt}.

  Section add.
    Variable elt : Set.
    Fixpoint addToBT (l : L.t) (e : elt) (t : BT elt) : BT elt :=
      match t with
      | EmptyBT _ => Branch (EmptyBT elt) l e (EmptyBT elt)
      | Branch t1 l' e' t2 =>
        match l ?= l' with
        | Eq => Branch t1 l e t2
        | Lt => Branch (addToBT l e t1) l' e' t2
        | Gt => Branch t1 l' e' (addToBT l e t2)
        end
      end.
    
    Lemma addToPreservesBounds : forall (l l' : L.t) (e : elt) (t : BT elt),
        (forallLocationsInTree t (fun l'' : L.t => l'' < l') -> l < l' -> forallLocationsInTree (addToBT l e t) (fun l'' : L.t => l'' < l'))
        /\ (forallLocationsInTree t (fun l'' : L.t => l' < l'') -> l' < l -> forallLocationsInTree (addToBT l e t) (fun l'' : L.t => l' < l'')).
    Proof using.
      intros l l' e t; induction t as [|t1 IHt1 loc e' t2 IHt2] ; cbn; split; [split; [auto | split; auto] | split; [auto|split; auto] |  | ].
      - destruct (l ?= loc) eqn:l_loc_eq. 
        -- apply compare_Eq_to_eq in l_loc_eq; subst.
           intros H _; destruct H as [loc_le_l' H]; destruct H as [t1_bounded t2_bounded]; cbn; split; [|split]; auto.
        -- apply compare_Lt_to_lt in l_loc_eq.
           intros H l_le_l'; destruct H as [loc_le_l' H]; destruct H as [t1_bounded t2_bounded]; cbn; split; [|split]; auto.
           apply IHt1; auto.
        -- apply compare_Gt_to_gt in l_loc_eq.
           intros H l_le_l'; destruct H as [loc_le_l' H]; destruct H as [t1_bounded t2_bounded]; cbn; split; [|split]; auto.
           apply IHt2; auto.
      - intros H l'_lt_l; destruct H as [l'_lt_loc H]; destruct H as [t1_bdd t2_bdd]; destruct (l ?= loc) eqn:cmpr_eq; cbn.
        -- apply compare_Eq_to_eq in cmpr_eq; subst. split; [|split]; auto.
        -- apply compare_Lt_to_lt in cmpr_eq. split; [|split]; auto. apply IHt1; auto.
        -- apply compare_Gt_to_gt in cmpr_eq. split; [|split]; auto. apply IHt2; auto.
    Qed.
                                                                            
    Theorem addToPreservesBST : forall (l : L.t) (e : elt) (t : BT elt), isBST t -> isBST (addToBT l e t).
    Proof using.
      intros l e t iBST. induction t as [| t1 IHt1 l' e' t2 IHt2]; cbn; [repeat constructor |].
      destruct (l ?= l') eqn:eq.
      all: cbn in iBST; destruct iBST as [Hlt iBST]; destruct iBST as [Hrt iBST]; destruct iBST as [lBST rBST].
      - cbn; split; [| split; [| split]]; auto.
        all: apply compare_Eq_to_eq in eq; subst; auto.
      - cbn; split; [| split; [| split]]; auto.
        apply addToPreservesBounds; auto. apply compare_Lt_to_lt in eq; auto. 
      - cbn; split; [| split; [| split]]; auto.
        apply addToPreservesBounds; auto. apply compare_Gt_to_gt in eq; auto.
    Qed.

    Definition add : L.t -> elt -> t elt -> t elt :=
      fun l e t => match t with
                | Build_BST U U_corr => {| U := addToBT l e U; U_corr := addToPreservesBST l e U U_corr |}
                end.

    Theorem add_1 : forall (m : t elt) (l : L.t)  (e : elt), MapsTo l e (add l e m).
    Proof using.
      intros m l e; unfold MapsTo; unfold add; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l' el t2 IHt2]; cbn; [constructor|].
      destruct BSTt as [_ H]; destruct H as [_ H]; destruct H as [BSTt1 BSTt2].
      destruct (l ?= l') eqn:l_l'.
      - constructor.
      - apply MapsToLeft; apply IHt1; exact BSTt1.
      - apply MapsToRight; apply IHt2; exact BSTt2.
    Qed.
    Theorem add_2 : forall  (m : t elt) (l l' : L.t) (e e' : elt), l <> l' -> MapsTo l' e m -> MapsTo l' e (add l e' m).
    Proof using.
      intros m l l' e el'; unfold MapsTo; unfold add; destruct m as [t BSTt]; cbn; intros n mt.
      induction t as [| t1 IHt1 l'' el t2 IHt2]; cbn; [| destruct BSTt as [_ H]; destruct H as [_ H]; destruct H as [BSTt1 BSTt2]]; inversion mt; subst.
      - destruct (l ?= l'') eqn:l_l''; try (constructor; auto; fail).
        apply compare_Eq_to_eq in l_l''; exfalso; apply n; exact l_l''.
      - destruct (l ?= l'') eqn:l_l''; apply MapsToLeft; auto.
      - destruct (l ?= l'') eqn:l_l''; apply MapsToRight; auto.
    Qed.
    Theorem add_3 : forall (m : t elt) (l l' : L.t) (e e' : elt), l <> l' -> MapsTo l' e (add l e' m) -> MapsTo l' e m.
    Proof using.
      intros m l l' e e'; unfold MapsTo; unfold add; destruct m as [t BSTt]; cbn; intros n mt.
      induction t as [| t1 IHt1 l'' el t2 IHt2]; cbn in mt; [| destruct BSTt as [_ H]; destruct H as [_ H]; destruct H as [BSTt1 BSTt2]].
      inversion mt; subst;
        try match goal with
            | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
            | [ H : MapsToInBT _ _ (EmptyBT _) |- _ ] => inversion H
            end.
      destruct (l ?= l'') eqn: l_l''; inversion mt; subst;
        try match goal with
            | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
            end; try (constructor; auto; fail).
    Qed.
  End add.
  Arguments addToBT {elt}.
  Arguments add {elt}.

  Section find.
    Variable elt : Set.
    Fixpoint findInBT (l : L.t) (t : BT elt) : option elt :=
      match t with
      | EmptyBT _ => None
      | Branch t1 l' e t2 =>
        match (l ?= l') with
        | Eq => Some e
        | Lt => findInBT l t1
        | Gt => findInBT l t2
        end
      end.

    Theorem findBT_1 : forall (x : L.t) (e : elt) (t : BT elt), isBST t -> MapsToInBT x e t -> findInBT x t = Some e.
    Proof using.
      intros x e t BSTt; induction t as [| t1 IHt1 l el t2 IHt2]; cbn; intro mt; [inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      destruct (x ?= l) eqn:x_l; [apply compare_Eq_to_eq in x_l | apply compare_Lt_to_lt in x_l | apply compare_Gt_to_gt in x_l];
        inversion mt; subst; auto;
          try match goal with
              | [ H : ?l < ?l |- _ ] => exfalso; apply lt_irrefl with (x := l); exact H
              end.
      - apply forallLocationsInTree_1 with (el0 := e) (l0 := l) in t1_bdd; auto. apply lt_irrefl in t1_bdd; destruct t1_bdd.
      - apply forallLocationsInTree_1 with (el0 := e) (l0 := l) in t2_bdd; auto. apply lt_irrefl in t2_bdd; destruct t2_bdd.
      - apply forallLocationsInTree_1 with (el0 := e) (l0 := x) in t2_bdd; auto. exfalso; apply lt_irrefl with (x := l); transitivity x; auto.
      - apply forallLocationsInTree_1 with (el0 := e) (l0 := x) in t1_bdd; auto. exfalso; apply lt_irrefl with (x := l); transitivity x; auto.
    Qed.
    Theorem findBT_2 : forall (x : L.t) (e : elt) (t : BT elt), findInBT x t = Some e -> MapsToInBT x e t.
    Proof using.
      intros x e t. induction t as [| t1 IHt1 l el t2 IHt2]; cbn; intro find_eq; [discriminate find_eq |].
      (* destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2]. *)
      destruct (x ?= l) eqn:x_l; [apply compare_Eq_to_eq in x_l; inversion find_eq; subst | apply compare_Lt_to_lt in x_l | apply compare_Gt_to_gt in x_l];
        constructor; auto; fail.
    Qed.
    
    Definition find : L.t -> t elt -> option elt :=
      fun l t => match t with
              | Build_BST U _ => findInBT l U
              end.

    Theorem find_1 : forall (m : t elt) (x : L.t) (e : elt), MapsTo x e m -> find x m = Some e.
    Proof using.
      intros m x e; unfold MapsTo; unfold find; destruct m as [t BSTt]; cbn.
      apply findBT_1; auto.
    Qed.
    Theorem find_2 : forall (m : t elt) (x : L.t) (e : elt), find x m = Some e -> MapsTo x e m.
    Proof using.
      intros m x e; unfold MapsTo; unfold find; destruct m as [t BSTt]; cbn; apply findBT_2.
    Qed.
  End find.
  Arguments findInBT {elt}.
  Arguments find {elt}.

  Section greatestLocation.
    Variable elt : Set.
    Fixpoint greatestLocation (t : BT elt) : option L.t :=
      match t with
      | EmptyBT _ => None
      | Branch t1 l _ t2 =>
        match greatestLocation t1, greatestLocation t2 with
        | None, None => Some l
        | None, Some l2 => match L.compare l l2 with
                          | Lt => Some l2
                          | _ => Some l
                          end
        | Some l1, None => match L.compare l l1 with
                          | Lt => Some l1
                          | _ => Some l
                          end
        | Some l1, Some l2 => match L.compare l l1 with
                             | Lt => match L.compare l1 l2 with
                                    | Lt => Some l2
                                    | _ => Some l1
                                    end
                             | _ => match L.compare l l2 with
                                   | Lt => Some l2
                                   | _ => Some l
                                   end
                             end
        end
      end.

    Theorem greatestLocation_None_Empty : forall (t : BT elt), greatestLocation t = None -> t = EmptyBT elt.
    Proof using.
      intro t; induction t; intro H; cbn in H; auto.
      destruct (greatestLocation t1); destruct (greatestLocation t3).
      destruct (t2 ?= t0); [destruct (t2 ?= t4) | destruct (t0 ?= t4) | destruct (t2 ?= t4)]; inversion H.
      destruct (t2 ?= t0); inversion H.
      destruct (t2 ?= t0); inversion H.
      inversion H.
    Qed.
    
    Theorem greatestLocation_sound : forall (t : BT elt) (l : L.t), greatestLocation t = Some l -> forallLocationsInTree t (fun l' => l' <= l).
    Proof using.
      intro t; induction t as [|t1 IHt1 l' e t2 IHt2]; intros l gl; cbn; auto; split; [|split]; cbn in gl.
      all: destruct (greatestLocation t1) as [l1|] eqn:gl1; destruct (greatestLocation t2) as [l2 |] eqn:gl2; auto.
      all: repeat match goal with
                  | [ |- True ] => constructor
                  | [ H : ?P |- ?P ] => exact H
                  | [ |- ?l <= ?l ] => reflexivity
                  | [ H : ?l1 < ?l2 |- ?l1 <= ?l2 ] => apply lt_to_le; exact H
                  | [ H1 : ?l1 <= ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3 |- ?l1 <= ?l3 ] => apply lt_to_le; transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [apply lt_to_le; exact H1 | exact H2]
                  | [ H: (?l1 ?= ?l2) = Lt |- _ ] => apply compare_Lt_to_lt in H
                  | [ H: (?l1 ?= ?l2) = Gt |- _ ] => apply compare_Gt_to_gt in H
                  | [ H: (?l1 ?= ?l2) = Eq |- _ ] => apply compare_Eq_to_eq in H; subst
                  | [ H : forall l0, Some ?l = Some l0 -> ?P |- _] => specialize (H l eq_refl)
                  | [ H : Some ?l1 = Some ?l2 |- _] => inversion H; subst; clear H
                  | [ H : greatestLocation ?t = None |- _ ] => apply greatestLocation_None_Empty in H; subst; cbn
                  | [ H1 : forallLocationsInTree _ (fun l' => l' <= ?l1), H2 : ?l1 < ?l2 |- _ ] =>
                    apply ChangeOfProperty with (Q := fun l' => l' <= l2) in H1; [| let l := fresh "l"
                                                                                in let H := fresh "H"
                                                                                   in intros l H; transitivity l1; [exact H | apply lt_to_le; exact H2]]
                  | [ H : context[?l1 ?= ?l2] |- _ ] => let H := fresh "cmp" in destruct (l1 ?= l2) eqn:H
                  end.
    Qed.

    Theorem greatestLocation_complete : forall (t : BT elt) (l1 l2 : L.t), forallLocationsInTree t (fun l' => l' <= l1) -> greatestLocation t = Some l2 -> l2 <= l1.
    Proof using.
      intro t; induction t as [|t1 IHt1 l e t2 IHt2]; intros l1 l2 fa gl; cbn in gl; [inversion gl|].
      destruct fa as [l_l1 H]; destruct H as [t1_bdd t2_bdd].
      destruct (greatestLocation t1) as [lt1|] eqn:gl1; destruct (greatestLocation t2) as [lt2|] eqn:gl2.
      all: repeat match goal with
                  | [ |- True ] => constructor
                  | [ H : ?P |- ?P ] => exact H
                  | [ |- ?l <= ?l ] => reflexivity
                  | [ H : ?l1 < ?l2 |- ?l1 <= ?l2 ] => apply lt_to_le; exact H
                  | [ H1 : ?l1 <= ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3 |- ?l1 <= ?l3 ] => apply lt_to_le; transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [apply lt_to_le; exact H1 | exact H2]
                  | [ H: (?l1 ?= ?l2) = Lt |- _ ] => apply compare_Lt_to_lt in H
                  | [ H: (?l1 ?= ?l2) = Gt |- _ ] => apply compare_Gt_to_gt in H
                  | [ H: (?l1 ?= ?l2) = Eq |- _ ] => apply compare_Eq_to_eq in H; subst
                  | [ H : forall l0, Some ?l = Some l0 -> ?P |- _] => specialize (H l eq_refl)
                  | [ H : Some ?l1 = Some ?l2 |- _] => inversion H; subst; clear H
                  | [ H : greatestLocation ?t = None |- _ ] => apply greatestLocation_None_Empty in H; subst; cbn
                  | [ H1 : forallLocationsInTree _ (fun l' => l' <= ?l1), H2 : ?l1 < ?l2 |- _ ] =>
                    apply ChangeOfProperty with (Q := fun l' => l' <= l2) in H1; [| let l := fresh "l"
                                                                                in let H := fresh "H"
                                                                                   in intros l H; transitivity l1; [exact H | apply lt_to_le; exact H2]]
                  | [ H : context[?l1 ?= ?l2] |- _ ] => let H := fresh "cmp" in destruct (l1 ?= l2) eqn:H
                  end.
      all: try (specialize (IHt2 l1 l2 t2_bdd eq_refl); auto; fail).
      all: specialize (IHt1 l1 l2 t1_bdd eq_refl); auto.
    Qed.
    Theorem greatestLocation_complete2 : forall (t : BT elt) (l1 l2 : L.t), forallLocationsInTree t (fun l' => l' < l1) -> greatestLocation t = Some l2 -> l2 < l1.
    Proof using.
      intro t; induction t as [|t1 IHt1 l e t2 IHt2]; intros l1 l2 fa gl; cbn in gl; [inversion gl|].
      destruct fa as [l_l1 H]; destruct H as [t1_bdd t2_bdd].
      destruct (greatestLocation t1) as [lt1|] eqn:gl1; destruct (greatestLocation t2) as [lt2|] eqn:gl2.
      all: repeat match goal with
                  | [ |- True ] => constructor
                  | [ H : ?P |- ?P ] => exact H
                  | [ |- ?l <= ?l ] => reflexivity
                  | [ H : ?l1 < ?l2 |- ?l1 <= ?l2 ] => apply lt_to_le; exact H
                  | [ H1 : ?l1 <= ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3 |- ?l1 < ?l3 ] => transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3 |- ?l1 <= ?l3 ] => apply lt_to_le; transitivity l2; [exact H1 | exact H2]
                  | [ H1 : ?l1 < ?l2, H2 : ?l2 <= ?l3 |- ?l1 <= ?l3 ] => transitivity l2; [apply lt_to_le; exact H1 | exact H2]
                  | [ H: (?l1 ?= ?l2) = Lt |- _ ] => apply compare_Lt_to_lt in H
                  | [ H: (?l1 ?= ?l2) = Gt |- _ ] => apply compare_Gt_to_gt in H
                  | [ H: (?l1 ?= ?l2) = Eq |- _ ] => apply compare_Eq_to_eq in H; subst
                  | [ H : forall l0, Some ?l = Some l0 -> ?P |- _] => specialize (H l eq_refl)
                  | [ H : Some ?l1 = Some ?l2 |- _] => inversion H; subst; clear H
                  | [ H : greatestLocation ?t = None |- _ ] => apply greatestLocation_None_Empty in H; subst; cbn
                  | [ H1 : forallLocationsInTree _ (fun l' => l' < ?l1), H2 : ?l1 < ?l2 |- _ ] =>
                    apply ChangeOfProperty with (Q := fun l' => l' < l2) in H1; [| let l := fresh "l"
                                                                                in let H := fresh "H"
                                                                                   in intros l H; transitivity l1; [exact H | exact H2]]
                  | [ H : context[?l1 ?= ?l2] |- _ ] => let H := fresh "cmp" in destruct (l1 ?= l2) eqn:H
                  end.
      all: try (specialize (IHt2 l1 l2 t2_bdd eq_refl); auto; fail).
      all: specialize (IHt1 l1 l2 t1_bdd eq_refl); auto.
    Qed.
  End greatestLocation.
  Arguments greatestLocation {elt}.

    Section elements.
    Variable elt : Set.

    Fixpoint elementsOfBT (t : BT elt) : list (L.t * elt) :=
      match t with
      | EmptyBT _ => nil
      | Branch t1 l e t2 => elementsOfBT t1 ++ (l, e) :: elementsOfBT t2
      end.

    Theorem elementsOfBT_3 : forall (t : BT elt) (l : L.t) (el : elt), InA eq_key (l, el) (elementsOfBT t) -> InBT l t.
    Proof using.
      intro t; induction t as  [| t1 IHt1 l' el' t2 IHt2]; cbn; intros l el i; [inversion i|].
      rewrite InA_app_iff in i; destruct i as [i | i]; [destruct (IHt1 l el i) as [el'' H]; exists el''; apply MapsToLeft; auto |].
      inversion i; subst; [unfold eq_key in H0; cbn in H0; subst; exists el'; constructor| destruct (IHt2 l el H0) as [el'' H]; exists el''; apply MapsToRight; auto].
    Qed.      

    Definition elements : t elt -> list (L.t * elt) := fun t => elementsOfBT (U t).

    Theorem elements_1 : forall (m : t elt) (x : L.t) (e : elt), MapsTo x e m -> InA eq_key_elt (x, e) (elements m).
    Proof using.
      intros m x e; unfold MapsTo; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; intro mt; inversion mt; subst; rewrite InA_app_iff;
        destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      - right; constructor; cbn; split; reflexivity.
      - left; apply IHt1; auto.
      - right; constructor; auto; fail.
    Qed.
    Theorem elements_2 : forall (m : t elt) (x : L.t) (e : elt), InA eq_key_elt (x, e) (elements m) -> MapsTo x e m.
    Proof using.
      intros m x e; unfold MapsTo; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; intro i; [inversion i|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      rewrite InA_app_iff in i; destruct i; [apply MapsToLeft; apply IHt1; auto|].
      inversion H; subst. unfold eq_key_elt in H1; cbn in H1; destruct H1 as [x_l e_el]; subst; constructor.
      apply MapsToRight; apply IHt2; auto.
    Qed.
    Theorem elements_3w : forall (m : t elt), NoDupA eq_key (elements m).
    Proof using.
      intro m; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [constructor|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      apply NoDupA_app; auto.
      - constructor. unfold Reflexive; intro p; destruct p as [l' ell]; unfold eq_key; cbn; reflexivity.
        unfold Symmetric; intros p q; destruct p as [lp ep]; destruct q as [lq eq]; unfold eq_key; cbn; auto.
        unfold Transitive; intros p q r; destruct p as [lp ep]; destruct q as [lq eq]; destruct r as [lr er]; unfold eq_key; cbn; intros H1 H2; transitivity lq; auto.
      - constructor; [| apply IHt2; auto].
        intro H; apply elementsOfBT_3 in H; destruct H as [el' mt]; apply forallLocationsInTree_1 with (l0 := l) (el0 := el') in t2_bdd; auto;
          apply lt_irrefl with (x := l); exact t2_bdd.
      - intro x0; destruct x0 as [l' el']; intros i1 i2.
        apply elementsOfBT_3 in i1.
        inversion i2; subst.
        -- unfold eq_key in H0; cbn in H0; subst; destruct i1 as [el'' mt]; apply forallLocationsInTree_1 with (l0 := l) (el0 := el'') in t1_bdd; auto;
             apply lt_irrefl with (x := l); exact t1_bdd.
        -- apply elementsOfBT_3 in H0. destruct i1 as [el1 mt1]; destruct H0 as [el2 mt2].
           eapply forallLocationsInTree_1 in t1_bdd; eauto. eapply forallLocationsInTree_1 in t2_bdd; eauto.
           apply lt_irrefl with (x := l); transitivity l'; auto.
    Qed.
    Theorem elements_3 : forall (m : t elt), sort lt_key (elements m).
    Proof using.
      intro m; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [constructor|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      apply SortA_app with (eqA := eq_key); auto.
      - constructor. unfold Reflexive; intro p; destruct p as [l' ell]; unfold eq_key; cbn; reflexivity.
        unfold Symmetric; intros p q; destruct p as [lp ep]; destruct q as [lq eq]; unfold eq_key; cbn; auto.
        unfold Transitive; intros p q r; destruct p as [lp ep]; destruct q as [lq eq]; destruct r as [lr er]; unfold eq_key; cbn; intros H1 H2; transitivity lq; auto.
      - constructor; [apply IHt2; auto|]. apply In_InfA. intro y0; destruct y0 as [ly ey]; intro i.
        assert (InA eq_key (ly,ey) (elementsOfBT t2)).
        clear BSTt2 IHt1 IHt2. induction (elementsOfBT t2). inversion i.
        destruct i; subst. constructor; unfold eq_key; cbn; reflexivity.
        right; apply IHl0; auto.
        apply elementsOfBT_3 in H. destruct H as [nl mt]. eapply forallLocationsInTree_1 in t2_bdd; eauto.
      - intros x0 y0; destruct x0 as [lx ex]; destruct y0 as [ly ey]; intros i1 i2.
        apply elementsOfBT_3 in i1. inversion i2; subst; [unfold eq_key in H0; cbn in H0; subst|].
        unfold lt_key; cbn; destruct i1 as [l1 mt1]; eapply forallLocationsInTree_1 in t1_bdd; eauto.
        apply elementsOfBT_3 in H0. destruct i1 as [l1 mt1]; destruct H0 as [l2 mt2].
        eapply forallLocationsInTree_1 in t1_bdd; eauto. eapply forallLocationsInTree_1 in t2_bdd; eauto.
        unfold lt_key; cbn; transitivity l; auto.
    Qed.
  End elements.
  Arguments elementsOfBT {elt}.
  Arguments elements {elt}.

  Section cardinal.
    Variable elt : Set.
    Fixpoint cardinalOfBT (t : BT elt) : nat :=
      match t with
      | EmptyBT _ => 0
      | Branch t1 _ _ t2 => S (cardinalOfBT t1 + cardinalOfBT t2)
      end.
    Definition cardinal : t elt -> nat := fun t => cardinalOfBT (U t).

    Theorem cardinal_1 : forall (m : t elt), cardinal m = length (elements m).
    Proof using.
      unfold cardinal; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [reflexivity|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      rewrite app_length; cbn; rewrite PeanoNat.Nat.add_succ_r; auto.
    Qed.
  End cardinal.
  Arguments cardinalOfBT {elt}.
  Arguments cardinal {elt}.
  
  Section merge.
    Variable elt : Set.

    Fixpoint mergeBTs (l : BT elt) (r : BT elt) : BT elt :=
      match r with
      | EmptyBT _ => l
      | Branch rl loc e rr => Branch (mergeBTs l rl) loc e rr
      end.

    Lemma mergeBTsPreserveLs : forall (t1 t2 : BT elt) (P : L.t -> Prop), forallLocationsInTree t1 P -> forallLocationsInTree t2 P -> forallLocationsInTree (mergeBTs t1 t2) P.
    Proof using.
      intros t1 t2; revert t1; induction t2 as [|t21 IHt21 l2 e2 t22 IHt22]; cbn; intros t1 P fat1 fat2; auto.
      destruct fat2 as [Pl2 H]; destruct H as [fat21 fat22]; split; [|split]; auto.
    Qed.
    Lemma mergeBTsPreservesUpperBounds : forall (l : L.t) (t1 t2 : BT elt),
        forallLocationsInTree t1 (fun l' : L.t => l' < l) -> forallLocationsInTree t2 (fun l' : L.t => l' < l) ->
        forallLocationsInTree (mergeBTs t1 t2) (fun l' : L.t => l' < l).
    Proof using.
      intros l t1 t2 H H0; apply mergeBTsPreserveLs; auto.
    Qed.
    Lemma mergeBTsPreservesLowerBounds : forall (l : L.t) (t1 t2 : BT elt),
        forallLocationsInTree t1 (fun l' : L.t => l < l') -> forallLocationsInTree t2 (fun l' : L.t => l < l') ->
        forallLocationsInTree (mergeBTs t1 t2) (fun l' : L.t => l < l').
    Proof using.
      intros l t1 t2 H H0; apply mergeBTsPreserveLs; auto.
    Qed.
    
    Theorem mergeBTsPreservesBST : forall (t1 t2 : BT elt),
        isBST t1 -> isBST t2 ->
        (t1 = EmptyBT elt \/ exists l, greatestLocation t1 = Some l /\ forallLocationsInTree t2 (fun l' => l < l'))
        -> isBST (mergeBTs t1 t2).
    Proof using.
      intros t1 t2; revert t1; induction t2 as [|t21 IHt21 l e t22 IHt22]; intros t1 BST1 BST2 H1; cbn; auto.
      destruct H1 as [t1_empty | H]; [subst | destruct H as [l' H]; destruct H as [gl1 fa2]]; auto.
      all: cbn in BST2; destruct BST2 as [t21_bdd H]; destruct H as [t22_bdd H]; destruct H as [BST21 BST22].
      - specialize (IHt21 (EmptyBT elt) I BST21 (or_introl eq_refl)).
        split; [|split; [|split]]; auto.
        apply mergeBTsPreservesUpperBounds; cbn; auto.
      - specialize (IHt21 t1 BST1 BST21).
        split; [|split; [|split]]; auto.
        apply mergeBTsPreservesUpperBounds; cbn; auto.
        destruct fa2 as [l'_l H]. apply greatestLocation_sound in gl1. apply ChangeOfProperty with (P := fun l'0 => l'0 <= l'); auto.
        intros l0 l0_le_l'; apply L.le_lteq in l0_le_l'; destruct l0_le_l' as [l0_lt_l' | eq]; [transitivity l'|subst]; auto.
        apply IHt21. right; exists l'; split; auto.
        destruct fa2 as [l'_l H]; destruct H as [t21_bdd' t22_bdd']; auto.
    Qed.
    Lemma cardinalOfMerge : forall (t1 t2 : BT elt), (cardinalOfBT (mergeBTs t1 t2)) = (cardinalOfBT t1) + (cardinalOfBT t2).
    Proof using.
      intros t1; induction t2 as [| t21 IHt21 l2 e2 t22 IHt22]; cbn; [apply plus_n_O|].
      rewrite PeanoNat.Nat.add_succ_r; rewrite IHt21; lia.
    Qed.
    Lemma mergeEmpty : forall(t : BT elt), mergeBTs (EmptyBT _) t = t.
    Proof using.
      intros t; induction t as [| t1 IHt1 l a t2 IHt2]; cbn; auto.
      rewrite IHt1; auto.
    Qed.

    Lemma mergeBTsCreatesForalls : forall(t1 t2 : BT elt) (P : L.t -> Prop), forallLocationsInTree (mergeBTs t1 t2) P -> forallLocationsInTree t1 P /\ forallLocationsInTree t2 P.
    Proof using.
      intros t1 t2 P; revert t1; induction t2 as [|t21 IHt21 l' e t22 IHt22]; cbn; intros t1 fatmerge; [split|]; auto.
      destruct fatmerge as [Pl h]; destruct h as [fatmerge fat22].
      specialize (IHt21 t1 fatmerge). destruct IHt21 as [fat1 fat21].
      split; [|split; [|split]]; auto.
    Qed.
    
    Lemma mergeBTsCreatesBST : forall (l : L.t) (t1 t2 :BT elt),
        isBST (mergeBTs t1 t2) -> isBST t1 /\ isBST t2 /\ (t1 = EmptyBT _ \/ exists l', greatestLocation t1 = Some l' /\ forallLocationsInTree t2 (fun l'' => l' < l'')).
    Proof using.
      intros l t1 t2; revert t1; induction t2 as [|t21 IHt21 l' e t22 IHt22]; cbn; intros t1 BSTmerge; [split; [|split]|]; auto.
      destruct (greatestLocation t1) eqn:eq; [right; exists t0; auto; split; auto | apply greatestLocation_None_Empty in eq; left; auto].
      destruct BSTmerge as [merge_bdd h]; destruct h as [t22_bdd h]; destruct h as [BSTmerge BSTt22].
      apply IHt21 in BSTmerge. destruct BSTmerge as [BSTt1 h]; destruct h as [BSTt21 t21_lb].
      split; [|split; [split|]]; auto.
      apply mergeBTsCreatesForalls in merge_bdd; destruct merge_bdd; auto.
      destruct t21_lb as [H|]; [left; auto|].
      destruct H as [l'' H]; destruct H as [gl t21_bdd].
      right; exists l''; split; [|split; [|split]]; auto.
      all: apply mergeBTsCreatesForalls in merge_bdd; destruct merge_bdd as [t1_bdd t21_bdd']; apply greatestLocation_complete2 with (l1 := l') in gl; auto.
      apply ChangeOfProperty with (P := fun l0 => l' < l0); auto. intros l0 h; transitivity  l'; auto.
    Qed.
    
    Lemma findBT_mergeBT_None : forall (l : L.t) (t1 t2 : BT elt), isBST (mergeBTs t1 t2) -> findInBT l (mergeBTs t1 t2) = None -> findInBT l t1 = None /\ findInBT l t2 = None.
    Proof using.
      intros l t1 t2; revert t1; induction t2 as [|t21 IHt21 l' e t22 IHt22]; cbn; intros t1 BSTmerge eq; [split; auto|].
      destruct BSTmerge as [merge_bdd h]; destruct h as [t22_bdd h]; destruct h as [BSTmerge BSTt22].
      destruct (l ?= l') eqn:l_l'; [inversion eq| |].
      apply IHt21; auto.
      split; auto.
      destruct (findInBT l t1) eqn:mt; auto.
      apply findBT_2 in mt. apply forallLocationsInTree_1 with (P := fun l => l < l') in mt. apply compare_Gt_to_gt in l_l'; exfalso; apply lt_irrefl with (x := l); transitivity l'; auto.
      apply mergeBTsCreatesForalls in merge_bdd; destruct merge_bdd; auto.
    Qed.
    
    Theorem mergeBTs_1 : forall (t1 t2 : BT elt) (l : L.t) (el : elt), MapsToInBT l el t1 \/ MapsToInBT l el t2 -> MapsToInBT l el (mergeBTs t1 t2).
    Proof using.
      intros t1 t2; revert t1; induction t2 as [|t21 IHt21 l2 el2 t22 _]; intros t1 l el; cbn; [intro H; destruct H as [H|H]; [exact H|inversion H]|].
      intro H; destruct H as [mt | mt].
      apply MapsToLeft; apply IHt21; auto.
      inversion mt; subst; constructor; auto; fail.
    Qed.
    
    Theorem mergeBTs_2 : forall (t1 t2 : BT elt) (l : L.t) (el : elt), MapsToInBT l el (mergeBTs t1 t2) -> MapsToInBT l el t1 \/ MapsToInBT l el t2.
    Proof using.
      intros t1 t2; revert t1; induction t2 as [|t21 IHt21 l2 el2 t22 _]; intros t1 l el; cbn; intro mt; [left; exact mt|].
      inversion mt; subst.
      - right; constructor; auto; fail.
      - apply IHt21 in H2; auto. destruct H2 as [H2 | H2]; [left; exact H2 | right; constructor; auto; fail].
      - right; constructor; auto; fail.
    Qed.
  End merge.
  Arguments mergeBTs {elt}.

  Section remove.
    Variable elt : Set.

    Fixpoint removeFromBT (l : L.t) (t : BT elt) : BT elt :=
      match t with
      | EmptyBT _ => EmptyBT elt
      | Branch t1 l' e t2 =>
        match (l ?= l') with
        | Eq => mergeBTs t1 t2
        | Lt => Branch (removeFromBT l t1) l' e t2
        | Gt => Branch t1 l' e (removeFromBT l t2)
        end
      end.

    Lemma removePreservesForalls : forall (l : L.t) (t : BT elt) P, forallLocationsInTree t P -> forallLocationsInTree (removeFromBT l t) P.
    Proof using.
      intros l t; revert l; induction t as [| t1 IHt1 l e t2 IHt2]; intros l' P fat; cbn; auto.
      destruct fat as [Pl H]; destruct H as [fat1 fat2].
      destruct (l' ?= l) eqn:l'_l; [apply mergeBTsPreserveLs; auto| |]; cbn.
      all: split; [|split]; auto.
    Qed.

    Lemma removePreservesUpperBounds : forall (l l' : L.t) (t : BT elt), forallLocationsInTree t (fun l'' => l'' < l') -> forallLocationsInTree (removeFromBT l t) (fun l'' => l'' < l').
    Proof using.
      intros l l' t; revert l l'; induction t as [| t1 IHt1 loc e t2 IHt2]; intros l l' fat; cbn; auto.
      destruct fat as [loc_lt_l' H]; destruct H as [t1_bdd t2_bdd]; destruct (l ?= loc); try (split; auto).
      apply mergeBTsPreservesUpperBounds; auto.
    Qed.

    Lemma removePreservesLowerBounds : forall (l l' : L.t) (t : BT elt), forallLocationsInTree t (fun l'' => l' < l'') -> forallLocationsInTree (removeFromBT l t) (fun l'' => l' < l'').
    Proof using.
      intros l l' t; revert l l'; induction t as [| t1 IHt1 loc e t2 IHt2]; intros l l' fat; cbn; auto.
      destruct fat as [loc_lt_l' H]; destruct H as [t1_bdd t2_bdd]; destruct (l ?= loc); try (split; auto).
      apply mergeBTsPreservesLowerBounds; auto.
    Qed.
    
    Theorem removePreservesBST : forall (l : L.t) (t : BT elt), isBST t -> isBST (removeFromBT l t).
    Proof using.
      intros l t; revert l; induction t as [|t1 IHt1 l' e t2 IHt2]; intros l iBST; cbn; auto.
      destruct iBST as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BST1 BST2].
      destruct (l ?= l').
      - apply mergeBTsPreservesBST; auto.
        destruct (greatestLocation t1) as [l1|] eqn:gl1; [right; exists l1; split; [reflexivity|] | left; apply greatestLocation_None_Empty in gl1; subst; auto].
        apply ChangeOfProperty with (Q := fun l'0 => l'0 <= l') in t1_bdd; [| intros l'0 l'0_lt_l'; apply lt_to_le; exact l'0_lt_l'].
        apply (greatestLocation_complete _ t1 l' l1) in t1_bdd; [|exact gl1].
        apply ChangeOfProperty with (P := fun l'0 => l' < l'0); auto. intros l0 l'_lt_l0.
        apply L.le_lteq in t1_bdd; destruct t1_bdd; [transitivity l' | subst]; auto.
      - split; [|split; [|split]]; auto.
        specialize (IHt1 l BST1). apply removePreservesUpperBounds; auto.
      - split; [|split; [|split]]; auto.
        specialize (IHt2 l BST2). apply removePreservesLowerBounds; auto.
    Qed.

    Lemma cardinalOfRemove : forall (t : BT elt) (l : L.t), le (cardinalOfBT (removeFromBT l t)) (cardinalOfBT t).
    Proof using.
      intros t l; induction t as [| t1 IHt1 l' e' t2 IHt2]; cbn; [reflexivity|].
      destruct (l ?= l') eqn:l_l'; cbn; [rewrite cardinalOfMerge | |]; lia.
    Qed.

    Definition remove : L.t -> t elt -> t elt := fun l t => {| U := removeFromBT l (U t); U_corr := removePreservesBST l (U t) (U_corr t) |}.

    Theorem remove_1 : forall  (m : t elt) (x : L.t), ~ In x (remove x m).
    Proof using.
      intros m x; unfold remove; unfold In; unfold MapsTo; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [intro ext; destruct ext as [e0 mt]; inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      destruct (x ?= l) eqn:x_l.
      - apply compare_Eq_to_eq in x_l; subst.
        intro H; destruct H as [el' mt]. apply mergeBTs_2 in mt; destruct mt as [mt | mt].
        apply forallLocationsInTree_1 with (l0 := l) (el0 := el') in t1_bdd; auto.
        apply lt_irrefl in t1_bdd; inversion t1_bdd.
        apply forallLocationsInTree_1 with (l0 := l) (el0 := el') in t2_bdd; auto.
        apply lt_irrefl in t2_bdd; inversion t2_bdd.
      - intro H; destruct H as [el' mt]; inversion mt; subst; [apply compare_Lt_to_lt in x_l; apply lt_irrefl in x_l; inversion x_l | apply IHt1; auto; exists el'; auto |].
        apply compare_Lt_to_lt in x_l. apply forallLocationsInTree_1 with (l0 := x) (el0 := el') in t2_bdd; auto.
        assert (l < l) as H by (transitivity x; auto); apply lt_irrefl in H; inversion H.
      - apply compare_Gt_to_gt in x_l.
        intro H; destruct H as [el' mt]; inversion mt; subst; [apply lt_irrefl in x_l; inversion x_l | | apply IHt2; auto; exists el'; auto].
        apply forallLocationsInTree_1 with (l0 := x) (el0 := el') in t1_bdd; auto.
        assert (l < l) as H by (transitivity x; auto); apply lt_irrefl in H; inversion H.
    Qed.
    Theorem remove_2 : forall (m : t elt) (x y : L.t) (e : elt), x <> y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof using.
      intros m x y e; unfold remove; unfold MapsTo; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [intros n mt; inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      intros n mt; destruct (x ?= l) eqn:x_l.
      - apply compare_Eq_to_eq in x_l; subst.
        inversion mt; subst; [exfalso; apply n; auto| |]; apply mergeBTs_1; auto.
      - apply compare_Lt_to_lt in x_l.
        inversion mt; subst; constructor; auto; fail.
      - apply compare_Gt_to_gt in x_l.
        inversion mt; subst; constructor; auto; fail.
    Qed.
    Theorem remove_3 : forall (m : t elt) (x y : L.t) (e : elt), x <> y  -> MapsTo y e (remove x m) -> MapsTo y e m.
    Proof using.
      intros m x y e; unfold remove; unfold MapsTo; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [intros n mt; inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      intros n mt; destruct (x ?= l) eqn:x_l.
      - apply compare_Eq_to_eq in x_l; subst.
        apply mergeBTs_2 in mt; destruct mt as [mt | mt]; constructor; auto; fail.
      - apply compare_Lt_to_lt in x_l.
        inversion mt; subst; constructor; auto; fail.
      - apply compare_Gt_to_gt in x_l.
        inversion mt; subst; constructor; auto; fail.
    Qed.
  End remove.
  Arguments removeFromBT {elt}.
  Arguments remove {elt}.

  Section mem.
    Variable elt : Set.

    Fixpoint memOfBT (l : L.t) (t : BT elt) : bool :=
      match t with
      | EmptyBT _ => false
      | Branch t1 l' _ t2 =>
        if L.eq_dec l l' then true else (memOfBT l t1) || (memOfBT l t2)
      end.
    Definition mem : L.t -> t elt -> bool := fun l t => memOfBT l (U t).

    Theorem mem_1 : forall (m : t elt) (l : L.t) , In l m -> mem l m = true.
    Proof using.
      intros m l i; destruct i as [el mt]; unfold mem; destruct m as [t BSTt]; unfold MapsTo in mt; cbn in *.
      induction t; cbn; [inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      inversion mt; subst. destruct (L.eq_dec t2 t2) as [_ | n]; [|exfalso; apply n]; reflexivity.
      destruct (L.eq_dec l t2) as [_ | _]; [| specialize (IHt1 BSTt1 H2); rewrite IHt1; cbn]; reflexivity.
      destruct (L.eq_dec l t2) as [_ | _]; [| specialize (IHt2 BSTt2 H2); rewrite IHt2; rewrite orb_true_r]; reflexivity.
    Qed.
    Theorem mem_2 : forall (m : t elt) (l : L.t) , mem l m = true -> In l m.
    Proof using.
      intros m l; unfold mem; destruct m as [t BSTt]; unfold In; unfold MapsTo; cbn; intro mem_eq.
      induction t as [| t1 IHt1 loc el t2 IHt2]; cbn in mem_eq; [discriminate mem_eq|].
      destruct (L.eq_dec l loc) as [x_loc | _]; [subst; exists el; constructor|].
      destruct BSTt as [_ H]; destruct H as [_ H]; destruct H as [BSTt1 BSTt2].
      destruct (memOfBT l t1) eqn:eq. destruct (IHt1 BSTt1 eq_refl) as [el' mt]; exists el'; constructor; auto.
      destruct (memOfBT l t2); [clear mem_eq| discriminate mem_eq].
      destruct (IHt2 BSTt2 eq_refl) as [el' mt]; exists el'; (constructor; auto; fail).
    Qed.
  End mem.
  Arguments memOfBT {elt}.
  Arguments mem {elt}.
  
  Section map.
    Variable elt elt' : Set.

    Fixpoint mapBT (f : elt -> elt') (t : BT elt) : BT elt' :=
      match t with
      | EmptyBT _ => EmptyBT _
      | Branch t1 l e t2 => Branch (mapBT f t1) l (f e) (mapBT f t2)
      end.
    Theorem mapPreservesForalls : forall (f : elt -> elt') P (t : BT elt), forallLocationsInTree t P -> forallLocationsInTree (mapBT f t) P.
    Proof using.
      intros f P t; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; intro fat; [auto|].
      destruct fat as [Pl H]; destruct H as [fat1 fat2]; split; [exact Pl|split; [apply IHt1 | apply IHt2]; auto].
    Qed.

    Lemma mapBTPreservesUB : forall (f : elt -> elt') (t : BT elt) (l : L.t), forallLocationsInTree t (fun l' => l' < l) -> forallLocationsInTree (mapBT f t) (fun l' => l' < l).
    Proof using.
      intros f t0 l H; apply mapPreservesForalls; auto.
    Qed.
    Lemma mapBTPreservesLB : forall (f : elt -> elt') (t : BT elt) (l : L.t), forallLocationsInTree t (fun l' => l < l') -> forallLocationsInTree (mapBT f t) (fun l' => l < l').
    Proof using.
      intros f t0 l H; apply mapPreservesForalls; auto.
    Qed.
    Theorem mapBTPreservesBST : forall (f : elt -> elt') (t : BT elt), isBST t -> isBST (mapBT f t).
    Proof using.
      intros f t; revert f; induction t as [|t1 IHt1 l e t2 IHt2]; intros f iBST; cbn; auto.
      destruct iBST as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BST1 BST2].
      split; [apply mapBTPreservesUB | split; [apply mapBTPreservesLB | split]]; auto.
    Qed.

    Theorem mapBT_1 : forall (t : BT elt) (l : L.t) (e : elt)(f : elt -> elt'), MapsToInBT l e t -> MapsToInBT l (f e) (mapBT f t).
    Proof using.
      intros t; induction t as [| t1 IHt1 l el t2 IHt2]; intros l' e f mt; [inversion mt|]; cbn.
      inversion mt; subst; constructor; auto; fail.
    Qed.

    Theorem mapBT_2 : forall (t : BT elt) (l : L.t) (f : elt -> elt'), InBT l (mapBT f t) -> InBT l t.
    Proof using.
      intros t; induction t as [| t1 IHt1 l el t2 IHt2]; intros l' f i; [destruct i as [e mt]; inversion mt|].
      destruct i as [e mt]; cbn in mt; inversion mt; subst; [exists el; constructor | |].
      - destruct (IHt1 l' f (ex_intro _ e H2)) as [e' mt']; exists e'; constructor; auto; fail.
      - destruct (IHt2 l' f (ex_intro _ e H2)) as [e' mt']; exists e'; constructor; auto; fail.
    Qed.

    Definition map : (elt -> elt') -> t elt -> t elt' := fun f t => {| U := mapBT f (U t); U_corr := mapBTPreservesBST f (U t) (U_corr t) |}.

    Theorem map_1 : forall (m : t elt) (x : L.t) (e : elt)(f : elt -> elt'), MapsTo x e m -> MapsTo x (f e) (map f m).
    Proof using.
      unfold MapsTo; intros m; destruct m as [t BSTt]; cbn.
      intros x e f H; apply mapBT_1; auto.
    Qed.
    
    Theorem map_2 : forall(m : t elt) (x : L.t) (f : elt -> elt'), In x (map f m) -> In x m.
    Proof using.
      unfold In; unfold MapsTo; intros m; destruct m as [t BSTt]; cbn.
      apply mapBT_2.
    Qed.

  End map.
  Arguments mapBT {elt} {elt'}.
  Arguments map {elt} {elt'}.
  
  Section mapi.
    Variable elt elt' : Set.
    
    Fixpoint mapiBT (f : L.t -> elt -> elt') (t : BT elt) : BT elt' :=
      match t with
      | EmptyBT _ => EmptyBT _
      | Branch t1 l e t2 => Branch (mapiBT f t1) l (f l e) (mapiBT f t2)
      end.
    Lemma mapiBTPreservesUB : forall (f : L.t -> elt -> elt') (t : BT elt) (l : L.t), forallLocationsInTree t (fun l' => l' < l) -> forallLocationsInTree (mapiBT f t) (fun l' => l' < l).
    Proof using.
      intros f t; revert f; induction t as [|t1 IHt1 l' e t2 IHt2]; intros f l fat; cbn; auto.
      destruct fat as [l'_lt_l H]; destruct H as [t1_bdd t2_bdd].
      split; [|split]; auto.
    Qed.
    Lemma mapiBTPreservesLB : forall (f : L.t -> elt -> elt') (t : BT elt) (l : L.t), forallLocationsInTree t (fun l' => l < l') -> forallLocationsInTree (mapiBT f t) (fun l' => l < l').
    Proof using.
      intros f t; revert f; induction t as [|t1 IHt1 l' e t2 IHt2]; intros f l fat; cbn; auto.
      destruct fat as [l'_lt_l H]; destruct H as [t1_bdd t2_bdd].
      split; [|split]; auto.
    Qed.
    Theorem mapiBTPreservesBST : forall (f : L.t -> elt -> elt') (t : BT elt), isBST t -> isBST (mapiBT f t).
    Proof using.
      intros f t; revert f; induction t as [|t1 IHt1 l e t2 IHt2]; intros f iBST; cbn; auto.
      destruct iBST as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BST1 BST2].
      split; [apply mapiBTPreservesUB | split; [apply mapiBTPreservesLB | split]]; auto.
    Qed.
    
    Definition mapi : (L.t -> elt -> elt') -> t elt -> t elt' := fun f t => {| U := mapiBT f (U t); U_corr := mapiBTPreservesBST f (U t) (U_corr t) |}.

    Theorem mapi_1 : forall (m : t elt) (x : L.t) (e : elt) (f: L.t -> elt -> elt'), MapsTo x e m -> MapsTo x (f x e) (mapi f m).
    Proof using.
      unfold MapsTo; unfold mapi; intros m; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; intros x e f mt; [inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      inversion mt; subst; constructor; auto; fail.
    Qed.    
    Theorem mapi_2 : forall (m : t elt) (x : L.t) (f : L.t -> elt -> elt'), In x (mapi f m) -> In x m.
    Proof using.
      unfold In; unfold MapsTo; intros m; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; intros x f i; [destruct i as [e mt]; inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      destruct i as [e mt]; cbn in mt; inversion mt; subst; [exists el; constructor | |].
      - destruct (IHt1 BSTt1 x f (ex_intro _ e H2)) as [e' mt']; exists e'; constructor; auto; fail.
      - destruct (IHt2 BSTt2 x f (ex_intro _ e H2)) as [e' mt']; exists e'; constructor; auto; fail.
    Qed.

  End mapi.
  Arguments mapiBT {elt} {elt'}.
  Arguments mapi {elt} {elt'}.

  Section prune.
    Variable elt : Set.
    
    Fixpoint pruneBT  (t : BT (option elt)) : BT elt :=
      match t with
      | EmptyBT _ => EmptyBT elt
      | Branch t1 l e t2 =>
        match e with
        | Some e' => Branch (pruneBT t1) l e' (pruneBT t2)
        | None => mergeBTs (pruneBT t1) (pruneBT t2)
        end
      end.
    Lemma prunePreservesForalls : forall (t : BT (option elt)) (P : L.t -> Prop), forallLocationsInTree t P -> forallLocationsInTree (pruneBT t) P.
    Proof using.
      intros t; induction t as [| t1 IHt1 l e t2 IHt2]; intros P fat; cbn; auto.
      cbn in fat; destruct fat as [Pl H]; destruct H as [fat1 fat2].
      destruct e; [cbn| apply mergeBTsPreserveLs; [apply IHt1 | apply IHt2]; auto]; split; [|split]; auto.
    Qed.
    Lemma pruneBTPreservesBST : forall (t : BT (option elt)), isBST t -> isBST (pruneBT t).
    Proof using.
      intros t; induction t as [| t1 IHt1 l e t2 IHt2]; intro i; cbn; auto.
      cbn in i; destruct i as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      destruct e; [cbn | apply mergeBTsPreservesBST; auto]. split; [|split]; auto. 1,2: apply prunePreservesForalls; auto.
      destruct (greatestLocation (pruneBT t1)) as [gl|] eqn:eq; [right; exists gl; split; auto | left; apply greatestLocation_None_Empty in eq; exact eq].
      apply greatestLocation_complete2 with (l1 := l) in eq; [| apply prunePreservesForalls; exact t1_bdd].
      apply ChangeOfProperty with (P := fun l' => l < l'); [apply prunePreservesForalls; exact t2_bdd| intros l0 lt; transitivity l; auto].
    Qed.

    Theorem prune_1 : forall (t : BT (option elt)) (l : L.t) (e : elt),
        MapsToInBT l (Some e) t -> MapsToInBT l e (pruneBT t).
    Proof using.
      intros t; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; intros l' e' mt; [inversion mt|].
      destruct e as [e|]; inversion mt; subst.
      all: try (constructor; auto; fail).
      apply mergeBTs_1; left; auto.
      apply mergeBTs_1; right; auto.
    Qed.
    Theorem prune_2 : forall (t : BT (option elt)) (l : L.t) (e : elt),
        isBST t -> MapsToInBT l e (pruneBT t) -> MapsToInBT l (Some e) t.
    Proof using.
      intros t l e BSTt; revert l e; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; intros l' e' mt; [inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2]; specialize (IHt1 BSTt1); specialize (IHt2 BSTt2).
      destruct e as [e|]; [inversion mt; subst|]; try (constructor; auto; fail).
      apply mergeBTs_2 in mt; destruct mt as [mt|mt]; [apply IHt1 in mt | apply IHt2 in mt]; constructor; auto; fail.
    Qed.
    Theorem prune_3 : forall (t : BT (option elt)) (l : L.t),
        isBST t -> MapsToInBT l None t -> ~ InBT l (pruneBT t).
    Proof using.
      intros t l BSTt; revert l; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; intros l' mt; [inversion mt|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2]; specialize (IHt1 BSTt1); specialize (IHt2 BSTt2).
      inversion mt; subst.
      - intro i. destruct i as [e mt']. apply mergeBTs_2 in mt'; destruct mt' as [mt' | mt']; apply prune_2 in mt'; auto.
        all: assert (None = Some e) as H by (apply (MapsToInBTUnique (Branch t1 l None t2) l); auto; [cbn; auto | constructor; auto; fail]); inversion H.
      - intro i. destruct i as [e' mt']. destruct e as [e|]. inversion mt'; subst.
        -- assert (None = Some e) as H by (apply MapsToInBTUnique with (t := Branch t1 l (Some e) t2) (l0 := l); auto; [cbn; auto | constructor; auto; fail]); inversion H.
        -- apply IHt1 with (l := l'); auto. exists e'; auto.
        -- apply prune_2 in H3; auto. apply forallLocationsInTree_1 with (P := fun l' => l < l') in H3; auto.
           apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto. apply lt_irrefl with (x := l); transitivity l'; auto.
        -- apply mergeBTs_2 in mt'. destruct mt' as [mt' | mt'].
           apply IHt1 with (l := l'); auto. exists e'; auto.
           apply prune_2 in mt'; auto. apply forallLocationsInTree_1 with (P := fun l' => l < l') in mt'; auto.
           apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto. apply lt_irrefl with (x := l); transitivity l'; auto.
      - intro i. destruct i as [e' mt']. destruct e as [e|]. inversion mt'; subst.
        -- assert (None = Some e) as H by (apply MapsToInBTUnique with (t := Branch t1 l (Some e) t2) (l0 := l); auto; [cbn; auto | constructor; auto; fail]); inversion H.
        -- apply prune_2 in H3; auto. apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H3; auto.
           apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto. apply lt_irrefl with (x := l); transitivity l'; auto.
        -- apply IHt2 with (l := l'); auto. exists e'; auto.
        -- apply mergeBTs_2 in mt'. destruct mt' as [mt' | mt'].
           apply prune_2 in mt'; auto. apply forallLocationsInTree_1 with (P := fun l' => l' < l) in mt'; auto.
           apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto. apply lt_irrefl with (x := l); transitivity l'; auto.
           apply IHt2 with (l := l'); auto. exists e'; auto.
    Qed.
  End prune.
  Arguments pruneBT {elt}.

  Section split.
    Variable elt : Set.
    
    Fixpoint splitBT (t : BT elt) (l : L.t) : BT elt * BT elt :=
      match t with
      | EmptyBT _ => (EmptyBT _, EmptyBT _)
      | Branch t1 l' e t2 =>
        match l ?= l' with
        | Eq => (t1, t2)
        | Lt => match splitBT t1 l with
               | (t11, t12) => (t11, Branch t12 l' e t2)
               end
        | Gt => match splitBT t2 l with
               | (t21, t22) => (Branch t1 l' e t21, t22)
               end
        end
      end.
    Theorem splitBTCardinalLeft : forall (t : BT elt) (l : L.t), le (cardinalOfBT (fst (splitBT t l))) (cardinalOfBT t).
    Proof using.
      intros t l; induction t as [| t1 IHt1 l' e t2 IHt2]; cbn; [reflexivity|].
      destruct (l ?= l'); cbn; [|destruct (splitBT t1 l) | destruct (splitBT t2 l)]; cbn in *; lia.
    Qed.
    Theorem splitBTCardinalRight: forall (t : BT elt) (l : L.t), le (cardinalOfBT (snd (splitBT t l))) (cardinalOfBT t).
    Proof using.
      intros t l; induction t as [| t1 IHt1 l' e t2 IHt2]; cbn; [reflexivity|].
      destruct (l ?= l'); cbn; [|destruct (splitBT t1 l) | destruct (splitBT t2 l)]; cbn in *; lia.
    Qed.
    Theorem splitBTPreservesForalls : forall  (t : BT elt) (l : L.t) (P : L.t -> Prop),
        forallLocationsInTree t P -> forallLocationsInTree (fst (splitBT t l)) P /\ forallLocationsInTree (snd (splitBT t l)) P.
    Proof using.
      intros t l P; induction t as [| t1 IHt1 l' e t2 IHt2]; cbn; intro fat; auto.
      destruct fat as [Pl' H]; destruct H as [fat1 fat2].
      specialize (IHt1 fat1); specialize (IHt2 fat2).
      destruct IHt1 as [fat11 fat12]; destruct IHt2 as [fat21 fat22].
      destruct (l ?= l'); split; auto.
      1,2: destruct (splitBT t1 l); cbn in *; auto.
      all: destruct (splitBT t2 l); cbn in *; auto.
    Qed.
    Lemma splitBTPreservesForallsLeft : forall (t : BT elt) (l : L.t) (P : L.t -> Prop),
        forallLocationsInTree t P -> forallLocationsInTree (fst (splitBT t l)) P.
    Proof using.
      intros t0 l P H; apply splitBTPreservesForalls; auto.
    Qed.
    Lemma splitBTPreservesForallsRight : forall (t : BT elt) (l : L.t) (P : L.t -> Prop),
        forallLocationsInTree t P -> forallLocationsInTree (snd (splitBT t l)) P.
    Proof using.
      intros t0 l P H; apply splitBTPreservesForalls; auto.
    Qed.
    Lemma splitBTPreservesBST : forall (t : BT elt) (l : L.t), isBST t -> isBST (fst (splitBT t l)) /\ isBST (snd (splitBT t l)).
    Proof using.
      intros t l; induction t as [| t1 IHt1 l' e t2 IHt2]; intro BSTt; cbn; auto.
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2]; specialize (IHt1 BSTt1); specialize (IHt2 BSTt2);
        destruct IHt1 as [BST11 BST12]; destruct IHt2 as [BST21 BST22].
      destruct (splitBTPreservesForalls t1 l _ t1_bdd) as [t11_bdd t12_bdd].
      destruct (splitBTPreservesForalls t2 l _ t2_bdd) as [t21_bdd t22_bdd].
      destruct (l ?= l'); split; auto.
      1,2: destruct (splitBT t1 l); cbn in *; auto.
      all: destruct (splitBT t2 l); cbn in *; auto.
    Qed.
    Lemma splitBTBounds : forall (t : BT elt) (l : L.t),
        isBST t -> forallLocationsInTree (fst (splitBT t l)) (fun l' => l' < l) /\ forallLocationsInTree (snd (splitBT t l)) (fun l' => l < l').
    Proof using.
      intros t l; induction t as [| t1 IHt1 l' e t2 IHt2]; cbn; intro BSTt; auto.
      destruct BSTt as [t1_bdd h]; destruct h as [t2_bdd h]; destruct h as [BSTt1 BSTt2].      
      specialize (IHt1 BSTt1); destruct IHt1 as [t11_bdd t12_bdd]; specialize (IHt2 BSTt2); destruct IHt2 as [t21_bdd t22_bdd].
      destruct (l ?= l') eqn:l_l'; cbn in *; [apply compare_Eq_to_eq in l_l'; subst; split;auto| apply compare_Lt_to_lt in l_l' | apply compare_Gt_to_gt in l_l'].
      - destruct (splitBT t1 l); cbn in *; split; [|split; [|split]]; auto.
        apply ChangeOfProperty with (P := fun l'0 => l' < l'0); auto; intros l0 h; transitivity l'; auto.
      - destruct (splitBT t2 l); cbn in *; split; [split; [|split]|]; auto.
        apply ChangeOfProperty with (P := fun l'0 => l'0 < l'); auto; intros l0 h; transitivity l'; auto.
    Qed.

    Lemma find_splitBT_1 : forall (t : BT elt) (l l' : L.t), l < l' -> findInBT l (fst (splitBT t l')) = findInBT l t.
    Proof using.
      intros t l' l'' l'_lt_l''; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; auto.
      destruct (l' ?= l) eqn:l'_l.
      - apply compare_Eq_to_eq in l'_l; subst.
        destruct (l'' ?= l) eqn: l''_l; [apply compare_Eq_to_eq in l''_l; subst; exfalso; apply lt_irrefl with (x := l); auto
                                        |apply compare_Lt_to_lt in l''_l; exfalso; apply lt_irrefl with (x := l); transitivity l''; auto |].
        destruct (splitBT t2 l''); cbn in *.
        destruct (l ?= l) eqn:l_l; auto; [apply compare_Lt_to_lt in l_l | apply compare_Gt_to_gt in l_l]; exfalso; apply lt_irrefl with (x := l); auto.
      - destruct (l'' ?= l) eqn:l''_l; cbn; auto; [destruct (splitBT t1 l'') | destruct (splitBT t2 l'')]; cbn in *; auto.
        destruct (l' ?= l); auto; inversion l'_l.
      - destruct (l'' ?= l) eqn:l''_l; [ apply compare_Gt_to_gt in l'_l |  apply compare_Gt_to_gt in l'_l |].
        apply compare_Eq_to_eq in l''_l; subst; exfalso; apply lt_irrefl with (x := l); transitivity l'; auto.
        apply compare_Lt_to_lt in l''_l; exfalso; apply lt_irrefl with (x := l''); transitivity l'; auto; transitivity l; auto.
        destruct (splitBT t2 l''); cbn in *. destruct (l' ?= l); auto; inversion l'_l.
    Qed.
    Lemma find_splitBT_2 : forall(t : BT elt) (l l' : L.t), l' < l -> findInBT l (snd (splitBT t l')) = findInBT l t.
    Proof using.
      intros t l' l'' l'_lt_l''; induction t as [|t1 IHt1 l e t2 IHt2]; cbn; auto.
      destruct (l' ?= l) eqn:l'_l.
      - apply compare_Eq_to_eq in l'_l; subst.
        destruct (l'' ?= l) eqn: l''_l; [apply compare_Eq_to_eq in l''_l; subst; exfalso; apply lt_irrefl with (x := l); auto
                                        | |apply compare_Gt_to_gt in l''_l; exfalso; apply lt_irrefl with (x := l); transitivity l''; auto].
        destruct (splitBT t1 l''); cbn in *.
        destruct (l ?= l) eqn:l_l; auto; [apply compare_Lt_to_lt in l_l | apply compare_Gt_to_gt in l_l]; exfalso; apply lt_irrefl with (x := l); auto.
      - destruct (l'' ?= l) eqn:l''_l; [ apply compare_Lt_to_lt in l'_l |  | apply compare_Lt_to_lt in l'_l].
        apply compare_Eq_to_eq in l''_l; subst; exfalso; apply lt_irrefl with (x := l); transitivity l'; auto.
        destruct (splitBT t1 l''); cbn in *; destruct (l' ?= l); auto; inversion l'_l.
        apply compare_Gt_to_gt in l''_l; exfalso; apply lt_irrefl with (x := l''); transitivity l'; auto; transitivity l; auto.
      - destruct (l'' ?= l) eqn:l''_l; cbn; auto; [destruct (splitBT t1 l'') | destruct (splitBT t2 l'')]; cbn in *; auto.
        destruct (l' ?= l); auto; inversion l'_l.
    Qed.

    Lemma splitBT_1 : forall (t : BT elt) (l l' : L.t) (e : elt), MapsToInBT l e (fst (splitBT t l')) \/ MapsToInBT l e (snd (splitBT t l')) -> MapsToInBT l e t.
    Proof using.
      intros t l l'; induction t as [| t1 IHt1 l'' e t2 IHt2]; intros e' i.
      destruct i as [mt | mt]; inversion mt.
      cbn in i. destruct (l' ?= l'') eqn:l'_l''; cbn in i; [destruct i as [mt | mt]; constructor; auto; fail| |].
      destruct (splitBT t1 l') eqn:t1_eq; cbn in *.
      2: destruct (splitBT t2 l') eqn:t2_eq; cbn in *.
      all: destruct i as [mt | mt].
      - specialize (IHt1 e' (or_introl mt));  constructor; auto; fail.
      - inversion mt; subst; [constructor| | constructor; auto; fail].
        specialize (IHt1 e' (or_intror H2)); constructor; auto; fail.
      - inversion mt; subst; [constructor | constructor; auto; fail |].
        specialize (IHt2 e' (or_introl H2)); constructor; auto; fail.
      - inversion mt; subst.
        -- specialize (IHt2 e' (or_intror mt));constructor; auto; fail.
        -- assert (MapsToInBT l e' (Branch t0 l'0 e'0 t3)) as for_IHt2 by (constructor; auto; fail).
           specialize (IHt2 e' (or_intror for_IHt2)); constructor; auto; fail.
        -- assert (MapsToInBT l e' (Branch t0 l'0 e'0 t3)) as for_IHt2 by (constructor; auto; fail).
           specialize (IHt2 e' (or_intror for_IHt2)); constructor; auto; fail.
    Qed.
    Lemma splitBT_11 : forall (t : BT elt) (l l' : L.t) (e : elt), MapsToInBT l e (fst (splitBT t l')) -> MapsToInBT l e t.
    Proof using.
      intros t0 l l' e H; apply splitBT_1 with (l' := l'); left; auto.
    Qed.
    Lemma splitBT_12 : forall (t : BT elt) (l l' : L.t) (e : elt), MapsToInBT l e (snd (splitBT t l')) -> MapsToInBT l e t.
    Proof using.
      intros t0 l l' e H; apply splitBT_1 with (l' := l'); right; auto.
    Qed.
    Lemma splitBT_2 : forall (t : BT elt) (l l' : L.t) (e : elt), isBST t -> MapsToInBT l e t -> l < l' -> MapsToInBT l e (fst (splitBT t l')).
    Proof using.
      intros t l l' e' BSTt mt l_lt_l'; induction t as [| t1 IHt1 l'' e t2 IHt2]; cbn; auto.
      destruct BSTt as [t1_bdd h]; destruct h as [t2_bdd h]; destruct h as [BSTt1 BSTt2].
      inversion mt; subst.
      - destruct (l' ?= l'') eqn:l'_l''. apply compare_Eq_to_eq in l'_l''; subst; exfalso; apply lt_irrefl with (x := l''); auto.
        apply compare_Lt_to_lt in l'_l''. exfalso; apply lt_irrefl with (x := l''); transitivity l'; auto.
        destruct (splitBT t2 l'); cbn in *; constructor.
      - destruct (l' ?= l'') eqn:l'_l''; cbn; auto.
        destruct (splitBT t1 l'); cbn in *. apply IHt1; auto.
        apply compare_Gt_to_gt in l'_l''.
        destruct (splitBT t2 l'); cbn in *. constructor; auto; fail.
      - destruct (l' ?= l'') eqn:l'_l''; cbn; auto.
        apply compare_Eq_to_eq in l'_l''; subst; apply forallLocationsInTree_1 with (P := fun l' => l'' < l') in H2; auto; exfalso; apply lt_irrefl with (x := l); transitivity l''; auto.
        apply compare_Lt_to_lt in l'_l'';
          apply forallLocationsInTree_1 with (P := fun l' => l'' < l') in H2; auto; exfalso; apply lt_irrefl with (x := l'); transitivity l''; auto; transitivity  l; auto.
        destruct (splitBT t2 l'); cbn in *; apply MapsToRight; apply IHt2; auto.
    Qed.
    Lemma splitBT_3 : forall (t : BT elt) (l l' : L.t) (e : elt), isBST t -> MapsToInBT l e t -> l' < l -> MapsToInBT l e (snd (splitBT t l')).
    Proof using.
      intros t l l' e' BSTt mt l_lt_l'; induction t as [| t1 IHt1 l'' e t2 IHt2]; cbn; auto.
      destruct BSTt as [t1_bdd h]; destruct h as [t2_bdd h]; destruct h as [BSTt1 BSTt2].
      inversion mt; subst.
      - destruct (l' ?= l'') eqn:l'_l''. apply compare_Eq_to_eq in l'_l''; subst; exfalso; apply lt_irrefl with (x := l''); auto.
        destruct (splitBT t1 l'); cbn in *; constructor.
        apply compare_Gt_to_gt in l'_l''. exfalso; apply lt_irrefl with (x := l''); transitivity l'; auto.
      - destruct (l' ?= l'') eqn:l'_l''; cbn; auto.
        apply compare_Eq_to_eq in l'_l''; subst; apply forallLocationsInTree_1 with (P := fun l' => l' < l'') in H2; auto; exfalso; apply lt_irrefl with (x := l); transitivity l''; auto.
        destruct (splitBT t1 l'); cbn in *; apply MapsToLeft; apply IHt1; auto.
        apply compare_Gt_to_gt in l'_l'';
          apply forallLocationsInTree_1 with (P := fun l' => l' < l'') in H2; auto; exfalso; apply lt_irrefl with (x := l'); transitivity l''; auto; transitivity  l; auto.
      - destruct (l' ?= l'') eqn:l'_l''; cbn; auto.
        destruct (splitBT t1 l'); cbn in *; constructor; auto; fail.
        destruct (splitBT t2 l'); cbn in *; apply IHt2; auto.
    Qed.
  End split.
  Arguments splitBT {elt}.

  Section fold.
    Fixpoint foldBT {elt : Set} {A : Type} (f: L.t -> elt -> A -> A) (t : BT elt) (a : A) : A :=
      match t with
      | EmptyBT _ => a
      | Branch t1 l e t2 => foldBT f t2 (f l e (foldBT f t1 a))
      end.
    Definition fold : forall {elt : Set} {A : Type}, (L.t -> elt -> A -> A) -> t elt -> A -> A := fun elt A f t a => foldBT f (U t) a.

    Theorem fold_1 : forall {elt : Set} (m : t elt) (A : Type) (i : A) (f : L.t -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof using.
      unfold fold; unfold elements; destruct m as [t BSTt]; cbn.
      induction t as [| t1 IHt1 l el t2 IHt2]; cbn; [reflexivity|].
      destruct BSTt as [t1_bdd H]; destruct H as [t2_bdd H]; destruct H as [BSTt1 BSTt2].
      intros A i f. rewrite IHt2; auto. rewrite IHt1; auto.
      rewrite fold_left_app. reflexivity.
    Qed.
  End fold.

  Section equal.
    Variable elt : Set.

    Fixpoint equalBT (cmp : elt -> elt -> bool) (t1 : BT elt) (t2 : BT elt) : bool :=
      match t1 with
      | EmptyBT _ =>
        match t2 with
        | EmptyBT _ => true
        | Branch _ _ _ _ => false
        end
      | Branch t11 l e1 t12 =>
        match findInBT l t2 with
        | Some e2 => cmp e1 e2 && equalBT cmp t11 (fst (splitBT t2 l)) && equalBT cmp t12 (snd (splitBT t2 l))
        | None => false
        end
      end.
    Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool := fun cmp t1 t2 => equalBT cmp (U t1) (U t2).

    Definition Equal (m m' : t elt) := forall (y : L.t), find y m = find y m'.
    Definition Equiv (eq_elt : elt -> elt -> Prop) m m' :=
      (forall k, In k m <-> In k m') /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb (cmp : elt -> elt -> bool) := Equiv (fun e1 e2 => cmp e1 e2 = true).
    
    Theorem equal_1 : forall (m m' : t elt) (cmp : elt -> elt -> bool), Equivb cmp m m' -> equal cmp m m' = true.
    Proof using.
      intros m m' cmp; destruct m as [t BSTt]; destruct m' as [t' BSTt'].
      unfold equal; unfold Equivb; unfold Equiv; unfold In; unfold MapsTo; cbn.
      revert BSTt t' BSTt'. induction t as [| t11 IHt11 l e t12 IHt12]; cbn; intros BSTt t' BSTt'.
      - intros H; destruct H as [i mt]; destruct t' as [| t21 l' e' t22]; auto.
        assert (exists e : elt, MapsToInBT l' e (EmptyBT elt)) as H by (apply i; exists e'; constructor).
        destruct H as [e mt']; inversion mt'.
      - intro H; destruct H as [ins mts].
        destruct BSTt as [t11_bdd H]; destruct H as [t12_bdd H]; destruct H as [BSTt11 BSTt12]; specialize (IHt11 BSTt11); specialize (IHt12 BSTt12).
        assert (exists e, MapsToInBT l e t') as H by (apply ins; exists e; constructor). destruct H as [e' mt].
        rewrite findBT_1 with (e := e'); auto.
        apply andb_true_intro; split; [ apply andb_true_intro; split|].
        -- apply mts with (k := l); [constructor | auto].
        -- apply IHt11; auto. apply splitBTPreservesBST; auto. split; [intro k; split; intro H; destruct H as [e'' mt'] | intros k e'' e''' mt11 mt'].
           --- assert (exists e0, MapsToInBT k e0 t') as H by (apply ins; exists e''; constructor; auto; fail); destruct H as [e3 mt''].
               assert (k < l) as k_l by (apply forallLocationsInTree_1 with (P := fun l' => l' < l) in mt'; auto).
               exists e3; apply splitBT_2; auto.
           --- assert (MapsToInBT k e'' t') by (apply splitBT_1 with (l' := l); left; auto).
               assert (k < l) as k_l by (apply forallLocationsInTree_1 with (P := fun l' => l' < l) in mt'; auto; apply splitBTBounds; auto).
               assert (exists e0, MapsToInBT k e0 (Branch t11 l e t12)) as mt'' by (apply ins; exists e''; auto); destruct mt'' as [e4 mt''].
               inversion mt''; subst. exfalso; apply lt_irrefl with (x := l); auto. exists e4; auto. apply forallLocationsInTree_1 with (P := fun l' => l < l') in H3; auto.
               exfalso; apply lt_irrefl with (x := l); transitivity k; auto.
           --- apply mts with (k := k). constructor; auto; fail. apply splitBT_1 with (l' := l); left; auto.
        -- apply IHt12; auto. apply splitBTPreservesBST; auto. split; [intro k; split; intro H; destruct H as [e'' mt'] | intros k e'' e''' mt11 mt'].
           --- assert (exists e0, MapsToInBT k e0 t') as H by (apply ins; exists e''; constructor; auto; fail); destruct H as [e3 mt''].
               assert (l < k) as l_k by (apply forallLocationsInTree_1 with (P := fun l' => l < l') in mt'; auto).
               exists e3; apply splitBT_3; auto.
           --- assert (MapsToInBT k e'' t') by (apply splitBT_1 with (l' := l); right; auto).
               assert (l < k) as l_k by (apply forallLocationsInTree_1 with (P := fun l' => l < l') in mt'; auto; apply splitBTBounds; auto).
               assert (exists e0, MapsToInBT k e0 (Branch t11 l e t12)) as mt'' by (apply ins; exists e''; auto); destruct mt'' as [e4 mt''].
               inversion mt''; subst. exfalso; apply lt_irrefl with (x := l); auto. apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H3; auto.
               exfalso; apply lt_irrefl with (x := l); transitivity k; auto.  exists e4; auto. 
           --- apply mts with (k := k). constructor; auto; fail. apply splitBT_1 with (l' := l); right; auto.
    Qed.
      
    Theorem equal_2 : forall (m m' : t elt) (cmp : elt -> elt -> bool), equal cmp m m' = true -> Equivb cmp m m'.
    Proof using.
      intros m m' cmp; destruct m as [t BSTt]; destruct m' as [t' BSTt'].
      unfold equal; unfold Equivb; unfold Equiv; unfold In; unfold MapsTo; cbn.
      revert BSTt t' BSTt'. induction t as [| t11 IHt11 l e t12 IHt12]; cbn; intros BSTt t' BSTt' equal_m_m'.
      - destruct t'; [|inversion equal_m_m']; split. intro k; split; intro H; destruct H as [e mt]; inversion mt.
        intros k e e' mt1; inversion mt1.
      - destruct (findInBT l t') as [e0|] eqn:l_t'; [|inversion equal_m_m'].
        assert (MapsToInBT l e0 t') as mt by (apply findBT_2; auto).
        apply andb_prop in equal_m_m'; destruct equal_m_m' as [H equal_t12_t']; apply andb_prop in H; destruct H as [cmp_e_e0 equal_t11_t'].
        destruct BSTt as [t11_bdd H]; destruct H as [t12_bdd H]; destruct H as [BSTt11 BSTt12]; specialize (IHt11 BSTt11); specialize (IHt12 BSTt12).
        assert (isBST (fst (splitBT t' l))) as for_IHt11 by (apply splitBTPreservesBST; auto).
        assert (isBST (snd (splitBT t' l))) as for_IHt12 by (apply splitBTPreservesBST; auto).
        specialize (IHt11 (fst (splitBT t' l)) for_IHt11 equal_t11_t'); clear for_IHt11.
        specialize (IHt12 (snd (splitBT t' l)) for_IHt12 equal_t12_t'); clear for_IHt12.
        destruct IHt11 as [mts1 eq_cmp1]; destruct IHt12 as [mts2 eq_cmp2].
        split; [intro k; split; intro H; destruct H as [e1 mt'] | intros k e1 e' mt1 mt2].
        -- inversion mt'; subst. exists e0; auto.
           assert (exists e2, MapsToInBT k e2 (fst (splitBT t' l))) as H by (apply mts1; exists e1; auto); destruct H as [e2 mtt']; exists e2; apply splitBT_1 with (l' := l); left; auto.
           assert (exists e2, MapsToInBT k e2 (snd (splitBT t' l))) as H by (apply mts2; exists e1; auto); destruct H as [e2 mtt']; exists e2; apply splitBT_1 with (l' := l); right; auto.
        -- destruct (k ?= l) eqn:k_l.
           --- apply compare_Eq_to_eq in k_l; subst; exists e; constructor.
           --- apply compare_Lt_to_lt in k_l. apply splitBT_2 with (l' := l) in mt'; auto.
               assert (exists e2, MapsToInBT k e2 t11) as H by (apply mts1; exists e1; auto); destruct H as [e2 H]; exists e2; constructor; auto; fail.
           --- apply compare_Gt_to_gt in k_l. apply splitBT_3 with (l' := l) in mt'; auto.
               assert (exists e2, MapsToInBT k e2 t12) as H by (apply mts2; exists e1; auto); destruct H as [e2 H]; exists e2; constructor; auto; fail.
        -- inversion mt1; subst. apply MapsToInBTUnique with (e1 := e0) in mt2; subst; auto.
           apply eq_cmp1 with (k := k); auto. apply splitBT_2; auto. apply forallLocationsInTree_1 with (P := fun l' => l' < l) in H2; auto.
           apply eq_cmp2 with (k := k); auto. apply splitBT_3; auto. apply forallLocationsInTree_1 with (P := fun l' => l < l') in H2; auto.
    Qed.
  End equal.
  Arguments equalBT {elt}.
  Arguments equal {elt}.
                                               
  Section map2.
    Variable elt elt' elt'' : Set.
      
    Local Obligation Tactic := Coq.Program.Tactics.program_simpl; try lia.
    Equations mapBT2 (f : option elt -> option elt' -> option elt'') (t1 : BT elt) (t2 : BT elt') : BT elt'' by wf (cardinalOfBT t1 + cardinalOfBT t2) lt :=
      {
        mapBT2 f (EmptyBT _) t2 := pruneBT (mapBT (fun e => f None (Some e)) t2);
        mapBT2 f t1 (EmptyBT _) := pruneBT (mapBT (fun e => f (Some e) None) t1);
        mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) with (L.compare l1 l2) :=
          {
          mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Eq with (f (Some e1) (Some e2)) :=
            {
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Eq (Some e) := Branch (mapBT2 f t11 t21) l1 e (mapBT2 f t12 t22);
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Eq None := mergeBTs (mapBT2 f t11 t21) (mapBT2 f t12 t22)
            };
          mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Lt with (f (findInBT l2 t12) (Some e2)) :=
            {
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Lt (Some e) :=
              Branch (mapBT2 f (Branch t11 l1 e1 (fst (splitBT t12 l2))) t21) l2 e (mapBT2 f (snd (splitBT t12 l2)) t22);
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Lt None :=
              mergeBTs (mapBT2 f (Branch t11 l1 e1 (fst (splitBT t12 l2))) t21) (mapBT2 f (snd (splitBT t12 l2)) t22)
            };
          mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Gt with (f (Some e1) (findInBT l1 t22)) :=
            {
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Gt (Some e) :=
              Branch (mapBT2 f t11 (Branch t21 l2 e2 (fst (splitBT t22 l1)))) l1 e (mapBT2 f t12 (snd (splitBT t22 l1)));
            mapBT2 f (Branch t11 l1 e1 t12) (Branch t21 l2 e2 t22) Gt None :=
              mergeBTs (mapBT2 f t11 (Branch t21 l2 e2 (fst (splitBT t22 l1)))) (mapBT2 f t12 (snd (splitBT t22 l1)))
            }
          }
      }.
    Next Obligation.
      assert (le (cardinalOfBT (fst (splitBT t12 l2))) (cardinalOfBT t12)) by (apply splitBTCardinalLeft); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (snd (splitBT t12 l2))) (cardinalOfBT t12)) by (apply splitBTCardinalRight); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (fst (splitBT t12 l2))) (cardinalOfBT t12)) by (apply splitBTCardinalLeft); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (snd (splitBT t12 l2))) (cardinalOfBT t12)) by (apply splitBTCardinalRight); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (fst (splitBT t22 l1))) (cardinalOfBT t22)) by (apply splitBTCardinalLeft); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (snd (splitBT t22 l1))) (cardinalOfBT t22)) by (apply splitBTCardinalRight); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (fst (splitBT t22 l1))) (cardinalOfBT t22)) by (apply splitBTCardinalLeft); lia.
    Defined.
    Next Obligation.
      assert (le (cardinalOfBT (snd (splitBT t22 l1))) (cardinalOfBT t22)) by (apply splitBTCardinalRight); lia.
    Defined.

    Theorem mapBT2PreservesForalls : forall f t1 t2 P, forallLocationsInTree t1 P -> forallLocationsInTree t2 P -> forallLocationsInTree (mapBT2 f t1 t2) P.
    Proof using.
      intros f t1 t2 P fat1 fat2. funelim (mapBT2 f t1 t2); simp mapBT2.
      1,2: apply prunePreservesForalls; apply mapPreservesForalls; auto.
      all: rewrite Heq0; simp mapBT2; rewrite Heq; simp mapBT2; cbn.
      all: destruct fat1 as [Pt0 H']; destruct H' as [fatb fatb0].
      all: destruct fat2 as [Pt1 H']; destruct H' as [fatb1 fatb2].
      - split; [|split; [apply H | apply H0]]; auto.
      - apply mergeBTsPreserveLs; [apply H | apply H0]; auto.
      - split; [|split]; auto. apply H; auto. split; [|split]; auto; cbn; auto.
        apply splitBTPreservesForallsLeft; auto.
        apply H0; auto. apply splitBTPreservesForallsRight; auto.
      - apply mergeBTsPreserveLs. apply H; cbn; auto. split; [| split]; auto. apply splitBTPreservesForallsLeft; auto. apply H0; cbn; auto. apply splitBTPreservesForallsRight; auto.
      - split; [|split;[apply H | apply H0]]; auto.
        cbn; auto. split; [|split]; auto. apply splitBTPreservesForalls; auto. apply splitBTPreservesForalls; auto. 
      - apply mergeBTsPreserveLs. apply H; auto.
        cbn; auto; split; [| split]; auto. apply splitBTPreservesForalls; auto.
        apply H0; auto. apply splitBTPreservesForalls; auto.
    Qed.

    Theorem mapBT2PreservesBST : forall f t1 t2, isBST t1 -> isBST t2 -> isBST (mapBT2 f t1 t2).
    Proof using.
      intros f t1 t2 BSTt1 BSTt2. funelim (mapBT2 f t1 t2); simp mapBT2.
      1,2: apply pruneBTPreservesBST; apply mapBTPreservesBST; cbn; auto.
      all: rewrite Heq0; simp mapBT2; rewrite Heq; simp mapBT2; cbn.
      all: destruct BSTt1 as [b_bdd Ht1]; destruct Ht1 as [b0_bdd Ht1]; destruct Ht1 as [BSTb BSTb0].
      all: destruct BSTt2 as [b1_bdd Ht2]; destruct Ht2 as [b2_bdd Ht2]; destruct Ht2 as [BSTb1 BSTb2].
      - apply compare_Eq_to_eq in Heq0; subst. split; [|split;[|split]]; auto.
        apply mapBT2PreservesForalls; auto.
        apply mapBT2PreservesForalls; auto.
      - apply mergeBTsPreservesBST; [apply H | apply H0 | ]; auto.
        destruct (greatestLocation (mapBT2 f b b1)) as [gt1|] eqn:eq1 ; [right;exists gt1; split; auto | left; apply greatestLocation_None_Empty in eq1; auto].
        apply mapBT2PreservesForalls; auto.
        -- apply compare_Eq_to_eq in Heq0; subst.
           assert (forallLocationsInTree (mapBT2 f b b1) (fun l' => l' < t1)) by (apply mapBT2PreservesForalls; auto).
           apply greatestLocation_complete2 with (l1 := t1) in eq1; auto. apply ChangeOfProperty with (P := fun l' => t1 < l'); auto.
           intros l h; transitivity t1; auto.
        -- apply compare_Eq_to_eq in Heq0; subst.
           assert (forallLocationsInTree (mapBT2 f b b1) (fun l' => l' < t1)) by (apply mapBT2PreservesForalls; auto).
           apply greatestLocation_complete2 with (l1 := t1) in eq1; auto. apply ChangeOfProperty with (P := fun l' => t1 < l'); auto.
           intros l h; transitivity t1; auto.
      - apply compare_Lt_to_lt in Heq0; split; [|split; [|split]].
        -- apply mapBT2PreservesForalls; auto; cbn; split; [exact Heq0|split;[|apply splitBTBounds; auto]].
           apply ChangeOfProperty with (P := fun l' => l' < t0); auto; intros l l_t0; transitivity t0; auto.
        -- apply mapBT2PreservesForalls; auto. apply splitBTBounds; auto.
        -- apply H; auto; cbn; split; [|split; [|split]]; auto.
           apply splitBTPreservesForalls; auto.
           apply splitBTPreservesBST; auto.
        -- apply H0; auto; cbn. apply splitBTPreservesBST; auto.
      - apply compare_Lt_to_lt in Heq0; apply mergeBTsPreservesBST.
        -- apply H; auto; cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto.
        -- apply H0; auto; apply splitBTPreservesBST; auto.
        -- destruct (greatestLocation (mapBT2 f (Branch b t0 e (fst (splitBT b0 t1))) b1)) eqn:eq; [| apply greatestLocation_None_Empty in eq; left; exact eq].
           right; exists t2; split; [reflexivity|].
           apply greatestLocation_complete2 with (l1 := t1) in eq. apply mapBT2PreservesForalls; auto.
           apply ChangeOfProperty with (P := fun l' => t1 < l'); [apply splitBTBounds; auto | intros l h; transitivity t1; auto].
           apply ChangeOfProperty with (P := fun l' => t1 < l'); auto. intros l h. transitivity t1; auto. 
           apply mapBT2PreservesForalls; auto; cbn; split; [exact Heq0 | split].
           apply ChangeOfProperty with (P := fun l' => l' < t0); auto. intros l h; transitivity t0; auto.
           apply splitBTBounds; auto.
      - apply compare_Gt_to_gt in Heq0; split; [|split; [|split]].
        -- apply mapBT2PreservesForalls; auto. cbn; split; [|split]; auto.
           apply ChangeOfProperty with (P := fun l' => l' < t1); auto; intros l h; transitivity t1; auto.
           apply splitBTBounds; auto.
        -- apply mapBT2PreservesForalls; auto. apply splitBTBounds; auto.
        -- apply H; auto. cbn; split; [| split; [|split]]; auto.
           apply splitBTPreservesForalls; auto.
           apply splitBTPreservesBST; auto.
        -- apply H0; auto. apply splitBTPreservesBST; auto.
      - apply mergeBTsPreservesBST.
        apply H; auto; cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls; auto | apply splitBTPreservesBST; auto].
        apply H0; auto. apply splitBTPreservesBST; auto.
        destruct (greatestLocation (mapBT2 f b (Branch b1 t1 e0 (fst (splitBT b2 t0))))) as [gl|] eqn:eq; [right; exists gl; split; auto| apply greatestLocation_None_Empty in eq; left; auto].
        apply compare_Gt_to_gt in Heq0.
        apply greatestLocation_complete2 with (l1 := t0) in eq.
        apply mapBT2PreservesForalls.
        apply ChangeOfProperty with (P := fun l' => t0 < l'); auto; intros l h; transitivity t0; auto.
        apply ChangeOfProperty with (P := fun l' => t0 < l'); [ apply splitBTBounds;auto |intros l h; transitivity t0; auto].
        apply mapBT2PreservesForalls; auto. cbn; split; [|split]; auto. apply ChangeOfProperty with (P := fun l' => l' < t1); auto; intros l h; transitivity t1; auto.
        apply splitBTBounds; auto.
    Qed.
    
    Definition map2 : (option elt -> option elt' -> option elt'') -> t elt -> t elt' -> t elt'' :=
      fun f t1 t2 => {| U := mapBT2 f (U t1) (U t2); U_corr := mapBT2PreservesBST f (U t1) (U t2) (U_corr t1) (U_corr t2) |}.

    Theorem map2_1 : forall (m : t elt) (m' : t elt') (x : L.t) (f : option elt -> option elt' -> option elt''),
        In x m \/ In x m' -> find x (map2 f m m') = f (find x m) (find x m').
    Proof using.
      unfold map2; unfold In; unfold MapsTo; unfold find; intros m m'; destruct m as [t BSTt]; destruct m' as [t' BSTt']; cbn; intros l f H.
      funelim (mapBT2 f t t'); simp mapBT2.
      - cbn. destruct H as [H|H]; destruct H as [e mt]; [inversion mt|].
        assert (findInBT l t2 = Some e) as h by (apply findBT_1 in mt; auto). rewrite h.
        apply mapBT_1 with (f := fun e0 => f None (Some e0)) in mt.
        destruct (f None (Some e)). apply prune_1 in mt; auto. apply findBT_1 in mt; auto.
        apply pruneBTPreservesBST; apply mapBTPreservesBST; auto.
        apply prune_3 in mt; [|apply mapBTPreservesBST; auto].
        destruct (findInBT l (pruneBT (mapBT (fun e0 => f None (Some e0)) t2))) eqn:eq; auto.
        apply findBT_2 in eq. exfalso. apply mt. exists e0; auto.
      - remember (Branch b t0 e b0) as t1. cbn. destruct H as [H|H]; destruct H as [e' mt]; [|inversion mt].
        assert (findInBT l t1 = Some e') as h by (apply findBT_1 in mt; auto). rewrite h.
        apply mapBT_1 with (f := fun e0 => f (Some e0) None) in mt.
        destruct (f (Some e') None). apply prune_1 in mt; auto. apply findBT_1 in mt; auto. 
        apply pruneBTPreservesBST; apply mapBTPreservesBST; auto.
        apply prune_3 in mt; [|apply mapBTPreservesBST; auto].
        destruct (findInBT l (pruneBT (mapBT (fun e0 => f (Some e0) None) t1))) eqn:eq; auto.
        apply findBT_2 in eq. exfalso. apply mt. exists e0; auto.
      - rewrite Heq0; cbn. rewrite Heq; cbn.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        specialize (H BSTb BSTb1). specialize (H0 BSTb0 BSTb2).
        apply compare_Eq_to_eq in Heq0; subst.
        destruct (l ?= t1) eqn:l_t1; auto; [apply compare_Lt_to_lt in l_t1; apply H | apply compare_Gt_to_gt in l_t1; apply H0].
        destruct H1 as [H1 | H1]; destruct H1 as [e'' H1].
        inversion H1; subst; [exfalso; apply lt_irrefl with (x := t1); auto| left; exists e''; auto | ].
        apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto; exfalso; apply lt_irrefl with (x := t1); transitivity l; auto.
        inversion H1; subst; [exfalso; apply lt_irrefl with (x := t1); auto| right; exists e''; auto | ].
        apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto; exfalso; apply lt_irrefl with (x := t1); transitivity l; auto.
        destruct H1 as [H1 | H1]; destruct H1 as [e'' H1].
        inversion H1; subst; [exfalso; apply lt_irrefl with (x := t1); auto|  | left; exists e''; auto].
        apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto; exfalso; apply lt_irrefl with (x := t1); transitivity l; auto.
        inversion H1; subst; [exfalso; apply lt_irrefl with (x := t1); auto|  | right; exists e''; auto].
        apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto; exfalso; apply lt_irrefl with (x := t1); transitivity l; auto.
      - rewrite Heq0; cbn; rewrite Heq; cbn; apply compare_Eq_to_eq in Heq0; subst.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        specialize (H BSTb BSTb1). specialize (H0 BSTb0 BSTb2).
        destruct (l ?= t1) eqn:l_t1; auto.
        -- apply compare_Eq_to_eq in l_t1; subst. destruct (findInBT t1 (mergeBTs (mapBT2 f b b1) (mapBT2 f b0 b2))) eqn:eq.
           apply findBT_2 in eq. apply mergeBTs_2 in eq. destruct eq as [mt|mt].
           apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in mt; [exfalso; apply lt_irrefl with (x := t1); exact mt| apply mapBT2PreservesForalls; auto].
           apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in mt; [exfalso; apply lt_irrefl with (x := t1); exact mt| apply mapBT2PreservesForalls; auto].
           rewrite Heq; auto.
        -- destruct (findInBT l (mergeBTs (mapBT2 f b b1) (mapBT2 f b0 b2))) eqn:eq.
           apply findBT_2 in eq. apply mergeBTs_2 in eq. destruct eq as [mt|mt].
           --- apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto]. rewrite <- mt. apply H.
               apply compare_Lt_to_lt in l_t1.
               destruct H1 as [H1 | H1]; destruct H1 as [e'' H1]; [left | right]; exists e''.
               inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | auto |].
               apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto; exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
               inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | auto |].
               apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto; exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
           --- apply compare_Lt_to_lt in l_t1; apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in mt; [exfalso; apply lt_irrefl with (x := l); transitivity t1; auto|].
               apply mapBT2PreservesForalls; auto.
           --- rewrite <- H. destruct (findInBT l (mapBT2 f b b1)) eqn:eq'; [|auto]. apply findBT_2 in eq'.
               assert (MapsToInBT l e1 (mergeBTs (mapBT2 f b b1) (mapBT2 f b0 b2))) by (apply mergeBTs_1; left; auto).
               apply findBT_1 in H2; [etransitivity; [symmetry; exact eq | exact H2] | rewrite Heqcall; apply mapBT2PreservesBST; cbn; auto].
               destruct H1 as [H1 | H1]; destruct H1 as [e'' H1]; [left | right]; exists e''.
               apply compare_Lt_to_lt in l_t1. inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | auto |].
               apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto. exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
               apply compare_Lt_to_lt in l_t1. inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | auto |].
               apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H5; auto. exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
        -- destruct (findInBT l (mergeBTs (mapBT2 f b b1) (mapBT2 f b0 b2))) eqn:eq.
           apply findBT_2 in eq. apply mergeBTs_2 in eq. destruct eq as [mt|mt].
           --- apply compare_Gt_to_gt in l_t1; apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in mt; [exfalso; apply lt_irrefl with (x := l); transitivity t1; auto|].
               apply mapBT2PreservesForalls; auto.
           --- apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto]. rewrite <- mt. apply H0.
               apply compare_Gt_to_gt in l_t1.
               destruct H1 as [H1 | H1]; destruct H1 as [e'' H1]; [left | right]; exists e''.
               inversion H1; subst; [exfalso; eapply lt_irrefl; eauto |  | auto].
               apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto; exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
               inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | | auto].
               apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto; exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
           --- rewrite <- H0. destruct (findInBT l (mapBT2 f b0 b2)) eqn:eq'; [|auto]. apply findBT_2 in eq'.
               assert (MapsToInBT l e1 (mergeBTs (mapBT2 f b b1) (mapBT2 f b0 b2))) by (apply mergeBTs_1; right; auto).
               apply findBT_1 in H2; [etransitivity; [symmetry; exact eq | exact H2] | rewrite Heqcall; apply mapBT2PreservesBST; cbn; auto].
               destruct H1 as [H1 | H1]; destruct H1 as [e'' H1]; [left | right]; exists e''.
               apply compare_Gt_to_gt in l_t1. inversion H1; subst; [exfalso; eapply lt_irrefl; eauto | | auto].
               apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto. exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
               apply compare_Gt_to_gt in l_t1. inversion H1; subst; [exfalso; eapply lt_irrefl; eauto |  | auto].
               apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H5; auto. exfalso; apply lt_irrefl with (x := l); transitivity t1; auto.
      - rewrite Heq0; cbn; rewrite Heq; cbn. apply compare_Lt_to_lt in Heq0.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        assert (isBST (Branch b t0 e (fst (splitBT b0 t1)))) as for_H by (cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
          specialize (H for_H BSTb1); clear for_H.
        assert (isBST (snd (splitBT b0 t1))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 for_H0 BSTb2); clear for_H0.
        destruct (l ?= t1) eqn: l_t1.
        -- apply compare_Eq_to_eq in l_t1; subst;
             destruct (t1 ?= t0) eqn: l_t0; auto; 
               [apply compare_Eq_to_eq in l_t0; subst; exfalso; eapply lt_irrefl; eauto |  apply compare_Lt_to_lt in l_t0; exfalso; apply lt_irrefl with (x := t0); transitivity t1; auto].
        -- rewrite H; cbn.  destruct (l ?= t0) eqn:l_t0; auto; apply compare_Lt_to_lt in l_t1; rewrite find_splitBT_1; auto.
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt].
           inversion mt; subst; [left; exists e; constructor | left; exists e'; constructor; auto; fail | left; exists e'; apply MapsToRight; apply compare_Lt_to_lt in l_t1; apply splitBT_2; auto].
           inversion mt; subst;
             [apply compare_Lt_to_lt in l_t1; exfalso; apply lt_irrefl with (x := t1); auto | right; exists e'; auto |
              apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H4; auto; apply compare_Lt_to_lt in l_t1; exfalso; apply lt_irrefl with (x := l); transitivity t1; auto].
        -- rewrite H0; cbn. destruct (l ?= t0) eqn:l_t0; auto; apply compare_Gt_to_gt in l_t1; rewrite find_splitBT_2; auto.
           apply compare_Eq_to_eq in l_t0; subst; exfalso; apply lt_irrefl with (x := t0); transitivity t1; auto.
           apply compare_Lt_to_lt in l_t0. exfalso; apply lt_irrefl with (x := t1); transitivity t0; auto; transitivity l; auto.
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst.
           --- apply compare_Gt_to_gt in l_t1; exfalso; apply lt_irrefl with (x := t0); transitivity t1; auto.
           --- apply forallLocationsInTree_1 with (P := fun l' => l' < t0) in H4; auto. apply compare_Gt_to_gt in l_t1.
               exfalso; apply lt_irrefl with (x := l); transitivity t0; auto; transitivity t1; auto.
           --- apply compare_Gt_to_gt in l_t1. left; exists e'; apply splitBT_3; auto.
           --- apply compare_Gt_to_gt in l_t1; exfalso; apply lt_irrefl with (x := t1); auto.
           --- apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H4; auto; apply compare_Gt_to_gt in l_t1; exfalso; apply lt_irrefl with (x := t1); transitivity l; auto.
           --- right; exists e'; auto.
      - rewrite Heq0; cbn; rewrite Heq; cbn. apply compare_Lt_to_lt in Heq0.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        assert (isBST (Branch b t0 e (fst (splitBT b0 t1)))) as for_H by (cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
          specialize (H for_H BSTb1); clear for_H.
        assert (isBST (snd (splitBT b0 t1))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 for_H0 BSTb2); clear for_H0.
        destruct (findInBT l (mergeBTs (mapBT2 f (Branch b t0 e (fst (splitBT b0 t1))) b1) (mapBT2 f (snd (splitBT b0 t1)) b2))) eqn:eq.
        2: {
          apply findBT_mergeBT_None in eq; destruct eq as [eq1 eq2].
          Ltac after_destruct :=           repeat match goal with
                                                  | [ H : ?l < ?l |- _ ] => exfalso; apply lt_irrefl with (x := l); exact H
                                                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l1 |- _ ] => exfalso; apply lt_irrefl with (x := l1); transitivity l2; [exact H1 | exact H2] 
                                                  | [ H1 : ?l1 < ?l2, H2 : ?l2 < ?l3, H3 : ?l3 < ?l1 |- _ ] => exfalso; apply lt_irrefl with (x := l1); transitivity l2; [exact H1 | transitivity l3; [exact H2 | exact H3]] 
                                                  | [ H : (?l ?= ?l') = Eq |- _ ] => apply compare_Eq_to_eq in H; subst
                                                  | [ H : (?l ?= ?l') = Lt |- _ ] => apply compare_Lt_to_lt in H
                                                  | [ H : (?l ?= ?l') = Gt |- _ ] => apply compare_Gt_to_gt in H
                                                  end; auto. 
          destruct (l ?= t1) eqn: l_t1; destruct (l ?= t0) eqn:l_t0; after_destruct.
          - rewrite H in eq1; cbn in eq1. destruct (t0 ?= t0) eqn:t0_t0; after_destruct. left; exists e; constructor.
          - rewrite H in eq1; cbn in eq1. destruct (l ?= t0) eqn:l_t0'; after_destruct.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- left; exists e'; constructor; auto; fail.
            -- left; exists e'; apply MapsToRight. apply splitBT_2; auto.
            -- right; exists e'; auto.
            -- apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H4; auto; after_destruct.
          - rewrite H in eq1. cbn in eq1. destruct (l ?= t0) eqn:eq5; after_destruct; clear eq5.
            rewrite find_splitBT_1 in eq1; auto.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- left; exists e'; constructor; auto; fail.
            -- left; exists e'; apply MapsToRight. apply splitBT_2; auto.
            -- right; exists e'; auto.
            -- apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H4; auto; after_destruct.
          - rewrite H0 in eq2; cbn in eq2. rewrite find_splitBT_2 in eq2; auto.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H4; auto; after_destruct.
               apply ChangeOfProperty with (P := fun l' => l' < t0); auto; intros l0 h; transitivity t0; auto.
            -- left; exists e'. apply splitBT_3; auto.
            -- apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in H4; auto; after_destruct.
            -- right; exists e'; auto.
          - apply mergeBTsPreservesBST. apply mapBT2PreservesBST; auto. cbn; split; [|split; [|split]]; auto.
            apply splitBTPreservesForalls; auto.
            apply splitBTPreservesBST; auto.
            apply mapBT2PreservesBST; auto.
            apply splitBTPreservesBST; auto.
            destruct (greatestLocation (mapBT2 f (Branch b t0 e (fst (splitBT b0 t1))) b1)) eqn:gl; [right | left; apply greatestLocation_None_Empty in gl; auto].
            exists t2; split; auto.
            apply greatestLocation_complete2 with (l1 := t1) in gl. apply mapBT2PreservesForalls; auto.
            apply ChangeOfProperty with (P := fun l' => t1 < l'); auto. apply splitBTBounds; auto. intros l0 h; transitivity t1; auto.
            apply ChangeOfProperty with (P := fun l' => t1 < l'); auto. intros l0 h; transitivity t1; auto.
            apply mapBT2PreservesForalls; auto. cbn; split; [|split]; auto. 
            apply ChangeOfProperty with (P := fun l' => l' < t0); auto. intros l0 h; transitivity t0; auto.
            apply splitBTBounds; auto.
        }
        apply findBT_2 in eq. apply mergeBTs_2 in eq.
        destruct eq as [mt | mt].
        -- apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto; cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto]. 
           rewrite <- mt. rewrite H.
           destruct (l ?= t0) eqn:l_t0; destruct (l ?= t1) eqn:l_t1; after_destruct; cbn; auto.
           destruct (t0 ?= t0) eqn:t0_t0; after_destruct.
           1,3,4: destruct (l ?= t0) eqn:l_t0'; after_destruct.
           3: destruct (t1 ?= t0) eqn:t1_t0; after_destruct.
           rewrite find_splitBT_1; auto.
           1,2: apply findBT_2 in mt; apply forallLocationsInTree_1 with (P := fun l => l < t1) in mt; after_destruct;
             apply mapBT2PreservesForalls; auto; cbn; split; [|split]; auto;
               [apply ChangeOfProperty with (P := fun l' => l' < t0); auto; intros l0 h; transitivity t0; auto
               |apply splitBTBounds; auto].
           apply findBT_2 in mt.
           apply forallLocationsInTree_1 with (P := fun l' => l' < t1) in mt .
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt']; inversion mt'; subst.
           --- left; exists e; constructor.
           --- left; exists e'; constructor; auto; fail.
           --- left; exists e'; apply MapsToRight. apply splitBT_2; auto.
           --- exfalso; apply lt_irrefl with (x := t1); auto.
           --- right; exists e'; auto.
           --- apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in H4; auto; after_destruct.
           --- apply mapBT2PreservesForalls; auto. cbn; split; [|split]; auto.
               apply ChangeOfProperty with (P := fun l' => l' < t0); auto. intros l0 h; transitivity t0; auto.
               apply splitBTBounds; auto.
        -- assert (t1 < l). apply forallLocationsInTree_1 with (P := fun l' => t1 < l') in mt; auto.
           apply mapBT2PreservesForalls; auto. apply splitBTBounds; auto.
           apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto; apply splitBTPreservesBST; auto].
           rewrite <- mt. rewrite H0.
           destruct (l ?= t0) eqn:l_t0; destruct (l ?= t1) eqn:l_t1; after_destruct; cbn; auto.
           rewrite find_splitBT_2; auto.
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt']; inversion mt'; subst; after_destruct.
           --- apply forallLocationsInTree_1 with (P := fun l => l < t0) in H5; after_destruct.
           --- left; exists e'; apply splitBT_3; auto.
           --- apply forallLocationsInTree_1 with (P := fun l => l < t1) in H5; auto; after_destruct.
           --- right; exists e'; auto.
      - rewrite Heq0; cbn; rewrite Heq; cbn. apply compare_Gt_to_gt in Heq0.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        assert (isBST (Branch b1 t1 e0 (fst (splitBT b2 t0)))) as for_H by (cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
          specialize (H BSTb for_H); clear for_H.
        assert (isBST (snd (splitBT b2 t0))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 BSTb0 for_H0); clear for_H0.
        destruct (l ?= t1) eqn: l_t1; after_destruct.
        -- destruct (t1 ?= t0) eqn: l_t0; after_destruct.
           rewrite H; cbn. destruct (t1 ?= t1) eqn:obv; after_destruct. right; exists e0; constructor.
        -- rewrite H; cbn.  destruct (l ?= t0) eqn:l_t0; after_destruct.
           destruct (l ?= t1) eqn:l_t1'; after_destruct.
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt].
           inversion mt; subst; after_destruct; [left; exists e'; auto | apply forallLocationsInTree_1 with (P := fun l => t0 < l) in H4; auto; after_destruct].
           inversion mt; subst; after_destruct; right. exists e'; constructor; auto; fail. exists e'; apply MapsToRight. apply splitBT_2; auto.
           apply forallLocationsInTree_1 with (P := fun l => t1 < l) in H4; after_destruct.
        -- destruct (l ?= t0) eqn:l_t0; after_destruct. 
           --- rewrite H; cbn. destruct (l ?= t1) eqn:l_t1'; after_destruct; rewrite find_splitBT_1; auto.
               destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
               left; exists e'; auto. apply forallLocationsInTree_1 with (P := fun l => t0 < l) in H4; after_destruct.
               right; exists e'; constructor; auto; fail. right; exists e'; apply MapsToRight; apply splitBT_2; auto.
           --- rewrite H0; cbn. rewrite find_splitBT_2; auto.
               destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
               apply forallLocationsInTree_1 with (P := fun l => l < t0)in H4; after_destruct. left; exists e'; auto.
               apply forallLocationsInTree_1 with (P := fun l => l < t1) in H4; after_destruct. right; exists e'; apply splitBT_3; auto.
      - rewrite Heq0; cbn; rewrite Heq; cbn. apply compare_Gt_to_gt in Heq0.
        destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
        destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
        assert (isBST (Branch b1 t1 e0 (fst (splitBT b2 t0)))) as for_H by (cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
          specialize (H BSTb for_H); clear for_H.
        assert (isBST (snd (splitBT b2 t0))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 BSTb0 for_H0); clear for_H0.
        destruct (findInBT l (mergeBTs (mapBT2 f  b (Branch b1 t1 e0 (fst (splitBT b2 t0)))) (mapBT2 f b0 (snd (splitBT b2 t0))))) eqn:eq.
        2: {
          apply findBT_mergeBT_None in eq; destruct eq as [eq1 eq2].
          destruct (l ?= t1) eqn: l_t1; destruct (l ?= t0) eqn:l_t0; after_destruct.
          - rewrite H in eq1; cbn in eq1. destruct (t1 ?= t1) eqn:t1_t1; after_destruct. right; exists e0; constructor.
          - rewrite H in eq1; cbn in eq1. destruct (l ?= t1) eqn:l_t1'; after_destruct.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- left; exists e'; auto.
            -- apply forallLocationsInTree_1 with (P := fun l => t0 < l) in H4; after_destruct.
            -- right; exists e'; constructor; auto; fail.
            -- right; exists e'; apply MapsToRight; apply splitBT_2; auto.
          - rewrite H in eq1; cbn in eq1. destruct (l ?= t1) eqn:eq5; after_destruct; clear eq5.
            rewrite find_splitBT_1 in eq1; auto.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- left; exists e'; auto.
            -- apply forallLocationsInTree_1 with (P := fun l => t0 < l) in H4; after_destruct.
            -- right; exists e'; constructor; auto; fail.
            -- right; exists e'; apply MapsToRight; apply splitBT_2; auto.
          - rewrite H0 in eq2; cbn in eq2. rewrite find_splitBT_2 in eq2; auto.
            destruct H1 as [H1 | H1]; destruct H1 as [e' mt]; inversion mt; subst; after_destruct.
            -- apply forallLocationsInTree_1 with (P := fun l => l < t0) in H4; after_destruct.
            -- left; exists e'; auto.
            -- apply forallLocationsInTree_1 with (P := fun l => l < t1) in H4; after_destruct.
            -- right; exists e'; apply splitBT_3; auto.
          - apply mergeBTsPreservesBST. apply mapBT2PreservesBST; auto. cbn; split; [|split; [|split]]; auto.
            apply splitBTPreservesForalls; auto.
            apply splitBTPreservesBST; auto.
            apply mapBT2PreservesBST; auto.
            apply splitBTPreservesBST; auto.
            destruct (greatestLocation (mapBT2 f  b (Branch b1 t1 e0 (fst (splitBT b2 t0))))) eqn:gl; [right | left; apply greatestLocation_None_Empty in gl; auto].
            exists t2; split; auto.
            apply greatestLocation_complete2 with (l1 := t0) in gl. apply mapBT2PreservesForalls; auto.
            apply ChangeOfProperty with (P := fun l' => t0 < l'); auto. intros l0 h; transitivity t0; auto.
            apply ChangeOfProperty with (P := fun l' => t0 < l'); auto. apply splitBTBounds; auto. intros l0 h; transitivity t0; auto.
            apply mapBT2PreservesForalls; auto. cbn; split; [|split]; auto. 
            apply ChangeOfProperty with (P := fun l' => l' < t1); auto. intros l0 h; transitivity t1; auto.
            apply splitBTBounds; auto.
        }
        apply findBT_2 in eq; apply mergeBTs_2 in eq; destruct eq as [mt | mt].
        -- assert (l < t0) as l_t0
              by (apply forallLocationsInTree_1 with (P := fun l => l < t0) in mt; after_destruct; 
                  apply mapBT2PreservesForalls; auto; cbn; split; [|split]; auto;
                  [apply ChangeOfProperty with (P := fun l => l < t1); auto; intros l0 h; transitivity t1; auto
                  |apply splitBTBounds; auto]).
           apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto; cbn; split; [|split;[|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto]. 
           rewrite <- mt; rewrite H.
           destruct (l ?= t0) eqn:l_t0'; after_destruct; cbn; destruct (l ?= t1) eqn:l_t1; after_destruct; cbn; rewrite find_splitBT_1; auto.
           destruct H1 as [H1 | H1]; destruct H1 as [e' mt']; inversion mt'; subst; after_destruct.
           --- left; exists e'; auto.
           --- apply forallLocationsInTree_1 with (P := fun l => t0 < l) in H4; after_destruct.
           --- right; exists e0; constructor.
           --- right; exists e'; constructor; auto; fail.
           --- right; exists e'; apply MapsToRight; apply splitBT_2; auto.
        -- (* Note: I should go back and re-write the other branches with this idea *)
          assert (t0 < l) as t1_l
              by (apply forallLocationsInTree_1 with (P := fun l' => t0 < l') in mt; auto;
                  apply mapBT2PreservesForalls; auto; apply splitBTBounds; auto).
          assert (t1 < l) by (transitivity t0; auto).
          apply findBT_1 in mt; [|apply mapBT2PreservesBST; auto; apply splitBTPreservesBST; auto].
          rewrite <- mt. rewrite H0.
          destruct (l ?= t1) eqn:l_t1; after_destruct. destruct (l ?= t0) eqn:l_t0; after_destruct; cbn; auto.
          rewrite find_splitBT_2; after_destruct.
          destruct H1 as [H1 | H1]; destruct H1 as [e' mt']; inversion mt'; subst; after_destruct.
          --- apply forallLocationsInTree_1 with (P := fun l => l < t0) in H5; after_destruct.
          --- left; exists e'; auto.
          --- apply forallLocationsInTree_1 with (P := fun l => l < t1) in H5; auto; after_destruct.
          --- right; exists e'; apply splitBT_3; auto.
    Qed.

    Theorem map2_2 : forall (m : t elt) (m' : t elt') (x : L.t) (f : option elt -> option elt' -> option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
    Proof using.
      unfold map2; unfold In; unfold MapsTo; unfold find; intros m m'; destruct m as [t BSTt]; destruct m' as [t' BSTt']; cbn; intros l f i.
      funelim (mapBT2 f t t'); simp mapBT2 in i.
      3,4,5,6,7,8: destruct BSTt as [b_bdd h]; destruct h as [b0_bdd h]; destruct h as [BSTb BSTb0].
      3,4,5,6,7,8: destruct BSTt' as [b1_bdd h]; destruct h as [b2_bdd h]; destruct h as [BSTb1 BSTb2].
      - destruct i as [e mt]. apply prune_2 in mt; [|apply mapBTPreservesBST; auto]. Check mapBT_2.
        right. apply mapBT_2 with (elt' := option elt'') (f := fun e => f None (Some e)); exists (Some e); auto.
      - remember (Branch b t0 e b0) as t. destruct i as [e' mt]. apply prune_2 in mt; [|apply mapBTPreservesBST; auto].
        left. apply mapBT_2 with (elt' := option elt'') (f := fun e : elt => f (Some e) None); exists (Some e'); auto.
      - specialize (H BSTb BSTb1); specialize (H0 BSTb0 BSTb2).
        rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
        apply compare_Eq_to_eq in Heq0; subst.
        destruct i as [e' mt].
        inversion mt; subst.
        -- left; exists e; constructor; auto; fail.
        -- destruct (H l (ex_intro _ e' H4)) as [H5 | H5]; destruct H5 as [e'' mt']; [left | right]; exists e''; constructor; auto; fail.
        -- destruct (H0 l (ex_intro _ e' H4)) as [H5 | H5]; destruct H5 as [e'' mt']; [left | right]; exists e''; constructor; auto; fail.
      - specialize (H BSTb BSTb1); specialize (H0 BSTb0 BSTb2).
        rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
        apply compare_Eq_to_eq in Heq0; subst.
        destruct i as [e' mt]; apply mergeBTs_2 in mt.
        destruct mt as [mt1 | mt2]; [destruct (H l (ex_intro _ e' mt1)) as [H5 | H5] | destruct (H0 l (ex_intro _ e' mt2)) as [H5 | H5]]; destruct H5 as [e'' mt].
        1,3: left.
        3,4: right.
        all: exists e''; constructor; auto; fail.
               - assert (isBST (Branch b t0 e (fst (splitBT b0 t1)))) as for_H by (cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
                   specialize (H for_H BSTb1); clear for_H.
                 assert (isBST (snd (splitBT b0 t1))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 for_H0 BSTb2); clear for_H0.
                 rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
                 apply compare_Lt_to_lt in Heq0.
                 destruct i as [e' mt]; inversion mt; subst; [right; exists e0; constructor| |].
                 destruct (H l (ex_intro _ e' H4)) as [H5 | H5].
                 3: destruct (H0 l (ex_intro _ e' H4)) as [H5 | H5].
                 all: destruct H5 as [e'' mt'].
                 all: try (left; exists e''; constructor; auto; fail); try (right; exists e''; constructor; auto; fail).
                 all: inversion mt'; subst; auto; try (left; exists e''; constructor; auto; fail); try (right; exists e''; constructor; auto; fail).
                 left; exists e; constructor.
                 all: try (apply splitBT_11 in H5; left; exists e''; constructor; auto; fail).
                 all: try (apply splitBT_12 in mt'; left; exists e''; constructor; auto; fail).
               - assert (isBST (Branch b t0 e (fst (splitBT b0 t1)))) as for_H by (cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
                   specialize (H for_H BSTb1); clear for_H.
                 assert (isBST (snd (splitBT b0 t1))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 for_H0 BSTb2); clear for_H0.
                 rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
                 apply compare_Lt_to_lt in Heq0.
                 destruct i as [e' mt]; apply mergeBTs_2 in mt; destruct mt as [mt | mt];
                   [specialize (H l (ex_intro _ e' mt)); destruct H as [i | i] | specialize (H0 l (ex_intro _ e' mt)); destruct H0 as [i | i]]; destruct i as [e'' mt'].
                 -- inversion mt'; subst; [left; exists e; constructor | | apply splitBT_11 in H3]; left; exists e''; constructor; auto; fail.
                 -- right; exists e''; constructor; auto; fail.
                 -- apply splitBT_12 in mt'; left; exists e''; constructor; auto; fail.
                 -- right; exists e''; constructor; auto; fail.
               - assert (isBST (Branch b1 t1 e0 (fst (splitBT b2 t0)))) as for_H by (cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
                   specialize (H BSTb for_H); clear for_H.
                 assert (isBST (snd (splitBT b2 t0))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 BSTb0 for_H0); clear for_H0.
                 rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
                 apply compare_Gt_to_gt in Heq0.
                 destruct i as [e' mt]; inversion mt; subst; [left; exists e; constructor| |].
                 destruct (H l (ex_intro _ e' H4)) as [H5 | H5].
                 3: destruct (H0 l (ex_intro _ e' H4)) as [H5 | H5].
                 all: destruct H5 as [e'' mt'].
                 all: try (left; exists e''; constructor; auto; fail); try (right; exists e''; constructor; auto; fail).
                 all: inversion mt'; subst; auto; try (left; exists e''; constructor; auto; fail); try (right; exists e''; constructor; auto; fail).
                 right; exists e0; constructor.
                 all: try (apply splitBT_11 in H5; right; exists e''; constructor; auto; fail).
                 all: try (apply splitBT_12 in mt'; right; exists e''; constructor; auto; fail).
               - assert (isBST (Branch b1 t1 e0 (fst (splitBT b2 t0)))) as for_H by (cbn; split; [|split; [|split]]; auto; [apply splitBTPreservesForalls | apply splitBTPreservesBST]; auto);
                   specialize (H BSTb for_H); clear for_H.
                 assert (isBST (snd (splitBT b2 t0))) as for_H0 by (apply splitBTPreservesBST; auto); specialize (H0 BSTb0 for_H0); clear for_H0.
                 rewrite Heq0 in i; cbn in i; rewrite Heq in i; cbn in i.
                 apply compare_Gt_to_gt in Heq0.
                 destruct i as [e' mt]; apply mergeBTs_2 in mt; destruct mt as [mt | mt];
                   [specialize (H l (ex_intro _ e' mt)); destruct H as [i | i] | specialize (H0 l (ex_intro _ e' mt)); destruct H0 as [i | i]]; destruct i as [e'' mt'].
                 -- left; exists e''; constructor; auto; fail.
                 -- inversion mt'; subst; [right; exists e0; constructor | | apply splitBT_11 in H3]; right; exists e''; constructor; auto; fail. 
                 -- left; exists e''; constructor; auto; fail.
                 -- apply splitBT_12 in mt'; right; exists e''; constructor; auto; fail.
    Qed.
  End map2.
  Arguments mapBT2 {elt} {elt'}.
  Arguments map2 {elt} {elt'}.
End TreeLMap.

