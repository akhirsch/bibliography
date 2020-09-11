Require Export Locations.

Require Import Coq.Structures.Orders Coq.Structures.Equalities.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.SetoidList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Program.Wf.
From Equations Require Import Equations.
Require Import Psatz.

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
  Arguments empty {elt}.

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

Module LocationMapFacts (L : Locations) (LM : LocationMap L).
  Lemma MapsToUnique : forall {elt : Set} {m : LM.t elt} {l : L.t} {e1 e2 : elt}, LM.MapsTo l e1 m -> LM.MapsTo l e2 m -> e1 = e2.
  Proof using.
    intros elt m l e1 e2 mt1 mt2; apply LM.find_1 in mt1; apply LM.find_1 in mt2; rewrite mt1 in mt2; inversion mt2; reflexivity.
  Qed.
  Lemma MapsTo2In : forall {elt : Set} {m : LM.t elt} {l : L.t} {e : elt}, LM.MapsTo l e m -> LM.In l m.
  Proof using.
    intros elt m l e mt; exists e; exact mt.
  Qed.
  Lemma find_None : forall {elt : Set} {m : LM.t elt} {l : L.t}, LM.find l m = None -> forall (e : elt), ~ LM.MapsTo l e m.
  Proof using.
    intros elt m l eq e mt; apply LM.find_1 in mt; rewrite mt in eq; inversion eq.
  Qed.

  Lemma find_add_1 : forall {elt : Set} (m : LM.t elt) (l : L.t) (e : elt), LM.find l (LM.add l e m) = Some e.
  Proof using.
    intros elt m l e. apply LM.find_1. apply LM.add_1.
  Qed.

  Lemma find_add_2 : forall {elt : Set} (m : LM.t elt) (l l' : L.t) (e : elt), l <> l' -> LM.find l (LM.add l' e m) = LM.find l m.
  Proof using.
    intros elt m l l' e H. destruct (LM.find l (LM.add l' e m)) eqn:eq. apply LM.find_2 in eq. apply LM.add_3 in eq; auto. apply LM.find_1 in eq; auto.
    destruct (LM.find l m) eqn:eq'; auto. apply LM.find_2 in eq'. apply (LM.add_2 e (fun e => H (eq_sym e))) in eq'. apply LM.find_1 in eq'.
    transitivity (LM.find l (LM.add l' e m)); auto.
  Qed.

  Lemma find_remove_1 : forall {elt : Set} (m : LM.t elt) (l : L.t), LM.find l (LM.remove l m) = None.
  Proof using.
    intros elt m l; destruct (LM.find l (LM.remove l m)) eqn:eq; [|reflexivity].
    apply LM.find_2 in eq. destruct (LM.remove_1 (ex_intro _ e eq)).
  Qed.
  Lemma find_remove_2 : forall {elt : Set} (m : LM.t elt) (l l' : L.t), l <> l' -> LM.find l (LM.remove l' m) = LM.find l m.
  Proof using.
    intros elt m l l' neq; destruct (LM.find l (LM.remove l' m)) eqn:eq.
    apply LM.find_2 in eq; apply LM.remove_3 in eq; auto; apply LM.find_1 in eq; auto.
    destruct (LM.find l m) eqn:eq'; [|reflexivity]. apply LM.find_2 in eq'. apply LM.remove_2 with (x := l') in eq'; auto.
    apply LM.find_1 in eq'; rewrite eq' in eq; inversion eq.
  Qed.

  Lemma map2_3 : forall {elt1 elt2 elt3 : Set} {f : option elt1 -> option elt2 -> option elt3} {m1 : LM.t elt1} {m2 : LM.t elt2} {l : L.t},
      LM.find l m1 = None -> LM.find l m2 = None -> LM.find l (LM.map2 f m1 m2) = None.
  Proof using.
    intros elt1 elt2 elt3 f m1 m2 l H H0.
    destruct (LM.find l (LM.map2 f m1 m2)) eqn:eq; auto.
    assert (LM.In l (LM.map2 f m1 m2)) as i by (apply LM.find_2 in eq; exists e; auto).
    apply LM.map2_2 in i; destruct i as [i|i]; destruct i as [n mt]; apply LM.find_1 in mt; exfalso; [rewrite mt in H; inversion H | rewrite mt in H0; inversion H0].
  Qed.
  Instance lm_Equal_refl : forall {elt : Set}, Reflexive (@LM.Equal elt).
  Proof using.
    intros elt. unfold Reflexive; intro m; unfold LM.Equal; intro y; reflexivity.
  Qed.
  Instance lm_Equal_sym : forall {elt : Set}, Symmetric (@LM.Equal elt).
  Proof using.
    intros elt; unfold Symmetric; intros m1 m2; unfold LM.Equal; intros H l; symmetry; apply H.
  Qed.
  Instance lm_Equal_trans : forall {elt : Set}, Transitive (@LM.Equal elt).
  Proof using.
    intros elt; unfold Transitive; intros m1 m2 m3; unfold LM.Equal; intros H1 H2 l;
      transitivity (LM.find l m2); auto.
  Qed.
  Lemma elements_1a : forall {elt : Set} (l : L.t) (e : elt) (m : LM.t elt), LM.MapsTo l e m -> In (l, e) (LM.elements m).
  Proof using.
    intros elt l e m mt. apply LM.elements_1 in mt. induction (LM.elements m). inversion mt.
    inversion mt; subst.
    destruct a. inversion H0. cbn in H; cbn in H1; subst; left; auto.
    right; apply IHl0; auto.
  Qed.

End LocationMapFacts.

  

