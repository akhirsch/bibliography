Require Export PiCalc.
Require Export LocationMap.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Program.Wf.
Require Import Coq.Lists.SetoidList.
Require Import Psatz.

(* Require Import Coq.Sorting.Sorted. *)

From Equations Require Import Equations.

Module IChoiceTree (E : Expression) (L : Locations) (LM : LocationMap L) (LS : LocationSorter L).

  Import E.
  Module LF := (LocationFacts L).
  Import LF.
  Module Pi := (PiCalc E L).
  Import Pi.
  Module LMF := (LocationMapFacts L LM).

Definition BothIChoice {A : Type} (P Q : Proc) (default : A) (f : L.t -> Proc -> Proc -> L.t -> Proc -> Proc -> A)  : A :=
    match P with
    | IChoice p P1 P2 =>
      match Q with
      | IChoice q Q1 Q2 => f p P1 P2 q Q1 Q2
      | _ => default
      end
    | _ => default
    end.
  Arguments BothIChoice : simpl nomatch.

  Inductive Action : Set :=
    EndAct : Action
  | UnknownAct : Action
  | VarAct : nat -> Action
  | DefAct : Proc -> Action
  | SendAct : L.t -> Expr -> Action
  | RecvAct : L.t -> Action
  | EChoiceLAct : L.t -> Action
  | EChoiceRAct : L.t -> Action
  | IChoiceAct : L.t -> Action
  | IfThenElseAct : Expr -> Action.

  Definition ActionEqDec : forall A1 A2 : Action, {A1 = A2} + {A1 <> A2}.
    decide equality; try (apply L.eq_dec); try (apply ProcEqDec); try (apply ExprEqDec); apply PeanoNat.Nat.eq_dec.
  Defined.

  (* Definiting this via Equations gives us access to the graph automatically. *)
  Equations ActionOf (P : Proc) : Action :=
    {
      ActionOf EndProc := EndAct;
      ActionOf (VarProc n) := VarAct n;
      ActionOf (DefProc P Q) := DefAct P;
      ActionOf (SendProc p e P) := SendAct p e;
      ActionOf (RecvProc p P) := RecvAct p;
      ActionOf (EChoiceL p P) := EChoiceLAct p;
      ActionOf (EChoiceR p P) := EChoiceRAct p;
      ActionOf (IChoice p P Q) := IChoiceAct p;
      ActionOf (IfThenElse e P Q) := IfThenElseAct e
    }.

  (*
    Things got really complicated when using the correct-by-construction type I had for different ICTrees before.
    So, I'm doing more idiomatic Coq and defining a "IsDifferentICTree" proposition.
    I'm then going to need functions to put an ICTree in order, etc.
   *)
  Inductive IChoiceTree : Set :=
    ICTLeaf : L.t -> Proc -> Proc -> IChoiceTree
  | ICTBranch : L.t -> IChoiceTree -> IChoiceTree -> IChoiceTree.

  Ltac ICTInduction t :=
    let l := fresh "l" in
    let P := fresh "P" in
    let Q := fresh "Q" in
    let t1 := fresh "t" in
    let t2 := fresh "t" in
    let IHt1 := fresh "IH" t1 in
    let IHt2 := fresh "IH" t2 in
    induction t as [l P Q | l t1 IHt1 t2 IHt2].
  Ltac ICTDestruct t :=
    let l := fresh "l" in
    let P := fresh "P" in
    let Q := fresh "Q" in
    let t1 := fresh "t" in
    let t2 := fresh "t" in
    destruct t as [l P Q | l t1 t2].
  
  Fixpoint IChoiceTreeToProc (t : IChoiceTree) : Proc :=
    match t with
    | ICTLeaf p P Q => IChoice p P Q
    | ICTBranch p l r => IChoice p (IChoiceTreeToProc l) (IChoiceTreeToProc r)
    end.
  
  Definition FirstDecider (t : IChoiceTree) : L.t :=
    match t with
    | ICTLeaf p _ _ => p
    | ICTBranch p _ _ => p
    end.

  Inductive IsOrderedICTree : IChoiceTree -> Prop :=
    IsOrderedLeaf : forall p P Q, IsOrderedICTree (ICTLeaf p P Q)
  | IsOrderedBranch : forall p t1 t2, (FirstDecider t1) <= p -> (FirstDecider t2) <= p -> IsOrderedICTree t1 -> IsOrderedICTree t2 -> IsOrderedICTree (ICTBranch p t1 t2).

  Program Fixpoint CheckOrderedICTree (t : IChoiceTree) : {IsOrderedICTree t} + {~ IsOrderedICTree t} :=
    match t with
    | ICTLeaf p P Q => left (IsOrderedLeaf p P Q)
    | ICTBranch p t1 t2 =>
      match L.compare (FirstDecider t1) p with
      | Gt => right _
      | _ => match L.compare (FirstDecider t2) p with
            | Gt => right _
            | _ =>  match CheckOrderedICTree t1 with
                   | left ord1 =>
                     match CheckOrderedICTree t2 with
                     | left ord2 => left (IsOrderedBranch p t1 t2 _ _ ord1 ord2)
                     | right n => right _
                     end
                   | right n => right _
                   end
            end
      end
    end.
  Next Obligation.
    inversion H; subst; LocationOrder.
  Defined.
  Next Obligation.
    inversion H0; subst; remember (FirstDecider t1) as q; DestructCompare q p.
    rewrite H1 in Heq_anonymous; LocationOrder.
  Defined.
  Next Obligation.
    remember (FirstDecider t1) as q; DestructCompare q p.
  Defined.
  Next Obligation.
    remember (FirstDecider t2) as q; DestructCompare q p.
  Defined.
  Next Obligation.
    inversion H1; auto.
  Defined.
  Next Obligation.
    inversion H1; auto.
  Defined.

  Import ListNotations.
  Inductive IsBalancedICTreewrt : IChoiceTree -> list L.t -> Prop :=
    IsBalancedLeaf : forall p P Q, IsBalancedICTreewrt (ICTLeaf p P Q) [p]
  | IsBalancedBranch : forall p t1 t2 l, IsBalancedICTreewrt t1 l -> IsBalancedICTreewrt t2 l -> IsBalancedICTreewrt (ICTBranch p t1 t2) (p :: l).

  Program Fixpoint CheckBalancedICTreewrt (t : IChoiceTree) (l : list L.t) : {IsBalancedICTreewrt t l} + {~ IsBalancedICTreewrt t l} :=
    match t with
    | ICTLeaf p P Q =>
      match l with
      | [] => right _
      | [q] => match L.eq_dec p q with
              | left e => left (IsBalancedLeaf p P Q)
              | right n => right _
              end
      | _ => right _
      end
    | ICTBranch p t1 t2 =>
      match l with
      | [] => right _
      | q :: l' => match L.eq_dec p q with
                 | left e => match CheckBalancedICTreewrt t1 l' with
                            | left b1 =>
                              match CheckBalancedICTreewrt t2 l' with
                              | left b2 => left (IsBalancedBranch p t1 t2 l' b1 b2)
                              | right n => right _
                              end
                            | right n => right _
                            end
                 | right n => right _
                 end
      end
    end.
  Next Obligation.
    inversion H.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H1; subst; apply (H p); auto.
  Defined.
  Next Obligation.
    split; [intro q |]; intro eq; discriminate eq.
  Defined.
  Next Obligation.
    inversion H.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.

  Fixpoint FindBalancingList (t : IChoiceTree) : option (list L.t) :=
    match t with
    | ICTLeaf p _ _ => Some [p]
    | ICTBranch p t1 t2 =>
      match FindBalancingList t1 with
      | Some l => match CheckBalancedICTreewrt t2 l with
                 | left _ => Some (p :: l)
                 | right _ => None
                 end
      | None => None
      end
    end.

  Lemma FindBalancingListSound : forall (t : IChoiceTree) (l : list L.t), FindBalancingList t = Some l -> IsBalancedICTreewrt t l.
  Proof using.
    intro t; ICTInduction t; intros ell eq; cbn in *.
    - inversion eq; subst; clear eq; constructor.
    - destruct (FindBalancingList t0); [| inversion eq].
      destruct (CheckBalancedICTreewrt t1 l0); [| inversion eq]. inversion eq; subst; clear eq.
      constructor; auto.
  Qed.

  Lemma FindBalancingListComplete : forall (t : IChoiceTree) (l : list L.t), IsBalancedICTreewrt t l -> FindBalancingList t = Some l.
  Proof using.
    intro t; ICTInduction t; intros ell b; inversion b; subst; cbn; auto.
    specialize (IHt0 l0 H3); rewrite IHt0.
    destruct (CheckBalancedICTreewrt t1 l0) as [_|n]; [|exfalso; apply n]; auto.
  Qed.    

  Definition IsBalancedICTree : IChoiceTree -> Prop := fun t => exists l, IsBalancedICTreewrt t l.

  Program Definition CheckBalancedICTree : forall t : IChoiceTree, {IsBalancedICTree t} + {~ IsBalancedICTree t} :=
    fun t => match FindBalancingList t with
          | Some l => left (ex_intro _ l _)
          | None => right _
          end.
  Next Obligation.
    apply FindBalancingListSound; symmetry; auto.
  Defined.
  Next Obligation.
    inversion H. apply FindBalancingListComplete in H0.
    assert (Some x = None) as eq by (transitivity (FindBalancingList t); auto); discriminate eq.
  Defined.

  Fixpoint NumberOfChoices (t : IChoiceTree) (p : L.t) : nat :=
    match t with
    | ICTLeaf q _ _ => if L.eq_dec p q then 1 else 0
    | ICTBranch q t1 t2 => (if L.eq_dec p q then 1 else 0) + (Nat.max (NumberOfChoices t1 p) (NumberOfChoices t2 p))
    end.

  Inductive IsDecider : L.t -> IChoiceTree -> Prop :=
  | IsLeafDecider : forall p P Q, IsDecider p (ICTLeaf p P Q)
  | IsCurrentBranchDecider : forall p t1 t2, IsDecider p (ICTBranch p t1 t2)
  | IsLeftChildDecider : forall p q t1 t2, IsDecider p t1 -> IsDecider p (ICTBranch q t1 t2)
  | IsRightChildDecider : forall p q t1 t2, IsDecider p t2 -> IsDecider p (ICTBranch q t1 t2).

  Program Fixpoint IsDeciderDec (p : L.t) (t : IChoiceTree) : {IsDecider p t} + {~ IsDecider p t} :=
    match t with
    | ICTLeaf q P Q =>
      match L.eq_dec p q with
      | left e => left (IsLeafDecider p P Q)
      | right n => right (fun id => _)
      end
    | ICTBranch q t1 t2 =>
      match L.eq_dec p q with
      | left e => left (IsCurrentBranchDecider p t1 t2)
      | right n1 =>
        match IsDeciderDec p t1 with
        | left id1 => left (IsLeftChildDecider p q t1 t2 id1)
        | right n2 =>
          match IsDeciderDec p t2 with
          | left id2 => left (IsRightChildDecider p q t1 t2 id2)
          | right n3 => right (fun id => _)
          end
        end
      end
    end.
  Next Obligation.
    inversion id; subst; apply n; reflexivity.
  Defined.
  Next Obligation.
    inversion id; subst; [apply n1 | apply n2 | apply n3]; auto.
  Defined.      
  
  Theorem IsDeciderOfBalancedwrt : forall (p : L.t) (t1 t2 : IChoiceTree) (l : list L.t), IsBalancedICTreewrt t1 l -> IsBalancedICTreewrt t2 l -> IsDecider p t1 -> IsDecider p t2.
  Proof using.
    intros p t1 t2 l ibt1 ibt2 id1; revert t2 l ibt1 ibt2; induction id1; intros t2' l0 ibt1 ibt2; inversion ibt1; subst; inversion ibt2; subst; try (constructor; auto; fail).
    - inversion H4.
    - apply IsLeftChildDecider. apply IHid1 with (l := l); auto.
    - inversion H4.
    - apply IsRightChildDecider. apply IHid1 with (l := l); auto.
  Qed.

  Fixpoint Deciders (t : IChoiceTree) : list L.t :=
    match t with
    | ICTLeaf p _ _ => [p]
    | ICTBranch p t1 t2 => p :: Deciders t1
    end.

  Theorem BalancedDeciderswrt : forall (t : IChoiceTree) (l : list L.t),
      IsBalancedICTreewrt t l -> l = Deciders t.
  Proof using.
    intros t; ICTInduction t; intros l' bal.
    inversion bal; subst; cbn; auto.
    inversion bal; subst; cbn; rewrite IHt0 with (l := l0); auto.
  Qed.

  Theorem BalancedDecidersBalancingList : forall (t : IChoiceTree), IsBalancedICTree t -> FindBalancingList t = Some (Deciders t).
  Proof using.
    intro t; ICTInduction t; intros ibt; cbn; auto.
    inversion ibt; subst. rename x into ell. cbn in H. destruct (FindBalancingList t0) eqn:eq; [destruct (CheckBalancedICTreewrt t1 l0) |]; inversion H; subst.
    - apply FindBalancingListSound in eq. specialize (IHt0 (ex_intro _ _ eq)); inversion IHt0; subst; reflexivity.
    - assert (Some l0 = Some l1) as eq' by (transitivity (FindBalancingList t0); apply FindBalancingListComplete in H4; auto); inversion eq'; subst; clear eq'.
      exfalso; apply n; exact H5.
    - apply FindBalancingListComplete in H4; discriminate (eq_trans (eq_sym H4) eq).
  Qed.

  Theorem DecidersSound : forall (t : IChoiceTree) (p : L.t), In p (Deciders t) -> IsDecider p t.
  Proof using.
    intro t; induction t as [q P Q | q t1 IHt1 t2 IHt2]; intros p i; cbn in i; destruct i as [eq | i]; subst; [ constructor | inversion i | constructor|].
    apply IsLeftChildDecider; apply IHt1; exact i.
  Qed.

  Theorem BalancedDecidersComplete : forall (t : IChoiceTree) (p : L.t), IsBalancedICTree t -> IsDecider p t -> In p (Deciders t).
  Proof using.
    intro t; induction t as [q P Q | q t1 IHt1 t2 IHt2]; intros p ibt decp; cbn in *.
    left; inversion decp; reflexivity.
    inversion decp; auto; subst; right; apply IHt1; auto.
    unfold IsBalancedICTree in ibt. destruct ibt as [l ibt]; inversion ibt; subst. exists l0; auto.
    destruct ibt as [l ibt]; inversion ibt; subst. exists l0; auto.
    destruct ibt as [l ibt]; inversion ibt; subst.
    apply IsDeciderOfBalancedwrt with (t1 := t2) (l := l0); auto.
  Qed.



  Record DecisionType (t : IChoiceTree) : Type := {
    raw_type : LM.t nat;
    all_deciders : forall p : L.t, IsDecider p t -> LM.mem p raw_type = true
    }.
  
  Inductive IsSameActionTreeA : IChoiceTree -> Action -> Prop :=
    IsSameActionTreeLeaf : forall p P Q A, ActionOf P = A -> ActionOf Q = A -> IsSameActionTreeA (ICTLeaf p P Q) A
  | IsSameActionTreeBranch : forall p t1 t2 A, IsSameActionTreeA t1 A -> IsSameActionTreeA t2 A -> IsSameActionTreeA (ICTBranch p t1 t2) A.

  Program Fixpoint CheckSameActionTreeA (t : IChoiceTree) (A : Action) : {IsSameActionTreeA t A} + {~ IsSameActionTreeA t A} :=
    match t with
    | ICTLeaf p P Q =>
      match ActionEqDec (ActionOf P) A with
      | left eq1 =>
        match ActionEqDec (ActionOf Q) A with
        | left eq2 => left (IsSameActionTreeLeaf p P Q A eq1 eq2)
        | right n => right _
        end  
      | right n => right _
      end
    | ICTBranch p t1 t2 =>
      match CheckSameActionTreeA t1 A with
      | left ista1 =>
        match CheckSameActionTreeA t2 A with
        | left ista2 => left (IsSameActionTreeBranch p t1 t2 A ista1 ista2)
        | right n => right _
        end
      | right n => right _
      end
    end.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.

  Fixpoint FindOnlyAction (t : IChoiceTree) : option Action :=
    match t with
    | ICTLeaf _ P Q =>
      if ActionEqDec (ActionOf P) (ActionOf Q) then Some (ActionOf P) else None
    | ICTBranch _ t1 t2 =>
      match FindOnlyAction t1 with
      | Some A => if CheckSameActionTreeA t2 A then Some A else None
      | None => None
      end
    end.

  Lemma FindOnlyActionSound : forall (t : IChoiceTree) (A : Action), FindOnlyAction t = Some A -> IsSameActionTreeA t A.
  Proof using.
    intros t A eq; induction t as [p P Q | p t1 IHt1 t2 IHt2]; cbn in eq.
    destruct (ActionEqDec (ActionOf P) (ActionOf Q)); inversion eq; constructor; auto.
    destruct (FindOnlyAction t1) as [B|]; [destruct (CheckSameActionTreeA t2 B)|]; inversion eq; subst.
    clear eq; specialize (IHt1 eq_refl); constructor; auto.
  Qed.

  Lemma FindOnlyActionComplete : forall (t : IChoiceTree) (A : Action), IsSameActionTreeA t A -> FindOnlyAction t = Some A.
  Proof using.
    intros t A isat; induction isat as [p P Q A eq1 eq2 | p t1 t2 A isat1 IHisat1 isat2 IHisat2]; cbn.
    destruct (ActionEqDec (ActionOf P) (ActionOf Q)); subst; auto; exfalso; apply n; auto.
    rewrite IHisat1. destruct (CheckSameActionTreeA t2 A); auto; exfalso; apply n; auto.
  Qed.
  
  Definition IsSameActionTree : IChoiceTree -> Prop := fun t : IChoiceTree => exists A : Action, IsSameActionTreeA t A.

  Definition CheckSameActionTree : forall t : IChoiceTree, {IsSameActionTree t} + {~ IsSameActionTree t}.
    intro t. destruct (FindOnlyAction t) as [A|] eqn:eq; [left; exists A; apply FindOnlyActionSound; auto|right].
    intro H; unfold IsSameActionTree in H; destruct H as [A H]; apply FindOnlyActionComplete in H.
    assert (Some A = None) as H' by (transitivity (FindOnlyAction t); auto); discriminate H'.
  Defined.

  Definition IsSameTree : IChoiceTree -> Prop := fun t : IChoiceTree => IsSameActionTree t /\ IsOrderedICTree t /\ IsBalancedICTree t.
  Definition CheckSameTree : forall t : IChoiceTree, {IsSameTree t} + {~ IsSameTree t}.
    intro t.
    destruct (CheckSameActionTree t); [ | right; intro ist; unfold IsSameTree in ist; destruct ist; apply n; auto].
    destruct (CheckOrderedICTree t); [ | right; intro ist; destruct ist as [_ H]; destruct H; apply n; auto].
    destruct (CheckBalancedICTree t); [ | right; intro ist; destruct ist as [_ H]; destruct H; apply n; auto].
    left; split; [| split]; auto.
  Defined.

  Definition IsDifferentTree : IChoiceTree -> Prop := fun t : IChoiceTree => IsOrderedICTree t /\ (~IsSameActionTree t \/ ~IsBalancedICTree t).
  Definition CheckDifferentTree : forall t : IChoiceTree, {IsDifferentTree t} + {~ IsDifferentTree t}.
    intro t.
    destruct (CheckOrderedICTree t) as [ord | n]; [ | right; intro idt; destruct idt as [ord _]; apply n; exact ord].
    destruct (CheckSameActionTree t) as [sat | n]; [|left; split; [|left]; auto].
    destruct (CheckBalancedICTree t) as [bal | n]; [|left; split; [|right]; auto].
    right; intro idt; destruct idt as [_ H]; destruct H as [n | n]; apply n; auto.
  Defined.

  Fixpoint ChoiceTypeOf (t : IChoiceTree) : LM.t nat :=
    match t with
    | ICTLeaf l P Q => LM.add l 1 (LM.empty)
    | ICTBranch l t1 t2 => match LM.find l (ChoiceTypeOf t1) with
                          | Some n => LM.add l (S n) (ChoiceTypeOf t1)
                          | None => LM.add l 1 (ChoiceTypeOf t1)
                          end
    end.

  Lemma ChoiceTypeDeciders : forall (t : IChoiceTree) (ℓ : list L.t),
      IsBalancedICTreewrt t ℓ -> forall (l : L.t), LM.In l (ChoiceTypeOf t) <-> IsDecider l t.
  Proof using.
    intro t; induction t as [l P Q | l t1 IHt1 t2 IHt2]; intros ℓ bal l'; split;
      [intro i | intro id | intro i | intro id].
    - unfold ChoiceTypeOf in i.
      destruct (L.eq_dec l' l) as [eq | neq]; subst; [constructor|].
      destruct i as [n mt]. apply LM.add_3 in mt; auto.
      apply LM.empty_1 in mt; destruct mt.
    - inversion id; subst; unfold ChoiceTypeOf; exists 1; apply LM.add_1.
    - cbn in i; destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq;
        destruct (L.eq_dec l' l); subst; try (constructor; fail);
          destruct i as [m mt]; apply LM.add_3 in mt; auto;
            apply IsLeftChildDecider; inversion bal; subst; apply (IHt1 l0 H3); exists m; auto.
    - inversion bal; subst. specialize (IHt1 l0 H3).
      cbn. destruct (LM.find l (ChoiceTypeOf t1)); inversion id; subst.
      exists (S n); apply LM.add_1.
      3: exists 1; apply LM.add_1.
      all: destruct (L.eq_dec l' l); subst; [eexists; apply LM.add_1|].
      2,4: apply IsDeciderOfBalancedwrt with (t2 := t1) (l := l0) in H1; auto.
      all: rewrite <- IHt1 in H1; destruct H1 as [m mt]; exists m; apply LM.add_2; auto.
  Qed.

  Fixpoint LocationCard (ℓ : list L.t) (l : L.t) : nat :=
    match ℓ with
    | [] => 0
    | l' :: ℓ' => (if L.eq_dec l l' then 1 else 0) + LocationCard ℓ' l
    end.

  Lemma LocationCardGt0 : forall (ℓ : list L.t) (l : L.t), gt (LocationCard ℓ l) 0 -> In l ℓ.
  Proof using.
    intros ℓ; induction ℓ as [| l' ℓ']; intros l gt; [inversion gt|].
    cbn in gt. destruct (L.eq_dec l l'); subst; [left; auto|].
    cbn in gt. right; apply IHℓ'; auto.
  Qed.
  Lemma LocationCard0 :  forall (ℓ : list L.t) (l : L.t), ~ In l ℓ -> (LocationCard ℓ l) = 0.
  Proof using.
    intros ℓ; induction ℓ as [| l' ℓ]; intros l ni; cbn; auto.
    destruct (L.eq_dec l l') as [e | n]; [subst; exfalso; apply ni; left; auto|]; cbn.
    apply IHℓ. intro i; apply ni; right; auto.
  Qed.

  Lemma ChoiceTypeBalanced : forall (t : IChoiceTree) (ℓ : list L.t),
      IsBalancedICTreewrt t ℓ ->
      forall l : L.t, In l ℓ -> LM.MapsTo l (LocationCard ℓ l) (ChoiceTypeOf t).
  Proof using.
    intro t; induction t as [l P Q | l t1 IHt1 t2 IHt2]; intros ℓ bal l' i.
    - unfold ChoiceTypeOf. inversion bal; subst.
      destruct i as [eq| i]; [|inversion i]; subst.
      unfold LocationCard; destruct (L.eq_dec l' l') as [_ | n]; [|exfalso; apply n; auto].
      unfold plus. apply LM.add_1.
    - inversion bal; subst; rename l0 into ℓ'.
      specialize (IHt1 ℓ' H3); cbn.
      destruct i as [e | i]; subst.
      -- destruct (L.eq_dec l' l') as [_ | n]; [|exfalso; apply n; auto].
         destruct (ListDec.In_dec L.eq_dec l' ℓ').
         --- specialize (IHt1 l' i). apply LM.find_1 in IHt1. rewrite IHt1.
             cbn. apply LM.add_1.
         --- assert (LocationCard ℓ' l' = 0) as H by (apply LocationCard0; auto);
               rewrite H; cbn; clear H.
             destruct (LM.find l' (ChoiceTypeOf t1)) eqn:eq; [|apply LM.add_1].
             assert (~ In l' (Deciders t1)) as H
                 by (apply BalancedDeciderswrt in H3; subst; auto).
             exfalso; apply H.
             apply BalancedDecidersComplete; [exists ℓ'; auto|].
             rewrite <- ChoiceTypeDeciders; [|exact H3].
             apply LM.find_2 in eq; exists n0; auto.
      -- specialize (IHt1 l' i).
         destruct (L.eq_dec l' l) as [e | n]; subst.
         --- apply LM.find_1 in IHt1; rewrite IHt1; cbn; apply LM.add_1.
         --- cbn. destruct (LM.find l (ChoiceTypeOf t1));
                    apply LM.add_2; auto.
  Qed.
      
  Lemma ChoiceTypeBalancedEq : forall (t1 t2 : IChoiceTree) (ℓ : list L.t),
      IsBalancedICTreewrt t1 ℓ -> IsBalancedICTreewrt t2 ℓ ->
      LM.Equal (ChoiceTypeOf t1) (ChoiceTypeOf t2).
  Proof using.
    intros t1 t2 ℓ H H0.
    unfold LM.Equal; intro l.
    destruct (ListDec.In_dec L.eq_dec l ℓ).
    apply ChoiceTypeBalanced with (l := l) in H; auto;
      apply LM.find_1 in H; rewrite H;
        apply ChoiceTypeBalanced with (l := l) in H0; auto;
          apply LM.find_1 in H0; rewrite H0; reflexivity.
    assert (~ LM.In l (ChoiceTypeOf t1))
      by (assert (ℓ = Deciders t1) by (apply BalancedDeciderswrt in H; auto); subst;
          intro i; apply n; rewrite ChoiceTypeDeciders in i; [| exact H];
          apply BalancedDecidersComplete in i; [auto | exists (Deciders t1); auto]).
    assert (~ LM.In l (ChoiceTypeOf t2))
      by (assert (ℓ = Deciders t2) by (apply BalancedDeciderswrt in H0; auto); subst;
          intro i; apply n; rewrite ChoiceTypeDeciders in i; [| exact H0];
          apply BalancedDecidersComplete in i; [auto | exists (Deciders t2); auto]).
    destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq1;
      [apply LM.find_2 in eq1; exfalso; apply H1; exists n0; auto|].
    destruct (LM.find l (ChoiceTypeOf t2)) eqn:eq2;
      [apply LM.find_2 in eq2; exfalso; apply H2; exists n0; auto|].
    reflexivity.
  Qed.

  Inductive LRChoice : Set := L : LRChoice | R : LRChoice.
  Definition ChoiceTyping (ty : LM.t nat) (cs : LM.t (list LRChoice)) : Prop :=
    (forall (l : L.t) (chs : list LRChoice), LM.MapsTo l chs cs -> LM.MapsTo l (length chs) ty)
    /\ (forall (l : L.t) (n : nat), LM.MapsTo l n ty -> exists chs : list LRChoice, length chs = n /\ LM.MapsTo l chs cs).

  Lemma ctproper : forall (ct1 ct2 : LM.t nat), LM.Equal ct1 ct2 -> forall cs1 cs2, LM.Equal cs1 cs2 -> ChoiceTyping ct1 cs1 <-> ChoiceTyping ct2 cs2.
  Proof using.
    intros ct1 ct2 ct_eq cs1 cs2 cs_eq. unfold LM.Equal in *; unfold ChoiceTyping; split; [split | split].
    1,3: intros l chs mt. 3,4: intros l n mt. all: destruct H as [ctyping1 ctyping2].
    - apply LM.find_2; rewrite <- ct_eq; apply LM.find_1; apply ctyping1; apply LM.find_2; rewrite cs_eq; apply LM.find_1; auto. 
    - apply LM.find_2; rewrite ct_eq; apply LM.find_1; apply ctyping1; apply LM.find_2; rewrite <- cs_eq; apply LM.find_1; auto.
    - apply LM.find_1 in mt; rewrite <- ct_eq in mt; apply LM.find_2 in mt.
      specialize (ctyping2 l n mt); destruct ctyping2 as [chs H]; destruct H as [len mt'].
      exists chs; split; auto. apply LM.find_2; rewrite <- cs_eq; apply LM.find_1; auto.
    - apply LM.find_1 in mt; rewrite ct_eq in mt; apply LM.find_2 in mt.
      specialize (ctyping2 l n mt); destruct ctyping2 as [chs H]; destruct H as [len mt'].
      exists chs; split; auto. apply LM.find_2; rewrite cs_eq; apply LM.find_1; auto.
  Qed.

  Fixpoint RunChoices (t : IChoiceTree) (cs : LM.t (list LRChoice)) : option Proc :=
    match t with
    | ICTLeaf l P Q => match LM.find l cs with
                      | Some (L :: _) => Some P
                      | Some (R :: _) => Some Q
                      | _ => None
                      end
    | ICTBranch l t1 t2 => match LM.find l cs with
                          | Some (L :: lcs) =>
                            match lcs with
                            | [] => RunChoices t1 (LM.remove l cs)
                            | _ :: _ => RunChoices t1 (LM.add l lcs cs)
                            end
                          | Some (R :: lcs) =>
                            match lcs with
                            | [] => RunChoices t2 (LM.remove l cs)
                            | _ :: _ => RunChoices t2 (LM.add l lcs cs)
                            end
                          | _ => None
                          end
    end.

  Lemma TypingNotZero : forall (l : L.t) (t : IChoiceTree), ~ LM.MapsTo l 0 (ChoiceTypeOf t).
  Proof using.
    intros l t; revert l; induction t as [l P Q | l t1 IHt1 t2 IHt2]; intros l'.
    - unfold ChoiceTypeOf. intro H. destruct (L.eq_dec l' l); subst.
      apply LM.find_1 in H.
      remember (LM.add_1 LM.empty l 1) as H0; clear HeqH0.
      apply LM.find_1 in H0. rewrite H0 in H. inversion H.
      apply LM.add_3 in H; auto. apply LM.empty_1 in H; auto.
    - cbn. intro H. apply (IHt1 l').
      destruct (LM.find l (ChoiceTypeOf t1)).
      destruct (L.eq_dec l l'); subst.
      assert (0 = S n) as H0 by (eapply LMF.MapsToUnique; [exact H| apply LM.add_1]);
        inversion H0.
      apply LM.add_3 in H; auto.
      destruct (L.eq_dec l l'); subst.
      assert (0 = 1) as H0 by (eapply LMF.MapsToUnique; [exact H | apply LM.add_1]);
        inversion H0.
      apply LM.add_3 in H; auto.
  Qed.

  Definition inspect {Y} (x : Y) : {y | x = y}.
  Proof using. now exists x. Qed.
  Equations RunTypedChoices (t : IChoiceTree) (cs : LM.t (list LRChoice)) (bal : IsBalancedICTree t) (ct: ChoiceTyping (ChoiceTypeOf t) cs) : Proc :=
    {
      RunTypedChoices (ICTLeaf l P Q) cs bal ct with inspect (LM.find l cs) :=
        {
        RunTypedChoices (ICTLeaf l P Q) cs bal ct (exist _ (Some [L]) _) := P;
        RunTypedChoices (ICTLeaf l P Q) cs bal ct (exist _ (Some [R]) _) := Q;
        RunTypedChoices (ICTLeaf l P Q) cs bal ct (exist _ _ eq) := _
        };
      RunTypedChoices (ICTBranch l t1 t2) cs bal ct with inspect (LM.find l cs) :=
        {
        RunTypedChoices (ICTBranch l t1 t2) cs bal ct (exist _ (Some [L]) _) := RunTypedChoices t1 (LM.remove l cs) _ _;
        RunTypedChoices (ICTBranch l t1 t2) cs bal ct (exist _ (Some [R]) _) := RunTypedChoices t2 (LM.remove l cs) _ _;
        RunTypedChoices (ICTBranch l t1 t2) cs bal ct (exist _ (Some (L :: lcs)) _) := RunTypedChoices t1 (LM.add l lcs cs) _ _;
        RunTypedChoices (ICTBranch l t1 t2) cs bal ct (exist _ (Some (R :: rcs)) _) := RunTypedChoices t2 (LM.add l rcs cs) _ _;
        RunTypedChoices (ICTBranch l t1 t2) cs bal ct (exist _ _ eq) := _
        }
    }.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply LM.find_2 in eq; specialize (ct1 l [] eq); apply LM.find_1 in ct1; cbn in ct1.
    DestructCompare l l.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply LM.find_2 in eq; specialize (ct1 l (L :: l0 :: l1) eq); apply LM.find_1 in ct1; cbn in ct1.
    DestructCompare l l.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply LM.find_2 in eq; specialize (ct1 l (R :: l0 :: l1) eq); apply LM.find_1 in ct1; cbn in ct1.
    DestructCompare l l.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    exfalso; specialize (ct2 l 1); destruct ct2 as [chs H]; [ apply LM.find_2; cbn; DestructCompare l l; subst| destruct H as [len mt]].
    apply LM.find_1; apply LM.add_1.
    apply LM.find_1 in mt. rewrite eq in mt. inversion mt.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply LM.find_2 in eq; specialize (ct1 l [] eq); apply LM.find_1 in ct1; cbn in ct1.
    destruct (LM.find l (ChoiceTypeOf t1)).
    assert (LM.MapsTo l (S n) (LM.add l (S n) (ChoiceTypeOf t1))) as H by (apply LM.add_1).
    2: assert (LM.MapsTo l 1 (LM.add l 1 (ChoiceTypeOf t1))) as H by (apply LM.add_1).
    all: apply LM.find_1 in H; rewrite ct1 in H; inversion H.
  Defined.
  Next Obligation.
    destruct bal as [l' bal]; inversion bal; subst; exists l0; auto.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq; unfold ChoiceTyping; split; intro l0; destruct (L.eq_dec l l0); subst.
    - intros chs mt; exfalso; apply LM.remove_1 with (m := cs) (x := l0); exists chs; auto.
    - intros chs mt; apply LM.remove_3 in mt; auto. specialize (ct1 l0 chs mt); apply LM.add_3 in ct1; auto.
    - intros m mt. apply LM.find_1 in mt; rewrite eq in mt; inversion mt; subst; clear mt.
      apply LM.find_2 in wildcard. specialize (ct1 l0 [L] wildcard). cbn in ct1.
      assert (1 = S m) as H by (eapply LMF.MapsToUnique; [exact ct1 | apply LM.add_1]);
        inversion H; subst.
      apply LM.find_2 in eq. exfalso; eapply TypingNotZero; exact eq.
    - intros m mt. destruct (ct2 l0 m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']].
      exists chs; split; auto; apply LM.remove_2; auto.
    - intros chs mt; exfalso; eapply LM.remove_1; exists chs; exact mt.
    - intros chs mt. apply LM.remove_3 in mt; auto. specialize (ct1 l0 chs mt). apply LM.add_3 in ct1; auto.
    - intros n mt; apply LM.find_1 in mt; rewrite eq in mt; inversion mt.
    - intros m mt. destruct (ct2 l0 m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.remove_2; auto.
  Defined.
  Next Obligation.
    destruct bal as [l_bal bal]; inversion bal; subst. exists l2; auto.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq; unfold ChoiceTyping; split; intro l'; destruct (L.eq_dec l l'); subst.
    - intros chs mt.
      assert (chs = l0 :: l1) as H by (eapply LMF.MapsToUnique; [exact mt | apply LM.add_1]); subst.
      cbn. apply LM.find_2 in wildcard1. specialize (ct1 l' (L :: l0 :: l1) wildcard1). cbn in ct1.
      assert (S (S (length l1)) = S n) as H by (eapply LMF.MapsToUnique; [exact ct1 | apply LM.add_1]); inversion H; subst; clear H.
      apply LM.find_2 in eq; auto.
    - intros chs mt. apply LM.add_3 in mt; auto. specialize (ct1 l' chs mt). apply LM.add_3 in ct1; auto.
    - intros m mt. apply LM.find_1 in mt; rewrite eq in mt; inversion mt; subst; clear mt.
      apply LM.find_2 in wildcard1. specialize (ct1 l' (L :: l0 :: l1) wildcard1).
      assert (length (L :: l0 :: l1) = S m) as H by (eapply LMF.MapsToUnique; [exact ct1 | apply LM.add_1]); inversion H; subst; clear H.
      exists (l0 :: l1); cbn; split; auto. apply LM.add_1.
    - intros m mt; destruct (ct2 l' m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.add_2; auto.
    - intros chs mt. apply LM.find_2 in wildcard1. specialize (ct1 l' (L :: l0 :: l1) wildcard1). cbn in ct1.
      assert (S (S (length l1)) = 1) as H by (eapply LMF.MapsToUnique; [exact ct1 | apply LM.add_1]); inversion H.
    - intros chs mt. apply LM.add_3 in mt; auto. specialize (ct1 l' chs mt). apply LM.add_3 in ct1; auto.
    - intros n mt; apply LM.find_1 in mt; rewrite eq in mt; inversion mt.
    - intros m mt; destruct (ct2 l' m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.add_2; auto.
  Defined.
  Next Obligation.
    destruct bal as [l' bal]; inversion bal; subst; exists l0; auto.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply ctproper with (ct1 := ChoiceTypeOf t1) (cs1 := LM.remove l cs); auto. destruct bal as [ℓ bal]; inversion bal; subst; apply ChoiceTypeBalancedEq with (ℓ := l0); auto.
    unfold LM.Equal; auto.
    destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq; unfold ChoiceTyping; split; intro l0; destruct (L.eq_dec l l0); subst.
    - intros chs mt; exfalso; apply LM.remove_1 with (m := cs) (x := l0); exists chs; auto.
    - intros chs mt; apply LM.remove_3 in mt; auto. specialize (ct1 l0 chs mt); apply LM.add_3 in ct1; auto.
    - intros m mt. apply LM.find_1 in mt; rewrite eq in mt; inversion mt; subst; clear mt.
      apply LM.find_2 in wildcard0. specialize (ct1 l0 [R] wildcard0). cbn in ct1.
      assert (1 = S m) as H by (eapply LMF.MapsToUnique; [exact ct1 | apply LM.add_1]); inversion H; subst; clear H.
      apply LM.find_2 in eq. exfalso; eapply TypingNotZero; exact eq.
    - intros m mt. destruct (ct2 l0 m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']].
      exists chs; split; auto; apply LM.remove_2; auto.
    - intros chs mt; exfalso; eapply LM.remove_1; exists chs; exact mt.
    - intros chs mt. apply LM.remove_3 in mt; auto. specialize (ct1 l0 chs mt). apply LM.add_3 in ct1; auto.
    - intros n mt; apply LM.find_1 in mt; rewrite eq in mt; inversion mt.
    - intros m mt. destruct (ct2 l0 m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.remove_2; auto.
  Defined.
  Next Obligation.
    destruct bal as [l_bal bal]; inversion bal; subst. exists l2; auto.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    apply ctproper with (ct1 := ChoiceTypeOf t1) (cs1 := LM.add l (l0 :: l1) cs); auto. destruct bal as [ℓ bal]; inversion bal; subst; apply ChoiceTypeBalancedEq with (ℓ := l2); auto.
    unfold LM.Equal; auto.
    destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq; unfold ChoiceTyping; split; intro l'; destruct (L.eq_dec l l'); subst.
    - intros chs mt. assert (LM.MapsTo l' (l0 :: l1) (LM.add l' (l0 :: l1) cs)) by (apply LM.add_1). apply LM.find_1 in H; apply LM.find_1 in mt; rewrite H in mt; inversion mt; subst.
      cbn. apply LM.find_2 in wildcard2. specialize (ct1 l' (R :: l0 :: l1) wildcard2). cbn in ct1.
      assert (LM.MapsTo l' (S n) (LM.add l' (S n) (ChoiceTypeOf t1))) by (apply LM.add_1). apply LM.find_1 in H0; apply LM.find_1 in ct1; rewrite H0 in ct1; inversion ct1; subst.
      apply LM.find_2 in eq; auto.
    - intros chs mt. apply LM.add_3 in mt; auto. specialize (ct1 l' chs mt). apply LM.add_3 in ct1; auto.
    - intros m mt. apply LM.find_1 in mt; rewrite eq in mt; inversion mt; subst; clear mt.
      apply LM.find_2 in wildcard2. specialize (ct1 l' (R :: l0 :: l1) wildcard2).
      assert (LM.MapsTo l' (S m) (LM.add l' (S m) (ChoiceTypeOf t1))) by (apply LM.add_1). apply LM.find_1 in H; apply LM.find_1 in ct1; rewrite H in ct1; inversion ct1; subst.
      exists (l0 :: l1); cbn; split; auto. apply LM.add_1.
    - intros m mt; destruct (ct2 l' m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.add_2; auto.
    - intros chs mt. apply LM.find_2 in wildcard2. specialize (ct1 l' (R :: l0 :: l1) wildcard2). cbn in ct1. apply LM.find_1 in ct1.
      assert (LM.MapsTo l' 1 (LM.add l' 1 (ChoiceTypeOf t1))) as H by (apply LM.add_1); apply LM.find_1 in H; rewrite ct1 in H; inversion H; subst.
    - intros chs mt. apply LM.add_3 in mt; auto. specialize (ct1 l' chs mt). apply LM.add_3 in ct1; auto.
    - intros n mt; apply LM.find_1 in mt; rewrite eq in mt; inversion mt.
    - intros m mt; destruct (ct2 l' m) as [chs H]; [apply LM.add_2; auto | destruct H as [len mt']]. exists chs; split; auto. apply LM.add_2; auto.
  Defined.
  Next Obligation.
    unfold ChoiceTyping in ct; destruct ct as [ct1 ct2].
    exfalso; destruct (LM.find l (ChoiceTypeOf t1)) eqn:eq2;
    destruct (ct2 l _ (LM.add_1 _ _ _)) as [chs H]; destruct H as [len mt]; apply LM.find_1 in mt; rewrite mt in eq; inversion eq.
  Defined.    

  Theorem RunChoicesTyping (t : IChoiceTree) (cs : LM.t (list LRChoice)) (bal : IsBalancedICTree t) (ct : ChoiceTyping (ChoiceTypeOf t) cs)
    : RunChoices t cs = Some (RunTypedChoices t cs bal ct).
  Proof using.
    funelim (RunTypedChoices t cs bal ct); simp RunTypedChoices; unfold ChoiceTyping in ct; destruct ct as [ct1 ct2];
      try (cbn; rewrite e at 1; rewrite H; rewrite Heqcall; simp RunTypedChoices; auto; fail).
    - unfold ChoiceTypeOf in ct1. assert (LM.MapsTo t [] cs) by (clear Heq Heqcall; apply LM.find_2 in e; auto). remember (ct1 t [] H) as mt; clear Heqmt.
      assert (0 = 1) as H0 by (eapply LMF.MapsToUnique; [exact mt | apply LM.add_1]); inversion H0.
    - rewrite Heq; cbn; rewrite e; auto.
    - unfold ChoiceTypeOf in ct1. assert (LM.MapsTo t 1 (LM.add t 1 LM.empty)) as mt' by (apply LM.add_1).
      assert (LM.MapsTo t (L :: l :: l0) cs) by (clear Heq Heqcall; apply LM.find_2 in e; auto).
      assert (LM.MapsTo t (length (L :: l :: l0)) (LM.add t 1 LM.empty)) as mt by (apply ct1; auto). apply LM.find_1 in mt; apply LM.find_1 in mt'; rewrite mt' in mt; inversion mt.
    - rewrite Heq; cbn; rewrite e; auto.
    - unfold ChoiceTypeOf in ct1. assert (LM.MapsTo t 1 (LM.add t 1 LM.empty)) as mt' by (apply LM.add_1).
      assert (LM.MapsTo t (R :: l :: l0) cs) by (clear Heq Heqcall; apply LM.find_2 in e; auto).
      assert (LM.MapsTo t (length (R :: l :: l0)) (LM.add t 1 LM.empty)) as mt by (apply ct1; auto). apply LM.find_1 in mt; apply LM.find_1 in mt'; rewrite mt' in mt; inversion mt.
    - unfold ChoiceTypeOf in ct2. destruct (ct2 t 1 (LM.add_1 _ _ _)) as [chs H]; destruct H as [len mt].
      apply LM.find_1 in mt; rewrite e in mt; inversion mt.
    - cbn in ct1. assert (LM.MapsTo t0 [] cs) by (clear Heq Heqcall; apply LM.find_2 in e; auto). remember (ct1 t0 [] H) as mt; clear Heqmt.
      destruct (LM.find t0 (ChoiceTypeOf i)) in mt. assert (LM.MapsTo t0 (S n) (LM.add t0 (S n) (ChoiceTypeOf i))) as mt' by (apply LM.add_1).
      2: assert (LM.MapsTo t0 1 (LM.add t0 1 (ChoiceTypeOf i))) as mt' by (apply LM.add_1).
      all: apply LM.find_1 in mt; apply LM.find_1 in mt'; rewrite mt' in mt; inversion mt.
    - exfalso; clear Heq Heqcall; cbn in ct2; destruct (LM.find t0 (ChoiceTypeOf i)); [specialize (ct2 t0 (S n) (LM.add_1 _ _ _)) | specialize (ct2 t0 1 (LM.add_1 _ _ _))];
        destruct ct2 as [chs H]; destruct H as [len mt].
      all: apply LM.find_1 in mt; rewrite e in mt; inversion mt.
  Qed.
  Print ChoiceTyping.
  Definition LaxChoiceTyping (ty : LM.t nat) (cs : LM.t (list LRChoice)) :=
    forall (l : L.t) (n : nat), LM.MapsTo l n ty -> exists chs : list LRChoice, le n (length chs) /\ LM.MapsTo l chs cs.

  Definition CombineChoiceTypes : LM.t nat -> LM.t nat -> LM.t nat :=
    fun ct1 ct2 => 
      LM.map2 (fun sn sm => match sn with
                         | Some n =>
                           match sm with
                           | Some m => Some (Max.max n m)
                           | None => Some n
                           end
                         | None =>
                           match sm with
                           | Some m => Some m
                           | None => None
                           end
                         end) ct1 ct2.
  Lemma CombineComm : forall ct1 ct2, LM.Equal (CombineChoiceTypes ct1 ct2) (CombineChoiceTypes ct2 ct1).
  Proof using.
    intros ct1 ct2; unfold CombineChoiceTypes; unfold LM.Equal; intro l.
    match goal with
    | [|- context[LM.find l ?a]] => let eq := fresh "eq" in destruct (LM.find l a) eqn:eq
    end.
    assert (LM.In l ct1 \/ LM.In l ct2)
      by (eapply LM.map2_2; unfold LM.In; exists n; apply LM.find_2 in eq; eauto).
    rewrite LM.map2_1; auto; [|destruct H; [right | left]; auto].
    rewrite LM.map2_1 in eq; auto.
    destruct (LM.find l ct2); destruct (LM.find l ct1); auto.
    inversion eq; subst. rewrite Max.max_comm; auto.
    match goal with
    | [|- context[LM.find l ?a]] => let eq := fresh "eq" in destruct (LM.find l a) eqn:eq
    end; auto.
    assert (LM.In l ct2 \/ LM.In l ct1) as H
      by ( eapply LM.map2_2; unfold LM.In; exists n; apply LM.find_2 in eq0; eauto).
    rewrite LM.map2_1 in eq; [|destruct H; [right | left]; auto].
    destruct (LM.find l ct1) eqn:eq1; destruct (LM.find l ct2) eqn:eq2; try (inversion eq; fail).
    destruct H as [H | H]; unfold LM.In in H; destruct H as [m H]; apply LM.find_1 in H;
      [rewrite H in eq2; inversion eq2 | rewrite H in eq1; inversion eq1].
  Qed.
  Lemma CombineIdempotent : forall (ct : LM.t nat), LM.Equal (CombineChoiceTypes ct ct) ct.
  Proof using.
    intro ct; unfold LM.Equal; intro l; unfold CombineChoiceTypes.
    destruct (LM.find l ct) eqn:eq. 
    rewrite LM.map2_1;[repeat rewrite eq; rewrite Max.max_idempotent; reflexivity|right; exists n; apply LM.find_2; auto]. 
    rewrite LMF.map2_3; auto.
  Qed.
  
  Instance CombineChoiceTypesProper : Proper ((@LM.Equal nat) ==> (@LM.Equal nat) ==> (@LM.Equal nat)) CombineChoiceTypes.
  Proof using.
    unfold Proper; unfold respectful; intros m1 m2 eq12 m3 m4 eq34;
      unfold CombineChoiceTypes; unfold LM.Equal; intro l.
    match goal with
    | [|- context[LM.find l ?a]] => let eq := fresh "eq" in destruct (LM.find l a) eqn:eq
    end.
    assert (LM.In l m1 \/ LM.In l m3) as H
        by (eapply LM.map2_2; unfold LM.In; apply LM.find_2 in eq; exists n; eauto).
    assert (LM.In l m2 \/ LM.In l m4) as H0
        by (destruct H as [H|H]; [left|right]; destruct H as [m mt]; apply LM.find_1 in mt;
            [rewrite eq12 in mt | rewrite eq34 in mt]; apply LM.find_2 in mt;
            unfold LM.In; exists m; auto).
    rewrite LM.map2_1; rewrite LM.map2_1 in eq; auto.
    destruct (LM.find l m1) eqn:eq0; destruct (LM.find l m3) eqn:eq1;
      try (inversion eq; fail).
    all: try (rewrite eq12 in eq0; rewrite eq0).
    all: try (rewrite eq34 in eq1; rewrite eq1); auto.
    match goal with
    | [|- context[LM.find l ?a]] => let eq := fresh "eq" in destruct (LM.find l a) eqn:eq
    end; auto.
    assert (LM.In l m2 \/ LM.In l m4) as H
        by (eapply LM.map2_2; unfold LM.In; apply LM.find_2 in eq0; exists n; eauto).
    assert (LM.In l m1 \/ LM.In l m3) as H0
        by (destruct H as [H|H]; [left|right]; destruct H as [m mt]; apply LM.find_1 in mt;
            [rewrite <- eq12 in mt | rewrite <- eq34 in mt]; apply LM.find_2 in mt;
            unfold LM.In; exists m; auto).
    rewrite LM.map2_1 in eq; rewrite LM.map2_1 in eq0; auto.
    destruct (LM.find l m2) eqn:eq1; destruct (LM.find l m4) eqn:eq2; try (inversion eq0; fail).
    all: try (rewrite <- eq12 in eq1; rewrite eq1 in eq).
    all: try (rewrite <- eq34 in eq2; rewrite eq2 in eq); inversion eq.
  Qed.
  
  Fixpoint LaxChoiceTypeOf (t : IChoiceTree) : LM.t nat :=
    match t with
    | ICTLeaf l _ _ => LM.add l 1 LM.empty
    | ICTBranch l t1 t2 => let ct' := CombineChoiceTypes (LaxChoiceTypeOf t1)
                                                       (LaxChoiceTypeOf t2)
                          in match LM.find l ct' with
                             | Some n => LM.add l (S n) ct'
                             | None => LM.add l 1 ct'
                             end
    end.

  Lemma SameBalancerLaxChoice : forall (t1 t2 : IChoiceTree) (ℓ : list L.t), IsBalancedICTreewrt t1 ℓ -> IsBalancedICTreewrt t2 ℓ -> LM.Equal (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2).
  Proof using.
    intros t1 t2 ℓ; revert t1 t2; induction ℓ as [| l ℓ]; intros t1 t2 bal1 bal2.
    inversion bal1.
    inversion bal1; subst; inversion bal2; subst;
      try match goal with
          | [ H : IsBalancedICTreewrt _ [] |- _ ] => inversion H
          end; cbn; unfold LM.Equal; intro l'; try reflexivity.
    unfold CombineChoiceTypes.
    destruct (LM.find l (LaxChoiceTypeOf t0)) eqn:eq0.
    - assert (LM.In l (LaxChoiceTypeOf t0)) by (unfold LM.In; exists n; apply LM.find_2 in eq0; auto).
      rewrite LM.map2_1; [|left; auto; fail]. rewrite (IHℓ t3 t0 H3 H2); rewrite eq0.
      assert (LM.In l (LaxChoiceTypeOf t1)) by (unfold LM.In; exists n; rewrite (IHℓ t0 t1 H2 H4) in eq0; apply LM.find_2 in eq0; auto).
      rewrite LM.map2_1 with (m := LaxChoiceTypeOf t1); [|left; auto].
      rewrite (IHℓ t1 t0 H4 H2); rewrite (IHℓ t4 t0 H5 H2); rewrite eq0.
      destruct (L.eq_dec l l'); subst.
      repeat rewrite LM.find_1 with (e := S (PeanoNat.Nat.max n n)); auto; apply LM.add_1.
      match goal with
      | [|-context[LM.find l' ?A]] => let eq := fresh "eq" in destruct (LM.find l' A) eqn:eq
      end.
      -- symmetry. apply LM.find_1 with (e := n1); auto.
         apply LM.find_2 in eq. apply LM.add_3 in eq; auto. apply LM.add_2; auto.
         assert (LM.In l' (LaxChoiceTypeOf t0) \/ LM.In l' (LaxChoiceTypeOf t3)) by (eapply LM.map2_2; unfold LM.In; exists n1; eauto).
         apply LM.find_2. rewrite LM.map2_1.
         destruct H1; unfold LM.In in H1; destruct H1 as [e mt]; apply LM.find_1 in mt.
         rewrite (IHℓ t1 t0 H4 H2); rewrite mt. rewrite (IHℓ t4 t0 H5 H2); rewrite mt.
         apply LM.find_1 in eq. rewrite LM.map2_1 in eq. rewrite mt in eq. rewrite (IHℓ t3 t0 H3 H2) in eq; rewrite mt in eq; auto.
         left; unfold LM.In; exists e; apply LM.find_2; auto.
         rewrite (IHℓ t1 t3 H4 H3); rewrite mt. rewrite (IHℓ t4 t3 H5 H3); rewrite mt.
         apply LM.find_1 in eq; rewrite LM.map2_1 in eq. rewrite (IHℓ t0 t3 H2 H3) in eq; repeat rewrite mt in eq; auto.
         left; unfold LM.In; exists e; apply LM.find_2; rewrite (IHℓ t0 t3 H2 H3); auto.
         left; destruct H1; unfold LM.In; unfold LM.In in H1; destruct H1 as [e mt]; exists e; apply LM.find_2; apply LM.find_1 in mt;
           [rewrite (IHℓ t1 t0 H4 H2) | rewrite (IHℓ t1 t3 H4 H3)]; auto.
      -- match goal with
         | [|-context[LM.find l' ?A]] => let eq := fresh "eq" in destruct (LM.find l' A) eqn:eq
         end; auto.
         apply LM.find_2 in eq1. apply LM.add_3 in eq1; auto. apply LM.find_1 in eq1.
         rewrite LM.map2_1 in eq1; [| eapply LM.map2_2; unfold LM.In; exists n1; apply LM.find_2 in eq1; eauto].
         destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq2.
         2: rewrite (IHℓ t4 t1 H5 H4) in eq1; rewrite eq2 in eq1; inversion eq1.
         all: exfalso; apply LMF.find_None with (e := n1) in eq; apply eq.
         all: apply LM.add_2; auto.
         apply LM.find_2. rewrite LM.map2_1; [| left; unfold LM.In; exists n2; apply LM.find_2; rewrite (IHℓ t0 t1 H2 H4); auto].
         rewrite (IHℓ t0 t1 H2 H4); rewrite eq2. rewrite (IHℓ t3 t1 H3 H4); rewrite eq2. rewrite (IHℓ t4 t1 H5 H4) in eq1; rewrite eq2 in eq1; auto.
    - assert (forall f : option nat -> option nat -> option nat, LM.find l (LM.map2 f (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t3)) = None) as find03
          by (intro f; destruct (LM.find l (LM.map2 f (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t3))) eqn:eq; auto;
              assert (LM.In l (LM.map2 f (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t3))) by (unfold LM.In; exists n; apply LM.find_2; auto);
              apply LM.map2_2 in H; destruct H; unfold LM.In in H; destruct H as [m mt]; apply LM.find_1 in mt; try (rewrite mt in eq0; inversion eq0);
              rewrite (IHℓ t3 t0 H3 H2) in mt; rewrite mt in eq0; inversion eq0).
      rewrite find03.
      assert (forall f : option nat -> option nat -> option nat, LM.find l (LM.map2 f (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t4)) = None) as find14
        by (intro f; destruct (LM.find l (LM.map2 f (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t4))) eqn:eq1; auto;
            assert (LM.In l (LM.map2 f (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t4))) by (unfold LM.In; exists n; apply LM.find_2; auto);
            apply LM.map2_2 in H; destruct H; unfold LM.In in H; destruct H as [m mt]; apply LM.find_1 in mt;
            [rewrite (IHℓ t1 t0 H4 H2) in mt; rewrite mt in eq0; inversion eq0
            |rewrite (IHℓ t4 t0 H5 H2) in mt; rewrite mt in eq0; inversion eq0]).
      rewrite find14.
      destruct (L.eq_dec l l'); subst.
      repeat rewrite LMF.find_add_1; auto.
      repeat rewrite LMF.find_add_2; auto.
      fold (CombineChoiceTypes (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t3)).
      fold (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t4)).
      assert (LM.Equal (CombineChoiceTypes (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t3)) (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t4))).
      apply CombineChoiceTypesProper; apply IHℓ; auto. 
      apply H.
  Qed.
  Lemma CombineChoiceTypesAdd : forall  l n m1 m2, LM.Equal (CombineChoiceTypes (LM.add l n m1) (LM.add l n m2)) (LM.add l n (CombineChoiceTypes m1 m2)).
  Proof using.
    intros l n m1 m2.
    unfold CombineChoiceTypes; unfold LM.Equal; intro l'.
    destruct (L.eq_dec l l'); subst.
    rewrite LMF.find_add_1. rewrite LM.map2_1. repeat rewrite LMF.find_add_1. rewrite Max.max_idempotent; auto.
    left; unfold LM.In; exists n; apply LM.add_1.
    rewrite LMF.find_add_2; auto. destruct (LM.find l' m1) eqn:eq1.
    repeat rewrite LM.map2_1. 
    rewrite LMF.find_add_2; auto; rewrite eq1.
    rewrite LMF.find_add_2; auto; destruct (LM.find l' m2) eqn:eq2.
    left; apply LM.find_2 in eq1; exists n1; auto.
    left; exists n1; apply LM.add_2; apply LM.find_2 in eq1; auto.
    destruct (LM.find l' m2) eqn:eq2.
    repeat rewrite LM.map2_1.
    rewrite LMF.find_add_2; auto; rewrite eq1.
    rewrite LMF.find_add_2; auto; rewrite eq2.
    right; exists n1; apply LM.find_2; auto.
    right; exists n1; apply LM.add_2; auto; apply LM.find_2; auto.
    repeat rewrite LMF.map2_3; auto.
    all: rewrite LMF.find_add_2; auto.
  Qed.
    
  Lemma SameBalancerCombine : forall (t1 t2 : IChoiceTree) (ℓ : list L.t),
      IsBalancedICTreewrt t1 ℓ -> IsBalancedICTreewrt t2 ℓ ->
      LM.Equal (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)) (LaxChoiceTypeOf t1).
  Proof using.
    intros t1 t2 ℓ H H0.
    transitivity (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t1)).
    apply CombineChoiceTypesProper; [reflexivity | apply SameBalancerLaxChoice with (ℓ := ℓ); auto].
    apply CombineIdempotent.
  Qed.
    
  Lemma BalancedChoiceIsLax : forall (t : IChoiceTree), IsBalancedICTree t -> LM.Equal (LaxChoiceTypeOf t) (ChoiceTypeOf t).
  Proof using.
    intro t; ICTInduction t; intro bal; unfold LM.Equal; intro y; cbn; auto.
    destruct bal as [ℓ balℓ]; inversion balℓ; subst; rename l0 into ℓ.
    rewrite SameBalancerCombine with (ℓ := ℓ); auto. rewrite IHt0; [|exists ℓ; auto].
    destruct (LM.find l (ChoiceTypeOf t0)) eqn:eq; destruct (L.eq_dec y l); subst.
    - repeat rewrite LMF.find_add_1; auto.
    - repeat rewrite LMF.find_add_2; auto.
      rewrite SameBalancerCombine with (ℓ := ℓ); auto. rewrite IHt0; [reflexivity|exists ℓ; auto].
    - repeat rewrite LMF.find_add_1; auto.
    -repeat rewrite LMF.find_add_2; auto.
     rewrite SameBalancerCombine with (ℓ := ℓ); auto. rewrite IHt0; [reflexivity|exists ℓ; auto].
  Qed.

  Theorem LiftChoiceTyping : forall (ct : LM.t nat) (cs : LM.t (list LRChoice)), ChoiceTyping ct cs -> LaxChoiceTyping ct cs.
  Proof using.
    unfold ChoiceTyping; unfold LaxChoiceTyping; intros ct cs ct_cs l n mt.
    destruct ct_cs as [cs_to_ct ct_to_cs]. apply ct_to_cs in mt. destruct mt as [chs H]; destruct H as [length_chs mt]; subst.
    exists chs; split; auto.
  Qed.

  Equations RunLaxTypedChoices (t : IChoiceTree) (cs : LM.t (list LRChoice)) (ct: LaxChoiceTyping (LaxChoiceTypeOf t) cs) : Proc :=
    {
      RunLaxTypedChoices (ICTLeaf l P Q) cs ct with inspect (LM.find l cs) :=
        {
        RunLaxTypedChoices (ICTLeaf l P Q) cs ct (exist _ (Some (L :: ℓ)) _) := P;
        RunLaxTypedChoices (ICTLeaf l P Q) cs ct (exist _ (Some (R :: ℓ)) _) := Q;
        RunLaxTypedChoices (ICTLeaf l P Q) cs ct (exist _ _ eq) := _
        };
      RunLaxTypedChoices (ICTBranch l t1 t2) cs ct with inspect (LM.find l cs) :=
        {
        RunLaxTypedChoices (ICTBranch l t1 t2) cs ct (exist _ (Some (L :: lcs)) _) := RunLaxTypedChoices t1 (LM.add l lcs cs) _;
        RunLaxTypedChoices (ICTBranch l t1 t2) cs ct (exist _ (Some (R :: rcs)) _) := RunLaxTypedChoices t2 (LM.add l rcs cs) _;
        RunLaxTypedChoices (ICTBranch l t1 t2) cs ct (exist _ _ eq) := _
        }
    }.
  Next Obligation.
    unfold LaxChoiceTyping in ct.
    specialize (ct l 1 (LM.add_1 LM.empty l 1)).
    exfalso; destruct ct as [chs H]; destruct H as [length_chs mt].
    apply LM.find_1 in mt; rewrite mt in eq; inversion eq; subst. inversion length_chs.
  Defined.
  Next Obligation.
    unfold LaxChoiceTyping in ct; specialize (ct l 1 (LM.add_1 LM.empty l 1)).
    exfalso; destruct ct as [chs H]; destruct H as [length_chs mt].
    apply LM.find_1 in mt; rewrite mt in eq; inversion eq; subst.
  Defined.
  Next Obligation.
    exfalso; unfold LaxChoiceTyping in ct.
    destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:e.
    all: specialize (ct l _ (LM.add_1 _ l _)); destruct ct as [chs H]; destruct H as [length_chs mt].
    all: apply LM.find_1 in mt; rewrite mt in eq; inversion eq; subst; inversion length_chs.
  Defined.
  Next Obligation.
    destruct (L.eq_dec l0 l); subst.
    - exists lcs. unfold CombineChoiceTypes at 1 in ct; rewrite LM.map2_1 in ct; [|left; exists n; auto]; rewrite (LM.find_1 H) in ct.
      destruct (LM.find l (LaxChoiceTypeOf t2)) eqn:eq2.
      -- unfold LaxChoiceTyping in ct. specialize (ct l _ (@LM.add_1 nat _ l _)).
         let H := fresh "H" in (destruct ct as [chs H]; destruct H as [length_chs mt]).
         apply LM.find_1 in mt; rewrite mt in wildcard; inversion wildcard; subst.
         split; [|apply LM.add_1]. cbn in length_chs. transitivity (PeanoNat.Nat.max n n0); lia.
      -- unfold LaxChoiceTyping in ct. split; [|apply LM.add_1].
         specialize (ct l (S n) (@LM.add_1 nat _ l _)). destruct ct as [chs H0]; destruct H0 as [length_chs mt].
         apply LM.find_1 in mt; rewrite mt in wildcard; inversion wildcard; subst. cbn in length_chs; lia.
    - destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:eq.
      all:unfold LaxChoiceTyping in ct;
        destruct (LM.find l0 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:eq'.
      all: unfold CombineChoiceTypes in eq'; rewrite LM.map2_1 in eq'; [| left; exists n; auto]; rewrite (LM.find_1 H) in eq';
        destruct (LM.find l0 (LaxChoiceTypeOf t2)) eqn:eq''; inversion eq'; subst.
      assert (LM.MapsTo l0 (PeanoNat.Nat.max n n3) (LM.add l (S n1) (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|left; exists n; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      2: assert (LM.MapsTo l0 n2 (LM.add l (S n1) (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|left; exists n2; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      3: assert (LM.MapsTo l0 (PeanoNat.Nat.max n n2) (LM.add l 1 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|left; exists n; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      4: assert (LM.MapsTo l0 n1 (LM.add l 1 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|left; exists n1; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      all: specialize (ct l0 _ H0); let H := fresh in destruct ct as [chs H]; destruct H as [length_chs mt].
      all: exists chs; split; [lia| apply LM.add_2; auto].
  Defined.
  Next Obligation.
   destruct (L.eq_dec l0 l); subst.
    - exists rcs. unfold CombineChoiceTypes at 1 in ct; rewrite LM.map2_1 in ct; [|right; exists n; auto]. 
      destruct (LM.find l (LaxChoiceTypeOf t1)) eqn:eq1; rewrite (LM.find_1 H) in ct.
      -- unfold LaxChoiceTyping in ct. specialize (ct l _ (@LM.add_1 nat _ l _)).
         let H := fresh "H" in (destruct ct as [chs H]; destruct H as [length_chs mt]).
         apply LM.find_1 in mt; rewrite mt in wildcard0; inversion wildcard0; subst.
         split; [|apply LM.add_1]. cbn in length_chs. transitivity (PeanoNat.Nat.max n n0); lia.
      -- unfold LaxChoiceTyping in ct. split; [|apply LM.add_1].
         specialize (ct l (S n) (@LM.add_1 nat _ l _)). destruct ct as [chs H0]; destruct H0 as [length_chs mt].
         apply LM.find_1 in mt; rewrite mt in wildcard0; inversion wildcard0; subst. cbn in length_chs; lia.
    - destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:eq.
      all:unfold LaxChoiceTyping in ct;
        destruct (LM.find l0 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:eq'.
      all: unfold CombineChoiceTypes in eq'; rewrite LM.map2_1 in eq'; [| right; exists n; auto]; 
        destruct (LM.find l0 (LaxChoiceTypeOf t1)) eqn:eq''; rewrite (LM.find_1 H) in eq'; inversion eq'; subst.
      assert (LM.MapsTo l0 (PeanoNat.Nat.max n3 n) (LM.add l (S n1) (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      2: assert (LM.MapsTo l0 n2 (LM.add l (S n1) (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n2; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      3: assert (LM.MapsTo l0 (PeanoNat.Nat.max n2 n) (LM.add l 1 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      4: assert (LM.MapsTo l0 n1 (LM.add l 1 (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2)))) as H0
          by (apply LM.add_2; auto; unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n1; auto]; rewrite (LM.find_1 H); rewrite eq''; auto).
      all: specialize (ct l0 _ H0); let H := fresh in destruct ct as [chs H]; destruct H as [length_chs mt].
      all: exists chs; split; [lia| apply LM.add_2; auto].
  Defined.
  Next Obligation.
    exfalso; unfold LaxChoiceTyping in ct.
    destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t1) (LaxChoiceTypeOf t2))) eqn:eq'.
    specialize (ct l (S n) ltac:(apply LM.add_1)); destruct ct as [chs H]; destruct H as [length_chs mt]; apply LM.find_1 in mt; rewrite mt in eq; inversion eq.
    specialize (ct l 1 ltac:(apply LM.add_1));destruct ct as [chs H]; destruct H as [length_chs mt]; apply LM.find_1 in mt; rewrite mt in eq; inversion eq.
  Defined.

  Definition EquivalentChoices : LM.t (list LRChoice) -> LM.t (list LRChoice) -> Prop :=
    fun (cs1 cs2 : LM.t (list LRChoice)) => forall l : L.t, LM.find l cs1 = LM.find l cs2 \/ (LM.find l cs1 = Some [] /\ LM.find l cs2 = None) \/ (LM.find l cs1 = None /\ LM.find l cs2 = Some []).
  Instance ec_refl : Reflexive EquivalentChoices.
  unfold Reflexive; unfold EquivalentChoices; intros cs l; left; reflexivity.
  Defined.
  Instance ec_sym : Symmetric EquivalentChoices.
  unfold Symmetric; unfold EquivalentChoices; intros cs1 cs2 ecs12 l.
  specialize (ecs12 l). destruct ecs12 as [eq | ecs12]; [left; auto|destruct ecs12 as [ecs12 | ecs12]; destruct ecs12; right; [right | left]]; split; auto.
  Defined.
  Instance ec_trans : Transitive EquivalentChoices.
  unfold Transitive; unfold EquivalentChoices; intros cs1 cs2 cs3 ecs12 ecs23 l.
  specialize (ecs12 l); specialize (ecs23 l).
  destruct ecs12 as [eq | ecs12]; [|destruct ecs12 as [ecs12 | ecs12]; destruct ecs12].
  all: destruct ecs23 as [eq' | ecs23]; [|destruct ecs23 as [ecs23 | ecs23]; destruct ecs23].
  - left; transitivity (LM.find l cs2); auto.
  - right; left; rewrite eq; rewrite H; split; auto.
  - right; right; split; [rewrite eq|]; auto.
  - right; left; split; [|rewrite <- eq']; auto.
  - rewrite H0 in H1; inversion H1.
  - left; rewrite H; rewrite H2; auto.
  - right; right; split; [|rewrite <- eq']; auto.
  - left; rewrite H; rewrite H2; auto.
  - right; right; split; auto.
  Defined.

  Lemma RemovePreservesEquivalentChoices : forall (cs1 cs2 : LM.t (list LRChoice)) (l : L.t), EquivalentChoices cs1 cs2 -> EquivalentChoices (LM.remove l cs1) (LM.remove l cs2).
  Proof using.
    intros cs1 cs2 l ecs; unfold EquivalentChoices in *; intro l'.
    destruct (L.eq_dec l l'); subst. left; repeat rewrite LMF.find_remove_1; reflexivity.
    repeat rewrite LMF.find_remove_2; auto.
  Qed.

  Lemma AddPreservesEquivalentChoices  : forall (cs1 cs2 : LM.t (list LRChoice)) (l : L.t) (ℓ : list LRChoice),
      EquivalentChoices cs1 cs2 -> EquivalentChoices (LM.add l ℓ cs1) (LM.add l ℓ cs2).
  Proof using.
    intros cs1 cs2 l ℓ ecs; unfold EquivalentChoices in *; intro l'.
    destruct (L.eq_dec l l'); subst. left; repeat rewrite LMF.find_add_1; reflexivity.
    repeat rewrite LMF.find_add_2; auto.
  Qed.
  
  Lemma RunChoicesEquivalentChoices : forall (t : IChoiceTree) (cs1 cs2 : LM.t (list LRChoice)), EquivalentChoices cs1 cs2 -> RunChoices t cs1 = RunChoices t cs2.
  Proof using.
    intros t; ICTInduction t; intros cs1 cs2 ecs; cbn.
    all: destruct (ecs l); [rewrite H | destruct H as [H | H]; destruct H as [eq1 eq2]; rewrite eq1; rewrite eq2]; auto.
    destruct (LM.find l cs2) as [ℓ|]; auto. destruct ℓ as [| chc ℓ]; [|destruct chc]; auto; destruct ℓ as [|chc ℓ].
    1,2: apply IHt0. 3,4: apply IHt1.
    1,3: apply RemovePreservesEquivalentChoices; auto.
    all: apply AddPreservesEquivalentChoices; auto.
  Qed.
    
    
  Theorem RunChoicesLaxTyping (t : IChoiceTree) (cs : LM.t (list LRChoice)) (ct : LaxChoiceTyping (LaxChoiceTypeOf t) cs)
    : RunChoices t cs = Some (RunLaxTypedChoices t cs ct).
  Proof using.
    funelim (RunLaxTypedChoices t cs ct); simp RunLaxTypedChoices.
    - exfalso. cbn in ct; unfold LaxChoiceTyping in ct; remember (ct t 1 ltac:(apply LM.add_1)) as H; clear HeqH.
      destruct H as [chs H]; destruct H as [len_chs mt]; apply LM.find_1 in mt; clear Heq Heqcall; rewrite mt in e; inversion e; subst.
      inversion len_chs.
    - rewrite Heq; cbn; rewrite e; auto.
    - rewrite Heq; cbn; rewrite e; auto.
    - exfalso; clear Heq Heqcall. cbn in ct; unfold LaxChoiceTyping in ct. specialize (ct t 1 ltac:(apply LM.add_1)).
      destruct ct as [chs H]; destruct H as [len mt]; apply LM.find_1 in mt; rewrite mt in e; inversion e.
    - exfalso; clear Heq Heqcall. cbn in ct.
      destruct (LM.find t0 (CombineChoiceTypes (LaxChoiceTypeOf i) (LaxChoiceTypeOf i0))) eqn:eq.
      -- unfold LaxChoiceTyping in ct. specialize (ct t0 (S n) ltac:(apply LM.add_1)); destruct ct as [chs H]; destruct H as [len mt].
         apply LM.find_1 in mt; rewrite mt in e; inversion e; subst. inversion len.
      -- unfold LaxChoiceTyping in ct. specialize (ct t0 1 ltac:(apply LM.add_1)); destruct ct as [chs H]; destruct H as [len mt].
         apply LM.find_1 in mt; rewrite mt in e; inversion e; subst. inversion len.
    - rewrite Heq; cbn. rewrite e at 1.
      rewrite <- H.
      destruct l0; auto.
      apply RunChoicesEquivalentChoices. unfold EquivalentChoices; intro l.
      destruct (L.eq_dec l t0); subst.
      right; right; rewrite LMF.find_remove_1; rewrite LMF.find_add_1; split; reflexivity.
      left; rewrite LMF.find_remove_2; auto; rewrite LMF.find_add_2; auto.
    - rewrite Heq; cbn. rewrite e at 1. rewrite <- H.
      destruct l0; auto.
      apply RunChoicesEquivalentChoices. unfold EquivalentChoices; intro l.
      destruct (L.eq_dec l t0); subst.
      right; right; rewrite LMF.find_remove_1; rewrite LMF.find_add_1; split; reflexivity.
      left; rewrite LMF.find_remove_2; auto; rewrite LMF.find_add_2; auto.
    - exfalso. cbn in ct.
      clear Heq Heqcall.
      destruct (LM.find t0 (CombineChoiceTypes (LaxChoiceTypeOf i) (LaxChoiceTypeOf i0))) eqn:eq;
        unfold LaxChoiceTyping in ct; specialize (ct t0 _ ltac:(apply LM.add_1)); destruct ct as [chs H]; destruct H as [len mt];
          apply LM.find_1 in mt; rewrite mt in e; inversion e.
  Qed.

  Equations IChoiceDifferential (t : IChoiceTree) (l : L.t) (d : LRChoice) : option (Proc + IChoiceTree) :=
    {
      IChoiceDifferential (ICTLeaf l' P Q) l L with L.eq_dec l l' :=
        {
        IChoiceDifferential (ICTLeaf ?(l) P Q) l L (left eq_refl) := Some (inl P);
        IChoiceDifferential (ICTLeaf l' P Q) l L (right neq) := None
        };
      IChoiceDifferential (ICTLeaf l' P Q) l R with L.eq_dec l l' :=
        {
        IChoiceDifferential (ICTLeaf ?(l) P Q) l R (left eq_refl) := Some (inl Q);
        IChoiceDifferential (ICTLeaf l' P Q) l R (right neq) := None
        };
      IChoiceDifferential (ICTBranch l' t1 t2) l L with L.eq_dec l l' :=
        {
        IChoiceDifferential (ICTBranch ?(l) t1 t2) l L (left eq_refl) := Some (inr t1);
        IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) with IChoiceDifferential t1 l L :=
          {
          IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) None with IChoiceDifferential t2 l L :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) None None := None;
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) None (Some (inl Q)) := Some (inr (ICTLeaf l' (IChoiceTreeToProc t1) Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) None (Some (inr t2')) := Some (inr (ICTBranch l' t1 t2'))
            };
          IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inl P)) with IChoiceDifferential t2 l L :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inl P)) None := Some (inr (ICTLeaf l' P (IChoiceTreeToProc t2)));
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inl P)) (Some (inl Q)) := Some (inr (ICTLeaf l' P Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inl P)) (Some (inr t2')) := Some (inr (ICTLeaf l' P (IChoiceTreeToProc t2')))
            };
          IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inr t1')) with IChoiceDifferential t2 l L :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inr t1')) None := Some (inr (ICTBranch l' t1' t2));
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inr t1')) (Some (inl Q)) := Some (inr (ICTLeaf l' (IChoiceTreeToProc t1') Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l L (right neq) (Some (inr t1')) (Some (inr t2')) := Some (inr (ICTBranch l' t1' t2'))
            }
          }
        };
      IChoiceDifferential (ICTBranch l' t1 t2) l R with L.eq_dec l l' :=
        {
        IChoiceDifferential (ICTBranch ?(l) t1 t2) l R (left eq_refl) := Some (inr t1);
        IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) with IChoiceDifferential t1 l R :=
          {
          IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) None with IChoiceDifferential t2 l R :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) None None := None;
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) None (Some (inl Q)) := Some (inr (ICTLeaf l' (IChoiceTreeToProc t1) Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) None (Some (inr t2')) := Some (inr (ICTBranch l' t1 t2'))
            };
          IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inl P)) with IChoiceDifferential t2 l R :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inl P)) None := Some (inr (ICTLeaf l' P (IChoiceTreeToProc t2)));
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inl P)) (Some (inl Q)) := Some (inr (ICTLeaf l' P Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inl P)) (Some (inr t2')) := Some (inr (ICTLeaf l' P (IChoiceTreeToProc t2')))
            };
          IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inr t1')) with IChoiceDifferential t2 l R :=
            {
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inr t1')) None := Some (inr (ICTBranch l' t1' t2));
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inr t1')) (Some (inl Q)) := Some (inr (ICTLeaf l' (IChoiceTreeToProc t1') Q));
            IChoiceDifferential (ICTBranch l' t1 t2) l R (right neq) (Some (inr t1')) (Some (inr t2')) := Some (inr (ICTBranch l' t1' t2'))
            }
          }
        }
    }.
  Lemma IChoiceDifferentialDefined : forall t l d, IsDecider l t -> IChoiceDifferential t l d <> None.
  Proof using.
    intros t l d id; funelim (IChoiceDifferential t l d); simp IChoiceDifferential.
    all: try (rewrite Heq; cbn; discriminate).
    all: try (rewrite Heq1; cbn; rewrite Heq0; cbn; rewrite Heq; cbn; discriminate).
    all: try (exfalso; inversion id; subst; destruct (L.eq_dec t t); [inversion Heq| apply n0; reflexivity]).
    all: inversion id; subst; [exfalso; apply n; reflexivity | specialize (Hind0 H1); exfalso; apply Hind0; auto | specialize (Hind H1); exfalso; apply Hind; auto]. 
  Qed.
  Corollary IChoiceDifferentialNotDefined : forall t l d, IChoiceDifferential t l d = None -> ~ IsDecider l t.
  Proof using.
    intros t l d eq H; eapply IChoiceDifferentialDefined; eauto.
  Qed.

  Lemma IChoiceDifferentialDefinedExact : forall t l d, ~ IsDecider l t -> IChoiceDifferential t l d = None.
  Proof using.
    intros t l d nid; funelim (IChoiceDifferential t l d); simp IChoiceDifferential.
    all: try (exfalso; apply nid; constructor; auto; fail).
    all: try (rewrite Heq; cbn; auto).
    all: repeat match goal with
                | [ H1 : ?A = Some _, H2 : ?B -> ?A = None, H3 : ?B |- _ ] => specialize (H2 H3); rewrite H2 in H1; inversion H1
                | [ n : ~ IsDecider ?l (ICTBranch ?l' ?t1 ?t2) |- _ ] =>
                  match goal with
                  | [ _ : ~ IsDecider l t1, _ : ~ IsDecider l t2 |- _] => fail 1
                  | _ => 
                    assert (~ IsDecider l t1) by (let H := fresh in intro H; apply n; constructor; auto; fail);
                      assert (~ IsDecider l t2) by (let H := fresh in intro H; apply n; constructor; auto; fail)
                  end
                end.
    all: rewrite Heq1; cbn; rewrite Heq0; cbn; rewrite Heq; cbn; auto.
  Qed.
  
  Fixpoint IChoiceTreeSize (t : IChoiceTree) :=
    match t with
    | ICTLeaf _ _ _ => 1
    | ICTBranch _ t1 t2 => S (IChoiceTreeSize t1 + IChoiceTreeSize t2)
    end.

  Lemma IChoiceTreeSizeNeverZero : forall t : IChoiceTree, IChoiceTreeSize t <> 0.
  Proof using.
    intro t; destruct t; cbn; intro H; inversion H.
  Qed.

  Lemma IChoiceDifferentialReducesSize : forall t l d t', IChoiceDifferential t l d = Some (inr t') -> lt (IChoiceTreeSize t') (IChoiceTreeSize t).
  Proof using.
    intros t l d t'; funelim (IChoiceDifferential t l d); simp IChoiceDifferential; intro eq; cbn.
    all: try (rewrite Heq in eq; cbn in eq).
    all: try (inversion eq; fail).
    all: try (inversion eq; subst; lia; fail).
    all: try (simp IChoiceDifferential in Heqcall; rewrite <- Heqcall in eq; inversion eq).
    all: try (cbn; destruct (IChoiceTreeSize i) eqn:eq'; [exfalso; apply (IChoiceTreeSizeNeverZero i); auto | lia]).
    all: try (cbn; specialize (Hind i2 Heq); specialize (Hind0 i1 Heq0); lia).
    1,3: cbn; specialize (Hind0 i1 Heq0); lia.
    all: cbn; specialize (Hind i1 Heq); lia.
  Qed.

  Definition InverseChoice : LRChoice -> LRChoice :=
    fun d => match d with
          | L => R
          | R => L
          end.

  Lemma DifferentialLeftProc : forall t l P, IChoiceDifferential t l L = Some (inl P) -> exists Q, t = ICTLeaf l P Q.
  Proof using.
    intros t l P eq; funelim (IChoiceDifferential t l L); simp IChoiceDifferential in eq;
      try match goal with
          | [ H : L = R |- _ ] => inversion H
          | [ H : R = L |- _ ] => inversion H
          | [ H : L = L |- _ ] => clear H
          end.
    all: try (rewrite Heq in eq; cbn in eq; inversion eq;
              match goal with
              | [ |- exists Q : Proc, ICTLeaf ?l ?P ?R = ICTLeaf ?l ?P Q ] => exists R; reflexivity
              end).
    all: rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq.
  Qed.
  Lemma DifferentialRightProc : forall t l Q, IChoiceDifferential t l R = Some (inl Q) -> exists P, t = ICTLeaf l P Q.
  Proof using.
    intros t l P eq; funelim (IChoiceDifferential t l R); simp IChoiceDifferential in eq;
      try match goal with
          | [ H : L = R |- _ ] => inversion H
          | [ H : R = L |- _ ] => inversion H
          | [ H : L = L |- _ ] => clear H
          | [ H : R = R |- _ ] => clear H
          end.
    all: try (rewrite Heq in eq; cbn in eq; inversion eq;
              match goal with
              | [ |- exists P : Proc, ICTLeaf ?l ?R ?Q = ICTLeaf ?l P ?Q ] => exists R; reflexivity
              end).
    all: try (rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq; fail).
  Qed.
  Lemma DifferentialLiftDecider : forall t l d t', IChoiceDifferential t l d = Some (inr t') -> forall l', IsDecider l' t' -> IsDecider l' t.
  Proof using.
    intros t l d t' eq (* it *) l' dcdr; funelim (IChoiceDifferential t l d); simp IChoiceDifferential in eq; try (inversion eq; fail); try (constructor; auto; fail).
    all: try (rewrite Heq in eq; cbn in eq;  inversion eq; subst; constructor; auto; fail).
    all: rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq;
              inversion eq; subst.
    all: try (inversion dcdr; subst; apply DifferentialLeftProc in Heq;
              destruct Heq as [Q eq']; subst; constructor; constructor; auto; fail).
    all: try (inversion dcdr; subst; apply DifferentialLeftProc in Heq0;
              destruct Heq0 as [Q eq']; subst; constructor; constructor; auto; fail).
    all: try (inversion dcdr; subst; constructor; auto; fail).
    all: inversion dcdr; subst; [constructor | |]; try (constructor; auto; fail).
    all: try (specialize (Hind0 i1 Heq0 l' H1); constructor; auto; fail).
    all: try (specialize (Hind i2 Heq l' H1); constructor; auto; fail).
    all: try (specialize (Hind i1 Heq l' H1); constructor; auto; fail).
  Qed.
  (* Lemma DifferentialPreserveDecider : forall t l d t', IChoiceDifferential t l d = Some (inr t') -> forall l', IsDecider l' t -> IsDecider l' t' \/ (l = l' /\ NumberOfChoices t l' = 1). *)
  (* Proof using. *)
  (*   intros t l d t' eq l' id; funelim (IChoiceDifferential t l d); simp IChoiceDifferential in eq; cbn. *)
  (*   all: try (rewrite Heq in eq; cbn in eq; inversion eq; subst). *)
  (*   inversion id; subst.  *)
    

  Lemma DifferentialFewerChoices : forall t l d t' l', IChoiceDifferential t l d = Some (inr t') -> le (NumberOfChoices t' l') (NumberOfChoices t l').
  Proof using.
    intros t l d t' l' eq; funelim (IChoiceDifferential t l d); simp IChoiceDifferential in eq; cbn; try lia.
    all: try (rewrite Heq in eq; cbn in eq; inversion eq; fail).
    all: try (rewrite Heq in eq; cbn in eq; inversion eq; subst; lia).
    all: rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq; subst; cbn; try lia.
    all: try specialize (Hind _ l' Heq).
    all: try specialize (Hind0 _ l' Heq0).
    all: try (cbn; lia).
  Qed.
  Lemma NumberOfChoicesDecider : forall t l, IsDecider l t -> NumberOfChoices t l <> 0.
  Proof using.
    intro t; ICTInduction t; intros l' dcdr; inversion dcdr; subst; cbn.
    - destruct (L.eq_dec l l). lia. exfalso; apply n; reflexivity.
    - destruct (L.eq_dec l l). lia. exfalso; apply n; reflexivity.
    - specialize (IHt0 l' H1). destruct (L.eq_dec l' l); lia.
    - specialize (IHt1 l' H1). destruct (L.eq_dec l' l); lia.
  Qed.

  Lemma NumberOfChoicesNonDecider : forall t l, ~ IsDecider l t -> NumberOfChoices t l = 0.
  Proof using.
    intro t; ICTInduction t; intros l' nd; cbn; destruct (L.eq_dec l' l); auto; subst;
      try (exfalso; apply nd; constructor; fail).
    rewrite IHt0. rewrite IHt1. lia.
    all: intro H; apply nd; constructor; auto; fail.
  Qed.

  Lemma DifferentialStrictlyFewerChoices : forall t l d t', IChoiceDifferential t l d = Some (inr t') -> lt (NumberOfChoices t' l) (NumberOfChoices t l).
  Proof using.
    intros t l d t' eq; funelim (IChoiceDifferential t l d); simp IChoiceDifferential in eq; cbn in *; try lia.
    all: try (rewrite Heq in eq; cbn in eq; inversion eq; subst); try lia.
    all: try rewrite Heq; try lia.
    all: rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq; subst; cbn; try lia.
    all: try (destruct (NumberOfChoices i l) eqn:eq';
      try match goal with
          | [ H : NumberOfChoices ?a ?l = 0, H' : IChoiceDifferential ?a ?l ?D = Some _ |- _ ] =>
            let H'' := fresh in
            let e := fresh "e" in
            let n := fresh "n" in
            assert (IsDecider l a) as H'' by (destruct (IsDeciderDec l a) as [e | n]; auto; apply IChoiceDifferentialDefinedExact with (d := D) in n; rewrite n in H'; inversion H');
              apply NumberOfChoicesDecider in H''; apply H'' in H; destruct H
          end; lia).
    all: try (specialize (Hind i2 Heq)); try (specialize (Hind0 i1 Heq0)); try lia.
    all: match goal with
         | [ H: IChoiceDifferential ?t ?l ?d = None |- _ ] => apply IChoiceDifferentialNotDefined in H; apply NumberOfChoicesNonDecider in H; rewrite H in *
         end; try lia.
    all: repeat match goal with
                | [ H : IChoiceDifferential ?t ?l L = Some (inl _) |- _ ] =>
                  let Q := fresh "Q" in
                  let H' := fresh H in 
                  apply DifferentialLeftProc in H; destruct H as [Q H']; subst; cbn
                | [ H : IChoiceDifferential ?t ?l R = Some (inl _) |- _ ] =>
                  let P := fresh "P" in
                  let H' := fresh H in 
                  apply DifferentialRightProc in H; destruct H as [Q H']; subst; cbn
                | [|- context[L.eq_dec ?l ?l]] => let e := fresh "e" in let n := fresh "n" in destruct (L.eq_dec l l) as [e | n]; [|exfalso; apply n; auto]
                end; try lia.
    all: repeat rewrite PeanoNat.Nat.max_0_l.
    all: specialize (Hind i1 Heq); lia.
  Qed.

  Notation "( a ; b )" := (exist _ a b).    

  Local Obligation Tactic := Coq.Program.Tactics.program_simpl; try lia.
  Equations SortICTHelper (t : IChoiceTree) (elts : list (L.t * nat)) : option IChoiceTree by wf (IChoiceTreeSize t + length elts) lt :=
    {
      SortICTHelper t [] := None;
      SortICTHelper t ((l, 0) :: elts) := SortICTHelper t elts;
      SortICTHelper t ((l, S n) :: elts) with inspect (IChoiceDifferential t l L) :=
        {
        SortICTHelper t ((l, S n) :: elts) (None; eq1) := SortICTHelper t elts;
        SortICTHelper t ((l, S n) :: elts) ((Some (inl P)); eq1) with inspect (IChoiceDifferential t l R) :=
          {
          SortICTHelper t ((l, S n) :: elts) ((Some (inl P)); eq1) (None; eq2) := SortICTHelper t elts;
          SortICTHelper t ((l, S n) :: elts) ((Some (inl P)); eq1) ((Some (inl Q)); eq2) := Some (ICTLeaf l P Q);
          SortICTHelper t ((l, S n) :: elts) ((Some (inl P)); eq1) ((Some (inr t2)); eq2) := Some (ICTLeaf l P (IChoiceTreeToProc t2))
          };
        SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) with inspect (IChoiceDifferential t l R) :=
          {
          SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) (None; eq2) := SortICTHelper t elts;
          SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inl Q)); eq2) := Some (ICTLeaf l (IChoiceTreeToProc t1) Q);
          SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inr t2)); eq2) with SortICTHelper t1 ((l, n) :: elts) :=
            {
            SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inr t2)); eq2) None := None;
            SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inr t2)); eq2) (Some t1') with SortICTHelper t2 ((l, n) :: elts) :=
              {
              SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inr t2)); eq2) (Some t1') None := None;
              SortICTHelper t ((l, S n) :: elts) ((Some (inr t1)); eq1) ((Some (inr t2)); eq2) (Some t1') (Some t2') := Some (ICTBranch l t1' t2')
              }
            }
          }
        }
    }.
  Next Obligation.
    assert (lt (IChoiceTreeSize t1) (IChoiceTreeSize t)) by (eapply IChoiceDifferentialReducesSize; eauto); lia.
  Defined.  
  Next Obligation.
    assert (lt (IChoiceTreeSize t2) (IChoiceTreeSize t)) by (eapply IChoiceDifferentialReducesSize; eauto); lia.
  Defined.
  
  Definition CorrectElts (t : IChoiceTree) (elts : list (L.t * nat)) : Prop :=
    (forall l, IsDecider l t -> exists n, (le (NumberOfChoices t l) n) /\ In (l, n) elts)
    /\ (forall l n, In (l, n) elts -> le (NumberOfChoices t l) n)
    /\ (NoDupA (fun pr1 pr2 => fst pr1 = fst pr2) elts).

  Lemma CorrectEltsNeverNil : forall (t : IChoiceTree), ~CorrectElts t [].
  Proof using.
    intro t; ICTInduction t; intro cet; destruct cet as [elts_compl cet'];
      specialize (elts_compl l ltac:(constructor)); destruct elts_compl as [n H]; destruct H as [leq i]; destruct i.
  Qed.
  
  Lemma SortICTHelperDefined : forall t elts, CorrectElts t elts -> exists t' : IChoiceTree, SortICTHelper t elts = Some t'.
  Proof using.
    intros t elts corr_elts; funelim (SortICTHelper t elts); simp SortICTHelper.
    exfalso; apply CorrectEltsNeverNil with (t := t); auto.
    all: try (rewrite Heq0; cbn; rewrite Heq; cbn; match goal with
                                                   | [|- exists t', Some ?a = Some t' ] => exists a; reflexivity
                                                   end).
    all: let H := fresh in unfold CorrectElts in corr_elts; destruct corr_elts as [elts_compl H]; destruct H as [elts_sound elts_nodup].
    all: try ( rewrite Heq2; cbn; rewrite Heq1; cbn; rewrite Heq0; cbn; rewrite Heq;cbn; eexists; reflexivity).
    - apply H; unfold CorrectElts; split; [|split].
      -- intros l' id. specialize (elts_compl l' id). destruct elts_compl as [n ec]; destruct ec as [num_choices i].
         destruct i as [e | i]. inversion e; subst. apply Le.le_n_0_eq in num_choices. apply NumberOfChoicesDecider in id. symmetry in num_choices; apply id in num_choices; destruct num_choices.
         exists n; split; auto.
      -- intros l' n i; apply elts_sound; right; auto.
      -- inversion elts_nodup; subst; auto.
    - rewrite Heq; cbn. apply H. unfold CorrectElts; split; [|split].
      -- intros l' id. specialize (elts_compl l' id). destruct elts_compl as [m H']; destruct H' as [nc i].
         destruct i as [eq | i]; [inversion eq; subst; clear eq|]; [|exists m; split; auto].
         clear Heq; apply IChoiceDifferentialNotDefined in e; apply e in id; destruct id.
      -- intros l' m i. apply elts_sound; auto. right; auto.
      -- inversion elts_nodup; auto.
    - clear Heq Heq0; apply IChoiceDifferentialNotDefined in e0; apply IChoiceDifferentialDefinedExact with (d := L) in e0; rewrite e0 in e; inversion e.
    - clear Heq Heq0; apply IChoiceDifferentialNotDefined in e0; apply IChoiceDifferentialDefinedExact with (d := L) in e0; rewrite e0 in e; inversion e.
    - destruct Hind as [t' Ht']; [|rewrite Ht' in Heq; inversion Heq].
      unfold CorrectElts; split; [|split]; [| | inversion elts_nodup; subst; auto].
      -- intros l' id. assert (IsDecider l' t) as id' by (apply DifferentialLiftDecider with (t := t) (l := t0) (d := L) in id; auto); specialize (elts_compl l' id').
         destruct elts_compl as [m H]; destruct H as [nc in_l]. destruct in_l as [eq | in_l]; [inversion eq; subst; clear eq|].
         exists n; split; [|left; auto]. clear Heq1; apply DifferentialStrictlyFewerChoices in e; lia.
         clear Heq1; apply DifferentialFewerChoices with (l' := l') in e; exists m; split; [lia | right; auto].
      -- intros l' m in_l; destruct in_l as [eq | in_l]; [inversion eq; subst; clear eq|].
         specialize (elts_sound l' (S m) ltac:(left; auto)); clear Heq1; apply DifferentialStrictlyFewerChoices in e; lia.
         specialize (elts_sound l' m ltac:(right; auto)); clear Heq1; apply DifferentialFewerChoices with (l' := l') in e; lia.
      -- constructor; auto. intro HA; apply H1. inversion HA; subst; try (constructor; auto; fail). apply InA_cons_tl; apply InA_eqA with (x := (t0, n)); auto.
         split. unfold Reflexive; reflexivity. unfold Symmetric; intros a b eq; symmetry; auto. unfold Transitive; intros a b c eq1 eq2; transitivity (fst b); auto.
    - destruct Hind as [t' Ht']; [|rewrite Ht' in Heq; inversion Heq].
      unfold CorrectElts; split; [|split]; [| | inversion elts_nodup; subst; auto].
      -- intros l' id. assert (IsDecider l' t) as id' by (apply DifferentialLiftDecider with (t := t) (l := t0) (d := R) in id; auto); specialize (elts_compl l' id').
         destruct elts_compl as [m H]; destruct H as [nc in_l]. destruct in_l as [eq | in_l]; [inversion eq; subst; clear eq|].
         exists n; split; [|left; auto]. clear Heq1; apply DifferentialStrictlyFewerChoices in e0; lia.
         clear Heq1; apply DifferentialFewerChoices with (l' := l') in e0; exists m; split; [lia | right; auto].
      -- intros l' m in_l; destruct in_l as [eq | in_l]; [inversion eq; subst; clear eq|].
         specialize (elts_sound l' (S m) ltac:(left; auto)); clear Heq1; apply DifferentialStrictlyFewerChoices in e0; lia.
         specialize (elts_sound l' m ltac:(right; auto)); clear Heq1; apply DifferentialFewerChoices with (l' := l') in e0; lia.
      -- constructor; auto. intro HA; apply H1. inversion HA; subst; try (constructor; auto; fail). apply InA_cons_tl; apply InA_eqA with (x := (t0, n)); auto.
         split. unfold Reflexive; reflexivity. unfold Symmetric; intros a b eq; symmetry; auto. unfold Transitive; intros a b c eq1 eq2; transitivity (fst b); auto.
  Qed.

  Lemma LaxChoiceTypeOf_Decider : forall (t : IChoiceTree) (l : L.t), LM.In l (LaxChoiceTypeOf t) -> IsDecider l t.
  Proof using.
    intro t; ICTInduction t; intros l' in_lcto; cbn in *.
    destruct (L.eq_dec l l'); subst; [constructor|]. destruct in_lcto as [m mt]; apply LM.add_3 in mt; auto; apply LM.empty_1 in mt; destruct mt.
    destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t1))) eqn:eq.
    all: destruct (L.eq_dec l l'); subst; [constructor|]; destruct in_lcto as [m mt]; apply LM.add_3 in mt; auto.
    all: unfold CombineChoiceTypes in mt; destruct (LM.find l' (LaxChoiceTypeOf t0)) eqn:eq0.
    1,3: specialize (IHt0 _ ltac:(eexists; apply LM.find_2; eauto)); constructor; auto; fail.
    all: destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq1.
    1,3: specialize (IHt1 _ ltac:(eexists; apply LM.find_2; eauto)); constructor; auto; fail.
    all: apply LM.find_1 in mt; rewrite LMF.map2_3 in mt; auto; inversion mt.
  Qed.  

  Lemma LaxChoiceTypeOf_NumberOfChoices : forall (t : IChoiceTree) (l : L.t), IsDecider l t -> LM.MapsTo l (NumberOfChoices t l) (LaxChoiceTypeOf t).
  Proof using.
    intro t; ICTInduction t; intros l' id; cbn in *.
    - inversion id; subst. destruct (L.eq_dec l l); LocationOrder. apply LM.add_1.
    - destruct (LM.find l (CombineChoiceTypes (LaxChoiceTypeOf t0) (LaxChoiceTypeOf t1))) eqn:eq.
      -- unfold CombineChoiceTypes in eq. destruct (LM.find l (LaxChoiceTypeOf t0)) eqn:eq0.
         --- rewrite LM.map2_1 in eq; [|left; exists n0; apply LM.find_2; auto]. rewrite eq0 in eq.
             destruct (LM.find l (LaxChoiceTypeOf t1)) eqn:eq1; destruct (L.eq_dec l' l); subst; LocationOrder.
             ---- assert (IsDecider l t0) as id0 by (apply LaxChoiceTypeOf_Decider; eexists; apply LM.find_2; eauto).
                  assert (IsDecider l t1) as id1 by (apply LaxChoiceTypeOf_Decider; eexists; apply LM.find_2; eauto).
                  specialize (IHt0 l id0); specialize (IHt1 l id1).
                  apply LM.find_1 in IHt0; rewrite IHt0 in eq0; inversion eq0; subst; clear eq0.
                  apply LM.find_1 in IHt1; rewrite IHt1 in eq1; inversion eq1; subst; clear eq1.
                  cbn; apply LM.add_1.
             ---- cbn; apply LM.add_2; auto.
                  destruct (LM.find l' (LaxChoiceTypeOf t0)) eqn:eq0'.
                  apply LM.find_2; unfold CombineChoiceTypes; rewrite LM.map2_1; [|left; exists n; apply LM.find_2; auto].
                  rewrite eq0'.
                  all: destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq1'.
                  3: unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n; apply LM.find_2; auto]; rewrite eq0'; rewrite eq1'.
                  4: unfold CombineChoiceTypes; apply LM.find_2; rewrite LMF.map2_3; auto.
                  ----- apply LM.find_2 in eq0'. assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n3; apply LM.find_2; auto).
                  assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n; auto). specialize (IHt0 l' id0); specialize (IHt1 l' id1).
                  apply LM.find_1 in eq0'. apply LM.find_1 in IHt0; apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; rewrite IHt0 in eq0'; inversion eq1'; inversion eq0'; subst.
                  auto.
                  ----- assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n; apply LM.find_2; auto).
                  assert (~ IsDecider l' t1) as nid1 by (destruct (IsDeciderDec l' t1); auto; specialize (IHt1 l' i); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1').
                  specialize (IHt0 l' id0); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'. apply NumberOfChoicesNonDecider in nid1; rewrite nid1.
                  inversion eq0'; subst. rewrite Max.max_0_r; auto.
                  ----- assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n; apply LM.find_2; auto).
                  assert (~ IsDecider l' t0) as nid0 by (destruct (IsDeciderDec l' t0); auto; specialize (IHt0 l' i); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0').
                  specialize (IHt1 l' id1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'. apply NumberOfChoicesNonDecider in nid0; rewrite nid0.
                  inversion eq1'; subst. rewrite Max.max_0_l; auto.
                  ----- inversion id; subst; LocationOrder. specialize (IHt0 l' H1); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0'.
                  specialize (IHt1 l' H1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1'.
             ---- assert (~ IsDecider l t1) as nid1 by (destruct (IsDeciderDec l t1); auto; specialize (IHt1 l i); apply LM.find_1 in IHt1; rewrite IHt1 in eq1; inversion eq1).
                  assert (IsDecider l t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n; apply LM.find_2; auto).
                  apply NumberOfChoicesNonDecider in nid1; rewrite nid1. specialize (IHt0 l id0); apply LM.find_1 in IHt0; rewrite IHt0 in eq0; inversion eq0; subst.
                  rewrite Max.max_0_r. cbn; apply LM.add_1.
             ---- cbn; apply LM.add_2; auto.
                  destruct (LM.find l' (LaxChoiceTypeOf t0)) eqn:eq0'.
                  apply LM.find_2; unfold CombineChoiceTypes; rewrite LM.map2_1; [|left; exists n0; apply LM.find_2; auto].
                  rewrite eq0'.
                  all: destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq1'.
                  3: unfold CombineChoiceTypes; apply LM.find_2; rewrite LM.map2_1; [|right; exists n0; apply LM.find_2; auto]; rewrite eq0'; rewrite eq1'.
                  4: unfold CombineChoiceTypes; apply LM.find_2; rewrite LMF.map2_3; auto.
                  ----- apply LM.find_2 in eq0'. assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n2; apply LM.find_2; auto).
                  assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n0; auto). specialize (IHt0 l' id0); specialize (IHt1 l' id1).
                  apply LM.find_1 in eq0'. apply LM.find_1 in IHt0; apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; rewrite IHt0 in eq0'; inversion eq1'; inversion eq0'; subst; auto.
                  ----- assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n0; apply LM.find_2; auto).
                  assert (~ IsDecider l' t1) as nid1 by (destruct (IsDeciderDec l' t1); auto; specialize (IHt1 l' i); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1').
                  specialize (IHt0 l' id0); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'. apply NumberOfChoicesNonDecider in nid1; rewrite nid1.
                  inversion eq0'; subst. rewrite Max.max_0_r; auto.
                  ----- assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n0; apply LM.find_2; auto).
                  assert (~ IsDecider l' t0) as nid0 by (destruct (IsDeciderDec l' t0); auto; specialize (IHt0 l' i); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0').
                  specialize (IHt1 l' id1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'. apply NumberOfChoicesNonDecider in nid0; rewrite nid0.
                  inversion eq1'; subst. rewrite Max.max_0_l; auto.
                  ----- inversion id; subst; LocationOrder. specialize (IHt0 l' H1); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0'.
                  specialize (IHt1 l' H1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1'.
         --- destruct (LM.find l (LaxChoiceTypeOf t1)) eqn:eq1; destruct (L.eq_dec l' l); subst; LocationOrder.
             3,4: rewrite LMF.map2_3 in eq; auto; inversion eq.
             1,2: rewrite LM.map2_1 in eq; [| right; exists n0; apply LM.find_2; auto]; rewrite eq0 in eq; rewrite eq1 in eq.
             ---- inversion eq; subst; clear eq.
                  assert (~ IsDecider l t0) as nid0 by (destruct (IsDeciderDec l t0); auto; specialize (IHt0 l i); apply LM.find_1 in IHt0; rewrite IHt0 in eq0; inversion eq0).
                  assert (IsDecider l t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n; apply LM.find_2; auto).
                  apply NumberOfChoicesNonDecider in nid0; rewrite nid0; rewrite Max.max_0_l.
                  specialize (IHt1 l id1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1; inversion eq1; subst.
                  cbn; apply LM.add_1.
             ---- cbn; apply LM.add_2; auto.
                  destruct (LM.find l' (LaxChoiceTypeOf t0)) eqn:eq0'; destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq1'; unfold CombineChoiceTypes; apply LM.find_2; [| | | rewrite LMF.map2_3; auto]; try (rewrite LM.map2_1; [| left; exists n2; apply LM.find_2; auto; fail]); try (rewrite LM.map2_1; [| right; exists n2; apply LM.find_2; auto; fail]).
                  all: try (rewrite eq0'; rewrite eq1').
                  ----- assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n2; apply LM.find_2; auto).
                  assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n3; apply LM.find_2; auto).
                  specialize (IHt0 l' id0); specialize (IHt1 l' id1); apply LM.find_1 in IHt0; apply LM.find_1 in IHt1; rewrite IHt0 in eq0'; rewrite IHt1 in eq1';
                    inversion eq0'; inversion eq1'; subst; auto.
                  ----- assert (IsDecider l' t0) as id0 by (apply LaxChoiceTypeOf_Decider; exists n2; apply LM.find_2; auto).
                  assert (~ IsDecider l' t1) as nid1 by (destruct (IsDeciderDec l' t1); auto; specialize (IHt1 l' i); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1').
                  specialize (IHt0 l' id0); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0'; subst.
                  apply NumberOfChoicesNonDecider in nid1; rewrite nid1; rewrite Max.max_0_r; auto.
                  ----- assert (IsDecider l' t1) as id1 by (apply LaxChoiceTypeOf_Decider; exists n2; apply LM.find_2; auto).
                  assert (~ IsDecider l' t0) as nid0 by (destruct (IsDeciderDec l' t0); auto; specialize (IHt0 l' i); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0').
                  specialize (IHt1 l' id1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1'; subst.
                  apply NumberOfChoicesNonDecider in nid0; rewrite nid0; rewrite Max.max_0_l; auto.
                  ----- inversion id; LocationOrder. specialize (IHt0 l' H1); apply LM.find_1 in IHt0; rewrite IHt0 in eq0'; inversion eq0'.
                  specialize (IHt1 l' H1); apply LM.find_1 in IHt1; rewrite IHt1 in eq1'; inversion eq1'.
      -- destruct (L.eq_dec l' l); subst.
         --- unfold CombineChoiceTypes in eq.
             destruct (LM.find l (LaxChoiceTypeOf t0)) eqn:eq0; destruct (LM.find l (LaxChoiceTypeOf t1)) eqn:eq1.
             all: try (rewrite LM.map2_1 in eq; [|left; exists n; apply LM.find_2; auto; fail]); try (rewrite LM.map2_1 in eq; [|right; exists n; apply LM.find_2; auto; fail]);
               try (rewrite LMF.map2_3 in eq; [|auto; fail|auto;fail]); try (rewrite eq0 in eq; rewrite eq1 in eq); inversion eq.
             assert (~ IsDecider l t0) as nid0 by (destruct (IsDeciderDec l t0); auto; specialize (IHt0 l i); apply LM.find_1 in IHt0; rewrite IHt0 in eq0; inversion eq0).
             assert (~ IsDecider l t1) as nid1 by (destruct (IsDeciderDec l t1); auto; specialize (IHt1 l i); apply LM.find_1 in IHt1; rewrite IHt1 in eq1; inversion eq1).
             apply NumberOfChoicesNonDecider in nid0; rewrite nid0. apply NumberOfChoicesNonDecider in nid1; rewrite nid1; cbn. apply LM.add_1.
         --- apply LM.add_2; auto; cbn.
             unfold CombineChoiceTypes; apply LM.find_2.
             destruct (LM.find l' (LaxChoiceTypeOf t0)) eqn:eq0; destruct (LM.find l' (LaxChoiceTypeOf t1)) eqn:eq1.
             all: try (rewrite LM.map2_1; [|left; exists n0; apply LM.find_2; auto; fail]); try (rewrite LM.map2_1; [|right; exists n0; apply LM.find_2; auto; fail]);
               try (rewrite LMF.map2_3; [|auto; fail|auto;fail]); try (rewrite eq0; rewrite eq1).
             all: repeat match goal with
                         | [IH : forall l' : L.t, IsDecider l' ?t -> LM.MapsTo l' (NumberOfChoices ?t l') (LaxChoiceTypeOf ?t), eq : LM.find ?l (LaxChoiceTypeOf ?t) = Some _, H : IsDecider ?l ?t |- _] =>
                           specialize (IH l H); apply LM.find_1 in IH; rewrite IH in eq; inversion eq; subst

                         | [ H : LM.find ?l (LaxChoiceTypeOf ?t) = Some ?n |- _ ] =>
                           match goal with
                           | [ H' : IsDecider l t |- _ ] => fail 1
                           | _ => let id := fresh "id_" l "_" t in assert (IsDecider l t) as id by (apply LaxChoiceTypeOf_Decider; exists n; apply LM.find_2; auto)
                           end
                         | [ IH : forall l' : L.t, IsDecider l' ?t -> LM.MapsTo l' (NumberOfChoices ?t l') (LaxChoiceTypeOf ?t), H : LM.find ?l (LaxChoiceTypeOf ?t) = None |- _ ] =>
                           match goal with
                           | [ H' : ~ IsDecider l t |- _ ] => fail 1
                           | _ => let nid := fresh "nid_" l "_" t in
                                 assert (~ IsDecider l t) as nid
                                     by (let id := fresh "id" in destruct (IsDeciderDec l t) as [id | nid]; auto; specialize (IH l id);
                                                                apply LM.find_1 in IH; rewrite IH in H; inversion H)
                           end
                         | [ H : ~ IsDecider ?l ?t |- _ ] =>
                           match goal with
                           | [_ : NumberOfChoices t l = 0 |- _ ] => fail 1
                           | _ => let noc := fresh "noc_" t "_" l in assert (NumberOfChoices t l = 0) as noc by (apply NumberOfChoicesNonDecider in H; auto); try (rewrite noc in * )
                           end
                         | [|- context[Nat.max 0 _]] => rewrite Max.max_0_l
                         | [|- context[Nat.max _ 0]] => rewrite Max.max_0_r
                         end; auto.
             inversion id; subst; LocationOrder; match goal with | [H : ?P, H' : ~ ?P |- _] => exfalso; apply H'; exact H end.
  Qed.


  Lemma InAEqKeyElt : forall {elt: Set} a l, InA (@LM.eq_key_elt elt) a l -> In a l.
  Proof using.
    intros elt a l ia. induction ia.
    destruct y. unfold LM.eq_key_elt in H. cbn in H; destruct H; subst; left; auto. destruct a; cbn; auto.
    right; auto.
  Qed.
  Lemma LCTEltsCorrect : forall (t : IChoiceTree), CorrectElts t (LM.elements (LaxChoiceTypeOf t)).
  Proof using.
    intro t; unfold CorrectElts; split; [|split]; [| | apply LM.elements_3w].
    - intros l id. apply LaxChoiceTypeOf_NumberOfChoices in id. exists (NumberOfChoices t l); split; auto. apply LM.elements_1 in id.  apply InAEqKeyElt; auto.
    - intros l n H. apply @In_InA with (A := (L.t * nat)%type) (eqA := @LM.eq_key_elt (nat)) in H. apply LM.elements_2 in H.
      apply @LMF.MapsToUnique with (e1 := NumberOfChoices t l) in H; [subst;reflexivity |].
      apply LaxChoiceTypeOf_NumberOfChoices. apply LaxChoiceTypeOf_Decider. exists n; auto.
      split; unfold LM.eq_key_elt. unfold Reflexive; intro x; split; reflexivity. unfold Symmetric; intros x y H'; destruct H'; split; symmetry; auto.
      unfold Transitive; intros x y z H1 H2; destruct H1; destruct H2; split; etransitivity; eauto.
  Qed.

  Program Definition SortICTree (t : IChoiceTree) : IChoiceTree :=
    match SortICTHelper t (LM.elements (LaxChoiceTypeOf t)) as ot return (SortICTHelper t (LM.elements (LaxChoiceTypeOf t))) = ot -> IChoiceTree with
    | Some t' => fun _ => t'
    | None => fun eq => match _ : False with end
    end eq_refl.
  Next Obligation.
    destruct (SortICTHelperDefined t (LM.elements (LaxChoiceTypeOf t))); [apply LCTEltsCorrect|].
    rewrite H in eq; inversion eq.
  Qed.

  Equations ConformToBalancer (t : IChoiceTree) (ℓ : list L.t) : option IChoiceTree :=
    {
      ConformToBalancer (ICTLeaf l P Q) [] := None;
      ConformToBalancer (ICTLeaf l P Q) [l'] with L.eq_dec l l' :=
        {
        ConformToBalancer (ICTLeaf l P Q) [?(l)] (left eq_refl) := Some (ICTLeaf l P Q);
        ConformToBalancer (ICTLeaf l P Q) [l'] (right neq) := None
        };
      ConformToBalancer (ICTLeaf l P Q) _ := None;
      ConformToBalancer (ICTBranch t t1 t2) [] := None;
      ConformToBalancer (ICTBranch l t1 t2) (l' :: ℓ') with L.eq_dec l l' :=
        {
        ConformToBalancer (ICTBranch l t1 t2) [?(l)] (left eq_refl) := Some (ICTLeaf l (IChoiceTreeToProc t1) (IChoiceTreeToProc t2));
        ConformToBalancer (ICTBranch l t1 t2) (?(l) :: l' :: ℓ') (left eq_refl) with ConformToBalancer t1 (l' :: ℓ') :=
          {
          ConformToBalancer (ICTBranch l t1 t2) (?(l) :: l' :: ℓ') (left eq_refl) None := None;
          ConformToBalancer (ICTBranch l t1 t2) (?(l) :: l' :: ℓ') (left eq_refl) (Some t1') with ConformToBalancer t2 (l' :: ℓ') :=
            {
            ConformToBalancer (ICTBranch l t1 t2) (?(l) :: l' :: ℓ') (left eq_refl) (Some t1') None := None;
            ConformToBalancer (ICTBranch l t1 t2) (?(l) :: l' :: ℓ') (left eq_refl) (Some t1') (Some t2') := Some (ICTBranch l t1' t2')
            }
          };
        ConformToBalancer (ICTBranch l t1 t2) (l :: ℓ') (right neq) := None
        }
    }.
  Lemma ConformToPrefixBalancer : forall (t : IChoiceTree) (ℓ ℓ' ℓ'' : list L.t), IsBalancedICTreewrt t ℓ -> ℓ' ++ ℓ'' = ℓ -> ℓ' <> [] -> ConformToBalancer t ℓ' <> None.
  Proof using.
    intros t ℓ ℓ' ℓ'' bal eq neq; funelim (ConformToBalancer t ℓ'); simp ConformToBalancer; cbn in *.
    all: try (rewrite Heq1; cbn).
    all: try (rewrite Heq0; cbn).
    all: try (rewrite Heq; cbn).
    Ltac ConformToPrefixBalancer := repeat (match goal with
                                            | [ |- [] = [] \/ _ ] => left; reflexivity
                                            | [ |- Some _ <> None ] => discriminate
                                            | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                                            end).
    all: ConformToPrefixBalancer.
    all: inversion bal; subst; ConformToPrefixBalancer.
    - specialize (Hind (t :: l ++ ℓ'') ℓ'' H1 eq_refl ltac:(discriminate)); exfalso; apply Hind; exact Heq.
    - specialize (Hind (t :: l ++ ℓ'') ℓ'' H4 eq_refl ltac:(discriminate)); exfalso; apply Hind; exact Heq.
  Qed.
  Corollary NotConformToBalancerNoPrefix : forall (t : IChoiceTree) (ℓ ℓ' : list L.t), IsBalancedICTreewrt t ℓ -> ConformToBalancer t ℓ' = None -> ℓ' = [] \/ forall ℓ'', ℓ' ++ ℓ'' <> ℓ.
  Proof using.
    intros t ℓ ℓ' bal eq. destruct ℓ'. left; auto. right; intros ℓ'' eq'; apply ConformToPrefixBalancer with (t := t) in eq'; auto. discriminate.
  Qed.

  Lemma ConformToBalancerBalanced : forall (t t' : IChoiceTree) (ℓ : list L.t), ConformToBalancer t ℓ = Some t' -> IsBalancedICTreewrt t' ℓ.
  Proof using.
    intros t t' ℓ eq; funelim (ConformToBalancer t ℓ); simp ConformToBalancer in eq.
    all: try (rewrite Heq1 in eq; cbn in eq); try (rewrite Heq0 in eq; cbn in eq); try (rewrite Heq in eq; cbn in eq); inversion eq; subst; clear eq.
    all: try (constructor; auto; fail).
  Qed.

  Lemma ConformToBalancerId : forall (t : IChoiceTree) (ℓ : list L.t), IsBalancedICTreewrt t ℓ -> ConformToBalancer t ℓ = Some t.
  Proof using.
    intros t ℓ bal; funelim (ConformToBalancer t ℓ); simp ConformToBalancer.
    all: try (rewrite Heq1; cbn); try (rewrite Heq0; cbn); try (rewrite Heq; cbn); auto; inversion bal; subst.
    all: try match goal with | [ H : IsBalancedICTreewrt _ [] |- _ ] => inversion H end.
    all: subst; try match goal with | [ H : ?a <> ?a |- _ ] => exfalso; apply H; auto end.
    all: try match goal with
             | [ H : ?a = None, H' : ?P -> ?a = Some _, H'' : ?P |- _ ] => specialize (H' H''); rewrite H' in H; inversion H
             end.
    specialize (Hind H4); specialize (Hind0 H1). rewrite Hind in Heq; inversion Heq; subst. rewrite Hind0 in Heq0; inversion Heq0; subst. reflexivity.
  Qed.
    
  Fixpoint GreatestCommonPrefix (ℓ1 ℓ2 : list L.t) : list L.t :=
    match ℓ1 with
    | [] => []
    | (l :: ℓ1) =>
      match ℓ2 with
      | [] => []
      | (l' :: ℓ2) => if L.eq_dec l l'
                    then l :: GreatestCommonPrefix ℓ1 ℓ2
                    else []
      end
    end.

  Lemma GCP_Prefix1 : forall ℓ1 ℓ2 : list L.t, exists ℓ1', (GreatestCommonPrefix ℓ1 ℓ2) ++ ℓ1' = ℓ1.
  Proof using.
    intros ℓ1; induction ℓ1 as [|l ℓ1]; intro ℓ2; cbn.
    - exists []; auto.
    - destruct ℓ2 as [|l' ℓ2]; cbn. exists (l :: ℓ1); auto.
      destruct (L.eq_dec l l'); subst; cbn. destruct (IHℓ1 ℓ2) as [ℓ1' H].
      exists ℓ1'; rewrite H; auto.
      exists (l :: ℓ1); auto.
  Qed.
  Lemma GCP_Prefix2 : forall ℓ1 ℓ2 : list L.t, exists ℓ2', (GreatestCommonPrefix ℓ1 ℓ2) ++ ℓ2' = ℓ2.
  Proof using.
    intros ℓ1; induction ℓ1 as [|l ℓ1]; intro ℓ2; cbn.
    - exists ℓ2; auto.
    - destruct ℓ2 as [|l' ℓ2]; cbn. exists []; auto.
      destruct (L.eq_dec l l'); subst; cbn. destruct (IHℓ1 ℓ2) as [ℓ2' H].
      exists ℓ2'; rewrite H; auto.
      exists (l' :: ℓ2); auto.
  Qed.

  (* If p is a common prefix of ℓ1 and ℓ2, then it is also a prefix of GreatestCommonPrefix ℓ1 ℓ2 *)
  Lemma GCP_Greatest : forall (ℓ1 ℓ2 p ℓ1' ℓ2' : list L.t), p ++ ℓ1' = ℓ1 -> p ++ ℓ2' = ℓ2 -> exists ℓ'', p ++ ℓ'' = GreatestCommonPrefix ℓ1 ℓ2.
  Proof using.
    intros ℓ1 ℓ2 p; revert ℓ1 ℓ2; induction p; intros ℓ1 ℓ2 ℓ1' ℓ2' eq1 eq2; subst; cbn in *.
    repeat (exists (GreatestCommonPrefix ℓ1' ℓ2')); split; auto.
    destruct (L.eq_dec a a); LocationOrder; clear e.
    specialize (IHp (p ++ ℓ1') (p ++ ℓ2') ℓ1' ℓ2' eq_refl eq_refl).
    destruct IHp as [ℓ'' H]. 
    exists ℓ''; rewrite H; auto.
  Qed.

  Equations BalanceTreeHelper (t : IChoiceTree) : IChoiceTree * (list L.t)  :=
    {
      BalanceTreeHelper (ICTLeaf l P Q) := (ICTLeaf l P Q, [l]);
      BalanceTreeHelper (ICTBranch l t1 t2) with BalanceTreeHelper t1 :=
        {
        BalanceTreeHelper (ICTBranch l t1 t2) (t1', bal1) with BalanceTreeHelper t2 :=
          {
          BalanceTreeHelper (ICTBranch l t1 t2) (t1', bal1) (t2', bal2) := let bal := GreatestCommonPrefix bal1 bal2
                                                                          in match ConformToBalancer t1' bal with
                                                                             | Some t1' =>
                                                                               match ConformToBalancer t2' bal with
                                                                               | Some t2' => (ICTBranch l t1' t2', l :: bal)
                                                                               | None => (ICTLeaf l (IChoiceTreeToProc t1) (IChoiceTreeToProc t2), [l])
                                                                               end
                                                                             | None => (ICTLeaf l (IChoiceTreeToProc t1) (IChoiceTreeToProc t2), [l])
                                                                             end
          }
        }
    }.
  Lemma BalanceTreeHBalancedwrt : forall (t : IChoiceTree), IsBalancedICTreewrt (fst (BalanceTreeHelper t)) (snd (BalanceTreeHelper t)).
  Proof using.
    intro t; funelim (BalanceTreeHelper t); simp BalanceTreeHelper; cbn; [constructor|].
    rewrite Heq in Hind; rewrite Heq0 in Hind0; cbn in *.
    destruct (GCP_Prefix1 l l0) as [l' l'_pfx].
    destruct (GCP_Prefix2 l l0) as [l0' l0'_pfx].
    destruct (ConformToBalancer i1 (GreatestCommonPrefix l l0)) eqn:eq1; [|cbn; constructor].
    destruct (ConformToBalancer i2 (GreatestCommonPrefix l l0)) eqn:eq2; cbn; constructor; eapply ConformToBalancerBalanced; eauto; fail.
  Qed.

  Lemma BalancersUnique : forall (t : IChoiceTree) (ℓ1 ℓ2 : list L.t), IsBalancedICTreewrt t ℓ1 -> IsBalancedICTreewrt t ℓ2 -> ℓ1 = ℓ2.
  Proof using.
    intro t; ICTInduction t; intros ℓ1 ℓ2 bal1 bal2.
    - inversion bal1; inversion bal2; subst; auto.
    - inversion bal1; inversion bal2; subst; auto. rewrite IHt0 with (ℓ1 := l0) (ℓ2 := l1); auto.
  Qed.

  Lemma GreatestCommonPrefixSame : forall (ℓ : list L.t), GreatestCommonPrefix ℓ ℓ = ℓ.
  Proof using.
    intro ℓ; induction ℓ; cbn; auto.
    destruct (L.eq_dec a a); cbn; auto. rewrite IHℓ; auto. exfalso; apply n; auto.
  Qed.
  
  Lemma BalanceTreeHBalancedId : forall (t : IChoiceTree), IsBalancedICTree t -> t = fst (BalanceTreeHelper t).
  Proof using.
    intros t bal; funelim (BalanceTreeHelper t); simp BalanceTreeHelper; cbn; auto.
    remember (BalanceTreeHBalancedwrt i0); clear Heqi3. rewrite Heq in i3; cbn in i3.
    remember (BalanceTreeHBalancedwrt i); clear Heqi4. rewrite Heq0 in i4; cbn in i4.
    destruct bal as [l1 bal]. inversion bal; subst.
    specialize (Hind ltac:(exists l2; auto)); subst; rewrite Heq in Hind; cbn in Hind; subst.
    specialize (Hind0 ltac:(exists l2; auto)); subst; rewrite Heq0 in Hind0; cbn in Hind0; subst.
    assert (l0 = l2) by (apply BalancersUnique with (t := i2); auto); subst.
    assert (l2 = l) by (apply BalancersUnique with (t := i1); auto); subst.
    repeat rewrite GreatestCommonPrefixSame.
    repeat rewrite ConformToBalancerId; auto.
  Qed.

  Definition BalanceTree (t : IChoiceTree) : IChoiceTree := fst (BalanceTreeHelper t).
                                                 
  Corollary BalanceTreeBalanced : forall (t : IChoiceTree), IsBalancedICTree (BalanceTree t).
  Proof using.
    intro t; unfold BalanceTree; exists (snd (BalanceTreeHelper t)); apply BalanceTreeHBalancedwrt.
  Qed.
  Corollary BalanceTreeBalancedId : forall (t : IChoiceTree), IsBalancedICTree t -> BalanceTree t = t.
  Proof using.
    intros t bal; unfold BalanceTree; rewrite BalanceTreeHBalancedId; auto.
  Qed.

  Equations ProcToICTree (P : Proc) : option IChoiceTree :=
    {
      ProcToICTree EndProc := None;
      ProcToICTree (VarProc _) := None;
      ProcToICTree (SendProc _ _ _) := None;
      ProcToICTree (RecvProc _ _) := None;
      ProcToICTree (EChoiceL _ _) := None;
      ProcToICTree (EChoiceR _ _) := None;
      ProcToICTree (IfThenElse _ _ _) := None;
      ProcToICTree (DefProc _ _) := None;
      ProcToICTree (IChoice l P Q) with ProcToICTree P :=
        {
        ProcToICTree (IChoice l P Q) None := Some (ICTLeaf l P Q);
        ProcToICTree (IChoice l P Q) (Some t1) with ProcToICTree Q :=
          {
          ProcToICTree (IChoice l P Q) (Some t1) None := Some (ICTLeaf l P Q);
          ProcToICTree (IChoice l P Q) (Some t1) (Some t2) := Some (ICTBranch l t1 t2)
          }
        }
    }.

  Lemma ProcToICTreeToProc : forall (P : Proc) (t : IChoiceTree), ProcToICTree P = Some t -> IChoiceTreeToProc t = P.
  Proof using.
    intros P t eq; funelim (ProcToICTree P); simp ProcToICTree in eq; try (inversion eq; fail).
    all: try (rewrite Heq0 in eq; cbn in eq).
    all: rewrite Heq in eq; cbn in eq; inversion eq; subst; cbn; auto.
    rewrite Hind0; auto; rewrite Hind; auto.
  Qed.

  Definition MakeDeepestICTree (l : L.t) (P Q : Proc) : IChoiceTree :=
    match ProcToICTree P with
    | Some t1 => match ProcToICTree Q with
                | Some t2 => BalanceTree (ICTBranch l t1 t2)
                | None => ICTLeaf l P Q
                end
    | None => ICTLeaf l P Q
    end.
                                      

  Program Fixpoint InsertIChoice (l : L.t) (P Q : Proc) : Proc * bool :=
    match P with
    | EndProc =>
      match Q with
      | EndProc => (EndProc, false)
      | _ => (IChoice l P Q, true)
      end
    | VarProc n =>
      match Q with
      | VarProc m => if PeanoNat.Nat.eq_dec n m then (VarProc n, false) else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | DefProc P1 Q1 =>
      match Q with
      | DefProc P2 Q2 => if ProcEqDec P1 P2
                        then match InsertIChoice l Q1 Q2 with
                             | (Q', b) => (DefProc P1 Q', b)
                             end
                        else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | SendProc l' e P' =>
      match Q with
      | SendProc l'' e' Q' => if L.eq_dec l' l''
                             then if ExprEqDec e e'
                                  then match InsertIChoice l P' Q' with
                                       | (Rp, b) => (SendProc l' e Rp, b)
                                       end
                                  else (IChoice l P Q, true)
                             else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | RecvProc l' P' =>
      match Q with
      | RecvProc l'' Q' => if L.eq_dec l' l''
                          then match InsertIChoice l P' Q' with
                               | (Rp, b) => (RecvProc l Rp, b)
                               end
                          else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | EChoiceL l' P' =>
      match Q with
      | EChoiceL l'' Q' => if L.eq_dec l' l''
                         then match InsertIChoice l P' Q' with
                              | (Rp, b) => (EChoiceL l Rp, b)
                              end
                         else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | EChoiceR l' P' => _
      match Q with
      | EChoiceR l'' Q' => if L.eq_dec l' l''
                         then match InsertIChoice l P' Q' with
                              | (Rp, b) => (EChoiceR l Rp, b)
                              end
                         else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    | IChoice l' P1 Q1 =>
      match Q with
      | IChoice l'' P2 Q2 =>
        match InsertICTBranch l (MakeDeepestICTree l' P1 Q1) (MakeDeepestICTree l' P2 Q2) with
        | (t, b) => (IChoiceTreeToProc t, b)
        end
      | _ => (IChoice l P Q, true)
      end
    | IfThenElse e P1 Q1 =>
      match Q with
      | IfThenElse e' P2 Q2 => if ExprEqDec e e'
                              then match InsertIChoice l P1 P2 with
                                   | (R1, b1) => match InsertIChoice l Q1 Q2 with
                                                | (R2, b2) => (IfThenElse e R1 R2, orb b1 b2) (* Issue: If true Then end Else IChoice l (send l 3) (send l 4). Need to insert an ichoice as deeply as possible in that case. *)
                                                end
                                   end
                              else (IChoice l P Q, true)
      | _ => (IChoice l P Q, true)
      end
    end
  with InsertICTBranch (l : L.t) (t1 t2 : IChoiceTree) : IChoiceTree * bool :=
         match t1 with
         | ICTLeaf l' P1 Q1 =>
           match t2 with
           | ICTLeaf l'' P2 Q2 => if L.eq_dec l' l''
                                 then match L.compare l l' with
                                      | Lt => match InsertIChoice l P1 P2 with
                                             | (P, b1) => match InsertIChoice l Q1 Q2 with
                                                        | (Q, b2) => (ICTLeaf l' P Q, orb b1 b2) (* Similar issue to above *)
                                                        end
                                             end
                                      | _ => ICTBranch l (ICTLeaf l' P1 Q1) (ICTLeaf l' P2 Q2)
                                      end
                                 else (ICTBranch l (ICTLeaf l' P1 Q1) (ICTLeaf l'' P2 Q2), true)
           | ICTBranch l'' t21 t22 => if L.eq_dec l' l''
                                     then match L.compare l l' with
                                          | Lt => match InsertIChoice l P1 (IChoiceTreeToProc t21) with
                                                 | (P, b1) => match InsertIChoice l Q1 (IChoiceTreeToProc t22) with
                                                             | (Q, b2) => (ICTLeaf l' P Q, orb b1 b2)
                                                             end
                                                 end
                                          | _ => (ICTBranch l (ICTLeaf l' P1 Q1) (ICTLeaf l' (IChoiceTreeToProc t21) (IChoiceTreeToProc t22)), true)
                                          end
                                     else (ICTBranch l (ICTLeaf l' P1 Q1) (ICTBranch l'' t21 t22), true)
           end
         | ICTBranch l' t11 t12 => _
         end.

  Equations InsertIChoice (l : L.t) (P Q : Proc) : Proc :=
    {
      InsertIChoice l P Q := _
    } 

  (* Theorem SortICTHelperBalancePreserving : forall (t t' : IChoiceTree) (elts : list (L.t * nat)), SortICTHelper t elts = Some t' -> IsBalancedICTree t -> IsBalancedICTree t'. *)
  (* Proof. *)
  (*   intros t t' elts eq bal; funelim (SortICTHelper t elts); simp SortICTHelper in eq; try (inversion eq; fail). *)
  (*   all: try (rewrite Heq in eq; cbn in eq; apply H in eq; auto). *)
  (*   all: try (rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq; eexists; econstructor; eauto; fail). *)
  (*   all: try (rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; apply H in eq; auto). *)
  (*   rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq. *)
  (*   all: rewrite Heq2 in eq; cbn in eq; rewrite Heq1 in eq; cbn in eq; rewrite Heq0 in eq; cbn in eq; rewrite Heq in eq; cbn in eq; inversion eq; subst. *)
  (*   specialize (Hind i2 Heq). specialize (Hind0 i1 Heq0). *)

  Lemma FirstDeciderIsDecider : forall t : IChoiceTree, IsDecider (FirstDecider t) t.
  Proof using.
    intro t; ICTDestruct t; cbn; constructor.
  Qed.
  
  Lemma SortICTHOrdered : forall (t t' : IChoiceTree) elts, Sorted (LM.lt_key (elt := nat)) elts -> SortICTHelper t elts = Some t' -> IsOrderedICTree t'.
  Proof using.
    intros t t' elts std eq; funelim (SortICTHelper t elts); simp SortICTHelper in eq.
    all: try (inversion eq; fail).
    all: try (rewrite Heq2 in eq; cbn in eq); try (rewrite Heq1 in eq; cbn in eq); try (rewrite Heq0 in eq; cbn in eq); try (rewrite Heq in eq; cbn in eq).
    all: try (apply H in eq; auto; inversion std; subst; auto; fail).
    all: inversion eq; subst; clear eq; try (constructor; auto; fail).
    assert (Sorted (LM.lt_key (elt := nat)) ((t0, n) :: l)).
    2: {constructor; [| | apply Hind0; auto | apply Hind; auto]; auto. 
    constructor; [inversion std; subst; auto|]. inversion std; subst; auto. apply InA_InfA with (eqA := LM.eq_key (elt := nat)).
    
    
    

  
  Theorem SortICTOrdered : forall (t : IChoiceTree), IsOrderedICTree (SortICTree t).

  Abort.

  
  Lemma SortICTHelperTypePres : forall (t t' : IChoiceTree) elts, SortICTHelper t elts = Some t' -> LM.Equal (LaxChoiceTypeOf t) (LaxChoiceTypeOf t').
  Proof using.
    intros t t' elts eq; funelim (SortICTHelper t elts); simp SortICTHelper in eq.
    all: try (inversion eq; fail).
    all: try (rewrite Heq2 in eq; cbn in eq); try (rewrite Heq1 in eq; cbn in eq); try (rewrite Heq0 in eq; cbn in eq); try (rewrite Heq in eq; cbn in eq).
    all: try (apply H in eq; auto; fail).
    all: try (inversion eq; subst; clear eq; cbn; clear Heq0; apply DifferentialLeftProc in e; destruct e as [Q e]; subst; cbn; reflexivity).
    clear Heq; apply DifferentialRightProc in e0; destruct e0 as [P e0]; subst; clear Heq0; cbn in e.
    simp IChoiceDifferential in e; destruct (L.eq_dec t0 t0); LocationOrder; cbn in e; destruct e0; inversion e.
    inversion eq; subst; clear eq; cbn. 
  
  Theorem SortICTreeTypePreserving : forall t : IChoiceTree, LM.Equal (LaxChoiceTypeOf t) (LaxChoiceTypeOf (SortICTree t)).
  Proof using.
      
  Abort.
  Theorem SortICTreeChoicePreserving : forall (t : IChoiceTree) (cs : LM.t (list LRChoice)), RunChoices t cs = RunChoices (SortICTree t) cs.
  Abort.
  Theorem SortICTOrdered_Same : forall (t : IChoiceTree), IsOrderedICTree t -> t = SortICTree t.
  Abort.

End IChoiceTree.
