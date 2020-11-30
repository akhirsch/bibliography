Require Export Expression.
Require Export Locations.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Sorted Orders Coq.Sorting.Mergesort Permutation.
Require Import Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Bool.
Require Import Psatz.
Require Import Coq.Program.Equality.

From Equations Require Import Equations.

Module Choreography (Import E : Expression) (L : Locations).

  Definition Loc : Set := L.t.
  Include (LocationNotations L).
  Module LF := (LocationFacts L).
  Import ListNotations.

  Inductive LRChoice : Set := LChoice | RChoice.
  Instance ChoiceEqDec : EqDec LRChoice.
  Proof using.
    unfold EqDec; decide equality.
  Defined.
  
  Inductive Chor : Set :=
    Done : Loc -> Expr -> Chor
  | Var : nat -> Chor
  | Send : Loc -> Expr -> Loc -> Chor -> Chor
  | If : Loc -> Expr -> Chor -> Chor -> Chor
  | Sync : Loc -> LRChoice -> Loc -> Chor -> Chor
  | DefLocal : Loc -> Chor -> Chor -> Chor
  | DefGlobal : Chor -> Chor -> Chor.
  Hint Constructors Chor : Chor.
  Notation "'Ret' p ⟪ e ⟫" := (Done p e) (at level 25).
  Notation "p ⟪ e ⟫ → q 'fby' C" := (Send p e q C) (at level 25).
  Notation "'Cond' p ⦃ e ⦄ 'Then' C1 'Else' C2" := (If p e C1 C2) (at level 25).
  Notation "p ⟨ d ⟩ → q 'fby' C" := (Sync p d q C) (at level 25).
  Notation "'LetLocal' p '⟪new⟫' ← C1 'fby' C2" := (DefLocal p C1 C2) (at level 25).
  Notation "'LetGlobal' '⟪new⟫' ← C1 'fby' C2" := (DefGlobal C1 C2) (at level 25).

  Ltac ChorInduction C := let p := fresh "l" in
                          let e := fresh "e" in
                          let x := fresh "x" in
                          let q := fresh "l'" in
                          let C1 := fresh "C1" in
                          let C2 := fresh "C2" in
                          let IHC := fresh "IH" C in
                          let IHC1 := fresh "IH" C1 in
                          let IHC2 := fresh "IH" C2 in
                          let n := fresh "n" in
                          let d := fresh "d" in
                          induction C as [p e | n | p e q C IHC | p e C1 IHC1 C2 IHC2 | p d q C IHC |p C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2].
  Ltac ChorDestruct C := let p := fresh "p" in
                         let n := fresh "n" in
                         let e := fresh "e" in
                         let x := fresh "x" in
                         let q := fresh "q" in
                         let d := fresh "d" in
                         let C1 := fresh "C1" in
                         let C2 := fresh "C2" in
                         destruct C as [p e | n | p e q C | p e C1 C2 |p d q C | p C1 C2 | C1 C2].
  Instance ChorEqDec : EqDec Chor.
  Proof using.
    unfold EqDec; decide equality.
    all: try (apply ExprEqDec).
    all: try (apply L.eq_dec).
    apply Nat.eq_dec.
    apply ChoiceEqDec.
  Defined.

  Inductive ChorVal : Chor -> Prop :=
  | ReturnVal : forall (l : Loc) (v : Expr),
      ExprVal v -> ChorVal (Done l v).

  Fixpoint NumberOfIfs (C : Chor) : nat :=
    match C with
    | Done p e => 0
    | Var n => 0
    | Send p e q C' => NumberOfIfs C'
    | If p e C1 C2 => S (NumberOfIfs C1 + NumberOfIfs C2)
    | Sync p d q C' => NumberOfIfs C'
    | DefLocal p C1 C2 => NumberOfIfs C1 + NumberOfIfs C2
    | DefGlobal C1 C2 => NumberOfIfs C1 + NumberOfIfs C2
    end.

  Fixpoint ChorSize (C : Chor) : nat :=
    match C with
    | Done p e => 1
    | Var n => 1
    | Send p e q C' => S (ChorSize C')
    | If p e C1 C2 => S(Nat.max (ChorSize C1) (ChorSize C2))
    | Sync p d q C' => S (ChorSize C')
    | DefLocal p C1 C2 => S (ChorSize C1 + ChorSize C2)
    | DefGlobal C1 C2 => S (ChorSize C1 + ChorSize C2)
    end.

  Definition ChorUpExprRename : (Loc -> nat -> nat) -> Loc -> Loc -> nat -> nat :=
    fun ξ p q => if L.eq_dec p q
              then ExprUpRename (ξ q)
              else ξ q.

  Fixpoint ChorExprRename (C : Chor) (ξ : Loc -> nat -> nat) : Chor :=
    match C with
    | Done p e => Done p (e ⟨e| (ξ p)⟩)
    | Var n => Var n
    | Send p e q C => Send p (e ⟨e| (ξ p)⟩) q (ChorExprRename C (ChorUpExprRename ξ q))
    | If p e C1 C2 => If p (e ⟨e| (ξ p)⟩) (ChorExprRename C1 ξ) (ChorExprRename C2 ξ)
    | Sync p d q C1 => Sync p d q (ChorExprRename C1 ξ)
    | DefLocal p C1 C2 => DefLocal p (ChorExprRename C1 ξ) (ChorExprRename C2 (ChorUpExprRename ξ p))
    | DefGlobal C1 C2 => DefGlobal (ChorExprRename C1 ξ) (ChorExprRename C2 ξ)
    end.
  Notation "C ⟨ce| x ⟩" := (ChorExprRename C x) (at level 20).

  Definition ChorIdExprRename : Loc -> nat -> nat := fun _ n => n.
  
  Lemma ChorUpIdExprRename : forall p q n, ChorUpExprRename ChorIdExprRename p q n = ChorIdExprRename p n.
  Proof using.
    intros p q n; destruct n; unfold ChorUpExprRename; unfold ChorIdExprRename.
    all: destruct (L.eq_dec p q) as [_|neq]; simpl; reflexivity.
  Qed.

  Lemma ChorUpExprRenameExt : forall (ξ1 ξ2 : Loc -> nat -> nat),
      (forall (p : Loc) (n : nat), ξ1 p n = ξ2 p n) ->
      forall (p q : Loc) (n : nat), ChorUpExprRename ξ1 p q n = ChorUpExprRename ξ2 p q n.
  Proof using.
    intros ξ1 ξ2 eq p q n. unfold ChorUpExprRename. unfold ExprUpRename.
    destruct (L.eq_dec p q); auto.
    destruct n; auto.
  Qed.

  Lemma ChorExprRenameExtensional : forall (ξ1 ξ2 : Loc -> nat -> nat),
      (forall (p : Loc) (n : nat), ξ1 p n = ξ2 p n) ->
      forall (C : Chor), C ⟨ce| ξ1 ⟩ = C ⟨ce| ξ2⟩.
  Proof using.
    intros ξ1 ξ2 eqv C; revert ξ1 ξ2 eqv; ChorInduction C; intros ξ1 ξ2 eqv; cbn; auto.
    - rewrite ExprRenameExt with (ξ2 := ξ2 l); auto.
    - rewrite ExprRenameExt with (ξ2 := ξ2 l); auto. rewrite IHC with (ξ2 := ChorUpExprRename ξ2 l'); auto.
      apply ChorUpExprRenameExt; auto.
    - rewrite ExprRenameExt with (ξ2 := ξ2 l); auto. rewrite IHC1 with (ξ2 := ξ2); auto; rewrite IHC2 with (ξ2 := ξ2); auto.
    - rewrite IHC with (ξ2 := ξ2); auto.
    - rewrite IHC1 with (ξ2 := ξ2); [rewrite IHC2 with (ξ2 := ChorUpExprRename ξ2 l)|]; auto; apply ChorUpExprRenameExt; auto.
    - rewrite IHC1 with (ξ2 := ξ2); [rewrite IHC2 with (ξ2 := ξ2)|]; auto.
  Qed.
  
  Lemma ChorExprRenameFusion : forall (C : Chor) (ξ1 ξ2 : Loc -> nat -> nat), (C ⟨ce| ξ1⟩)⟨ce| ξ2⟩ = C ⟨ce| fun p n => ξ2 p (ξ1 p n)⟩.
  Proof using.
    intros C; ChorInduction C; intros ξ1 ξ2; cbn; auto.
    all: try (rewrite ExprRenameFusion; auto).
    - rewrite IHC; auto; erewrite ChorExprRenameExtensional; eauto.
      intros p n; unfold ChorUpExprRename; destruct (L.eq_dec l' p); unfold ExprUpRename; destruct n; auto.
    - rewrite IHC1; auto; rewrite IHC2; auto; erewrite ChorExprRenameExtensional; eauto.
    - rewrite IHC; auto.
    - rewrite IHC1; auto; rewrite IHC2; auto. 
      rewrite ChorExprRenameExtensional with (ξ1 := fun p n => ChorUpExprRename ξ2 l p (ChorUpExprRename ξ1 l p n)) (ξ2 := ChorUpExprRename (fun p n => ξ2 p (ξ1 p n)) l); auto.
      unfold ChorUpExprRename; unfold ExprUpRename; intros p n; destruct (L.eq_dec l p); destruct n; auto.
    - rewrite IHC1; rewrite IHC2; reflexivity.
  Qed.
  Lemma ChorIdExprRenameSpec : forall C, C ⟨ce| ChorIdExprRename⟩ = C.
  Proof using.
    intros C; ChorInduction C; cbn; auto.
    all: try (rewrite IHC; auto).
    all: try (rewrite ExprIdRenamingSpec; auto).
    all: try (rewrite IHC1; rewrite IHC2; auto; fail).
    - rewrite ChorExprRenameExtensional with (ξ2 := ChorIdExprRename); [rewrite IHC; auto|].
      apply ChorUpIdExprRename.
    - rewrite IHC1. rewrite ChorExprRenameExtensional with (ξ2 := ChorIdExprRename); [rewrite IHC2| apply ChorUpIdExprRename]; auto.
  Qed.

  Definition ChorUpRename : (nat -> nat) -> nat -> nat :=
    fun f n => match n with
            | 0 => 0
            | S n => S (f n)
            end.
  Fixpoint ChorRename (C : Chor) (ξ : nat -> nat) :=
    match C with
    | Done l e => Done l e
    | Var n => Var (ξ n)
    | Send l1 e l2 C => Send l1 e l2 (ChorRename C ξ)
    | If l e C1 C2 => If l e (ChorRename C1 ξ) (ChorRename C2 ξ)
    | Sync l1 d l2 C => Sync l1 d l2 (ChorRename C ξ)
    | DefLocal l C1 C2 => DefLocal l (ChorRename C1 ξ) (ChorRename C2 ξ)
    | DefGlobal C1 C2 => DefGlobal (ChorRename C1 (ChorUpRename ξ)) (ChorRename C2 (ChorUpRename ξ))
    end.
  Notation "C ⟨c| x ⟩" := (ChorRename C x) (at level 20).

  Definition ChorIdRename := fun n : nat => n.

  Lemma ChorUpIdRename : forall n, ChorUpRename ChorIdRename n = ChorIdRename n.
  Proof using.
    intro n; destruct n; cbn; unfold ChorIdRename; auto.
  Qed.
  Lemma ChorUpRenameExt : forall ξ1 ξ2, (forall n, ξ1 n = ξ2 n) -> forall n, ChorUpRename ξ1 n = ChorUpRename ξ2 n.
  Proof using.
    intros ξ1 ξ2 eqv n; destruct n; cbn; auto.
  Qed.

  Lemma ChorRenameExt : forall C ξ1 ξ2, (forall n, ξ1 n = ξ2 n) -> C ⟨c| ξ1⟩ = C ⟨c| ξ2⟩.
  Proof using.
    intros C; ChorInduction C; intros ξ1 ξ2 eqv; cbn; auto.
    all: try (rewrite IHC with (ξ2 := ξ2); auto).
    all: try (rewrite IHC1 with (ξ2 := ξ2); [rewrite IHC2 with (ξ2 := ξ2)|]; auto; fail).
    rewrite IHC1 with (ξ2 := ChorUpRename ξ2); [rewrite IHC2 with (ξ2 := ChorUpRename ξ2)|];
      [| apply ChorUpRenameExt | apply ChorUpRenameExt]; auto.
  Qed.    

  
  Lemma ChorIdRenameSpec : forall C, C ⟨c| ChorIdRename ⟩ = C.
  Proof using.
    intro C; ChorInduction C; cbn; auto.
    all: try (rewrite IHC) ;auto.
    all: try (rewrite IHC1; rewrite IHC2; auto; fail).
    rewrite ChorRenameExt with (ξ2 := ChorIdRename); [rewrite IHC1|].
    rewrite ChorRenameExt with (ξ2 := ChorIdRename); [rewrite IHC2; reflexivity|].
    all: intro n; destruct n; cbn; auto.
  Qed.

  Definition ChorRenameFusion : forall C ξ1 ξ2, (C ⟨c| ξ1⟩) ⟨c|ξ2⟩ = C ⟨c| fun n => ξ2 (ξ1 n)⟩.
  Proof using.
    intro C; ChorInduction C; intros ξ1 ξ2; cbn; auto.
    all: try (rewrite IHC; auto).
    all: try (rewrite IHC1; rewrite IHC2; auto; fail).
    rewrite IHC1; rewrite IHC2.
    rewrite ChorRenameExt with (ξ2 := ChorUpRename (fun n => ξ2 (ξ1 n))).
    rewrite ChorRenameExt with (ξ1 := fun n => ChorUpRename ξ2 (ChorUpRename ξ1 n))
                               (ξ2 := ChorUpRename (fun n => ξ2 (ξ1 n))).
    reflexivity.
    all: intro n; unfold ChorUpRename; destruct n; auto.
  Qed.
      
  Definition ChorUpExprSubst : (Loc -> nat -> Expr) -> Loc -> Loc -> nat -> Expr :=
    fun σ p q n =>
      if L.eq_dec p q then
        match n with
        | 0 => ExprVar 0
        | S n => (σ q n) ⟨e| S ⟩
        end
      else σ q n.
  Definition SendUpChorExprSubst (σk : nat -> Chor) (p : Loc) : nat -> Chor :=
    fun n => (σk n)⟨ce| fun q m => if L.eq_dec p q then S m else m⟩.

  Fixpoint ChorExprSubst (C : Chor) (σ : Loc -> nat -> Expr) : Chor :=
    match C with
    | Done p e => Done p (e [e| (σ p)])
    | Var n => Var n
    | Send p e q C => Send p (e [e| (σ p)]) q (ChorExprSubst C (ChorUpExprSubst σ q))
    | If p e C1 C2 => If p (e [e| (σ p)]) (ChorExprSubst C1 σ) (ChorExprSubst C2 σ)
    | Sync p d q C => Sync p d q (ChorExprSubst C σ)
    | DefLocal p C1 C2 => DefLocal p (ChorExprSubst C1 σ) (ChorExprSubst C2 (ChorUpExprSubst σ p))
    | DefGlobal C1 C2 => DefGlobal (ChorExprSubst C1 σ) (ChorExprSubst C2 σ)
    end.
  Notation "C [ce| s ]" := (ChorExprSubst C s) (at level 20).

  Lemma ChorUpExprSubstExt : forall (σ1 σ2 : Loc -> nat -> Expr),
      (forall (p : Loc) (n : nat), σ1 p n = σ2 p n) ->
      forall (p q : Loc) (n : nat), ChorUpExprSubst σ1 p q n = ChorUpExprSubst σ2 p q n.
  Proof using.
    intros σ1 σ2 eq p q n; unfold ChorUpExprSubst; destruct n; auto; repeat (rewrite eq); reflexivity.
  Qed.

  Lemma ChorExprSubstExt : forall (σ1 σ2 : Loc -> nat -> Expr),
      (forall (p : Loc) (n : nat), σ1 p n = σ2 p n) ->
      forall C, C [ce| σ1] = C [ce| σ2].
  Proof using.
    intros σ1 σ2 eqv C; revert σ1 σ2 eqv; ChorInduction C; intros σ1 σ2 eqv; cbn.
    all: try (rewrite ExprSubstExt with (σ2 := σ2 l)); auto.
    all: try (rewrite IHC with (σ2 := σ2); auto; fail).
    - rewrite IHC with (σ2 := ChorUpExprSubst σ2 l'); auto; apply ChorUpExprSubstExt; auto.
    - rewrite IHC1 with (σ2 := σ2); [rewrite IHC2 with (σ2 := σ2)|]; auto.
    - rewrite IHC1 with (σ2 := σ2); [rewrite IHC2 with (σ2 := ChorUpExprSubst σ2 l)|]; auto; apply ChorUpExprSubstExt; auto.
    - erewrite IHC1; [erewrite IHC2|]; eauto.
  Qed.
  
  Definition ChorIdExprSubst : Loc -> nat -> Expr := fun _ n => ExprVar n.
  
  Lemma ChorIdExprSubstFibre : forall (p : Loc),
      ChorIdExprSubst p = ExprIdSubst.
  Proof using.
    intros p. unfold ChorIdExprSubst. unfold ExprIdSubst. reflexivity.
  Qed.

  Lemma ChorUpIdExprSubst : forall p q n, ChorIdExprSubst p n
                                 = ChorUpExprSubst ChorIdExprSubst q p n.
  Proof using.
    intros p q n; unfold ChorUpExprSubst; unfold ChorIdExprSubst;
      destruct (L.eq_dec q p); destruct n; auto; rewrite ExprRenameVar; reflexivity.
  Qed.
  
  Lemma ChorExprSubstIdSpec : forall (C : Chor), C [ce| ChorIdExprSubst] = C.
  Proof using.
    intro C; ChorInduction C; unfold ChorIdExprSubst; cbn; auto.
    all: try (rewrite ChorIdExprSubstFibre).
    all: try (rewrite ExprIdentitySubstSpec).
    - reflexivity.
    - rewrite ChorExprSubstExt with (σ2 := ChorIdExprSubst); [rewrite IHC|]; auto.
      intros p n; unfold ChorUpExprSubst; unfold ChorIdExprSubst; cbn.
      destruct (L.eq_dec l' p); cbn; destruct n; auto; rewrite ExprRenameVar; reflexivity.
    - fold ChorIdExprSubst; rewrite IHC1; rewrite IHC2; reflexivity.
    - fold ChorIdExprSubst; rewrite IHC; reflexivity.
    - fold ChorIdExprSubst; rewrite IHC1.
      rewrite ChorExprSubstExt with (σ2 := ChorIdExprSubst); [rewrite IHC2; reflexivity|].
      fold ChorIdExprSubst; intros p n; symmetry; apply ChorUpIdExprSubst.
    - fold ChorIdExprSubst; rewrite IHC1; rewrite IHC2; reflexivity.
  Qed.
      
  Theorem ChorExprRenameSpec : forall (C : Chor) (ξ : Loc -> nat -> nat),
      C ⟨ce| ξ ⟩ = C[ce| (fun p n => ExprVar (ξ p n))].
  Proof using.
    intro C; ChorInduction C; intros ξ; cbn.
    all: repeat (rewrite ExprRenameSpec).
    all: try (repeat (rewrite IHC)).
    all: try (rewrite IHC1; rewrite IHC2).
    all: try reflexivity.
    - rewrite ChorExprSubstExt with (σ2 := ChorUpExprSubst (fun p n => ExprVar (ξ p n)) l'); [reflexivity|].
      intros p n; unfold ChorUpExprSubst; unfold ChorUpExprRename; destruct (L.eq_dec l' p); destruct n; auto.
      unfold ExprUpRename. rewrite ExprRenameVar. reflexivity.
    - rewrite ChorExprSubstExt with (σ1 := fun p n => ExprVar (ChorUpExprRename ξ l p n )) (σ2 := ChorUpExprSubst (fun p n => ExprVar (ξ p n)) l); [reflexivity|].
      intros p n; unfold ChorUpExprSubst; unfold ChorUpExprRename; destruct (L.eq_dec l p); destruct n; auto.
      unfold ExprUpRename; rewrite ExprRenameVar; reflexivity.
  Qed.

  Definition ChorUpSubst : (nat -> Chor) -> nat -> Chor :=
    fun f  n => match n with
             | 0 => Var 0
             | S n => (f n) ⟨c| S⟩
             end.

  Definition ChorUpSubstForExpr : (nat -> Chor) -> Loc -> nat -> Chor :=
    fun f l n => (f n) ⟨ce|fun l' m => if L.eq_dec l l' then S m else m⟩.

  Fixpoint ChorSubst (C : Chor) (σ : nat -> Chor) :=
    match C with
    | Done l e => Done l e
    | Var n => σ n
    | Send l1 e l2 C => Send l1 e l2 (ChorSubst C (ChorUpSubstForExpr σ l2))
    | If l e C1 C2 => If l e (ChorSubst C1 σ) (ChorSubst C2 σ)
    | Sync l1 d l2 C => Sync l1 d l2 (ChorSubst C σ)
    | DefLocal l C1 C2 => DefLocal l (ChorSubst C1 σ) (ChorSubst C2 (ChorUpSubstForExpr σ l))
    | DefGlobal C1 C2 => DefGlobal (ChorSubst C1 (ChorUpSubst σ)) (ChorSubst C2 (ChorUpSubst σ))
    end.
  Notation "C [c| s ]" := (ChorSubst C s) (at level 20).
  Definition ChorIdSubst := fun n => Var n.

  Lemma ChorUpSubstExt : forall σ1 σ2 : nat -> Chor,
      (forall n, σ1 n = σ2 n) -> forall n, ChorUpSubst σ1 n = ChorUpSubst σ2 n.
  Proof using.
    intros σ1 σ2 H n; unfold ChorUpSubst; destruct n; cbn; auto. rewrite H; reflexivity.
  Qed.

  Lemma ChorUpSubstForExprExt : forall σ1 σ2,
      (forall n, σ1 n = σ2 n) ->
      forall l n, ChorUpSubstForExpr σ1 l n = ChorUpSubstForExpr σ2 l n.
  Proof using.
    intros σ1 σ2 eqv l n; unfold ChorUpSubstForExpr; rewrite eqv; reflexivity.
  Qed.

  Lemma ChorSubstExt : forall (C : Chor) (σ1 σ2 : nat -> Chor), (forall n, σ1 n = σ2 n) -> C[c|σ1] = C[c|σ2].
  Proof using.
    intro C; ChorInduction C; intros σ1 σ2 eqv; cbn; auto.
    all: try (erewrite IHC; eauto).
    all: try (erewrite IHC1; [erewrite IHC2|]; eauto; fail).
    apply ChorUpSubstForExprExt; auto.
    all: erewrite IHC1; [erewrite IHC2; [reflexivity|]|]; auto.
    apply ChorUpSubstForExprExt; auto.
    all: apply ChorUpSubstExt; auto.
  Qed.
  Lemma ChorSubstUpId : forall n, ChorUpSubst ChorIdSubst n = ChorIdSubst n.
  Proof using.
    intro n; unfold ChorUpSubst; unfold ChorIdSubst; destruct n; auto.
  Qed.

  Lemma ChorUpSubstForExprId : forall l n, ChorUpSubstForExpr ChorIdSubst l n = ChorIdSubst n.
  Proof using.
    intro n; unfold ChorUpSubstForExpr; unfold ChorIdSubst; cbn; reflexivity.
  Qed.
    
  Lemma ChorSubstIdSpec : forall C, C[c|ChorIdSubst] = C.
  Proof using.
    intro C; ChorInduction C; cbn; auto.
    all: try (rewrite IHC; auto).
    all: try (rewrite IHC1; rewrite IHC2; auto).
    erewrite ChorSubstExt; [|apply ChorUpSubstForExprId]; rewrite IHC; reflexivity.
    erewrite ChorSubstExt with (C := C2); [|apply ChorUpSubstForExprId]; rewrite IHC1; rewrite IHC2; reflexivity.
    erewrite ChorSubstExt; [|apply ChorSubstUpId]; rewrite IHC1.
    erewrite ChorSubstExt; [|apply ChorSubstUpId]; rewrite IHC2.
    reflexivity.
  Qed.      

  Lemma ChorRenameSpec : forall C ξ, C ⟨c| ξ⟩ = C [c| fun n => Var (ξ n)].
  Proof using.
    intros C; ChorInduction C; intros ξ; cbn; auto.
    all: try (rewrite IHC; auto).
    all: try (rewrite IHC1; rewrite IHC2; auto; fail).
    rewrite ChorSubstExt with (σ2 := fun n => Var (ChorUpRename ξ n)).
    rewrite ChorSubstExt with (σ1 := ChorUpSubst (fun n => Var (ξ n))) (σ2 := fun n => Var (ChorUpRename ξ n)).
    rewrite IHC1; rewrite IHC2; auto.
    all: intro n; unfold ChorUpSubst; unfold ChorUpRename; destruct n; auto.
  Qed.
    
  (* You might wonder why we don't have the ability to move over a def. It's because it's unsound! If you have l1 ⟪e⟫ → l2 ⟪x⟫ fby (let l3 ⟪y⟫ := C1 fby C2) (in the named form) then, you don't know if l2 uses x in C1 or not! *)
  
  Reserved Notation "C1 ≡ C2" (at level 30).
  Inductive equiv : Chor -> Chor -> Prop :=
  | equivTrans : forall C1 C2 C3, C1 ≡ C2 -> C2 ≡ C3 -> C1 ≡ C3
  | DoneRefl : forall l e, Done l e ≡ Done l e
  | VarRefl : forall n, Var n ≡ Var n
  | SendContext : forall l1 e l2 C1 C2,
      C1 ≡ C2 ->
      l1 ⟪e⟫ → l2 fby C1 ≡ l1 ⟪e⟫ → l2 fby C2
  | SyncContext : forall l1 d l2 C1 C2,
      C1 ≡ C2 ->
      l1 ⟨d⟩ → l2 fby C1 ≡ l1 ⟨d⟩ → l2 fby C2                  
  | IfContext : forall l e C11 C12 C21 C22,
      C11 ≡ C21 -> C12 ≡ C22 ->
      Cond l ⦃ e ⦄ Then C11 Else C12 ≡ Cond l⦃e⦄ Then C21 Else C22
  | DefLocalContext : forall l C11 C12 C21 C22,
      C11 ≡ C21 -> C12 ≡ C22 ->
      LetLocal l ⟪new⟫ ← C11 fby C12 ≡ LetLocal l ⟪new⟫ ← C21 fby C22
  | DefGlobalContext : forall C11 C12 C21 C22,
      C11 ≡ C21 -> C12 ≡ C22 ->
      LetGlobal ⟪new⟫ ← C11 fby C12 ≡ LetGlobal ⟪new⟫ ← C21 fby C22
  | SwapSendSend : forall l1 e l2 l3 e' l4 C,
      l1 <> l3 -> l1 <> l4 -> l2 <> l3 -> l2 <> l4 ->
      l1 ⟪e⟫ → l2 fby (l3 ⟪e'⟫ → l4 fby C) ≡ l3 ⟪e'⟫ → l4 fby (l1 ⟪e⟫ → l2 fby C)
  | SwapSendSync : forall l1 e l2 l3 d l4 C,
      l1 <> l3 -> l1 <> l4 -> l2 <> l3 -> l2 <> l4 ->
      l1 ⟪e⟫ → l2 fby (l3 ⟨d⟩ → l4 fby C) ≡ l3 ⟨d⟩ → l4 fby (l1 ⟪e⟫ → l2 fby C)
  | SwapSyncSend : forall l1 d l2 l3 e l4 C,
      l1 <> l3 -> l1 <> l4 -> l2 <> l3 -> l2 <> l4 ->
      l1 ⟨d⟩ → l2 fby (l3 ⟪e⟫ → l4 fby C) ≡ l3 ⟪e⟫ → l4 fby (l1 ⟨d⟩ → l2 fby C)
  | SwapSendIf : forall l1 e l2 l3 e' C1 C2,
      l1 <> l3 -> l2 <> l3 ->
      l1 ⟪e⟫ → l2 fby (Cond l3 ⦃e'⦄ Then C1 Else C2) ≡ Cond l3 ⦃e'⦄ Then (l1 ⟪e⟫ → l2 fby C1) Else (l1 ⟪e⟫ → l2 fby C2)
  | SwapIfSend : forall l1 e l2 e' l3 C1 C2,
      l1 <> l2 -> l1 <> l3 ->
      Cond l1 ⦃e⦄ Then (l2 ⟪e'⟫ → l3 fby C1) Else (l2 ⟪e'⟫ → l3 fby C2) ≡ l2 ⟪e'⟫ → l3 fby (Cond l1 ⦃e⦄ Then C1 Else C2)
  | SwapSyncSync : forall l1 d l2 l3 d' l4 C,
      l1 <> l3 -> l1 <> l4 -> l2 <> l3 -> l2 <> l4 ->
      l1 ⟨d⟩ → l2 fby (l3 ⟨d'⟩ → l4 fby C) ≡ l3 ⟨d'⟩ → l4 fby (l1 ⟨d⟩ → l2 fby C)
  | SwapSyncIf : forall l1 d l2 l3 e C1 C2,
      l1 <> l3 -> l2 <> l3 ->
      l1 ⟨d⟩ → l2 fby (Cond l3 ⦃e⦄ Then C1 Else C2) ≡ Cond l3 ⦃e⦄ Then (l1 ⟨d⟩ → l2 fby C1) Else (l1 ⟨d⟩ → l2 fby C2)
  | SwapIfSync : forall l1 e l2 d l3 C1 C2,
      l1 <> l2 -> l1 <> l3 ->
      Cond l1 ⦃e⦄ Then (l2 ⟨d⟩ → l3 fby C1) Else (l2 ⟨d⟩ → l3 fby C2) ≡ l2 ⟨d⟩ → l3 fby (Cond l1 ⦃e⦄ Then C1 Else C2)
  | SwapIfIf : forall l1 e l2 e' C1 C2 C3 C4,
      l1 <> l2 ->
      Cond l1 ⦃e⦄ Then (Cond l2 ⦃e'⦄ Then C1 Else C2) Else (Cond l2 ⦃e'⦄ Then C3 Else C4) ≡ Cond l2 ⦃e'⦄ Then (Cond l1 ⦃e⦄ Then C1 Else C3) Else (Cond l1 ⦃e⦄ Then C2 Else C4)
  where "C1 ≡ C2" := (equiv C1 C2).
  Hint Constructors equiv : Chor.

  Fixpoint equivRefl (C : Chor) : C ≡ C :=
    match C with
    | Done l e => DoneRefl l e
    | Var n => VarRefl n
    | Send l1 e l2 C => SendContext l1 e l2 C C (equivRefl C)
    | If l e C1 C2 => IfContext l e C1 C2 C1 C2 (equivRefl C1) (equivRefl C2)
    | Sync l1 d l2 C => SyncContext l1 d l2 C C (equivRefl C)
    | DefLocal l C1 C2 => DefLocalContext l C1 C2 C1 C2 (equivRefl C1) (equivRefl C2)
    | DefGlobal C1 C2 => DefGlobalContext C1 C2 C1 C2 (equivRefl C1) (equivRefl C2)
    end.
  Hint Resolve equivRefl : Chor.
  Instance : Reflexive equiv := equivRefl.

  Theorem equivSym : forall C1 C2 : Chor, C1 ≡ C2 -> C2 ≡ C1.
  Proof using.
    intros C1 C2 equiv; induction equiv; eauto with Chor.
  Qed.
  Hint Resolve equivSym : Chor.
  Instance : Symmetric equiv := equivSym.

  Instance : Transitive equiv := equivTrans.
  
  (* Smart constructors for ≡ *)
  Lemma SmartSwapSendSend : forall (p q r s : Loc) (C1 C2 : Chor) (e1 e2 : Expr),
      p <> r -> q <> r -> p <> s -> q <> s ->
      C1 ≡ C2 ->
      Send p e1 q (Send r e2 s C1) ≡ Send r e2 s (Send p e1 q C2).
  Proof using.
    intros p q r s C1 C2 e1 e2 neq_p_r neq_q_r neq_p_s neq_q_s eqv; etransitivity; [apply SwapSendSend|]; auto with Chor.
  Qed.
  Lemma SmartSwapSendIf : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡ C1' -> C2 ≡ C2' ->
      Send q e2 r (If p e1 C1 C2) ≡ If p e1 (Send q e2 r C1') (Send q e2 r C2').
  Proof using.
    intros n p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1; etransitivity; [apply SwapSendIf |]; eauto with Chor.
  Qed.
  Lemma SmartSwapIfSend : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡ C1' -> C2 ≡ C2' ->
      If p e1 (Send q e2 r C1) (Send q e2 r C2) ≡ Send q e2 r (If p e1 C1' C2').
  Proof using.
    intros n p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1; etransitivity; [apply SwapIfSend|]; eauto with Chor.
  Qed.
  Lemma SmartSwapSendSync : forall (p q r s : Loc) (e : Expr) (d : LRChoice) (C C' : Chor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡ C' ->
      Send p e q (Sync r d s C) ≡ Sync r d s (Send p e q C').
  Proof using.
    intros p q r s e d C C' neq1 neq2 neq3 neq4 equiv; etransitivity; [apply SwapSendSync|]; eauto with Chor.
  Qed.
  Lemma SmartSwapSyncSend : forall (p q r s : Loc) (e : Expr) (d : LRChoice) (C C' : Chor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡ C' ->
      Sync p d q (Send r e s C) ≡ Send r e s (Sync p d q C').
  Proof using.
    intros p q r s e d C C' neq1 neq2 neq3 neq4 equiv; etransitivity; [apply SwapSyncSend|]; eauto with Chor.
  Qed.
  Lemma SmartSwapIfIf : forall p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22',
      p <> q ->
      C11 ≡ C11' -> C12 ≡ C12' -> C21 ≡ C21' -> C22 ≡ C22' ->
      If p e1 (If q e2 C11 C12) (If q e2 C21 C22) ≡ If q e2 (If p e1 C11' C21') (If p e1 C12' C22').
  Proof using.
    intros n p e1 m q e2 C11 C11' C12 C12' C21 C21' C22 C22' neq equiv1; etransitivity; [apply SwapIfIf|]; eauto with Chor.
  Qed.
  Lemma SmartSwapIfSync : forall (p q r : Loc) (e : Expr) (d : LRChoice) (C1 C1' C2 C2' : Chor),
      p <> q -> p <> r -> C1 ≡ C1' -> C2 ≡ C2' ->
      If p e (Sync q d r C1) (Sync q d r C2) ≡ Sync q d r (If p e C1' C2').
  Proof using.
    intros m p q r e d C1 C1' C2 C2' neq1 neq2 equiv1; etransitivity; [apply SwapIfSync|]; eauto with Chor.
  Qed.
  Lemma SmartSwapSyncIf : forall (p q r : Loc) (e : Expr) (d : LRChoice) (C1 C1' C2 C2' : Chor),
      p <> r -> q <> r -> C1 ≡ C1' -> C2 ≡ C2' ->
      Sync p d q (If r e C1 C2) ≡ If r e (Sync p d q C1') (Sync p d q C2').
  Proof using.
    intros m p q r e d C1 C1' C2 C2' neq1 neq2 equiv1; etransitivity; [apply SwapSyncIf|]; eauto with Chor.
  Qed.
  Lemma SmartSwapSyncSync : forall (p q r s : Loc) (d d' : LRChoice) (C C' : Chor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡ C' ->
      Sync p d q (Sync r d' s C) ≡ Sync r d' s (Sync p d q C').
  Proof using.
    intros p q r s d d' C1 C1' neq1 neq2 neq3 neq4 equiv; etransitivity; [apply SwapSyncSync|]; auto with Chor.
  Qed.
  Hint Resolve SmartSwapSendSend SmartSwapSendIf SmartSwapIfSend SmartSwapIfIf SmartSwapSendSync SmartSwapSyncSend SmartSwapIfSync SmartSwapSyncSync : Chor.

  Lemma EquivStableExprRename : forall (ξ : Loc -> nat -> nat) (C1 C2 : Chor),
      C1 ≡ C2 -> C1 ⟨ce| ξ ⟩ ≡ C2 ⟨ce| ξ⟩.
  Proof using.
    intros ξ C1 C2 eqv; revert ξ; induction eqv; intros ξ; cbn; auto; try reflexivity.
    etransitivity; eauto.
    all: eauto with Chor.
    - unfold ChorUpExprRename at 1 4. destruct (L.eq_dec l2 l3) as [eq|_]; [destruct (H1 eq)|].
      destruct (L.eq_dec l4 l1) as [eq|_]; [destruct (H0 (eq_sym eq))|]. apply SmartSwapSendSend; auto.
      erewrite ChorExprRenameExtensional; [reflexivity|]. intros p n; unfold ChorUpExprRename.
      destruct (L.eq_dec l4 p); destruct (L.eq_dec l2 p); subst; try match goal with | [H : ?a <> ?a |- _ ] => destruct (H eq_refl) end; auto.
    - etransitivity; [apply SwapSendIf|]; auto.
      unfold ChorUpExprRename at 1; destruct (L.eq_dec l2 l3) as [eq|_]; [destruct (H0 eq)|]; reflexivity.
    - etransitivity; [apply SwapIfSend|]; auto.
      unfold ChorUpExprRename at 3. destruct (L.eq_dec l3 l1) as [eq|_]; [destruct (H0 (eq_sym eq))|]; reflexivity.
  Qed.

  Lemma EquivStableExprSubst : forall(σ : Loc -> nat -> Expr) (C1 C2 : Chor), C1 ≡ C2 -> C1 [ce| σ] ≡ C2 [ce| σ].
  Proof using.
    intros σ C1 C2 eqv; revert σ; induction eqv; intros σ; cbn; auto; try reflexivity.
    etransitivity; eauto.
    all: eauto with Chor.
    - unfold ChorUpExprSubst at 1 4; destruct (L.eq_dec l2 l3); destruct (L.eq_dec l4 l1); subst; try match goal with [H : ?a <> ?a |- _ ] => destruct (H eq_refl) end; auto.
      etransitivity; [apply SwapSendSend|]; auto; erewrite ChorExprSubstExt; [reflexivity|].
      intros p n1; unfold ChorUpExprSubst. destruct (L.eq_dec l4 p); destruct (L.eq_dec l2 p); subst; try match goal with [H : ?a <> ?a |- _] => destruct (H eq_refl) end; auto.
    - etransitivity; [apply SwapSendIf|]; auto.
      unfold ChorUpExprSubst at 1; destruct (L.eq_dec l2 l3) as [eq|_]; [destruct (H0 eq)|]; reflexivity.
    - etransitivity; [apply SwapIfSend|]; auto.
      unfold ChorUpExprSubst at 3; destruct (L.eq_dec l3 l1) as [eq|_]; [destruct (H0 (eq_sym eq))|]; reflexivity.
  Qed.

  Lemma EquivStableRename : forall (ξ : nat -> nat) (C1 C2 : Chor), C1 ≡ C2 -> C1 ⟨c| ξ⟩ ≡ C2 ⟨c| ξ ⟩.
  Proof using.
    intros ξ C1 C2 eqv; revert ξ; induction eqv; intro ξ; cbn; auto with Chor.
    transitivity (C2 ⟨c| ξ⟩); auto.
  Qed.

  Lemma EquivStableSubst : forall (σ : nat -> Chor) (C1 C2 : Chor), C1 ≡ C2 -> C1 [c| σ ] ≡ C2 [c| σ].
  Proof using.
    intros σ C1 C2 eqv; revert σ; induction eqv; intro σ; cbn; auto with Chor.
    transitivity (C2 [c| σ]); auto.
    apply SmartSwapSendSend; auto. erewrite ChorSubstExt; [reflexivity|].
    intro n; unfold ChorUpSubstForExpr.
    repeat rewrite ChorExprRenameFusion. apply ChorExprRenameExtensional.
    intros l' m; destruct (L.eq_dec l2 l'); destruct (L.eq_dec l4 l'); subst;
      try match goal with
          | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl)
          end; reflexivity.
  Qed.

  Lemma WeakSubstUpExt : forall (σ1 σ2 : nat -> Chor), (forall n, σ1 n ≡ σ2 n) -> forall n, ChorUpSubst σ1 n ≡ ChorUpSubst σ2 n.
  Proof using.
    intros σ1 σ2 H n; destruct n; unfold ChorUpSubst; cbn; auto with Chor. apply EquivStableRename; auto.
  Qed.
  Hint Resolve EquivStableExprRename EquivStableExprSubst EquivStableRename EquivStableSubst WeakSubstUpExt : Chor.

  Lemma WeakSubstUpForExprExt : forall (σ1 σ2 : nat -> Chor),
      (forall n, σ1 n ≡ σ2 n) -> forall l n, ChorUpSubstForExpr σ1 l n ≡ ChorUpSubstForExpr σ2 l n.
  Proof using.
    intros σ1 σ2 eqv l n.
    unfold ChorUpSubstForExpr. apply EquivStableExprRename; auto.
  Qed.
  Hint Resolve WeakSubstUpForExprExt : Chor.

  Lemma WeakSubstExt' : forall (σ1 σ2 : nat -> Chor) (C :Chor), (forall n, σ1 n ≡ σ2 n) -> C [c| σ1] ≡ C[c|σ2].
  Proof using.
    intros σ1 σ2 C; revert σ1 σ2; ChorInduction C; intros σ1 σ2 eqv; cbn; auto with Chor.
  Qed.
  Hint Resolve WeakSubstExt' : Chor.
  Lemma WeakSubstExt : forall (σ1 σ2 : nat -> Chor) (C1 C2 : Chor), C1 ≡ C2 -> (forall n, σ1 n ≡ σ2 n) -> C1 [c| σ1] ≡ C2 [c| σ2].
  Proof using.
    intros σ1 σ2 C1 C2 eqv; revert σ1 σ2; induction eqv; intros σ1 σ2 eqvσ; cbn; auto with Chor.
    transitivity (C2 [c|σ2]); auto with Chor.
    apply SmartSwapSendSend; auto. apply WeakSubstExt'.
    intro n. unfold ChorUpSubstForExpr. repeat rewrite ChorExprRenameFusion.
    transitivity (σ2 n ⟨ce| fun p n0 => if L.eq_dec l4 p
                                     then S (if L.eq_dec l2 p then S n0 else n0)
                                     else if L.eq_dec l2 p then S n0 else n0⟩).
    apply EquivStableExprRename; auto.
    erewrite ChorExprRenameExtensional; [reflexivity|].
    intros p n0; cbn. destruct (L.eq_dec l4 p); destruct (L.eq_dec l2 p); auto.
  Qed.
  Hint Resolve WeakSubstExt : Chor.

  Inductive Redex : Set :=
  | RDone : Loc -> Expr -> Expr -> Redex
  | RIfE : Loc -> Expr -> Expr -> Redex
  | RIfTT : Loc -> Redex
  | RIfFF : Loc -> Redex
  | RSendE : Loc -> Expr -> Expr -> Loc -> Redex
  | RSendV : Loc -> Expr -> Loc -> Redex
  | RSync : Loc -> LRChoice -> Loc -> Redex
  | RDefLocal : Loc -> Expr -> Redex
  | RDefGlobal : Redex.
  Hint Constructors Redex : Chor.
  
  Definition SendExprSubst (p : Loc) (v : Expr) : Loc -> nat -> Expr :=
    fun q n =>
      if L.eq_dec p q
      then match n with
           | 0 => v
           | S m => ExprVar m
           end
      else ExprVar n.
  Definition DefSubst (C : Chor) : nat -> Chor :=
    fun n => match n with
          | 0 => C [c| fun n => match n with
                            | 0 => DefGlobal C C
                            | S n => Var n
                            end]
          | S m => Var m
          end.

  Lemma UpSendExprSubst : forall (p q : Loc) (v : Expr),
      p <> q ->
      forall r n, ChorUpExprSubst (SendExprSubst p v) q r n = SendExprSubst p v r n.
  Proof using.
    intros l1 l2 v H l3 n.
    unfold ChorUpExprSubst; unfold SendExprSubst.
    destruct (L.eq_dec l2 l3);
      destruct (L.eq_dec l1 l3); auto.
    exfalso; apply H; transitivity l3; auto.
    destruct n; auto. rewrite ExprRenameVar; auto.
  Qed.

  Lemma DefSubstEquiv : forall C1 C2 : Chor, C1 ≡ C2 -> forall n, DefSubst C1 n ≡ DefSubst C2 n.
  Proof using.
    intros C1 C2 H n; destruct n; cbn; auto with Chor.
    apply WeakSubstExt; auto.
    intro n; destruct n; cbn; auto with Chor.
  Qed.
  Hint Resolve DefSubstEquiv : Chor.

  Inductive RChorStep : Redex -> list Loc -> Chor -> Chor -> Prop :=
  | DoneEStep : forall (l : Loc) (e1 e2 : Expr),
      ExprStep e1 e2 -> RChorStep (RDone l e1 e2) nil (Done l e1) (Done l e2)
  | SendEStep : forall (l1 l2 : Loc) (B : list Loc),
      ~ In l1 B -> ~ In l2 B -> l1 <> l2 ->
      forall (e1 e2 : Expr) (C : Chor),
        ExprStep e1 e2 -> RChorStep (RSendE l1 e1 e2 l2) B (Send l1 e1 l2 C) (Send l1 e2 l2 C)
  | SendIStep : forall (l1 l2 : Loc) (e : Expr) (C1 C2 : Chor) (B : list Loc) (R : Redex),
      RChorStep R (l1 :: l2 :: B) C1 C2 ->
      RChorStep R B (Send l1 e l2 C1) (Send l1 e l2 C2)
  | SendVStep : forall (l1 l2 : Loc) (v : Expr) (C : Chor) (B : list Loc),
      ~ In l1 B -> ~ In l2 B -> l1 <> l2 ->
      ExprVal v ->
      RChorStep (RSendV l1 v l2) B (Send l1 v l2 C) (C [ce| SendExprSubst l2 v])
  | IfEStep : forall (l1 : Loc) (e1 e2 : Expr) (C1 C2 : Chor) (B : list Loc),
      ~ In l1 B ->
      ExprStep e1 e2 ->
      RChorStep (RIfE l1 e1 e2) B (If l1 e1 C1 C2) (If l1 e2 C1 C2)
  | IfIStep : forall (l1 : Loc) (e : Expr) (C1 C2 C3 C4 : Chor) (B : list Loc) (R : Redex),
      RChorStep R (l1 :: B) C1 C3 ->
      RChorStep R (l1 :: B) C2 C4 ->
      RChorStep R B (If l1 e C1 C2) (If l1 e C3 C4)
  | IfTrueStep : forall (l1 : Loc) (C1 C2 : Chor) (B : list Loc),
      ~ In l1 B ->
      RChorStep (RIfTT l1) B (If l1 tt C1 C2) C1
  | IfFalseStep : forall (l1 : Loc) (C1 C2 : Chor) (B : list Loc),
      ~ In l1 B ->
      RChorStep (RIfFF l1) B (If l1 ff C1 C2) C2
  | DefLocalIStep : forall R l C1 C1' C2,
      RChorStep R [] C1 C1' -> (* I think this should be nil, but I'm not 100%. *)
      RChorStep R [] (DefLocal l C1 C2) (DefLocal l C1' C2)
  | DefLocalStep : forall (l : Loc) (v : Expr) (C2 : Chor),
      ExprVal v ->
      RChorStep (RDefLocal l v) nil (DefLocal l (Done l v) C2) (C2 [ce| SendExprSubst l v])
  | DefGlobalStep : forall C1 C2 : Chor,
      RChorStep RDefGlobal nil (DefGlobal C1 C2) (C2 [c| DefSubst C1])
  | SyncStep : forall (l1 l2 : Loc) (d : LRChoice) (C : Chor) (B : list Loc),
      ~ In l1 B -> ~ In l2 B ->
      RChorStep (RSync l1 d l2) B (Sync l1 d l2 C) C
  | SyncIStep : forall (l1 l2 : Loc) (d : LRChoice) (C1 C2 : Chor) (B : list Loc) (R : Redex),
      RChorStep R (l1 :: l2 :: B) C1 C2 ->
      RChorStep R B (Sync l1 d l2 C1) (Sync l1 d l2 C2).
  Hint Constructors RChorStep : Chor.

  Ltac NotInList :=
    repeat match goal with
           | [ |- ~ In ?a nil ] => let H := fresh in intro H; inversion H
           | [ nin : ~ In ?a ?l |- ~ In ?a ?l ] => exact nin
           | [ H : ~ In ?a (?b :: ?l) |- _ ] =>
             match goal with
             | [ _ : a <> b, _ : ~ In a l |- _ ] => fail 1
             | _ => assert (a <> b) by (let eq := fresh in intro eq; apply H; left; auto);
                   assert(~ In a l) by (let i := fresh in intro i; apply H; right; auto)
             end
           | [ neq : ?a <> ?b |- ~ In ?a (?b :: ?l) ] =>
             let H := fresh in
             intro H; destruct H as [eq | i]; [exfalso; apply neq; auto | revert i; fold (not (In a l))]
           | [i : ~ In ?p ?B1, ext : forall q, In q ?B1 <-> In q ?B2 |- ~ In ?p ?B2 ] =>
             let H := fresh in intro H; rewrite <- ext in H; apply i; exact H
           end.

  Lemma RStepRearrange : forall R B1 C1 C2,
      RChorStep R B1 C1 C2 -> forall B2, (forall q, In q B1 <-> In q B2) -> RChorStep R B2 C1 C2.
  Proof using.
    intros R B1 C1 C2 step; induction step; intros B2 ext.
    all: try match goal with
         | [H : forall q, In q [] <-> In q ?B |- _ ] =>
           let H' := fresh in
           assert (B = []) as H' by (let x := fresh in destruct B as [| x B]; [reflexivity | pose proof ((proj2 (H x)) ltac:(left; reflexivity)) as H'; inversion H']);
             subst; clear H
         | [H : forall q, In q ?B <-> In q [] |- _ ] =>
           let H' := fresh in
           assert (B = []) as H' by (let x := fresh in destruct B as [| x B]; [reflexivity | pose proof ((proj1 (H x)) ltac:(left; reflexivity)) as H'; inversion H']);
             subst; clear H
         end.
    all: try (constructor; try NotInList; auto; fail).
    - apply SendIStep; auto; apply IHstep; intro q; split; intro i; repeat (destruct i as [eq | i]; [left; exact eq | right]; auto); apply ext; auto.
    - apply IfIStep; [apply IHstep1 | apply IHstep2]; intro q; split; intro i; repeat (destruct i as [eq | i]; [left | right]; auto); apply ext; auto.
    - apply SyncIStep; auto; apply IHstep; intro q; split; intro i; repeat (destruct i as [eq | i]; [left; exact eq | right]; auto); apply ext; auto.
  Qed.

  Inductive RedexOf : Loc -> Redex -> Prop :=
  | RODone : forall p e1 e2, RedexOf p (RDone p e1 e2)
  | ROIfE : forall p e1 e2, RedexOf p (RIfE p e1 e2)
  | ROIfTT : forall p, RedexOf p (RIfTT p)
  | ROIfFF : forall p, RedexOf p (RIfFF p)
  | ROSendE1 : forall p e1 e2 q, RedexOf p (RSendE p e1 e2 q)
  | ROSendE2 : forall p e1 e2 q, RedexOf q (RSendE p e1 e2 q)
  | ROSendV1 : forall p v q, RedexOf p (RSendV p v q)
  | ROSendV2 : forall p v q, RedexOf q (RSendV p v q)
  | ROSync1 : forall p d q, RedexOf p (RSync p d q)
  | ROSync2 : forall p d q, RedexOf q (RSync p d q)
  | ROLDef : forall l e, RedexOf l (RDefLocal l e).
  Hint Constructors RedexOf: Chor.

  Lemma NoIStepInList : forall p B R,
      In p B ->
      RedexOf p R ->
      forall C1 C2, ~RChorStep R B C1 C2.
  Proof using.
    intros p B R H H0 C1 C2 step; induction step; inversion H0;
    match goal with
    | [ i : In ?p ?B, n : ~ In ?p' ?B, e : ?p = ?p' |- False ] =>
      apply n; rewrite <- e; exact i
    | [ i : In ?p ?B, n : ~ In ?p' ?B, e : ?p' = ?p |- False ] =>
      apply n; rewrite e; exact i
    | _ => idtac
    end.
    all: try (apply IHstep; auto; right; right; auto; fail).
    all: try (apply IHstep1; auto; right; auto; fail).
    all: inversion H.
  Qed.

  Corollary NoDoneIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RDone p e1 e2) B C1 C2.
  Proof using.
    intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply RODone.
  Qed.
  Corollary NoSendEIStepInList1 : forall p B,
      In p B ->
      forall e1 e2 C1 C2 q, ~RChorStep (RSendE p e1 e2 q) B C1 C2.
  Proof using.
    intros p B H q e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendE1.
  Qed.
  Corollary NoSendEIStepInList2 : forall B q,
      In q B ->
      forall p e1 e2 C1 C2, ~RChorStep (RSendE p e1 e2 q) B C1 C2.
  Proof using.
    intros B q H p e1 e2 C1 C2; apply NoIStepInList with (p := q); auto; apply ROSendE2.
  Qed.
  Corollary NoSendVIStepInList1 : forall p B,
      In p B ->
      forall v q C1 C2, ~RChorStep (RSendV p v q) B C1 C2.
  Proof using.
    intros p B H v q C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendV1.
  Qed.
  Corollary NoSendVIStepInList2 : forall B q,
      In q B ->
      forall p v C1 C2, ~RChorStep (RSendV p v q) B C1 C2.
  Proof using.
    intros B q H p v C1 C2; apply NoIStepInList with (p := q); auto; apply ROSendV2.
  Qed.
  Corollary NoIfEIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RIfE p e1 e2) B C1 C2.
  Proof using.
   intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfE.
  Qed.
  Corollary NoIfTTStepInList : forall p B,
      In p B ->
      forall C1 C2, ~RChorStep (RIfTT p) B C1 C2.
  Proof using.
   intros p B H C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfTT.
  Qed.
  Corollary NoIfFFStepInList : forall p B,
      In p B ->
      forall C1 C2, ~RChorStep (RIfFF p) B C1 C2.
  Proof using.
   intros p B H C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfFF.
  Qed.
  Corollary NoSyncStepInList1 : forall p B,
      In p B ->
      forall d q C1 C2, ~RChorStep (RSync p d q) B C1 C2.
  Proof using.
   intros p B H q C1 C2; apply NoIStepInList with (p := p); auto; constructor.
  Qed. 
  Corollary NoSyncStepInList2 : forall B q,
      In q B ->
      forall p d C1 C2, ~RChorStep (RSync p d q) B C1 C2.
  Proof using.
   intros B q H p C1 C2; apply NoIStepInList with (p := q); auto; constructor.
  Qed.
  Corollary NoLDefStepInList : forall B p,
      In p B ->
      forall e C1 C2, ~RChorStep (RDefLocal p e) B C1 C2.
  Proof using.
   intros B p H e C1 C2; apply NoIStepInList with (p := p); auto; constructor.
  Qed.

  Hint Resolve RStepRearrange NoDoneIStepInList : Chor.
  Hint Resolve NoSendEIStepInList1 NoSendVIStepInList1 NoSendEIStepInList2 NoSendVIStepInList2 : Chor.
  Hint Resolve NoIfEIStepInList NoIfTTStepInList NoIfFFStepInList: Chor.
  Hint Resolve NoSyncStepInList1 NoSyncStepInList2 NoLDefStepInList : Chor.

  Inductive RStepMany : list Redex -> list Loc -> Chor -> Chor -> Prop :=
  | RStepManyZero : forall B C, RStepMany nil B C C
  | RStepManyPlus : forall R Rs B C1 C2 C3, RChorStep R B C1 C2 -> RStepMany Rs B C2 C3 -> RStepMany (R :: Rs) B C1 C3.
  Hint Constructors RStepMany : Chor.

  Theorem RStepManyOne : forall (R : Redex) (B : list Loc) (C1 C2 : Chor),
      RChorStep R B C1 C2 -> RStepMany [R] B C1 C2.
  Proof using.
    intros R B C1 C2 step.
    eapply RStepManyPlus; [exact step | apply RStepManyZero].
  Qed.
  Hint Resolve RStepManyOne : Chor.

  Program Fixpoint RStepManyTrans (Rs1 Rs2 : list Redex) (B : list Loc) (C1 C2 C3 : Chor)
           (r1 : RStepMany Rs1 B C1 C2)
           (r2 : RStepMany Rs2 B C2 C3) {struct r1} : RStepMany (Rs1 ++ Rs2) B C1 C3 :=
   match r1 with
   | RStepManyZero B C => r2
   | RStepManyPlus R Rs B C1' C2' _ s1 r3 =>
     RStepManyPlus _ _ _ _ _ _ s1  (RStepManyTrans _ _ _ _ _ _ r3 r2)
   end.
  (* Hint Resolve RStepManyTrans : AChor. *)

  Lemma SendIStepMany : forall Rs B p e q C1 C2, RStepMany Rs (p :: q :: B) C1 C2 -> RStepMany Rs B (Send p e q C1) (Send p e q C2).
  Proof using.
    intros Rs B p e q C1 C2 step; revert e; dependent induction step; intros e; auto with Chor.
    apply RStepManyPlus with (R := R) (C2 := Send p e q C2). apply SendIStep; auto.
    apply IHstep; auto.
  Qed.

  Lemma IfIStepMany : forall Rs B p e C11 C12 C21 C22, RStepMany Rs (p :: B) C11 C12 -> RStepMany Rs (p :: B) C21 C22 -> RStepMany Rs B (If p e C11 C21) (If p e C12 C22).
  Proof using.
    intros Rs; induction Rs; intros B p e C11 C12 C21 C22 step1 step2; inversion step1; inversion step2; subst; auto with Chor.
    apply RStepManyPlus with (C2 := If p e C2 C4); [apply IfIStep; auto|]. apply IHRs; auto.
  Qed.
    
  Lemma SyncIStepMany : forall Rs B d p q C1 C2, RStepMany Rs (p :: q :: B) C1 C2 -> RStepMany Rs B (Sync p d q C1) (Sync p d q C2).
  Proof using.
    intros Rs; induction Rs; intros B d p q C1 C2 step; inversion step; subst; auto with Chor.
    apply RStepManyPlus with (C2 := Sync p d q C3); auto with Chor.
  Qed.
 
  Hint Resolve SendIStepMany IfIStepMany SyncIStepMany : Chor.

  Lemma ConsNotIn : forall {A : Type} (a b : A) (l : list A),
      a <> b -> ~ In a l -> ~ In a (b :: l).
  Proof using.
    intros A a b l H H0 H1.
    destruct H1; auto.
  Qed.
  Lemma NotInCons : forall {A : Type} (a b : A) (l : list A),
      ~ In a (b :: l) -> a <> b /\ ~ In a l.
  Proof using.
    intros A a b l H; split; intro H0; apply H; [left | right]; auto.
  Qed.    
  Hint Resolve ConsNotIn NotInCons : Chor.

  (* Ltac ListHelper := *)
  (*   match goal with *)
  (*   | [H : ~ In ?p (?p :: _) |- _ ] => *)
  (*     exfalso; apply H; left; reflexivity *)
  (*   | [H : ~ In ?p (_ :: ?p :: _) |- _ ] => *)
  (*     exfalso; apply H; right; left; reflexivity *)
  (*   | [H : ~ In ?r (?p :: ?q :: ?B) |- ~ In ?r ?B] => *)
  (*     let H' := fresh in intro H'; apply H; right; right; exact H' *)
  (*   | [H : ~ In ?r (?p :: ?B) |- ~ In ?r ?B ] => *)
  (*     let H' := fresh in intro H'; apply H; right; exact H' *)
  (*   | [H : ~ In ?r (?p :: _) |- ?r <> ?p ] => *)
  (*     let H' := fresh H in intro H'; apply H; left; auto *)
  (*   | [H : ~ In ?r (?p :: _) |- ?p <> ?r ] => *)
  (*     let H' := fresh H in intro H'; apply H; left; auto *)
  (*   | [H : ~ In ?r (_ :: ?p :: _) |- ?p <> ?r ] => *)
  (*     let H' := fresh H in intro H'; apply H; right; left; auto                                                       *)
  (*   | [H : ~ In ?r (_ :: ?p :: _) |- ?r <> ?p ] => *)
  (*     let H' := fresh H in intro H'; apply H; right; left; auto                                                       *)
  (*   end. *)
  Ltac InList := repeat match goal with
                        | [ H : ?P |- ?P ] => exact H
                        | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl)
                        | [ |- In ?a (?a :: _) ] => left; reflexivity
                        | [ i : In ?a (_ :: _) |- _ ] => destruct i; subst
                        | [ |- In ?a (_ :: _) ] => right
                        end.

  Lemma RetEquivInversion : forall l e C, Done l e ≡ C -> C = Done l e.
  Proof using.
    intros l e C eqv; dependent induction eqv; auto.
  Qed.
                                         
  Theorem EquivSimulation : forall C1 C2, C1 ≡ C2 -> forall R B C1',
        RChorStep R B C1 C1' -> exists C2', RChorStep R B C2 C2' /\ C1' ≡ C2'.
  Proof using.
    intros C1 C2 equiv; induction equiv; intros R B Cstep step;
      eauto with Chor; repeat match goal with
                              | [ H : RChorStep ?R ?B ?C1 ?C1' |- _ ] =>
                                tryif (let x := fresh "fail_" C1 in idtac)
                                then fail
                                else inversion H; subst; eauto with Chor; clear H
                              end.
    all: try (eexists; split; eauto with Chor; fail).
    all: repeat match goal with
                | [IH : forall R B C', RChorStep R B ?C C' -> exists C2', RChorStep R B ?C2 C2' /\ C' ≡ C2', H : RChorStep ?R ?B ?C ?C' |- _ ] =>
                  lazymatch goal with
                  | [ _ : RChorStep R B C2 ?C2', _ : C' ≡ ?C2' |- _] => fail
                  | _ => let H' := fresh in
                        let C2 := fresh "C" in
                        let step := fresh "step" in
                        let eqv := fresh "eqv" in
                        pose proof (IH R B C' H) as H'; destruct H' as [C2 [step eqv]]
                  end
                end; eauto with Chor.
    apply RetEquivInversion in equiv1; subst; eexists; split; eauto with Chor.
    all: try (exfalso; eapply NoIStepInList; eauto; eauto with Chor; InList; fail).
    all: try (eexists; split; [repeat econstructor |]; eauto with Chor; try NotInList; auto; try (eapply RStepRearrange; eauto with Chor; intros q; split; unfold In; intro i; tauto); fail).
    - exists (l1 ⟪e⟫ → l2 fby C [ce|SendExprSubst l4 e']); split; eauto with Chor.
      pose proof (SendVStep l3 l4 e' (l1 ⟪e⟫ → l2 fby C) B ltac:(NotInList) ltac:(NotInList) H13 H14) as H3; cbn in H3.
      unfold SendExprSubst in H3 at 1; destruct (L.eq_dec l4 l1) as [eq|_]; [destruct (H0 (eq_sym eq))|].
      fold ExprIdSubst in H3; rewrite ExprIdentitySubstSpec in H3.
      rewrite ChorExprSubstExt with (σ2 := SendExprSubst l4 e') in H3; auto.
      intros p n; unfold ChorUpExprSubst. unfold SendExprSubst.
      destruct (L.eq_dec l2 p) as [eq1 | neq1]; destruct(L.eq_dec l4 p) as [eq2 |neq2];
        subst; try match goal with
                   | [H : ?a <> ?a |- _ ] => destruct (H eq_refl)
                   end.
      destruct n; cbn; auto; apply ExprRenameVar.
      all: reflexivity.
    - exists (l3 ⟪e'⟫ → l4 fby (C [ce|SendExprSubst l2 e])); split; auto with Chor.
      cbn; unfold SendExprSubst at 1;
        destruct (L.eq_dec l2 l3) as [eq |_]; [destruct (H1 eq)|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec.
      rewrite ChorExprSubstExt with (σ2 := SendExprSubst l2 e); auto with Chor.
      intros p n; unfold ChorUpExprSubst; unfold SendExprSubst.
      destruct (L.eq_dec l4 p); destruct (L.eq_dec l2 p); subst;
        try (match goal with | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl) end).
      1,2: destruct n; cbn; auto. rewrite ExprRenameVar; reflexivity. reflexivity.
    - exists (Cond l3 ⦃ e' ⦄ Then C1 [ce|SendExprSubst l2 e] Else C2 [ce|SendExprSubst l2 e]);
        split; auto with Chor.
      cbn; unfold SendExprSubst at 1;
        destruct (L.eq_dec l2 l3) as [eq|_]; [destruct (H0 eq)|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec; reflexivity.
    - exists ((Cond l1 ⦃ e ⦄ Then C1 Else C2) [ce|SendExprSubst l3 e']); split; auto with Chor.
      apply SendVStep; try NotInList; auto.
      cbn; unfold SendExprSubst at 3; destruct (L.eq_dec l3 l1) as [eq | _];
        [destruct (H0 (eq_sym eq))|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec; reflexivity.
  Qed.

  Inductive StdChorStep : Chor -> Chor -> Prop :=
  | StdDoneEStep : forall (l : Loc) (e1 e2 : Expr),
      ExprStep e1 e2
      -> StdChorStep (Done l e1) (Done l e2)
  | StdSendEStep : forall (l1 l2 : Loc) (e1 e2 : Expr) (C : Chor),
      ExprStep e1 e2
      -> l1 <> l2
      -> StdChorStep (Send l1 e1 l2 C) (Send l1 e2 l2 C)
  | StdSendVStep : forall (l1 l2 : Loc) (v : Expr) (C : Chor),
      ExprVal v
      -> l1 <> l2
      -> StdChorStep (Send l1 v l2 C) (C [ce| SendExprSubst l2 v])
  | StdIfEStep : forall (l : Loc) (e1 e2 : Expr) (C1 C2 : Chor),
      ExprStep e1 e2
      -> StdChorStep (If l e1 C1 C2) (If l e2 C1 C2)
  | StdIfTrueStep : forall (l : Loc) (C1 C2 : Chor),
      StdChorStep (If l tt C1 C2) C1
  | StdIfFalseStep : forall (l : Loc) (C1 C2 : Chor),
      StdChorStep (If l ff C1 C2) C2
  | StdSyncStep : forall (l1 l2 : Loc) (d : LRChoice) (C : Chor),
      StdChorStep (Sync l1 d l2 C) C
  | StdDefLocalIStep : forall (l : Loc) (C1 C1' C2 : Chor),
      StdChorStep C1 C1' -> StdChorStep (DefLocal l C1 C2) (DefLocal l C1' C2)
  | StdDefLocalStep : forall (l : Loc) (v : Expr) (C : Chor),
      ExprVal v ->
      StdChorStep (DefLocal l (Done l v) C) (C [ce|SendExprSubst l v])
  | StdDefStep : forall (C1 C2 : Chor),
      StdChorStep (DefGlobal C1 C2) (C2 [c| DefSubst C1])
  | StdEquivStep : forall (C1 C1' C2 C2' : Chor),
      C1 ≡ C1'
      -> StdChorStep C1' C2'
      -> C2 ≡ C2'
      -> StdChorStep C1 C2.
  Hint Constructors StdChorStep : Chor.

  Theorem StdToRStep : forall (C1 C2 : Chor),
      StdChorStep C1 C2
      -> exists R C2', C2 ≡ C2' /\ RChorStep R nil C1 C2'.
  Proof using.
    intros C1 C2 stdstep; induction stdstep.
    all:try ( eexists; eexists; split; [reflexivity | constructor; auto]; fail).
    - destruct IHstdstep as [R [C2' [equiv step]]].
      exists R; exists (LetLocal l ⟪new⟫ ← C2' fby C2); split; auto with Chor.
    - destruct IHstdstep as [R [C2'' [equiv step]]].
      destruct (EquivSimulation C1' C1 ltac:(auto with Chor) R [] C2'' step) as [C2''' [step' equiv']].
      exists R; exists C2'''; split; auto with Chor. transitivity C2'; auto; transitivity C2''; auto.
  Qed.

  Inductive RedexOnTop : Redex -> Chor -> Prop :=
  | DoneOnTop : forall p e1 e2, RedexOnTop (RDone p e1 e2) (Done p e1)
  | SendEOnTop : forall p e1 e2 q C, RedexOnTop (RSendE p e1 e2 q) (Send p e1 q C)
  | SendVOnTop : forall p v q C, RedexOnTop (RSendV p v q) (Send p v q C)
  | IfEOnTop : forall p e1 e2 C1 C2, RedexOnTop (RIfE p e1 e2) (If p e1 C1 C2)
  | IfTTOnTop : forall p C1 C2, RedexOnTop (RIfTT p) (If p tt C1 C2)
  | IfFFOnTop : forall p C1 C2, RedexOnTop (RIfFF p) (If p ff C1 C2)
  | SyncOnTop : forall p d q C, RedexOnTop (RSync p d q) (Sync p d q C)
  | IDefLocalOntop : forall l C1 C2 R, RedexOnTop R C1 -> RedexOnTop R (DefLocal l C1 C2)
  | DefLocalOnTop : forall l e C, RedexOnTop (RDefLocal l e) (DefLocal l (Done l e) C)
  | DefGlobalOnTop : forall C1 C2, RedexOnTop RDefGlobal (DefGlobal C1 C2).
  Hint Constructors RedexOnTop : Chor.

  Lemma RStepOnTop : forall (R : Redex) (B : list Loc) (C1 C2 : Chor),
      RChorStep R B C1 C2 ->
      exists C1' C2', C1 ≡ C1' /\ C2 ≡ C2' /\ RChorStep R B C1' C2' /\ RedexOnTop R C1'.
  Proof using.
    intros R B C1 C2 step; induction step.
    all: try(eexists; eexists; split; [|split; [|split]]; eauto with Chor; fail).
    - destruct IHstep as [C1' [C2' [equiv1 [equiv2 [step' ontop]]]]].
      destruct R; inversion ontop; subst.
      all: inversion step'; subst.
      all: try (exfalso; eapply NoIStepInList; eauto; eauto with Chor; InList; fail).
      -- exists (If l e0 (Send l1 e l2 C0) (Send l1 e l2 C3)).
         exists (If l e1 (Send l1 e l2 C0) (Send l1 e l2 C3)).
         split; [|split;[|split]]; auto with Chor.
         --- transitivity (Send l1 e l2 (If l e0 C0 C3)); auto with Chor.
             apply SwapSendIf; auto with Chor; NotInList; auto.
         --- transitivity (Send l1 e l2 (If l e1 C0 C3)); auto with Chor.
             apply SwapSendIf; auto with Chor; NotInList; auto.
         --- constructor; auto; NotInList.
      -- exists (If l tt (Send l1 e l2 C2') (Send l1 e l2 C3));
           exists (Send l1 e l2 C2');
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (Send l1 e l2 (If l tt C2' C3)); auto with Chor.
             apply SwapSendIf; auto with Chor; NotInList; auto.
         --- apply IfTrueStep; NotInList; auto.
      -- exists (If l ff (Send l1 e l2 C0) (Send l1 e l2 C2'));
           exists (Send l1 e l2 C2');
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (Send l1 e l2 (If l ff C0 C2')); auto with Chor.
             apply SwapSendIf; auto with Chor; NotInList; auto.
         --- apply IfFalseStep; NotInList; auto.
      -- exists (Send l e0 l0 (Send l1 e l2 C));
           exists (Send l e1 l0 (Send l1 e l2 C));
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (Send l1 e l2 (Send l e0 l0 C)); auto with Chor.
             apply SwapSendSend; auto with Chor; NotInList; auto.
         --- transitivity (Send l1 e l2 (Send l e1 l0 C)); auto with Chor.
              apply SwapSendSend; auto with Chor; NotInList; auto.
         --- apply SendEStep; auto; NotInList; auto.
      -- exists (Send l e0 l0 (Send l1 e l2 C));
           exists (Send l1 e l2  C [ce| SendExprSubst l0 e0]);
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (Send l1 e l2 (Send l e0 l0 C)); auto with Chor.
             apply SwapSendSend; auto with Chor; NotInList; auto.
         ---  simpl. unfold SendExprSubst at 1.
              destruct (L.eq_dec l0 l1) as [eq | _];
                [subst; NotInList; match goal with
                                     [H : ?a <> ?a |- _ ] => destruct (H eq_refl)
                                   end|].
              fold ExprIdSubst; rewrite ExprIdentitySubstSpec.
              assert (C [ce|SendExprSubst l0 e0]
                      = C [ce|ChorUpExprSubst (SendExprSubst l0 e0) l2]) as H
                  by (apply ChorExprSubstExt;
                      intros p5 n; symmetry; apply UpSendExprSubst; NotInList; auto).
              rewrite <- H; auto with Chor.
         --- apply SendVStep; auto with Chor; NotInList; auto.
      -- rename l0 into d; rename l3 into l0; exists (Sync l d l0 (Send l1 e l2 C2')); exists (Send l1 e l2 C2'); split; [|split; [|split]]; eauto with Chor.
         --- transitivity (Send l1 e l2 (Sync l d l0 C2')); eauto with Chor. apply SwapSendSync; auto with Chor; NotInList; auto.
         --- apply SyncStep; intro i; [apply H5 | apply H6]; right; right; auto.
    - destruct IHstep1 as [C1' [C3' [equiv1 [equiv3 [step13 ontop1]]]]].
      destruct IHstep2 as [C2' [C4' [equiv2 [equiv4 [step24 ontop2]]]]].
      destruct R; inversion ontop1; subst; inversion ontop2; subst; inversion step13; subst; inversion step24; subst.
      all: try (exfalso; eapply NoIStepInList; eauto; eauto with Chor; InList; fail).
      -- exists (If l e0 (If l1 e C0 C6) (If l1 e C5 C7));
           exists (If l e1 (If l1 e C0 C6) (If l1 e C5 C7));
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (If l1 e (If l e0 C0 C5) (If l e0 C6 C7)); auto with Chor.
             apply SwapIfIf; auto with Chor; NotInList; auto.
         --- transitivity (If l1 e (If l e1 C0 C5) (If l e1 C6 C7)); auto with Chor.
             apply SwapIfIf; auto with Chor; NotInList; auto.
         --- apply IfEStep; auto with Chor; NotInList; auto.
      -- exists (If l tt (If l1 e C3' C4') (If l1 e C5 C7));
           exists (If l1 e C3' C4');
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (If l1 e (If l tt C3' C5) (If l tt C4' C7)); auto with Chor; apply SwapIfIf; auto with Chor; NotInList; auto.
         --- apply IfTrueStep; NotInList; auto.
      -- exists (If l ff (If l1 e C0 C6) (If l1 e C3' C4'));
           exists (If l1 e C3' C4');
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (If l1 e (If l ff C0 C3') (If l ff C6 C4')); auto with Chor; apply SwapIfIf; auto with Chor; NotInList; auto.
         --- apply IfFalseStep; NotInList; auto.
      -- exists (Send l e0 l0 (If l1 e C C0));
           exists (Send l e1 l0 (If l1 e C C0));
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (If l1 e (Send l e0 l0 C) (Send l e0 l0 C0)); auto with Chor.
             apply SwapIfSend; auto with Chor; NotInList; auto.
         --- transitivity (If l1 e (Send l e1 l0 C) (Send l e1 l0 C0)); auto with Chor.
             apply SwapIfSend; auto with Chor; NotInList; auto.
         --- apply SendEStep; auto; NotInList; auto.
      -- exists (Send l e0 l0 (If l1 e C C0));
           exists (If l1 e C C0 [ce|SendExprSubst l0 e0]);
           split; [| split; [| split]]; auto with Chor.
         --- transitivity (If l1 e (Send l e0 l0 C) (Send l e0 l0 C0)); auto with Chor.
             apply SwapIfSend; auto with Chor; NotInList; auto.
         --- transitivity (If l1 e (C [ce|SendExprSubst l0 e0]) (C0 [ce|SendExprSubst l0 e0])); auto with Chor.
             simpl. unfold SendExprSubst at 3.
             destruct (L.eq_dec l0 l1) as [eq | _]; 
               [subst; NotInList; match goal with [ H : ?a <> ?a |- _] => destruct (H eq_refl) end |].
             fold ExprIdSubst; rewrite ExprIdentitySubstSpec; reflexivity.
         --- apply SendVStep; auto; NotInList; auto.
      -- rename l0 into d; rename l2 into l0; exists (Sync l d l0 (If l1 e C3' C4')); exists (If l1 e C3' C4'); split; [|split; [|split]]; auto with Chor.
         assert (l1 <> l) by (intro eq; apply H5; left; auto).
         assert (l1 <> l0) by (intro eq; apply H6; left; auto).
         transitivity (If l1 e (Sync l d l0 C3') (Sync l d l0 C4')); auto with Chor.
         apply SyncStep; intro i; [apply H5 | apply H6]; right; auto.
    - destruct IHstep as [C1'' [C2' [equiv1 [equiv2 [step12 ontop1]]]]].
      exists (LetLocal l ⟪new⟫ ← C1'' fby C2);
        exists (LetLocal l ⟪new⟫ ← C2' fby C2);
        split; [|split; [|split]]; auto with Chor.
    - destruct IHstep as [C1' [C2' [equiv1 [equiv2 [step12 ontop1]]]]].
      destruct R; inversion ontop1; subst; inversion ontop1; subst; inversion step12; subst.
      all: try (exfalso; eapply NoIStepInList; eauto; eauto with Chor; InList; fail).
      all: NotInList.
      -- exists (If l e (Sync l1 d l2 C0) (Sync l1 d l2 C3));
           exists (If l e0 (Sync l1 d l2 C0) (Sync l1 d l2 C3)); split; [|split; [|split]];
             eauto with Chor.
      -- exists (If l tt (Sync l1 d l2 C2') (Sync l1 d l2 C3)); exists (Sync l1 d l2 C2'); split; [|split; [|split]]; eauto with Chor.
      -- exists (If l ff (Sync l1 d l2 C0) (Sync l1 d l2 C2')); exists (Sync l1 d l2 C2'); split; [|split; [|split]]; eauto with Chor.
      -- exists (Send l e l0 (Sync l1 d l2 C)); exists (Send l e0 l0 (Sync l1 d l2 C));
           split; [|split; [|split]]; eauto with Chor.
      -- exists (Send l e l0 (Sync l1 d l2 C)); exists (Sync l1 d l2 C [ce| SendExprSubst l0 e]);
           split; [|split; [|split]]; eauto with Chor.
      -- rename l0 into d'. rename l3 into l0. exists (Sync l d' l0 (Sync l1 d l2 C2')); exists (Sync l1 d l2 C2'); split; [|split; [|split]]; eauto with Chor.
  Qed.

  Lemma RStepOnTopToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Loc),
      RedexOnTop R C1 ->
      RChorStep R B C1 C2 ->
      StdChorStep C1 C2.
  Proof using.
    intros C1 C2 R B ontop rstep; induction rstep; inversion ontop; subst;
      eauto with Chor.
    - apply NoSendEIStepInList1 in rstep; [destruct rstep| left; reflexivity].
    - apply NoSendVIStepInList1 in rstep; [destruct rstep | left; reflexivity].
    - apply NoIfEIStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - apply NoIfTTStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - apply NoIfFFStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - inversion rstep.
    - apply NoSyncStepInList1 in rstep; [destruct rstep | left; reflexivity].
  Qed.
  Theorem RStepToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Loc),
      RChorStep R B C1 C2 -> StdChorStep C1 C2.
  Proof using.
    intros C1 C2 R B rstep.
    apply RStepOnTop in rstep;
      destruct rstep as [C1' H]; destruct H as [C2' H];
      destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [rstep ontop].
    apply StdEquivStep with (C1' := C1') (C2' := C2'); auto.
    apply RStepOnTopToStd with (R := R) (B := B); auto.
  Qed.
  
  Fixpoint ThreadNames (C : Chor) : list Loc :=
    match C with
    | Done p _ => p :: nil
    | Var _ => nil
    | Send p _ q C' => p :: q :: (ThreadNames C')
    | If p _ C1 C2 => p :: (ThreadNames C1) ++ (ThreadNames C2)
    | Sync p d q C => p :: q :: ThreadNames C
    | DefLocal l C1 C2 => l :: (ThreadNames C1) ++ (ThreadNames C2)
    | DefGlobal C1 C2 => (ThreadNames C1) ++ (ThreadNames C2)
    end.

  Reserved Infix "∈TN" (at level 20).
  Inductive InThreadNames : Loc -> Chor -> Prop :=
  | InDone : forall p e, p ∈TN (Done p e)
  | InSend1 : forall p e q C', p ∈TN (Send p e q C')
  | InSend2 : forall p e q C', q ∈TN (Send p e q C')
  | InSend3 : forall r p e q C', r ∈TN C' -> r ∈TN (Send p e q C')
  | InIf1 : forall p e C1 C2, p ∈TN (If p e C1 C2)
  | InIf2 : forall q p e C1 C2, q ∈TN C1 -> q ∈TN (If p e C1 C2)
  | InIf3 : forall q p e C1 C2, q ∈TN C2 -> q ∈TN (If p e C1 C2)
  | InSync1 : forall p d q C, p ∈TN (Sync p d q C)
  | InSync2 : forall p d q C, q ∈TN (Sync p d q C)
  | InSync3 : forall p d q r C, r ∈TN C -> r ∈TN (Sync p d q C)
  | InDefL1 : forall p C1 C2, p ∈TN (DefLocal p C1 C2)
  | InDefL2 : forall p q C1 C2, p ∈TN C1 -> p ∈TN (DefLocal q C1 C2)
  | InDefL3 : forall p q C1 C2, p ∈TN C2 -> p ∈TN (DefLocal q C1 C2)
  | InDefG1 : forall p C1 C2, p ∈TN C1 -> p ∈TN (DefGlobal C1 C2)
  | InDefG2 : forall p C1 C2, p ∈TN C2 -> p ∈TN (DefGlobal C1 C2)
  where "p ∈TN C" := (InThreadNames p C).

  Lemma InThreadNamesSpec : forall p C, p ∈TN C <-> In p (ThreadNames C).
  Proof using.
    intros p C; revert p; ChorInduction C; intro r; split; intro i; simpl in *.
    all: try (match goal with
              | [H : ?r ∈TN ?C |- _] => inversion H; subst
              end); auto.
    all: repeat (match goal with
                 | [H : In ?a (?b :: ?l) |- _] => simpl in H
                 | [H : In ?a (?l1 ++ ?l2) |- _] => apply in_app_or in H
                 | [H : ?P \/ ?Q |- _] => destruct H
                 | [H : ?P /\ ?Q |- _] => destruct H
                 | [H : False |- _ ] => destruct H
                 | [ |- ?p = ?q \/ _ ] =>
                   match p with
                   | q => left; reflexivity
                   | _ => right
                   end
                 end; subst).
    all: try (rewrite H; constructor; auto; fail).
    all: try (constructor; rewrite IHC; auto; fail).
    all: try (constructor; rewrite IHC1; auto; fail).
    all: try (constructor; rewrite IHC2; auto; fail).
    all: try (rewrite <- IHC; auto).
    all: try (apply in_or_app; left; rewrite <- IHC1; auto; fail).
    all: apply in_or_app; right; rewrite <- IHC2; auto.
  Qed.             

  Lemma ThreadNamesInvariant : forall C1 C2 : Chor,
      C1 ≡ C2 -> forall p : Loc, p ∈TN C1 <-> p ∈TN C2.
  Proof using.
    intros C1 C2 equiv; induction equiv; intros t; split; intros i; auto;
      repeat match goal with
             | [i : ?p ∈TN (_ _) |- _] => inversion i; subst; clear i
             end.
    all: try (constructor; auto; fail).
    all: try (constructor; constructor; auto; fail).
    all: try (constructor; apply IHequiv; auto; fail).
    all: try (constructor; rewrite IHequiv1; auto; fail).
    all: try (constructor; rewrite <- IHequiv1; auto; fail).
    all: try (constructor; rewrite IHequiv2; auto; fail).
    all: try (constructor; rewrite <- IHequiv2; auto; fail).
    - apply IHequiv1 in i; apply IHequiv2 in i; exact i.
    - apply (proj2 (IHequiv1 t)); apply (proj2 (IHequiv2 t)); exact i.
  Qed.

End Choreography.
 
