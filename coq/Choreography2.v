Require Export Expression.
Require Import PiCalc.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Sorted Orders Coq.Sorting.Mergesort Permutation.
Require Import Program.Tactics.

Module Choreography (Import E : Expression).

  Parameter Prin : Set.
  Parameter PrinEqDec : forall p q : Prin, {p = q} + {p <> q}.

  Inductive Chor : Set :=
    CDone : Prin -> Expr -> Chor
  | CVar : nat -> Chor
  | CSend : Prin -> Expr -> Prin -> Chor -> Chor
  | CIf : Prin -> Expr -> Chor -> Chor -> Chor
  | CDef : Chor -> Chor -> Chor.
  Hint Constructors Chor : Chor.

  Inductive ChorVal : Chor -> Prop :=
    VDone : forall (p : Prin) (v : Expr), ExprVal v -> ChorVal (CDone p v).

  Definition ChorUpRename : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S n => S (ξ n)
            end.
  Definition ChorUpExprRename : (Prin -> nat -> nat) -> Prin -> Prin -> nat -> nat :=
    fun ξ p q => if PrinEqDec p q
              then ExprUpRename (ξ q)
              else ξ q.
  
  Fixpoint ChorRename (C : Chor) (ξₖ : nat -> nat) (ξₑ : Prin -> nat -> nat) : Chor :=
    match C with
    | CDone p e => CDone p (e ⟨e| (ξₑ p)⟩)
    | CVar n => CVar (ξₖ n)
    | CSend p e q C => CSend p (e ⟨e| (ξₑ p)⟩) q (ChorRename C ξₖ (ChorUpExprRename ξₑ q))
    | CIf p e C1 C2 => CIf p (e ⟨e| (ξₑ p)⟩) (ChorRename C1 ξₖ ξₑ) (ChorRename C2 ξₖ ξₑ)
    | CDef C1 C2 => CDef (ChorRename C1 (ChorUpRename ξₖ) ξₑ) (ChorRename C2 (ChorUpRename ξₖ) ξₑ)
    end.
  Notation "C ⟨c| x1 ; x2 ⟩" := (ChorRename C x1 x2) (at level 20).

  Definition ChorIdRename : nat -> nat := fun n => n.
  Definition ChorIdExprRename : Prin -> nat -> nat := fun _ n => n.
  
  Lemma ChorUpIdRename : forall n, ChorUpRename ChorIdRename n = ChorIdRename n.
  Proof.
    intros n; destruct n; unfold ChorUpRename; unfold ChorIdRename; reflexivity.
  Qed.

  Lemma ChorUpIdExprRename : forall p q n, ChorUpExprRename ChorIdExprRename p q n
                                    = ChorIdExprRename p n.
  Proof.
    intros p q n; destruct n; unfold ChorUpExprRename; unfold ChorIdExprRename.
    all: destruct (PrinEqDec p q) as [_|neq]; simpl; reflexivity.
  Qed.

  Lemma ChorUpRenameExt : forall (ξ1 ξ2 : nat -> nat),
      (forall n : nat, ξ1 n = ξ2 n) ->
      forall n : nat, ChorUpRename ξ1 n = ChorUpRename ξ2 n.
  Proof.
    intros ξ1 ξ2 eq n; unfold ChorUpRename; destruct n; auto.
  Qed.

  Lemma ChorUpExprRenameExt : forall (ξ1 ξ2 : Prin -> nat -> nat),
      (forall (p : Prin) (n : nat), ξ1 p n = ξ2 p n) ->
      forall (p q : Prin) (n : nat), ChorUpExprRename ξ1 p q n = ChorUpExprRename ξ2 p q n.
  Proof.
    intros ξ1 ξ2 eq p q n. unfold ChorUpExprRename. unfold ExprUpRename.
    destruct (PrinEqDec p q); auto.
    destruct n; auto.
  Qed.
    
  Lemma ChorRenameExtensional : forall (ξₖ₁ ξₖ₂ : nat -> nat) (ξₑ₁ ξₑ₂ : Prin -> nat -> nat),
      (forall n : nat, ξₖ₁ n = ξₖ₂ n) -> (forall (p : Prin) (n : nat), ξₑ₁ p n = ξₑ₂ p n) ->
      forall (C : Chor), C ⟨c| ξₖ₁; ξₑ₁ ⟩ = C ⟨c| ξₖ₂; ξₑ₂⟩.
  Proof.
    intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2 C; revert ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; induction C;
      intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; simpl.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
    - rewrite eq1; auto.
    - rewrite IHC with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ChorUpExprRename ξₑ₂ p0); auto.
      rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      apply ChorUpExprRenameExt; auto.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      rewrite IHC1 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC2 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
    - rewrite IHC1 with (ξₖ₂ := ChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC2 with (ξₖ₂ := ChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      all: apply ChorUpRenameExt; auto.
  Qed.

  Lemma ChorRenameFusion : forall (C : Chor) (ξc1 ξc2 : nat -> nat) (ξe1 ξe2 : Prin -> nat -> nat),
      (C ⟨c| ξc1; ξe1⟩)⟨c| ξc2; ξe2⟩ = C ⟨c| fun n => ξc2 (ξc1 n); fun p n => ξe2 p (ξe1 p n)⟩.
  Proof.
    intro C; induction C; intros ξc1 ξc2 ξe1 ξe2; simpl.
    - rewrite ExprRenameFusion; reflexivity.
    - reflexivity.
    - rewrite IHC. unfold ChorUpExprRename. unfold ExprUpRename.
      rewrite ExprRenameFusion.
      erewrite ChorRenameExtensional;[reflexivity | simpl; reflexivity |].
      intros p1 n.
      simpl. destruct (PrinEqDec p0 p1); auto.
      destruct n; auto.
    - rewrite IHC1; rewrite IHC2; rewrite ExprRenameFusion; auto.
    - rewrite IHC1. rewrite IHC2. unfold ChorUpRename.
      rewrite ChorRenameExtensional with (ξₖ₂ := fun n => match n with
                                                      | 0 => 0
                                                      | S n0 => S (ξc2 (ξc1 n0))
                                                      end)
                                         (ξₑ₂ := fun p n => ξe2 p (ξe1 p n)).
      rewrite ChorRenameExtensional with (ξₖ₂ := fun n => match n with
                                                      | 0 => 0
                                                      | S n0 => S (ξc2 (ξc1 n0))
                                                      end)
                                         (ξₑ₂ := fun p n => ξe2 p (ξe1 p n))
                                         (ξₖ₁ := fun n => match match n with
                                                            | 0 => 0
                                                            | S n0 => S (ξc1 n0)
                                                            end with
                                                      | 0 => 0
                                                      | S n0 => S (ξc2 n0)
                                                      end); [reflexivity | |].
      -- intro n; destruct n; reflexivity.
      -- reflexivity.
      -- intro n; destruct n; reflexivity.
      -- reflexivity.
  Qed.
      
  Definition ChorUpSubst : (nat -> Chor) -> nat -> Chor :=
    fun σ n =>
      match n with
      | 0 => CVar 0
      | S n => (σ n) ⟨c| S ; fun _ => ExprIdRenaming⟩
      end.

  Definition ChorUpExprSubst : (Prin -> nat -> Expr) -> Prin -> Prin -> nat -> Expr :=
    fun σ p q n =>
      if PrinEqDec p q then
        match n with
        | 0 => ExprVar 0
        | S n => (σ q n) ⟨e| S ⟩
        end
      else σ q n.
  Definition SendUpChorSubst (σk : nat -> Chor) (p : Prin) : nat -> Chor :=
    fun n => (σk n)⟨c| ChorIdRename; fun q m => if PrinEqDec p q
                                          then S m
                                          else m⟩.

  Fixpoint ChorSubst (C : Chor) (σₖ : nat -> Chor) (σₑ : Prin -> nat -> Expr) : Chor :=
    match C with
    | CDone p e => CDone p (e [e| (σₑ p)])
    | CVar n => σₖ n
    | CSend p e q C => CSend p (e [e| (σₑ p)]) q (ChorSubst C (SendUpChorSubst σₖ q) (ChorUpExprSubst σₑ q))
    | CIf p e C1 C2 => CIf p (e [e| (σₑ p)]) (ChorSubst C1 σₖ σₑ) (ChorSubst C2 σₖ σₑ)
    | CDef C1 C2 => CDef (ChorSubst C1 (ChorUpSubst σₖ) σₑ) (ChorSubst C2 (ChorUpSubst σₖ) σₑ)
    end.
  Notation "C [c| s1 ; s2 ]" := (ChorSubst C s1 s2) (at level 20).

  Lemma ChorUpSubstExt : forall (σ1 σ2 : nat -> Chor),
      (forall n : nat, σ1 n = σ2 n) ->
      forall n : nat, ChorUpSubst σ1 n = ChorUpSubst σ2 n.
  Proof.
    intros σ1 σ2 eq n; unfold ChorUpSubst.
    destruct n; auto; rewrite eq; reflexivity.
  Qed.

  Lemma ChorUpExprSubstExt : forall (σ1 σ2 : Prin -> nat -> Expr),
      (forall (p : Prin) (n : nat), σ1 p n = σ2 p n) ->
      forall (p q : Prin) (n : nat), ChorUpExprSubst σ1 p q n = ChorUpExprSubst σ2 p q n.
  Proof.
    intros σ1 σ2 eq p q n; unfold ChorUpExprSubst; destruct n; auto; repeat (rewrite eq);
      reflexivity.
  Qed.

  Lemma ChorSubstExt : forall (σk1 σk2 : nat -> Chor) (σe1 σe2 : Prin -> nat -> Expr),
      (forall n : nat, σk1 n = σk2 n) ->
      (forall (p : Prin) (n : nat), σe1 p n = σe2 p n) ->
      forall C, C [c| σk1; σe1] = C [c| σk2; σe2].
  Proof.
    intros σk1 σk2 σe1 σe2 eqk eqe C; revert σk1 σk2 σe1 σe2 eqk eqe;
      induction C; intros σk1 σk2 σe1 σe2 eqk eqe; simpl; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC with (σk2 := SendUpChorSubst σk2 p0) (σe2 := ChorUpExprSubst σe2 p0); auto.
      intro n; unfold SendUpChorSubst; rewrite eqk; reflexivity.
      apply ChorUpExprSubstExt; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC1 with (σk2 := σk2) (σe2 := σe2); auto.
      rewrite IHC2 with (σk2 := σk2) (σe2 := σe2); auto.
    - rewrite IHC1 with (σk2 := ChorUpSubst σk2) (σe2 := σe2); auto.
      rewrite IHC2 with (σk2 := ChorUpSubst σk2) (σe2 := σe2); auto.
      all: apply ChorUpSubstExt; auto.
  Qed.
  
  Definition ChorIdSubst : nat -> Chor := fun n => CVar n.
  Definition ExprChorIdSubst : Prin -> nat -> Expr := fun _ n => ExprVar n.
  
  Lemma ExprChorIdSubstFibre : forall (p : Prin),
      ExprChorIdSubst p = ExprIdSubst.
  Proof.
    intros p. unfold ExprChorIdSubst. unfold ExprIdSubst. reflexivity.
  Qed.

  Lemma ChorUpIdExprSubst : forall p q n, ExprChorIdSubst p n
                                   = ChorUpExprSubst ExprChorIdSubst q p n.
  Proof.
    intros p q n; unfold ChorUpExprSubst; unfold ExprChorIdSubst;
      destruct (PrinEqDec q p); destruct n; auto; rewrite ExprRenameVar; reflexivity.
  Qed.
  
  Lemma ChorUpIdSubst : forall n,  ChorIdSubst n = ChorUpSubst ChorIdSubst n.
  Proof.
    unfold ChorUpSubst; unfold ChorIdSubst; destruct n;
      [|unfold ExprIdRenaming; simpl]; reflexivity.
  Qed.

  Lemma SendUpChorIdSubst : forall p n, SendUpChorSubst ChorIdSubst p n = ChorIdSubst n.
  Proof.
    intros p n. unfold ChorIdSubst; unfold SendUpChorSubst.
    simpl. unfold ChorIdRename. auto.
  Qed.

  Lemma ChorSubstIdSpec : forall (C : Chor), C [c| ChorIdSubst; ExprChorIdSubst] = C.
  Proof.
    intro C; induction C; unfold ChorIdSubst; simpl.
    all: try (rewrite ExprChorIdSubstFibre).
    all: try (rewrite ExprIdentitySubstSpec).
    all: try auto.
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      -- rewrite IHC; auto.
      -- symmetry; apply ChorUpIdExprSubst. 
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto;
        rewrite IHC1.
      rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto;
        rewrite IHC2.
      reflexivity.
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      rewrite IHC1.
      rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      rewrite IHC2; reflexivity.
      all: symmetry; apply ChorUpIdSubst.
  Qed.
      
  Theorem ChorRenameSpec : forall (C : Chor) (ξₖ : nat -> nat) (ξₑ : Prin -> nat -> nat),
      C ⟨c| ξₖ; ξₑ ⟩ = C[c| (fun n => CVar (ξₖ n)); (fun p n => ExprVar (ξₑ p n))].
  Proof.
    intro C; induction C; intros ξₖ ξₑ; simpl; try reflexivity.
    all: repeat (rewrite ExprRenameSpec).
    all: try (repeat (rewrite IHC)).
    all: try (rewrite IHC1; rewrite IHC2).
    all: try reflexivity.
    - unfold ChorUpExprSubst.
      symmetry.
      rewrite ChorSubstExt with (σk2 := fun n : nat => CVar (ξₖ n)) (σe2 := fun q n => ExprVar (ChorUpExprRename ξₑ p0 q n)); auto.
      unfold ChorUpExprRename; unfold ExprUpRename.
      intros q n; destruct n; auto; destruct (PrinEqDec p0 q); auto.
      rewrite ExprRenameVar. reflexivity.
    - rewrite ChorSubstExt with (σk2 := ChorUpSubst (fun n : nat => CVar (ξₖ n)))
                                (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C1); auto.
      rewrite ChorSubstExt with (σk2 := ChorUpSubst (fun n : nat => CVar (ξₖ n)))
                                (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C2); auto.
      all: unfold ChorUpSubst; unfold ChorUpRename;  destruct n; simpl; reflexivity.
  Qed.

  Reserved Notation " C1 ≡' C2" (at level 30).
  Inductive chorEquiv' : Chor -> Chor -> Prop :=
    DoneRefl : forall p e, CDone p e ≡' CDone p e
  | VarRefl : forall n, CVar n ≡' CVar n
  | SendContext' : forall p e q C1 C2,
      C1 ≡' C2 ->
      CSend p e q C1 ≡' CSend p e q C2
  | IfContext' : forall p e C11 C12 C21 C22,
      C11 ≡' C12 -> C21 ≡' C22 -> CIf p e C11 C21 ≡' CIf p e C12 C22
  | DefContext' : forall C11 C12 C21 C22,
      C11 ≡' C12 ->
      C21 ≡' C22 ->
      CDef C11 C21 ≡' CDef C12 C22
  | SwapSendSend' : forall (p q r s : Prin) (C1 C2 : Chor) (e1 e2 : Expr),
      (* if the two sends share any principals, swapping them would change things from
         one principal's point-of-view *)          
      p <> r -> q <> r -> p <> s -> q <> s ->
      C1 ≡' C2 ->
      CSend p e1 q (CSend r e2 s C1) ≡' CSend r e2 s (CSend p e1 q C2)
  | SwapSendIf' : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡' C1' -> C2 ≡' C2' ->
      CIf p e1 (CSend q e2 r C1) (CSend q e2 r C2) ≡' CSend q e2 r (CIf p e1 C1' C2')
  | SwapIfSend' : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡' C1' -> C2 ≡' C2' ->
       CSend q e2 r (CIf p e1 C1 C2) ≡' CIf p e1 (CSend q e2 r C1') (CSend q e2 r C2')
  (* | SwapIfIf' : forall p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22', *)
  (*     p <> q -> *)
  (*     C11 ≡' C11' -> C12 ≡' C12' -> C21 ≡' C21' -> C22 ≡' C22' -> *)
  (*     CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) ≡' *)
  (*         CIf q e2 (CIf p e1 C11' C21') (CIf p e1 C12' C22') *)
  where "C1 ≡' C2" := (chorEquiv' C1 C2).
  Hint Constructors chorEquiv' : Chor.

  Fixpoint Equiv'Refl (C : Chor) : C ≡' C :=
    match C with
    | CDone p e =>
      DoneRefl p e
    | CVar n =>
      VarRefl n
    | CSend p e q C =>
      SendContext' p e q C C (Equiv'Refl C)
    | CIf p e C1 C2 =>
      IfContext' p e C1 C1 C2 C2 (Equiv'Refl C1) (Equiv'Refl C2)
    | CDef C1 C2 =>
      DefContext' C1 C1 C2 C2 (Equiv'Refl C1) (Equiv'Refl C2)
    end.
  Hint Resolve Equiv'Refl : Chor.
  Instance chorEquiv'Refl : Reflexive chorEquiv' := Equiv'Refl.
  
  Theorem Equiv'Sym : forall (C1 C2 : Chor), C1 ≡' C2 -> C2 ≡' C1.
  Proof.
    intros C1 C2 equiv; induction equiv; eauto with Chor.
  Qed.
  Hint Resolve Equiv'Sym : Chor.

  Instance chorEquiv'Sym : Symmetric chorEquiv' := Equiv'Sym.

  Reserved Infix "≡" (at level 30).
  Inductive chorEquiv : Chor -> Chor -> Prop :=
    Equiv' : forall C1 C2, C1 ≡' C2 -> C1 ≡ C2
  | TransEquiv : forall C1 C2 C3, C1 ≡' C2 -> C2 ≡ C3 -> C1 ≡ C3
  where "C1 ≡ C2" := (chorEquiv C1 C2).
  Hint Constructors chorEquiv : Chor.

  Instance chorEquivRefl : Reflexive chorEquiv.
  Proof.
    unfold Reflexive; intro C; apply Equiv'; reflexivity.
  Defined.
  Hint Resolve chorEquivRefl : Chor.

  Lemma chorEquivTransitive : forall C1 C2 C3 : Chor, C1 ≡ C2 -> C2 ≡ C3 -> C1 ≡ C3.
  Proof.
    intros C1 C2 C3 equiv; revert C3; induction equiv; intros C3' equiv'.
    - eapply TransEquiv; eauto.
    - specialize (IHequiv C3' equiv'). eapply TransEquiv; eauto.
  Qed.
  Instance chorEquivTrans : Transitive chorEquiv := chorEquivTransitive.

  Instance chorEquivSym : Symmetric chorEquiv.
  Proof.
    unfold Symmetric; intros C1 C2 equiv; induction equiv; auto with Chor.
    - transitivity C2; auto with Chor.
  Qed.
  Hint Resolve chorEquivSym : Chor.

  (* Smart constructors for ≡ *)
  Lemma SendContext : forall (p q : Prin) (e : Expr) (C C' : Chor),
      C ≡ C' ->
      CSend p e q C ≡ CSend p e q C'.
  Proof.
    intros p q e C C' equiv; revert p q e; induction equiv; intros p q e; eauto with Chor.
  Qed.
  Lemma IfContext : forall (p : Prin) (e : Expr) (C1 C1' C2 C2' : Chor),
      C1 ≡ C1' -> C2 ≡ C2' ->
      CIf p e C1 C2 ≡ CIf p e C1' C2'.
  Proof.
    intros p e C1 C1' C2 C2' equiv; revert p e C2 C2'; induction equiv;
      intros p e C2' C2'' equiv'; revert p e; induction equiv'; intros p e;
        eauto with Chor.
  Qed.
  Lemma DefContext : forall (C1 C1' C2 C2' : Chor),
      C1 ≡ C1' -> C2 ≡ C2' ->
      CDef C1 C2 ≡ CDef C1' C2'.
  Proof.
    intros C1 C1' C2 C2' equiv; revert C2 C2'; induction equiv;
      intros C4 C4' equiv'; induction equiv'; eauto with Chor.
  Qed.

  Lemma SwapSendSend : forall (p q r s : Prin) (C1 C2 : Chor) (e1 e2 : Expr),
      p <> r -> q <> r -> p <> s -> q <> s ->
      C1 ≡ C2 ->
      CSend p e1 q (CSend r e2 s C1) ≡ CSend r e2 s (CSend p e1 q C2).
  Proof.
    intros p q r s C1 C2 e1 e2 neq1 neq2 neq3 neq4 equiv;
      revert p q r s e1 e2 neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e1 e2 neq1 neq2 neq3 neq4;
      auto with Chor.
    transitivity (CSend p e1 q (CSend r e2 s C2)); auto with Chor.
  Qed.

  Lemma SwapIfSend : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡ C1' -> C2 ≡ C2' ->
      CSend q e2 r (CIf p e1 C1 C2) ≡ CIf p e1 (CSend q e2 r C1') (CSend q e2 r C2').
  Proof.
    intros p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1;
      revert p e1 q e2 r C2 C2' neq1 neq2;
      induction equiv1;
      intros p e1 q e2 r C0 C0' neq1 neq2 equiv2;
      revert p e1 q e2 r neq1 neq2;
      induction equiv2;
      intros p e1 q e2 r neq1 neq2;
      eauto with Chor.
  Qed.

  Lemma SwapSendIf : forall p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡ C1' -> C2 ≡ C2' ->
      CIf p e1 (CSend q e2 r C1) (CSend q e2 r C2) ≡ CSend q e2 r (CIf p e1 C1' C2').
  Proof.
    intros p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1;
      revert p e1 q e2 r C2 C2' neq1 neq2;
      induction equiv1;
      intros p e1 q e2 r C0 C0' neq1 neq2 equiv2;
      revert p e1 q e2 r neq1 neq2;
      induction equiv2;
      intros p e1 q e2 r neq1 neq2;
      eauto with Chor.
    transitivity (CIf p e1 (CSend q e2 r C2) (CSend q e2 r C4));
      eauto with Chor.
  Qed.

  (* Lemma SwapIfIf : forall p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22', *)
  (*     p <> q -> *)
  (*     C11 ≡ C11' -> C12 ≡ C12' -> C21 ≡ C21' -> C22 ≡ C22' -> *)
  (*     CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) ≡ *)
  (*         CIf q e2 (CIf p e1 C11' C21') (CIf p e1 C12' C22'). *)
  (* Proof. *)
  (*   intros p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22' neq equiv1; *)
  (*     revert p e1 q e2 C12 C12' C21 C21' C22 C22' neq; *)
  (*     induction equiv1; eauto with Chor. *)
  (*     intros p e1 q e2 C12 C12' C21 C21' C22 C22' neq equiv2; *)
  (*     revert p e1 q e2 C21 C21' C22 C22' neq; *)
  (*     induction equiv2; eauto with Chor. *)
  (*     intros p e1 q e2 C21 C21' C22 C22' neq equiv3; *)
  (*     revert p e1 q e2 C22 C22' neq; *)
  (*     induction equiv3; eauto with Chor. *)
  (*     intros p e1 q e2 C22 C22' neq equiv4; *)
  (*     revert p e1 q e2 neq;  *)
  (*     induction equiv4; *)
  (*     intros p e1 q e2 neq; *)
  (*     eauto with Chor. *)
  (* Qed. *)
  Hint Resolve SendContext IfContext DefContext SwapSendSend SwapSendIf SwapIfSend (* SwapIfIf *) : Chor.


  Lemma Equiv'StableRename : forall (ξc : nat -> nat) (ξe : Prin -> nat -> nat) (C1 C2 : Chor),
      C1 ≡' C2 -> C1 ⟨c| ξc; ξe ⟩ ≡' C2 ⟨c| ξc; ξe⟩.
  Proof.
    intros ξc ξe C1 C2 equiv; revert ξc ξe; induction equiv; intros ξc ξe;
      simpl; eauto with Chor.
    - unfold ChorUpExprRename at 1.
      destruct (PrinEqDec q r) as [e | _]; [exfalso; apply H0; exact e |].
      unfold ChorUpExprRename at 3.
      destruct (PrinEqDec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e |].
      apply SwapSendSend'; auto.
      rewrite ChorRenameExtensional with (ξₖ₂ := ξc)
                                         (ξₑ₂ := ChorUpExprRename (ChorUpExprRename ξe s) q);
        auto.
      intros t n; unfold ChorUpExprRename.
      destruct (PrinEqDec s t) as [es | ns].
      destruct (PrinEqDec q t) as [eq | nq];
        [exfalso; apply H2; transitivity t; auto|].
      unfold ExprUpRename; destruct n; reflexivity.
      destruct (PrinEqDec q t); auto.
    - unfold ChorUpExprRename at 3.
      destruct (PrinEqDec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply SwapSendIf'; auto.
    - unfold ChorUpExprRename at 1.
      destruct (PrinEqDec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply SwapIfSend'; auto.
  Qed.

  Lemma EquivStableRename : forall (ξc : nat -> nat) (ξe : Prin -> nat -> nat) (C1 C2 : Chor),
      C1 ≡ C2 -> C1 ⟨c| ξc; ξe ⟩ ≡ C2 ⟨c| ξc; ξe⟩.
  Proof.
    intros ξc ξe C1 C2 equiv; induction equiv.
    - apply Equiv'; apply Equiv'StableRename; auto.
    - transitivity (C2 ⟨c| ξc; ξe⟩); auto.
      apply Equiv'; apply Equiv'StableRename; auto.
  Qed.

  Lemma Equiv'StableSubst : forall (σc1 σc2 : nat -> Chor) (σe : Prin -> nat -> Expr) (C1 C2 : Chor),
      (forall n : nat, σc1 n ≡ σc2 n) ->
      C1 ≡' C2 ->
      C1 [c| σc1; σe] ≡ C2 [c| σc2; σe].
  Proof.
    intros σc1 σc2 σe C1 C2 equivσ equiv; revert σc1 σc2 σe equivσ; induction equiv;
      intros σc1 σc2 σe equivσ; simpl; try (auto with Chor; fail).
    - assert (forall n, SendUpChorSubst σc1 q n ≡ SendUpChorSubst σc2 q n) as equivSendUpσ
        by (unfold SendUpChorSubst; intro n; apply EquivStableRename; auto).
      specialize (IHequiv (SendUpChorSubst σc1 q) (SendUpChorSubst σc2 q)
                          (ChorUpExprSubst σe q) equivSendUpσ).
      inversion IHequiv; auto with Chor.
    - apply DefContext.
      apply IHequiv1; intro n; unfold ChorUpSubst; destruct n; 
        [reflexivity | apply EquivStableRename; auto].
      apply IHequiv2; intro n; unfold ChorUpSubst; destruct n;
        [reflexivity | apply EquivStableRename; auto].
    - unfold ChorUpExprSubst at 1;
        destruct (PrinEqDec q r) as [e | _]; [exfalso; apply H0; exact e|].
      unfold ChorUpExprSubst at 3;
        destruct (PrinEqDec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e|].
      apply SwapSendSend; auto.
      rewrite ChorSubstExt with (σk2 := SendUpChorSubst (SendUpChorSubst σc1 s) q)
                                (σe2 := ChorUpExprSubst (ChorUpExprSubst σe s) q).
      -- apply IHequiv; intro n;
         unfold SendUpChorSubst; apply EquivStableRename;
           apply EquivStableRename; auto.
      -- intro n; unfold SendUpChorSubst.
         repeat (rewrite ChorRenameFusion). apply ChorRenameExtensional.
         reflexivity.
         intros t m. destruct (PrinEqDec s t).
         destruct (PrinEqDec q t) as [e' | _];
           [exfalso; apply H2; transitivity t; auto| reflexivity].
         reflexivity.
      --intros t n. unfold ChorUpExprSubst.
        destruct (PrinEqDec s t); [| reflexivity].
        destruct (PrinEqDec q t) as [e' | _];
          [exfalso; apply H2; transitivity t; auto | reflexivity].
    - unfold ChorUpExprSubst at 3.
      destruct (PrinEqDec r p) as [e | _];
        [exfalso; apply H0; symmetry; exact e |].
      apply SwapSendIf; auto with Chor; [apply IHequiv1 | apply IHequiv2].
      all: unfold SendUpChorSubst; intro n; apply EquivStableRename; auto.
    - unfold ChorUpExprSubst at 1.
      destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H0; symmetry; exact e |].
      apply SwapIfSend; auto; [apply IHequiv1 | apply IHequiv2]; intro n.
      all: unfold SendUpChorSubst; apply EquivStableRename; auto.
  Qed.
  Hint Resolve Equiv'StableSubst : Chor.
  Lemma EquivStableSubst : forall (σc1 σc2 : nat -> Chor) (σe : Prin -> nat -> Expr) (C1 C2 : Chor),
      (forall n : nat, σc1 n ≡ σc2 n) ->
      C1 ≡ C2 ->
      C1 [c| σc1; σe] ≡ C2 [c| σc2; σe].
  Proof.
    intros σc1 σc2 σe C1 C2 equivσ equiv. induction equiv.
    - apply Equiv'StableSubst; auto. 
    - transitivity (C2 [c| σc1; σe]); auto with Chor.
  Qed.
  Hint Resolve EquivStableSubst : Chor.

  Inductive Redex : Set :=
  | RDone : Prin -> Expr -> Expr -> Redex
  | RIfE : Prin -> Expr -> Expr -> Redex
  | RIfTT : Prin -> Redex
  | RIfFF : Prin -> Redex
  | RSendE : Prin -> Expr -> Expr -> Prin -> Redex
  | RSendV : Prin -> Expr -> Prin -> Redex
  | RDef.
  Hint Constructors Redex : Chor.
  

  Definition SendSubst (p : Prin) (v : Expr) : Prin -> nat -> Expr :=
    fun q n =>
      if PrinEqDec p q
      then match n with
           | 0 => v
           | S m => ExprVar m
           end
      else ExprVar n.

  Lemma UpSendSubst : forall (p q : Prin) (v : Expr),
      p <> q ->
      forall r n, ChorUpExprSubst (SendSubst p v) q r n = SendSubst p v r n.
  Proof.
    intros p q v H r n.
    unfold ChorUpExprSubst; unfold SendSubst.
    destruct (PrinEqDec q r);
      destruct (PrinEqDec p r); auto.
    exfalso; apply H; transitivity r; auto.
    destruct n; auto. rewrite ExprRenameVar; auto.
  Qed.
  
  Definition DefSubst (C1 : Chor) : nat -> Chor :=
    fun n => match n with
          | 0 => CDef C1 C1
          | S m => CVar m
          end.

  Inductive RChorStep : Redex -> list Prin -> bool -> Chor -> Chor -> Prop :=
  | DoneEStep : forall (p : Prin) (e1 e2 : Expr) (b : bool),
      ExprStep e1 e2 -> RChorStep (RDone p e1 e2) nil b (CDone p e1) (CDone p e2)
  | SendEStep : forall (p q : Prin) (B : list Prin),
      ~ In p B -> ~ In q B -> p <> q ->
      forall (e1 e2 : Expr) (C : Chor) (b : bool),
        ExprStep e1 e2 -> RChorStep (RSendE p e1 e2 q) B b (CSend p e1 q C) (CSend p e2 q C)
  | SendIStep : forall (p q : Prin) (e : Expr) (C1 C2 : Chor) (B : list Prin) (R : Redex) (b : bool),
      RChorStep R (p :: q :: B) b C1 C2 ->
      RChorStep R B b (CSend p e q C1) (CSend p e q C2)
  | SendVStep : forall (p q : Prin) (v : Expr) (C : Chor) (B : list Prin) (b : bool),
      ~ In p B -> ~ In q B -> p <> q ->
      ExprVal v ->
      RChorStep (RSendV p v q) B b (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
  | IfEStep : forall (p : Prin) (e1 e2 : Expr) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      ExprStep e1 e2 ->
      RChorStep (RIfE p e1 e2) B true (CIf p e1 C1 C2) (CIf p e2 C1 C2)
  | IfIStep : forall (p : Prin) (e : Expr) (C1 C2 C3 C4 : Chor) (B : list Prin) (R : Redex) (b : bool),
      RChorStep R (p :: B) false C1 C3 ->
      RChorStep R (p :: B) false C2 C4 ->
      RChorStep R B b (CIf p e C1 C2) (CIf p e C3 C4)
  | IfTrueStep : forall (p : Prin) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      RChorStep (RIfTT p) B true (CIf p tt C1 C2) C1
  | IfFalseStep : forall (p : Prin) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      RChorStep (RIfFF p) B true (CIf p ff C1 C2) C2
  | DefStep : forall (C1 C2 : Chor) (b : bool),
      RChorStep RDef nil b (CDef C1 C2) (C2 [c| DefSubst C1; ExprChorIdSubst]).
  Hint Constructors RChorStep : Chor.

  Ltac RStepRearrangeHelper :=
      match goal with
      | [i : ~ In ?p ?B1, ext : forall q, In q ?B1 <-> In q ?B2 |- ~ In ?p ?B2 ] =>
        let H := fresh in intro H; rewrite <- ext in H; apply i; exact H
      end.

  Lemma RStepRearrange : forall R B1 b C1 C2,
      RChorStep R B1 b C1 C2 -> forall B2, (forall q, In q B1 <-> In q B2) -> RChorStep R B2 b C1 C2.
  Proof.
    intros R B1 b C1 C2 step; induction step; intros B2 ext.
    all: try (constructor; try RStepRearrangeHelper; auto with Chor; fail).
    - assert (B2 = nil)
      by (destruct B2; auto;
          assert (In p0 nil) as H0
              by (apply ext; left; reflexivity);
          inversion H0).
      subst.
      clear ext; auto with Chor.
    - apply SendIStep. apply IHstep.
      intros r; split.
      all:intro i; destruct i as [eq | i];
        [ left; exact eq
        | destruct i as [eq | i];
          [ right; left; exact eq
          | right; right; apply ext; auto]].
    - apply IfIStep; [apply IHstep1 | apply IHstep2].
      all: intros q; split.
      all: intro i; destruct i as [eq | i]; [left; exact eq | right; apply ext; auto].
    - assert (B2 = nil)
        by (destruct B2; auto;
            assert (In p nil) as H0
                by (apply ext; left; reflexivity);
            inversion H0).
      rewrite H. apply DefStep.
  Qed.

  Inductive RedexOf : Prin -> Redex -> Prop :=
  | RODone : forall p e1 e2, RedexOf p (RDone p e1 e2)
  | ROIfE : forall p e1 e2, RedexOf p (RIfE p e1 e2)
  | ROIfTT : forall p, RedexOf p (RIfTT p)
  | ROIfFF : forall p, RedexOf p (RIfFF p)
  | ROSendE : forall p e1 e2 q, RedexOf p (RSendE p e1 e2 q)
  | ROSendV : forall p v q, RedexOf p (RSendV p v q).

  Lemma NoIStepInList : forall p B R,
      In p B ->
      RedexOf p R ->
      forall b C1 C2, ~RChorStep R B b C1 C2.
  Proof.
    intros p B R H H0 b C1 C2 step; induction step; inversion H0;
    match goal with
    | [ i : In ?p ?B, n : ~ In ?p' ?B, e : ?p = ?p' |- False ] =>
      apply n; rewrite <- e; exact i
    | [ i : In ?p ?B, n : ~ In ?p' ?B, e : ?p' = ?p |- False ] =>
      apply n; rewrite e; exact i
    | _ => idtac
    end.
    all: try (apply IHstep; auto; right; right; auto; fail).
    all: try (apply IHstep1; auto; right; auto; fail).
    inversion H.
  Qed.

  Corollary NoDoneIStepInList : forall p B,
      In p B ->
      forall e1 e2 b C1 C2, ~RChorStep (RDone p e1 e2) B b C1 C2.
  Proof.
    intros p B H e1 e2 b C1 C2; apply NoIStepInList with (p := p); auto; apply RODone.
  Qed.
  Corollary NoSendEIStepInList : forall p B,
      In p B ->
      forall e1 e2 b C1 C2 q, ~RChorStep (RSendE p e1 e2 q) B b C1 C2.
  Proof.
    intros p B H q e1 e2 b C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendE.
  Qed.
  Corollary NoSendVIStepInList : forall p B,
      In p B ->
      forall v q b C1 C2, ~RChorStep (RSendV p v q) B b C1 C2.
  Proof.
    intros p B H v q b C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendV.
  Qed.
  Corollary NoIfEIStepInList : forall p B,
      In p B ->
      forall e1 e2 b C1 C2, ~RChorStep (RIfE p e1 e2) B b C1 C2.
  Proof.
   intros p B H e1 e2 b C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfE.
  Qed.
  Corollary NoIfTTStepInList : forall p B,
      In p B ->
      forall b C1 C2, ~RChorStep (RIfTT p) B b C1 C2.
  Proof.
   intros p B H b C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfTT.
  Qed.
  Corollary NoIfFFStepInList : forall p B,
      In p B ->
      forall b C1 C2, ~RChorStep (RIfFF p) B b C1 C2.
  Proof.
   intros p B H b C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfFF.
  Qed.    
  
  Hint Resolve RStepRearrange NoDoneIStepInList : Chor.
  Hint Resolve NoSendEIStepInList NoSendVIStepInList : Chor.
  Hint Resolve NoIfEIStepInList NoIfTTStepInList NoIfFFStepInList: Chor.

  Inductive ChorStepMany : list Prin -> Chor -> Chor -> Prop :=
  | ChorManyZero : forall B C, ChorStepMany B C C
  | ChorManyPlus : forall R B b C1 C2 C3, RChorStep R B b C1 C2 -> ChorStepMany B C2 C3 -> ChorStepMany B C1 C3.
  Hint Constructors ChorStepMany : Chor.

  Theorem ChorManyOne : forall (R : Redex) (B : list Prin) (b : bool) (C1 C2 : Chor),
      RChorStep R B b C1 C2 -> ChorStepMany B C1 C2.
  Proof.
    intros R B b C1 C2 step.
    eapply ChorManyPlus; [exact step | apply ChorManyZero].
  Qed.
  Hint Resolve ChorManyOne : Chor.

  Program Fixpoint ChorStepManyTrans (B : list Prin) (C1 C2 C3 : Chor)
           (r1 : ChorStepMany B C1 C2)
           (r2 : ChorStepMany B C2 C3) {struct r1} : ChorStepMany B C1 C3 :=
   match r1 with
   | ChorManyZero B C => r2
   | ChorManyPlus R B b C1' C2' _ s1 r3 =>
     ChorManyPlus _ _ _ _ _ _ s1  (ChorStepManyTrans _ _ _ _ r3 r2)
   end.
  Hint Resolve ChorStepManyTrans : Chor.

  Lemma ConsNotIn : forall {A : Type} (a b : A) (l : list A),
      a <> b -> ~ In a l -> ~ In a (b :: l).
  Proof.
    intros A a b l H H0 H1.
    destruct H1; auto.
  Qed.
  Lemma NotInCons : forall {A : Type} (a b : A) (l : list A),
      ~ In a (b :: l) -> a <> b /\ ~ In a l.
  Proof.
    intros A a b l H; split; intro H0; apply H; [left | right]; auto.
  Qed.    
  Hint Resolve ConsNotIn NotInCons : Chor.

  Ltac ListHelper :=
    match goal with
    | [H : ~ In ?r (?p :: ?q :: ?B) |- ~ In ?r ?B] =>
      let H' := fresh in intro H'; apply H; right; right; exact H'
    | [H : ~ In ?r (?p :: ?B) |- ~ In ?r ?B ] =>
      let H' := fresh in intro H'; apply H; right; exact H'
    end.


  Theorem Equiv'Simulation : forall C1 C2, C1 ≡' C2 -> forall R B b C1',
        RChorStep R B b C1 C1' -> exists C2', RChorStep R B b C2 C2' /\ C1' ≡ C2'.
  Proof.
    intros C1 C2 equiv; induction equiv; intros R B b Cstep step;
      eauto with Chor; inversion step; eauto with Chor; subst.
    - exists (CSend p e2 q C2); split; auto with Chor.
    - destruct (IHequiv _ _ _ _ H7) as [C3' HC3'].
      destruct (HC3') as [step' equivC3].
      exists (CSend p e q C3'); split; auto with Chor.
    - exists (CIf p e2 C12 C22); split; auto with Chor.
    - destruct (IHequiv1 _ _ _ _ H7) as [C3' HC3'].
      destruct HC3' as [stepC3 equivC3].
      destruct (IHequiv2 _ _ _ _ H8) as [C4' HC4'].
      destruct HC4' as [stepC4 equivC4].
      exists (CIf p e C3' C4'); split; auto with Chor.
    - exists C12; split; auto with Chor.
    - exists C22; split; auto with Chor.
    - exists (C22 [c| DefSubst C12; ExprChorIdSubst]); split; auto with Chor.
      apply EquivStableSubst; auto with Chor.
      intro n; unfold DefSubst; destruct n; auto with Chor.
    - exists (CSend r e2 s (CSend p e3 q C2)); split; auto with Chor.
    - inversion H11; subst.
      -- exists (CSend r e3 s (CSend p e1 q C2)); split; eauto with Chor.
         apply SendEStep; auto; ListHelper.
      -- destruct (IHequiv _ _ _ _ H12) as [C4' HC4'];
           destruct HC4' as [stepC4' equivC4'].
         exists (CSend r e2 s (CSend p e1 q C4')); split; auto with Chor.
         apply SendIStep. apply SendIStep.
         eapply RStepRearrange;
           [exact stepC4'|].
         intros q1; split; intros H13.
         all: destruct H13;
           [ right; right; left
           | destruct H3; [right; right; right; left
                           | destruct H3; [left
                                           | destruct H3; [right; left
                                                           | right; right; right; right]]]];
           auto.
      -- exists (CSend p e1 q (C2 [c| ChorIdSubst; SendSubst s e2]));
           split; auto with Chor.
         assert ((CSend p e1 q (C2 [c| ChorIdSubst; SendSubst s e2]))
                 = (CSend p e1 q C2) [c| ChorIdSubst; SendSubst s e2]).
         simpl; unfold SendSubst at 2; destruct (PrinEqDec s p) as [eq | _];
           [exfalso; apply H1; symmetry; exact eq |].
         fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
         assert (C2 [c|ChorIdSubst; SendSubst s e2] =
                 C2 [c| SendUpChorSubst ChorIdSubst q; ChorUpExprSubst (SendSubst s e2) q])
           by (apply ChorSubstExt;
               [ intro n; symmetry; apply SendUpChorIdSubst
               | symmetry; apply UpSendSubst; auto]).
         rewrite H3; reflexivity.
         rewrite H3. apply SendVStep; auto; ListHelper.
    - exists (CSend r e2 s C2 [c| ChorIdSubst; SendSubst q e1]).
        split; auto with Chor.
        simpl.
        unfold SendSubst at 1; destruct (PrinEqDec q r) as [eq | _];
          [exfalso; apply H0; exact eq|]; fold ExprIdSubst; rewrite ExprIdentitySubstSpec.
        apply SendIStep.
        assert (C2 [c| SendUpChorSubst ChorIdSubst s; ChorUpExprSubst (SendSubst q e1) s]
                = C2 [c| ChorIdSubst; SendSubst q e1])
          by (apply ChorSubstExt; [intro n; apply SendUpChorIdSubst
                                  | apply UpSendSubst; auto]).
        rewrite H3.
        apply SendVStep; auto with Chor.
    - exists (CSend q e2 r (CIf p e3 C1' C2')); split; auto with Chor.
    - inversion H9; subst; inversion H10; subst.
      -- exists (CSend q e3 r (CIf p e1 C1' C2')); split; auto with Chor.
         apply SendEStep; auto. intro i; apply H8; right; auto.
         intro i; apply H12; right; auto.
      -- apply NoSendEIStepInList in H15; [destruct H15| left; auto].
      -- apply NoSendEIStepInList in H11; [destruct H11| left; auto].
      -- destruct (IHequiv1 _ _ _ _ H11) as [C3' HC3'];
           destruct HC3' as [stepC1' equivC3].
         destruct (IHequiv2 _ _ _ _ H12) as [C4' HC4'];
           destruct HC4' as [stepC2' equivC4].
         exists (CSend q e2 r (CIf p e1 C3' C4')); split; auto with Chor.
         apply SendIStep. apply IfIStep.
         1,2: apply RStepRearrange with (B1 := q :: r :: p :: B); auto.
         all: intro q0; split; intro i.
         1,3: destruct i as [eq | i];
           [ right; left; auto
           | destruct i as [eq | i];
             [ right; right; left; auto
             | destruct i as [eq | i];
               [ left; auto
               | right; right; right; auto]]].
         all: destruct i as [eq|i];
           [ right; right; left; auto
           | destruct i as [eq|i];
             [ left; auto
             | destruct i as [eq|i];
               [ right; left; auto
               | right; right; right; auto
               ]
             ]
           ].
      -- apply NoSendVIStepInList in H11; [destruct H11|left; auto].
      -- apply NoSendVIStepInList in H15; [destruct H15|left; auto].
      -- exists (CIf p e1 (C1' [c|ChorIdSubst; SendSubst r e2]) (C2' [c|ChorIdSubst; SendSubst r e2])); split; auto with Chor.
         assert ((CIf p e1 C1' C2')[c| ChorIdSubst; SendSubst r e2] =
                 CIf p e1 (C1' [c| ChorIdSubst; SendSubst r e2]) (C2' [c| ChorIdSubst; SendSubst r e2])).
         simpl.
         assert (e1 [e|SendSubst r e2 p] = e1[e|ExprIdSubst]).
         apply ExprSubstExt. intro n; unfold SendSubst.
         destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H12; left; auto|].
         unfold ExprIdSubst. reflexivity.
         rewrite H1. rewrite ExprIdentitySubstSpec. reflexivity.
         rewrite <- H1. apply SendVStep; auto. intro i; apply H8; right; auto.
         intro i; apply H12; right; auto.
    - exists (CSend q e2 r C1'); split; auto with Chor.
    - exists (CSend q e2 r C2'); split; auto with Chor.
    - exists (CIf p e1 (CSend q e3 r C1') (CSend q e3 r C2')); split; auto with Chor.
    - inversion H9; subst.
      -- exists (CIf p e3 (CSend q e2 r C1') (CSend q e2 r C2')); split; auto with Chor.
         apply IfEStep; auto; ListHelper.
      -- destruct (IHequiv1 _ _ _ _ H10) as [C5' H5']; destruct H5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ _ H11) as [C6' H6']; destruct H6' as [stepC6' equivC6'].
         exists (CIf p e1 (CSend q e2 r C5') (CSend q e2 r C6')); split; auto with Chor.
         apply IfIStep; auto; apply SendIStep;
           apply RStepRearrange with (B1 := p :: q :: r ::B); auto.
         all: intros t; split; intros i.
         2,4: destruct i as [eq | i];
           [right; left; exact eq (* t = q *)
           | destruct i as [eq | i];
             [right; right; left; exact eq (* t = r *)
             |destruct i as [eq | i];
              [left; apply eq (* t = p *)
              | right; right; right; exact i]]].
         all: destruct i as [eq | i];
           [right; right; left; exact eq
           | destruct i as [eq | i];
             [left; exact eq
             | right; destruct i as [eq | i];
               [left; exact eq
               | right; right; exact i]]].
      -- exists (CSend q e2 r C1'); split; auto with Chor.
         apply IfTrueStep; ListHelper.
      -- exists (CSend q e2 r C2'); split; auto with Chor.
         apply IfFalseStep; ListHelper.
    - exists (CIf p e1 (C1'[c| ChorIdSubst; SendSubst r e2])
             (C2'[c|ChorIdSubst; SendSubst r e2])); split; auto with Chor.
      simpl; unfold SendSubst at 1.
      destruct (PrinEqDec r p) as [eq | _];
        [exfalso; apply H0; symmetry; exact eq|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec; auto with Chor.
    (* - exists (CIf q e2 (CIf p e3 C11' C21') (CIf p e3 C12' C22')); split; auto with Chor. *)
    (* - inversion H7; subst. *)
    (*   -- inversion H8; subst. *)
    (*      2: { apply NoIfEIStepInList in H12; [destruct H12| left; reflexivity]. } *)
    (*      exists (CIf q e3 (CIf p e1 C11' C21') (CIf p e1 C12' C22')); split; auto with Chor. *)
    (*      apply IfEStep; auto. ListHelper. *)
    (*   -- inversion H8; subst. *)
    (*      apply NoIfEIStepInList in H9; [destruct H9| left; reflexivity]. *)
    (*      2: apply NoIfTTStepInList in H10; [destruct H10 | left; reflexivity]. *)
    (*      2: apply NoIfFFStepInList in H10; [destruct H10 | left; reflexivity]. *)
    (*      destruct (IHequiv1 _ _ _ H9) as [C0' HC0']; *)
    (*        destruct HC0' as [stepC0' equivC0']. *)
    (*      destruct (IHequiv2 _ _ _ H10) as [C5' HC5']; *)
    (*        destruct HC5' as [stepC5' equivC5']. *)
    (*      destruct (IHequiv3 _ _ _ H11) as [C3' HC3']; *)
    (*        destruct HC3' as [stepC3' equivC3']. *)
    (*      destruct (IHequiv4 _ _ _ H12) as [C6' HC6']; *)
    (*        destruct HC6' as [stepC6' equivC6']. *)
    (*      exists (CIf q e2 (CIf p e1 C0' C3') (CIf p e1 C5' C6')); split; auto with Chor. *)
    (*      apply IfIStep; apply IfIStep; eauto with Chor. *)
    (*      all: apply RStepRearrange with (B1 := q :: p :: B); auto. *)
    (*      all: intros t; split; intros i. *)
    (*      all: destruct i as [eq | i]; *)
    (*        [(* t = p *) right; left; exact eq *)
    (*                   | destruct i as [eq | i]; *)
    (*                     [ (* t = q *) left; exact eq *)
    (*                                 | right; right; exact i]]. *)
    (*   -- inversion H8; subst; *)
    (*        [apply NoIfTTStepInList in H10; [destruct H10 | left; reflexivity] |]. *)
    (*      exists (CIf p e1 C11' C21'); split; auto with Chor. *)
    (*      apply IfTrueStep; ListHelper. *)
    (*   -- inversion H8; subst; *)
    (*        [apply NoIfFFStepInList in H10; [destruct H10 | left; reflexivity] |]. *)
    (*      exists (CIf p e1 C12' C22'); split; auto with Chor. *)
    (*      apply IfFalseStep; ListHelper. *)
    (* - exists (CIf q e2 C11' C12'); split; auto with Chor. *)
    (* - exists (CIf q e2 C21' C22'); split; auto with Chor. *)
  Qed.

  Theorem EquivSimulation : forall C1 C2, C1 ≡ C2 -> forall C1' R B b, RChorStep R B b C1 C1' -> exists C2',
          RChorStep R B b C2 C2' /\ C1' ≡ C2'.
  Proof.
    intros C1 C2 H.
    induction H; intros C1' R B b step.
    apply Equiv'Simulation with (C1 := C1); auto.
    destruct (Equiv'Simulation _ _ H _ _ _ _ step) as [C2' HC2'].
    destruct HC2' as [stepC2' equivC2'].
    destruct (IHchorEquiv _ _ _ _ stepC2') as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
    exists C3'; split; auto. transitivity C2'; auto.
  Qed.

  Inductive StdChorStep : Chor -> Chor -> Prop :=
  | StdDoneEStep : forall (p : Prin) (e1 e2 : Expr),
      ExprStep e1 e2
      -> StdChorStep (CDone p e1) (CDone p e2)
  | StdSendEStep : forall (p q : Prin) (e1 e2 : Expr) (C : Chor),
      ExprStep e1 e2
      -> p <> q
      -> StdChorStep (CSend p e1 q C) (CSend p e2 q C)
  | StdSendVStep : forall (p q : Prin) (v : Expr) (C : Chor),
      ExprVal v
      -> p <> q
      -> StdChorStep (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
  | StdIfEStep : forall (p : Prin) (e1 e2 : Expr) (C1 C2 : Chor),
      ExprStep e1 e2
      -> StdChorStep (CIf p e1 C1 C2) (CIf p e2 C1 C2)
  | StdIfTrueStep : forall (p : Prin) (C1 C2 : Chor),
      StdChorStep (CIf p tt C1 C2) C1
  | StdIfFalseStep : forall (p : Prin) (C1 C2 : Chor),
      StdChorStep (CIf p ff C1 C2) C2
  | StdCDefStep : forall (C1 C2 : Chor),
      StdChorStep (CDef C1 C2) (C2 [c| DefSubst C1; ExprChorIdSubst])
  | StdEquivStep : forall (C1 C1' C2 C2' : Chor),
      C1 ≡ C1'
      -> StdChorStep C1' C2'
      -> C2 ≡ C2'
      -> StdChorStep C1 C2.
  Hint Constructors StdChorStep : StdChor.

  Theorem StdToRStep : forall (C1 C2 : Chor),
      StdChorStep C1 C2
      -> exists R C2', C2 ≡ C2' /\ RChorStep R nil true C1 C2'.
  Proof.
    intros C1 C2 stdstep; induction stdstep.
    all:try ( eexists; eexists; split; [reflexivity | constructor; auto]).
    rename H into equiv1; rename H0 into equiv2;
      destruct IHstdstep as [R H]; destruct H as [C2'' H]; destruct H as [equiv2' step].
    destruct (EquivSimulation _ C1 (chorEquivSym _ _ equiv1) _ _ _ _ step) as [C2''' H];
      destruct H as [step' equiv2''].
    exists R; exists C2'''; split; auto.
    transitivity C2'; auto. transitivity C2''; auto.
  Qed.

  Inductive RedexOnTop : Redex -> Chor -> Prop :=
  | DoneOnTop : forall p e1 e2, RedexOnTop (RDone p e1 e2) (CDone p e1)
  | SendEOnTop : forall p e1 e2 q C, RedexOnTop (RSendE p e1 e2 q) (CSend p e1 q C)
  | SendVOnTop : forall p v q C, RedexOnTop (RSendV p v q) (CSend p v q C)
  | IfEOnTop : forall p e1 e2 C1 C2, RedexOnTop (RIfE p e1 e2) (CIf p e1 C1 C2)
  | IfTTOnTop : forall p C1 C2, RedexOnTop (RIfTT p) (CIf p tt C1 C2)
  | IfFFOnTop : forall p C1 C2, RedexOnTop (RIfFF p) (CIf p ff C1 C2)
  | DefOnTop : forall C1 C2, RedexOnTop RDef (CDef C1 C2).
  Hint Constructors RedexOnTop : StdChor.

  Lemma RStepOnTop : forall (R : Redex) (B : list Prin) (b : bool) (C1 C2 : Chor),
      RChorStep R B b C1 C2 ->
      exists C1' C2', C1 ≡ C1' /\ C2 ≡ C2' /\ RChorStep R B b C1' C2' /\ RedexOnTop R C1'.
  Proof.
    intros R B b C1 C2 step; induction step.
    all: try(eexists; eexists; split; [|split; [|split]]; eauto with Chor StdChor; fail).
    - destruct IHstep as [C1' H]; destruct H as [C2' H]; destruct H as [equiv1 H];
        destruct H as [equiv2 H]; destruct H as [step' ontop].
      destruct R; inversion ontop;
      match goal with
      | [ C1'equiv : ?C = C1' |- _] => rewrite <- C1'equiv in step'
      end; inversion step'.
      all: try (match goal with
                | [H : RChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q ?e1 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      -- exists (CIf p0 e0 (CSend p e q C0) (CSend p e q C3)).
         exists (CIf p0 e1 (CSend p e q C0) (CSend p e q C3)).
         split; [|split;[|split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H3. apply SwapIfSend; auto with Chor.
             intro eq; apply H11; left; symmetry; exact eq.
             intro eq; apply H11; right; left; symmetry; exact eq.
         --- transitivity (CSend p e q C2'); auto with Chor.
             rewrite <- H8; apply SwapIfSend; auto with Chor.
             intro eq; apply H11; left; symmetry; exact eq.
             intro eq; apply H11; right; left; symmetry; exact eq.
         --- constructor; auto.
             intro i; apply H11; right; right; exact i.
      -- apply NoIfEIStepInList in H11; [destruct H11| left; auto].
      -- apply NoIfTTStepInList in H9; [destruct H9| left; auto].
      -- exists (CIf p0 tt (CSend p e q C0) (CSend p e q C3));
           exists (CSend p e q C0);
           subst;
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CIf p0 tt C2' C3)); auto with Chor.
             apply SwapIfSend; auto with Chor.
             intro eq; apply H7; left; symmetry; exact eq.
             intro eq; apply H7; right; left; symmetry; exact eq.
         --- apply IfTrueStep. intro i; apply H7; right; right; exact i.
      -- apply NoIfFFStepInList in H9; [destruct H9|left; auto].
      -- exists (CIf p0 ff (CSend p e q C0) (CSend p e q C3));
           exists (CSend p e q C3);
           subst;
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CIf p0 ff C0 C2')); auto with Chor.
             apply SwapIfSend; auto with Chor.
             intro eq; apply H7; left; symmetry; exact eq.
             intro eq; apply H7; right; left; symmetry; exact eq.
         --- apply IfFalseStep. intro i; apply H7; right; right; exact i.
      -- exists (CSend p0 e0 q0 (CSend p e q C));
           exists (CSend p0 e1 q0 (CSend p e q C));
           split; [| split; [| split]]; rewrite H3; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H4. apply SwapSendSend; auto with Chor.
             intro eq; apply H11; left; auto.
             intro eq; apply H11; right; left; auto.
             intro eq; apply H13; left; exact eq.
             intro eq; apply H13; right; left; exact eq.
         --- transitivity (CSend p e q C2'); auto with Chor.
             rewrite <- H12. apply SwapSendSend; auto with Chor.
             intro eq; apply H11; left; exact eq.
             intro eq; apply H11; right; left; exact eq.
             intro eq; apply H13; left; exact eq.
             intro eq; apply H13; right; left; exact eq.
         --- apply SendEStep; auto;
               intro i; [apply H11 | apply H13]; right; right; exact i.
      -- apply NoSendEIStepInList in H12; [destruct H12|left; auto].
      -- apply NoSendVIStepInList in H11; [destruct H11|left; auto].
      -- exists (CSend p0 e0 q0 (CSend p e q C));
           exists (CSend p e q C [c| ChorIdSubst; SendSubst q0 e0]);
           split; [| split; [| split]]; subst; auto with Chor StdChor.
         --- transitivity (CSend p e q (CSend p0 e0 p1 C)); auto with Chor.
             apply SwapSendSend; auto with Chor.
             intro eq; apply H7; left; exact eq.
             intro eq; apply H7; right; left; exact eq.
             intro eq; apply H10; left; exact eq.
             intro eq; apply H10; right; left; exact eq.
         --- transitivity (CSend p e q (C [c|ChorIdSubst; SendSubst p1 e0]));
               auto with Chor.
             simpl. unfold SendSubst at 2.
             destruct (PrinEqDec p1 p) as [eq | _];
               [exfalso; apply H10; left; symmetry; exact eq|].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
             assert (C [c|ChorIdSubst; SendSubst p1 e0]
                     = C [c|SendUpChorSubst ChorIdSubst q;
                            ChorUpExprSubst (SendSubst p1 e0) q]).
             apply ChorSubstExt.
             intro n; symmetry; apply SendUpChorIdSubst.
             intros p5 n; symmetry; apply UpSendSubst.
             intro eq; apply H10; right; left; symmetry; exact eq.
             rewrite H; auto with Chor.
         --- apply SendVStep; auto with Chor.
             intro i; apply H7; right; right; exact i.
             intro i; apply H10; right; right; exact i.
    - destruct IHstep1 as [C1' H]; destruct H as [C3' H]; destruct H as [equiv1 H];
        destruct H as [equiv3 H]; destruct H as [step13 ontop1].
      destruct IHstep2 as [C2' H]; destruct H as [C4' H]; destruct H as [equiv2 H];
        destruct H as [equiv4 H]; destruct H as [step24 ontop2].
      destruct R; inversion ontop1; inversion ontop2;
        match goal with
        | [ C1'equiv : ?C = C1' |- _] => rewrite <- C1'equiv in step13
        end;
        inversion step13;
        match goal with
        | [C2'equiv : ?C = C2' |- _] => rewrite <- C2'equiv in step24
        end;
        inversion step24.
      all: try (match goal with
                | [H : RChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q ?e ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : RChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply NoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      -- apply NoIfEIStepInList in H25; [destruct H25 | left; auto].
      -- apply NoIfTTStepInList in H21; [destruct H21 | left; auto].
      -- apply NoIfFFStepInList in H21; [destruct H21 | left; auto].
      (* -- exists (CIf p0 e0 (CIf p e C0 C6) (CIf p e C5 C7)); *)
      (*      exists (CIf p0 e1 (CIf p e C0 C6) (CIf p e C5 C7)); *)
      (*      split; [| split; [| split]]; auto with Chor StdChor. *)
      (*    --- transitivity (CIf p e C1' C2'); auto with Chor. *)
      (*        rewrite <- H3; rewrite <- H7. *)
      (*        apply SwapIfIf; auto with Chor. *)
      (*        intro eq; apply H23; left; exact eq. *)
      (*    --- transitivity (CIf p e C3' C4'); auto with Chor. *)
      (*        rewrite <- H11; rewrite <- H20. *)
      (*        apply SwapIfIf; auto with Chor. *)
      (*        intro eq; apply H23; left; exact eq. *)
      (*    --- apply IfEStep; auto with Chor. *)
      (*        intro i; apply H23; right; exact i. *)
      (* -- exists (CIf p0 tt (CIf p e C0 C6) (CIf p e C5 C7)); *)
      (*      exists (CIf p e C0 C6); *)
      (*      split; [| split; [| split]]; auto with Chor StdChor. *)
      (*    --- transitivity (CIf p e C1' C2'); auto with Chor. *)
      (*        rewrite <- H1; rewrite <- H3. apply SwapIfIf; auto with Chor. *)
      (*        intro eq; apply H14; left; exact eq. *)
      (*    --- transitivity (CIf p e C3' C4'); auto with Chor. *)
      (*        rewrite <- H6; rewrite <- H12; auto with Chor. *)
      (*    --- apply IfTrueStep. intro i; apply H14; right; exact i. *)
      (* -- exists (CIf p0 ff (CIf p e C0 C6) (CIf p e C5 C7)); *)
      (*      exists (CIf p e C5 C7); *)
      (*      split; [| split; [| split]]; auto with Chor StdChor. *)
      (*    --- transitivity (CIf p e C1' C2'); auto with Chor. *)
      (*        rewrite <- H1; rewrite <- H3. apply SwapIfIf; auto with Chor. *)
      (*        intro eq; apply H14; left; exact eq. *)
      (*    --- transitivity (CIf p e C3' C4'); auto with Chor. *)
      (*        rewrite <- H6; rewrite <- H12; auto with Chor. *)
      (*    --- apply IfFalseStep. intro i; apply H14; right; exact i. *)
      -- exists (CSend p0 e0 p1 (CIf p e C C0));
           exists (CSend p0 e1 p1 (CIf p e C C0));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H4; rewrite <- H9. apply SwapSendIf; auto with Chor.
             intro eq; apply H28; left; exact eq.
             intro eq; apply H30; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H17; rewrite <- H29. apply SwapSendIf; auto with Chor.
             intro eq; apply H28; left; exact eq.
             intro eq; apply H30; left; exact eq.
         --- apply SendEStep; auto.
             intro i; apply H28; right; exact i.
             intro i; apply H30; right; exact i.
      -- apply NoSendEIStepInList in H29; [destruct H29 | left; auto].
      -- apply NoSendEIStepInList in H17; [destruct H17 | left; auto].
      -- apply NoSendEIStepInList in H17; [destruct H17 | left; auto].
      -- apply NoSendVIStepInList in H15; [destruct H15 | left; auto].
      -- apply NoSendVIStepInList in H15; [destruct H15 | left; auto].
      -- apply NoSendVIStepInList in H26; [destruct H26 | left; auto].
      -- exists (CSend p0 e0 p1 (CIf p e C C0));
           exists (CIf p e C C0 [c|ChorIdSubst; SendSubst p1 e0]);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H3; rewrite <- H7. apply SwapSendIf; auto with Chor.
             intro eq; apply H22; left; exact eq.
             intro eq; apply H25; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H15; rewrite <- H26.
             simpl. unfold SendSubst at 3.
             destruct (PrinEqDec p1 p) as [eq | _];
               [exfalso; apply H25; left; symmetry; exact eq |].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec. reflexivity.
         --- apply SendVStep; auto.
             intro i; apply H22; right; exact i.
             intro i; apply H25; right; exact i.
  Qed.

  Lemma RStepOnTopToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Prin) (b : bool),
      RedexOnTop R C1 ->
      RChorStep R B b C1 C2 ->
      StdChorStep C1 C2.
  Proof.
    intros C1 C2 R B b ontop rstep; induction rstep; inversion ontop;
      auto with Chor StdChor.
    - rewrite <- H in ontop. inversion ontop. rewrite <- H in rstep; rewrite H1 in rstep.
      apply NoSendEIStepInList in rstep; [destruct rstep| left; reflexivity].
    - rewrite <- H in ontop; inversion ontop. rewrite <- H in rstep; rewrite H1 in rstep.
      apply NoSendVIStepInList in rstep; [destruct rstep | left; reflexivity].
    - rewrite <- H in ontop; inversion ontop. rewrite <- H in rstep1; rewrite H1 in rstep1.
      apply NoIfEIStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - rewrite <- H in ontop; inversion ontop. rewrite <- H in rstep1; rewrite H1 in rstep1.
      apply NoIfTTStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - rewrite <- H in ontop; inversion ontop. rewrite <- H in rstep1; rewrite H1 in rstep1.
      apply NoIfFFStepInList in rstep1; [destruct rstep1 | left; reflexivity].
  Qed.
  Theorem RStepToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Prin) (b : bool),
      RChorStep R B b C1 C2 -> StdChorStep C1 C2.
  Proof.
    intros C1 C2 R B b rstep.
    apply RStepOnTop in rstep;
      destruct rstep as [C1' H]; destruct H as [C2' H];
      destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [rstep ontop].
    apply StdEquivStep with (C1' := C1') (C2' := C2'); auto.
    apply RStepOnTopToStd with (R := R) (B := B) (b := b); auto.
  Qed.

  Parameter PrinOrder : Prin -> Prin -> Prop.
  Notation "p ≤p q" := (PrinOrder p q) (at level 20).
  Notation "p ≰p q" := (~ PrinOrder p q) (at level 20).
  Parameter PrinOrderDec : forall p q, {p ≤p q} + {p ≰p q}.
  Parameter PrinOrderTotal : forall p q, p ≤p q \/ q ≤p p.
  Parameter PrinOrderRefl : forall p, p ≤p p.
  Parameter PrinOrderAntisym : forall p q, p ≤p q -> q ≤p p -> p = q.
  Parameter PrinOrderTrans : forall p q r, p ≤p q -> q ≤p r -> p ≤p r.
  Module PrinOrderM <: TotalLeBool.
    Definition t := Prin.
    Definition leb p q :=
      match PrinOrderDec p q with
      | left _ => true
      | right _ => false
      end.
    Open Scope bool_scope.
    Theorem leb_total : forall p q, leb p q = true \/ leb q p = true.
    Proof.
      intros p q; unfold leb; destruct (PrinOrderDec p q);
        destruct (PrinOrderDec q p); auto.
      destruct (PrinOrderTotal p q); auto.
    Qed.
  End PrinOrderM.
  
  Module Import PrinSort := Sort PrinOrderM.

  Fixpoint ThreadNames (C : Chor) : list Prin :=
    match C with
    | CDone p _ => p :: nil
    | CVar _ => nil
    | CSend p _ q C' => p :: q :: (ThreadNames C')
    | CIf p _ C1 C2 => p :: (ThreadNames C1) ++ (ThreadNames C2)
    | CDef C1 C2 => (ThreadNames C1) ++ (ThreadNames C2)
    end.

  Reserved Infix "∈TN" (at level 20).
  Inductive InThreadNames : Prin -> Chor -> Prop :=
  | InDone : forall p e, p ∈TN (CDone p e)
  | InSend1 : forall p e q C', p ∈TN (CSend p e q C')
  | InSend2 : forall p e q C', q ∈TN (CSend p e q C')
  | InSend3 : forall r p e q C', r ∈TN C' -> r ∈TN (CSend p e q C')
  | InIf1 : forall p e C1 C2, p ∈TN (CIf p e C1 C2)
  | InIf2 : forall q p e C1 C2, q ∈TN C1 -> q ∈TN (CIf p e C1 C2)
  | InIf3 : forall q p e C1 C2, q ∈TN C2 -> q ∈TN (CIf p e C1 C2)
  | InDef1 : forall p C1 C2, p ∈TN C1 -> p ∈TN (CDef C1 C2)
  | InDef2 : forall p C1 C2, p ∈TN C2 -> p ∈TN (CDef C1 C2)
  where "p ∈TN C" := (InThreadNames p C).

  Lemma InThreadNamesSpec : forall p C, p ∈TN C <-> In p (ThreadNames C).
  Proof.
    intros p C; revert p; induction C; intro r; split; intro i; simpl in *.
    all: try (match goal with
              | [H : ?r ∈TN ?C |- _] => inversion H
              end); auto.
    all: repeat (match goal with
                 | [H : In ?a (?b :: ?l) |- _] => simpl in H
                 | [H : In ?a (?l1 ++ ?l2) |- _] => apply in_app_or in H
                 | [H : ?P \/ ?Q |- _] => destruct H
                 | [H : ?P /\ ?Q |- _] => destruct H
                 | [H : False |- _ ] => destruct H
                 end).
    2,6,7: right.
    all: try (rewrite H; constructor; auto; fail).
    all: try (constructor; rewrite IHC; auto; fail).
    all: try (constructor; rewrite IHC1; auto; fail).
    all: try (constructor; rewrite IHC2; auto; fail).
    - right; rewrite <- IHC; auto.
    - apply in_or_app; left; rewrite <- IHC1; exact H1.
    - apply in_or_app; right; rewrite <- IHC2; exact H1.
    - apply in_or_app; left; rewrite <- IHC1; exact H1.
    - apply in_or_app; right; rewrite <- IHC2; exact H1.
  Qed.             

  Lemma ThreadNamesInvariant' : forall C1 C2 : Chor,
      C1 ≡' C2 -> forall p : Prin, p ∈TN C1 <-> p ∈TN C2.
  Proof.
    intros C1 C2 equiv; induction equiv; intros t; split; intros i; auto;
      repeat match goal with
             | [i : ?p ∈TN (_ _) |- _] => inversion i; clear i
             end.
    all: try (constructor; auto; fail).
    all: try (constructor; apply IHequiv; auto; fail).
    all: try (constructor; rewrite <- IHequiv; auto; fail).
    all: try (constructor; rewrite IHequiv1; auto; fail).
    all: try (constructor; rewrite <- IHequiv1; auto; fail).
    all: try (constructor; rewrite IHequiv2; auto; fail).
    all: try (constructor; rewrite <- IHequiv2; auto; fail).
    all: try (constructor; constructor; auto; fail).
    all: try (constructor; constructor; rewrite IHequiv; auto; fail).
    all: try (constructor; constructor; rewrite <- IHequiv; auto; fail).
    all: try (constructor; constructor; rewrite IHequiv1; auto; fail).
    all: try (constructor; constructor; rewrite <- IHequiv1; auto; fail).
    all: try (constructor; constructor; rewrite <- IHequiv2; auto; fail).
    all: try (constructor; constructor; rewrite IHequiv2; auto; fail).
  Qed.
    
  Lemma ThreadNamesInvariant : forall C1 C2 : Chor,
      C1 ≡ C2 -> forall p : Prin, p ∈TN C1 <-> p ∈TN C2.
  Proof.
    intros C1 C2 equiv; induction equiv.
    - intro p; apply ThreadNamesInvariant'; auto.
    - intro p. apply ThreadNamesInvariant' with (p := p) in H. rewrite H.
      apply IHequiv.
  Qed.

  Fixpoint nubPrin (l : list Prin) : list Prin :=
    match l with
    | nil => nil
    | x :: xs => x :: (remove PrinEqDec x (nubPrin xs))
    end.
  Lemma In_remove : forall (p q : Prin) (l : list Prin),
      p <> q -> In p l -> In p (remove PrinEqDec q l).
  Proof.
    intros p q l; revert p q; induction l as [| r l']; intros p q n i; [inversion i|].
    simpl in *. destruct (PrinEqDec q r) as [ e|_].
    destruct i as [eq | i ]; [exfalso; apply n; transitivity r; auto | apply IHl'; auto].
    destruct i as [eq | i]; [left; exact eq | right; apply IHl'; auto].
  Qed.

  Lemma In_remove' : forall (p q : Prin) (l : list Prin),
      In p (remove PrinEqDec q l) -> p <> q /\ In p l.
  Proof.
    intros p q l; revert p q; induction l as [| r l']; intros p q; split.
    1,2: inversion H.
    simpl in H. destruct (PrinEqDec q r). apply IHl'; auto.
    simpl in H. destruct H; [| apply IHl'; auto].
    intro e; apply n; transitivity p; auto.
    simpl in H. destruct (PrinEqDec q r). right; apply (IHl' p q); auto.
    destruct H; [left; auto | right; apply (IHl' p q); auto].
  Qed.

  Lemma In_nub : forall (p : Prin) (l : list Prin),
      In p l <-> In p (nubPrin l).
  Proof.
    intros p l; revert p; induction l as [| q l']; intros p; split; intro i.
    1,2: inversion i.
    destruct (PrinEqDec p q) as [e | n]; [left; auto|].
    destruct i; simpl; [left; auto|right].
    apply In_remove with (q := q); auto.
    apply IHl'; auto.
    simpl in i. destruct i; [left; auto|].
    apply In_remove' in H; destruct H.
    right; apply IHl'; auto.
  Qed.

  Fixpoint countPrin (p : Prin) (l : list Prin) : nat :=
    match l with
    | nil => 0
    | q :: l' => if PrinEqDec p q
               then 1 + countPrin p l'
               else countPrin p l'
    end.

  Lemma countZero : forall (p : Prin) (l : list Prin),
      ~ In p l <-> countPrin p l = 0.
  Proof.
    intros p l; revert p; induction l as [| q l'].
    all: intro p; split; [intro i | intro c].
    - simpl; reflexivity.
    - intro H; inversion H.
    - simpl. destruct (PrinEqDec p q).
      -- exfalso; apply i; left; auto.
      -- apply IHl'. intro i'; apply i; right; exact i'.
    - simpl in c. destruct (PrinEqDec p q); [inversion c|].
      intro i; destruct i as [e | i].
      apply n; symmetry; exact e.
      apply IHl' in c; apply c; exact i.
  Qed.

  Lemma countPermutation : forall (p : Prin) (l l' : list Prin),
      Permutation l l' -> countPrin p l = countPrin p l'.
  Proof.
    intros p l l' perm; revert p; induction perm; intro p; auto; simpl.
    - destruct (PrinEqDec p x); auto.
    - destruct (PrinEqDec p y); destruct (PrinEqDec p x); auto.
    - transitivity (countPrin p l'); auto.
  Qed.
  
  Lemma remove_count : forall (p q : Prin) (l : list Prin),
      countPrin p (remove PrinEqDec q l) <= countPrin p l.
  Proof.
    intros p q l; revert p q; induction l as [| r l']; intros p q; simpl; [reflexivity|].
    destruct (PrinEqDec p r); destruct (PrinEqDec q r).
    - apply Nat.le_le_succ_r; apply IHl'.
    - simpl. destruct (PrinEqDec p r) as [_| n']; [| exfalso; apply n'; exact e].
      apply le_n_S. apply IHl'.
    - apply IHl'.
    - simpl. destruct (PrinEqDec p r) as [ e|_]; [exfalso; apply n; exact e|].
      apply IHl'.
  Qed.

  Lemma nubPrinCount : forall (p : Prin) (l : list Prin),
      In p l -> countPrin p (nubPrin l) = 1.
  Proof.
    intros p l; revert p; induction l as [| q l']; intros p i.
    - inversion i.
    - simpl in *. destruct (PrinEqDec p q).
      rewrite e. assert (countPrin q (remove PrinEqDec q (nubPrin l')) = 0) as c
        by (apply countZero; apply remove_In).
      rewrite c; reflexivity.
      destruct i as [ e|i]; [exfalso; apply n; symmetry; exact e|].
      assert (countPrin p (remove PrinEqDec q (nubPrin l')) <= 1).
      rewrite <- IHl' with (p := p); [|exact i]. apply remove_count.
      apply Nat.le_1_r in H. destruct H; [| auto].
      exfalso. rewrite <- countZero in H; apply H.
      apply In_remove; auto.
      apply -> In_nub; auto.
  Qed.

  Lemma nubPrinCount' : forall (p : Prin) (l : list Prin),
      countPrin p (nubPrin l) <= 1.
  Proof.
    intros p l.
    destruct (ListDec.In_dec PrinEqDec p l). rewrite nubPrinCount; auto.
    assert (~ In p (nubPrin l)). intro H; apply n; apply In_nub; exact H.
    rewrite countZero in H.  rewrite H. auto.
  Qed.

  Lemma HdRel_In : forall {A : Type} (R : A -> A -> Prop) (a b : A) (l : list A),
      Transitive R -> Sorted R l -> HdRel R a l -> In b l -> R a b.
  Proof.
    intros A R a b l; revert R a b; induction l as [| x xs]; intros R a b trans S H i;
      [inversion i|].
    destruct i; inversion H; [rewrite <- H0; auto|].
    clear b0 l H1 H3.
    inversion S; clear a0 l H1 H3.
    assert (R x b) by (apply IHxs; auto).
    unfold Transitive in trans; apply trans with (y := x); auto.
  Qed.

  Lemma CountBoundedCons : forall (p q : Prin) (l : list Prin),
      countPrin p l <= countPrin p (q :: l).
  Proof.
    intros p q l. simpl. destruct (PrinEqDec p q); auto.
  Qed.
    

  Lemma SortedCountUnique : forall (l1 l2 : list Prin),
      (forall p, In p l1 <-> In p l2)
      -> Sorted PrinOrder l1 -> Sorted PrinOrder l2
      -> (forall p, countPrin p l1 <= 1) -> (forall p, countPrin p l2 <= 1)
      -> l1 = l2.
  Proof.
    intros l1 l2 set_eq sorted1 sorted2 count1 count2.
    revert l2 set_eq sorted2 count2; induction sorted1; intros l2 set_eq sorted2 count2.
    - destruct l2; [reflexivity|].
      assert (In p nil) as H by (apply set_eq; left; reflexivity); inversion H.
    - inversion sorted2.
      assert (In a nil) as i
          by (rewrite H0; apply set_eq; left; reflexivity); inversion i.
      assert (a ≤p a0).
      destruct (PrinEqDec a a0); [rewrite e; apply PrinOrderRefl|].
      apply HdRel_In with (l1 := l); auto; [unfold Transitive; apply PrinOrderTrans|].
      rewrite <- H2 in set_eq. assert (In a0 (a0 :: l0)) by (left; reflexivity).
      apply set_eq in H3. destruct H3; [exfalso; apply n; auto|exact H3].
      assert (a0 ≤p a).
      destruct (PrinEqDec a0 a); [rewrite e; apply PrinOrderRefl|].
      assert (In a (a :: l)) by (left; reflexivity). rewrite set_eq in H4.
      rewrite <- H2 in H4. destruct H4; [exfalso; apply n; auto|].
      apply HdRel_In with (l1 := l0); auto; exact PrinOrderTrans.
      assert (a = a0) by (apply PrinOrderAntisym; auto).
      rewrite H5.  rewrite IHsorted1 with (l2 := l0); auto.
      intros p; transitivity (countPrin p (a :: l)); [apply CountBoundedCons | auto].
      rewrite <- H2 in set_eq. intro p; split; intro i.
      assert (In p (a0 :: l0)) by (apply set_eq; right; auto).
      destruct H6; [| exact H6].
      assert (countPrin p l <> 0).
      intro c. rewrite <- countZero in c; apply c; auto.
      specialize (count1 p); simpl in count1.
      destruct (PrinEqDec p a) as [_| n]; [| exfalso; apply n; transitivity a0; auto].
      destruct (countPrin p l); [exfalso; apply H7; auto | inversion count1; inversion H9].
      assert (In p (a :: l)) by (apply set_eq; right; auto).
      destruct H6; [| exact H6].
      assert (countPrin p l0 <> 0).
      intro c. rewrite <- countZero in c; apply c; auto.
      rewrite <- H2 in count2; specialize (count2 p); simpl in count2.
      destruct (PrinEqDec p a0) as [_| n]; [| exfalso; apply n; transitivity a; auto].
      destruct (countPrin p l0); [exfalso; apply H7; auto | inversion count2; inversion H9].
      intro p;
        transitivity (countPrin p (a0 :: l0));
        [apply CountBoundedCons | rewrite <- H2 in count2; auto].
  Qed.

  Definition CommList : Chor -> Chor -> list Prin :=
    fun C1 C2 => PrinSort.sort (nubPrin (ThreadNames C1 ++ ThreadNames C2)).

  Lemma CommListEq' : forall C1 C2 C1' C2' : Chor,
      C1 ≡' C1' -> C2 ≡' C2' -> CommList C1 C2 = CommList C1' C2'.
  Proof.
    intros C1 C2 C1' C2' equiv equiv'.
    unfold CommList.
    apply SortedCountUnique.
    - intro p; split; intro i.
      -- apply Permutation_in with (l' := nubPrin (ThreadNames C1 ++ ThreadNames C2)) in i;
           [| apply Permutation_sym; apply Permuted_sort].
         rewrite <- In_nub in i.
         apply in_app_or in i.
        apply Permutation_in with (l := nubPrin (ThreadNames C1' ++ ThreadNames C2'));
           [apply Permuted_sort|].
         rewrite <- In_nub.
         apply in_or_app.
         destruct i as [i | i]; [left | right]; rewrite <- InThreadNamesSpec.
         rewrite <- ThreadNamesInvariant' with (C1 := C1); auto.
         2:rewrite <- ThreadNamesInvariant' with (C1 := C2); auto.
         1,2: rewrite InThreadNamesSpec; auto.
      -- apply Permutation_in with (l' := nubPrin (ThreadNames C1' ++ ThreadNames C2')) in i;
           [| apply Permutation_sym; apply Permuted_sort].
         rewrite <- In_nub in i.
         apply in_app_or in i.
         apply Permutation_in with (l := nubPrin (ThreadNames C1 ++ ThreadNames C2));
           [apply Permuted_sort|].
         rewrite <- In_nub.
         apply in_or_app.
         destruct i as [i | i]; [left | right]; rewrite <- InThreadNamesSpec.
         rewrite <- ThreadNamesInvariant' with (C1 := C1'); [| symmetry; auto].
         2: rewrite <- ThreadNamesInvariant' with (C1 := C2'); auto.
         1,2: rewrite InThreadNamesSpec; auto.
         symmetry; auto.
    - remember (Sorted_sort (nubPrin (ThreadNames C1 ++ ThreadNames C2))).
      rewrite Sorted_LocallySorted_iff.
      clear Heql. rename l into std.
      remember (sort (nubPrin (ThreadNames C1 ++ ThreadNames C2))) as l.
      clear Heql.
      induction std; [constructor|constructor|].
      constructor; auto. destruct (PrinOrderDec a b); [auto | inversion H].
    - remember (Sorted_sort (nubPrin (ThreadNames C1' ++ ThreadNames C2'))).
      rewrite Sorted_LocallySorted_iff.
      clear Heql. rename l into std.
      remember (sort (nubPrin (ThreadNames C1' ++ ThreadNames C2'))) as l.
      clear Heql.
      induction std; [constructor|constructor|].
      constructor; auto. destruct (PrinOrderDec a b); [auto | inversion H].
    - intro p; rewrite countPermutation with (l' := nubPrin (ThreadNames C1 ++ ThreadNames C2)).
      apply nubPrinCount'.
      apply Permutation_sym; apply Permuted_sort.
    - intro p; rewrite countPermutation with (l' := nubPrin (ThreadNames C1' ++ ThreadNames C2')).
      apply nubPrinCount'.
      apply Permutation_sym; apply Permuted_sort.
  Qed.

  Lemma CommListEq :  forall C1 C2 C1' C2' : Chor,
      C1 ≡ C1' -> C2 ≡ C2' -> CommList C1 C2 = CommList C1' C2'.
  Proof.
    intros C1 C2 C1' C2' equiv1; revert C2 C2'; induction equiv1;
      intros C2' C2'' equiv2.
    induction equiv2.
    - apply CommListEq'; auto.
    - rewrite <- IHequiv2.
      apply CommListEq'; [reflexivity | auto].
    - transitivity (CommList C2 C2'). apply CommListEq'; [auto | reflexivity].
      apply IHequiv1; auto.
  Qed.

  Module PC := PiCalc E.
  Parameter PrinToRole : Prin -> PC.Role.
  Parameter PrinToRoleInj: forall p q, PrinToRole p = PrinToRole q -> p = q.
  Coercion PrinToRole : Prin >-> PC.Role.
  Parameter Env : PC.Role.
  Parameter EnvNotPrin : forall p : Prin, Env <> p.

  Fixpoint DoCommsLeft (l : list Prin) (P : PC.Proc) : PC.Proc :=
    match l with
    | nil => PC.EChoiceL Env P
    | q :: l' => PC.EChoiceL q (DoCommsLeft l' P)
    end.

  Fixpoint DoCommsRight (l : list Prin) (P : PC.Proc) : PC.Proc :=
    match l with
    | nil => PC.EChoiceR Env P
    | q :: l' => PC.EChoiceR q (DoCommsRight l' P)
    end.

  Definition DefValuation :  (nat -> list Prin) -> list Prin -> nat -> list Prin :=
    fun v l n => match n with
              | 0 => l
              | S n' => v n'
              end.

  Fixpoint MergeProcs (p : PC.Role) (P1 P2 : PC.Proc) : PC.Proc :=
    match P1 with
    | PC.EndProc =>
      match P2 with
      | PC.EndProc => PC.IChoice p PC.EndProc PC.EndProc
      | _ => PC.IChoice p PC.EndProc P2
      end
    | PC.VarProc n => PC.IChoice p P1 P2
    | PC.DefProc _ _ => 
      PC.IChoice p P1 P2
    | PC.SendProc q e P1' =>
      match P2 with
      | PC.SendProc r e' P2' =>
        if PC.RoleEqDec q r
        then if ExprEqDec e e'
             then if PC.RoleEqDec p q
                  then PC.IChoice p P1 P2
                  else PC.SendProc q e (MergeProcs p P1' P2')
             else PC.IChoice p P1 P2
        else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.RecvProc q P1' =>
      match P2 with
      |PC.RecvProc r P2' =>
       if PC.RoleEqDec q r
       then if PC.RoleEqDec p q
            then PC.IChoice p P1 P2
            else PC.RecvProc q (MergeProcs p P1' P2')
       else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.EChoiceL q P1' =>
      match P2 with
      | PC.EChoiceL r P2' =>
        if PC.RoleEqDec q r
        then (* if PC.RoleEqDec p q *)
             (* then PC.IChoice p P1 P2 *)
             (* else *) PC.EChoiceL q (MergeProcs p P1' P2')
        else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.EChoiceR q P1' => 
      match P2 with
      | PC.EChoiceR r P2' =>
        if PC.RoleEqDec q r
        then (* if PC.RoleEqDec p q *)
             (* then PC.IChoice p P1 P2 *)
             (* else *) PC.EChoiceR q (MergeProcs p P1' P2')
        else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.IChoice q P11 P12 =>
      match P2 with
      | PC.IChoice r P21 P22 =>
        if PC.RoleEqDec q r
        then if PC.RoleEqDec p q
             then PC.IChoice p P1 P2
             else PC.IChoice q (MergeProcs p P11 P21) (MergeProcs p P12 P22)
        else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.IfThenElse e P11 P12 =>
      match P2 with
      | PC.IfThenElse e' P21 P22 =>
        if ExprEqDec e e'
        then PC.IfThenElse e (MergeProcs p P11 P21) (MergeProcs p P12 P22)
        else PC.IChoice p P1 P2
      | _ => PC.IChoice p P1 P2
      end
    | PC.Par P11 P12 =>
      (* match P2 with *)
      (* | PC.Par P21 P22 => PC.Par (MergeProcs p P11 P21) (MergeProcs p P12 P22) *)
      (* |_ => PC.IChoice p P1 P2 *)
      (* end *)
      PC.IChoice p P1 P2
    end.
    
  Fixpoint EPP' (C : Chor) (p : Prin) (l : list Prin) : PC.Proc :=
    match C with
    | CDone q e =>
      if PrinEqDec p q
      then PC.SendProc Env e PC.EndProc
      else PC.EndProc
    | CVar n => PC.VarProc n
    | CSend q e r C' =>
      if PrinEqDec p q
      then PC.SendProc r e (EPP' C' p l)
      else if PrinEqDec p r
           then PC.RecvProc q (EPP' C' p l)
           else EPP' C' p l
    | CIf q e C1 C2 =>
      if PrinEqDec p q
      then let l' := remove PrinEqDec p l in
           PC.IfThenElse e (DoCommsLeft l' (EPP' C1 p l)) (DoCommsRight l' (EPP' C2 p l))
      else MergeProcs q (EPP' C1 p l) (EPP' C2 p l)
    | CDef C1 C2 => PC.DefProc (EPP' C1 p l) (EPP' C2 p l)
    end.

  Definition EPP (C : Chor) (p : Prin) := EPP' C p (PrinSort.sort (nubPrin (ThreadNames C))).

  Fixpoint InPrinList (r : PC.Role) (l : list Prin) : option Prin :=
    match l with
    | nil => None
    | cons p l => if PC.RoleEqDec p r
                 then Some p
                 else InPrinList r l       
    end.

  Lemma InPrinListSpec1 : forall r l p, InPrinList r l = Some p -> In p l.
  Proof.
    intros r l; revert r; induction l; intros r p eq.
    simpl in eq; inversion eq.
    simpl in eq. destruct (PC.RoleEqDec a r); [inversion eq|]; subst.
    left; auto. right; apply IHl with (r := r); auto.
  Qed.

  Lemma InPrinListSpec2 : forall r l p, InPrinList r l = Some p -> r = p.
  Proof.
    intros r l; revert r; induction l; intros r p eq.
    simpl in eq; inversion eq.
    simpl in eq. destruct (PC.RoleEqDec a r); [inversion eq; subst|].
    reflexivity. apply IHl; auto.
  Qed.

  Fixpoint ProjectEnv (C : Chor) : PC.Proc :=
    match C with
    | CDone p e => PC.RecvProc p PC.EndProc
    | CVar n => PC.VarProc n
    | CSend q e r C' => ProjectEnv C'
    | CIf p e C1 C2 => PC.IChoice p (ProjectEnv C1) (ProjectEnv C2)
    | CDef C1 C2 => PC.DefProc (ProjectEnv C1) (ProjectEnv C2)
    end.
    

  Definition FullEPP (C : Chor) : PC.Role -> PC.Proc :=
    fun r => match InPrinList r (ThreadNames C) with
          | Some p => EPP C p
          | None => if PC.RoleEqDec r Env
                   then ProjectEnv C
                   else PC.EndProc
          end.
  (* Lemma MergeCommsRight : forall (p : Prin) (l : list Prin) (P Q : PC.Proc), *)
  (*     MergeProcs p (DoCommsRight l P) (DoCommsRight l Q) = DoCommsRight l (MergeProcs p P Q). *)
  (* Proof. *)
  (*   intros p l; revert p; induction l; intros p P Q; simpl. *)
  (*   - destruct (PC.RoleEqDec Env Env) as [_ | neq]; [|exfalso; apply neq; reflexivity]. *)
  (*     destruct (PC.RoleEqDec p Env) as [eq | _]; [exfalso; apply (EnvNotPrin p); auto|]. *)
  (*     reflexivity. *)
  (*   - destruct (PC.RoleEqDec a a) as [_ | neq]; [|exfalso; apply neq; reflexivity]. *)
  (*     rewrite IHl; reflexivity. *)
  (* Qed.       *)

  (* Lemma SwapMerge : forall p q P1 P2 P3 P4, *)
  (*     MergeProcs p (MergeProcs q P1 P2) (MergeProcs q P3 P4) *)
  (*     = MergeProcs q (MergeProcs p P1 P3) (MergeProcs p P2 P4). *)
  (* Proof. *)
  (*   intros p q P1; induction P1; simpl; destruct P2; simpl. *)
  (* Abort. *)

  (* Infix "≡π'" := PC.PiEquiv' (at level 15). *)
  (* Infix "≡π" := PC.PiEquiv (at level 15). *)
  Import PC.

  (* Theorem PiCalcInBStep : forall (C1 C2 : Chor) (R : Redex) (B : list Prin), *)
  (*     RChorStep R B C1 C2 -> forall p l, In p B -> EPP' C1 p l = EPP' C2 p l. *)
  (* Proof. *)
  (*   intros C1 C2 R B step; induction step; simpl; *)
  (*     intros r l i; try (inversion i; fail). *)
  (*   - destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H; rewrite <- e; auto|]. *)
  (*     destruct (PrinEqDec r q) as [e |_]; [exfalso; apply H0; rewrite <- e; auto|]. *)
  (*     reflexivity. *)
  (*   - destruct (PrinEqDec r p). rewrite IHstep; auto. left; auto. *)
  (*     destruct (PrinEqDec r q). rewrite IHstep; auto. right; left; auto. *)
  (*     apply IHstep; right; right; auto. *)
  (*   - destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H; rewrite <- e; auto|]. *)
  (*     destruct (PrinEqDec r q) as [e |_]; [exfalso; apply H0; rewrite <- e; auto|]. *)
      

  
  (* Theorem PiCalcSimulation : forall (C1 C2 : Chor) (R : Redex) (B : list Prin), *)
  (*     RChorStep R B C1 C2 -> PiManyStep (FullEPP C1) (FullEPP C2). *)
  (* Proof. *)
  (*   intros C1 C2 R B step; induction step; unfold FullEPP; simpl. *)
  (*   - unfold EPP; simpl; apply PiOneStep. *)
  (*     apply CommEStep with (p := p) (q := Env) (e := e1) (e' := e2) (P := EndProc) (CC := Hole); *)
  (*       auto. *)
  (*     -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        simpl. reflexivity. *)
  (*     -- intros r nrp. destruct (RoleEqDec p r) as [e |_]; [exfalso; apply nrp; auto|]. *)
  (*        destruct (RoleEqDec r Env); auto. *)
  (*     -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        simpl. reflexivity. *)
  (*   - apply PiOneStep. *)
  (*     eapply CommEStep with (p := p) (q := q) (e := e1) (e' := e2) (CC := Hole); auto. *)
  (*     -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        simpl. unfold EPP. simpl. *)
  (*        destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (*     -- intros r n. destruct (RoleEqDec p r) as [e |_]; [exfalso; apply n; auto|]. *)
  (*        destruct (RoleEqDec q r); auto. *)
  (*        unfold EPP; simpl. *)
  (*        destruct (PrinEqDec q p) as [eq |_]; [exfalso; apply H1; auto|]. *)
  (*        destruct (PrinEqDec q q) as [_|neq]; [|exfalso; apply neq; auto]. *)
  (*        reflexivity. *)
  (*        destruct (InPrinList r (ThreadNames C)) eqn:eq. *)
  (*        apply InPrinListSpec2 in eq. *)
  (*        unfold EPP; simpl. *)
  (*        destruct (PrinEqDec p0 p) as [ e|_]; *)
  (*          [exfalso; apply n; transitivity p0; [apply eq| apply f_equal; exact e]|]. *)
  (*        destruct (PrinEqDec p0 q) as [ e|_]; *)
  (*          [exfalso; apply n0; transitivity p0; [apply f_equal; auto| auto]|]. *)
  (*        reflexivity. *)
  (*        reflexivity. *)
  (*     -- unfold EPP; simpl. *)
  (*        destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (*   -           *)
         

  Theorem DoCommsLeftEquiv' : forall (l : list Prin) (P Q : Proc),
      P ≡π' Q -> DoCommsLeft l P ≡π' DoCommsLeft l Q.
  Proof.
    intro l; induction l; intros P Q equiv; simpl; auto with PiC.
  Qed.

  Theorem DoCommsLeftEquiv : forall (l : list Prin) (P Q : Proc),
      P ≡π Q -> DoCommsLeft l P ≡π DoCommsLeft l Q.
  Proof.
    intro l; induction l; intros P Q equiv; simpl; auto with PiC.
  Qed.
    
  Theorem DoCommsRightEquiv' : forall (l : list Prin) (P Q : Proc),
      P ≡π' Q -> DoCommsRight l P ≡π' DoCommsRight l Q.
  Proof.
    intro l; induction l; intros P Q equiv; simpl; auto with PiC.
  Qed.

  Theorem DoCommsRightEquiv : forall (l : list Prin) (P Q : Proc),
      P ≡π Q -> DoCommsRight l P ≡π DoCommsRight l Q.
  Proof.
    intro l; induction l; intros P Q equiv; simpl; auto with PiC.
  Qed.

  Hint Resolve DoCommsLeftEquiv DoCommsRightEquiv : PiC.
  Lemma MergeCommsLeft : forall (p : Prin) (l : list Prin) (P Q : PC.Proc),
      MergeProcs p (DoCommsLeft l P) (DoCommsLeft l Q) = DoCommsLeft l (MergeProcs p P Q).
  Proof.
    intros p l; revert p; induction l; intros p P Q.
    - simpl; destruct (PC.RoleEqDec Env Env) as [_ | neq];
        [reflexivity|exfalso; apply neq; reflexivity].
    - simpl; destruct (RoleEqDec a a) as [_|n];[|exfalso;apply n; auto].
      rewrite IHl; auto.
  Qed.

  Theorem MergeProcsEquiv' : forall (p : Role) (P P' Q Q' : Proc),
      P ≡π' P' -> Q ≡π' Q' -> MergeProcs p P Q ≡π' MergeProcs p P' Q'.
  Proof.
    intros p P P' Q Q' equivP; revert p Q Q'; induction equivP; simpl;
      intros q Q Q' equivQ; auto with PiC.
    all: try (destruct Q; destruct Q'; auto with PiC; fail).
    all: try (destruct equivQ; auto with PiC;
              repeat match goal with
                     | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                     | [ H1 : ?a <> ?c, H2 : ?b = ?a, H3 : ?b = ?c |- _ ] =>
                       exfalso; apply H1; transitivity b; [symmetry; exact H2 | exact H3]
                     | [ |- context[RoleEqDec ?a ?b] ] =>
                       destruct (RoleEqDec a b); simpl
                     | [ |- context[ExprEqDec ?a ?b]]=>
                       destruct (ExprEqDec a b); simpl
                     end; auto with PiC; fail).
  Qed.
  Theorem MergeProcsEquiv : forall (p : Role) (P P' Q Q' : Proc),
      P ≡π P' -> Q ≡π Q' -> MergeProcs p P Q ≡π MergeProcs p P' Q'.
  Proof.
    intros p P P' Q Q' equivP; revert p Q Q'; induction equivP; simpl;
      intros p S S' equivS; auto with PiC.
    - revert p; induction equivS; intro p.
      -- econstructor; apply MergeProcsEquiv'; auto.
      -- transitivity (MergeProcs p P Q0); auto.
         constructor; apply MergeProcsEquiv'; auto with PiC.
    - specialize (IHequivP p S S' equivS).
      transitivity (MergeProcs p Q S); auto.
      constructor; apply MergeProcsEquiv'; auto with PiC.
  Qed.
  Hint Resolve MergeProcsEquiv MergeProcsEquiv' : PiC.
  
  Theorem Equiv'Project : forall (C1 C2 : Chor),
      C1 ≡' C2 -> forall (p : Prin) (l : list Prin), EPP' C1 p l = EPP' C2 p l.
  Proof.
    intros C1 C2 equiv'; induction equiv'; intros t l; unfold EPP; simpl in *; auto with PiC.
    all: try (rewrite IHequiv'1; rewrite IHequiv'2; reflexivity).
    all: repeat match goal with
                | [ H1 : ?a <> ?c, H2 : ?b = ?a, H3 : ?b = ?c |- _ ] =>
                  exfalso; apply H1; transitivity b; [symmetry; exact H2 | exact H3]
                | [ |- context[PrinEqDec ?a ?b] ] =>
                  destruct (PrinEqDec a b); simpl
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                end; try (rewrite IHequiv'); try (rewrite IHequiv'1; rewrite IHequiv'2);
      auto with PiC.
    all: repeat match goal with
                | [ H : PrinToRole ?a = PrinToRole ?b |- _ ] =>
                  match goal with
                  | [ H : a = b |- _ ] => fail 1
                  | _ => assert (a = b) by (apply PrinToRoleInj; auto)
                  end
                | [ H1 : ?a <> ?b, H2 : ?a = ?b |- _] =>
                  exfalso; apply H1; exact H1
                | [ H1 : ?b <> ?a, H2 : ?a = ?b |- _] =>
                  exfalso; apply H1; symmetry; exact H1
                | [ H1 : ?a <> ?c, H2 : ?a = ?b, H3 : ?b = ?c |- _ ] =>
                  exfalso; apply H1; transitivity b; auto
                | [ H1 : ?a <> ?c, H2 : ?a = ?b, H3 : ?c = ?b |- _ ] =>
                  exfalso; apply H1; transitivity b; auto
                | [ H1 : ?a <> ?c, H2 : ?b = ?a, H3 : ?b = ?c |- _ ] =>
                  exfalso; apply H1; transitivity b; auto
                | [ H1 : ?a <> ?c, H2 : ?b = ?a, H3 : ?c = ?b |- _ ] =>
                  exfalso; apply H1; transitivity b; auto
                | [ |- context[PrinEqDec ?a ?b] ] =>
                  destruct (PrinEqDec a b); simpl
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                | [ |- context[PC.RoleEqDec ?a ?b] ] =>
                  destruct (PC.RoleEqDec a b)
                | [ |- context[ExprEqDec ?a ?b] ] =>
                  destruct (ExprEqDec a b)
                end; auto with PiC.
  Qed.

  Theorem EquivProject : forall (C1 C2 : Chor),
      C1 ≡ C2 -> forall (p : Prin) (l : list Prin), EPP' C1 p l = EPP' C2 p l.
  Proof.
    intros C1 C2 equiv; induction equiv.
    intros; eapply Equiv'Project in H. exact H.
    intros p l; eapply Equiv'Project in H.
    transitivity (EPP' C2 p l); eauto.
  Qed.

  Lemma ThreadNamesExprSubst : forall (C : Chor) (σ : Prin -> nat -> Expr),
      ThreadNames C = ThreadNames (C [c|ChorIdSubst; σ]).
  Proof.
    intro C; induction C; intros σ; simpl; auto with Chor.
    transitivity (p :: p0 :: ThreadNames (C [c|ChorIdSubst; ChorUpExprSubst σ p0])).
    rewrite <- IHC; auto.
    assert ((C [c|ChorIdSubst; ChorUpExprSubst σ p0]) =
            (C [c|SendUpChorSubst ChorIdSubst p0; ChorUpExprSubst σ p0])).
    apply ChorSubstExt.
    intro n; rewrite SendUpChorIdSubst; auto.
    intros p1 n; auto.
    rewrite H; auto.
    rewrite <- IHC1; rewrite <- IHC2; auto.
    assert (C1 [c| ChorUpSubst ChorIdSubst; σ] = C1 [c| ChorIdSubst; σ]).
    apply ChorSubstExt. intro n; symmetry; apply ChorUpIdSubst.
    intros p n; reflexivity.
    assert (C2 [c| ChorUpSubst ChorIdSubst; σ] = C2 [c| ChorIdSubst; σ]).
    apply ChorSubstExt. intro n; symmetry; apply ChorUpIdSubst.
    intros p n; reflexivity.
    rewrite H; rewrite H0;
    rewrite <- IHC1; rewrite <- IHC2; auto.
  Qed.

  (* Theorem EPP'NonPList (C : Chor) (p : Prin) (l l' : list Prin), *)
  
  Theorem SortRemoveNub2 : forall (p q : Prin) (l : list Prin),
      In p l -> In q l ->
      sort (p :: q :: remove PrinEqDec p (remove PrinEqDec q (nubPrin l)))
      = sort (nubPrin l).
  Proof.
  Abort.
  
  Theorem StdEPPSimultation : forall (C1 C2 : Chor),
      StdChorStep C1 C2 -> PiCalcStep (FullEPP C1) (FullEPP C2).
  Proof.
    intros C1 C2 step; induction step; unfold FullEPP; unfold EPP; simpl.
    - apply CommEStep with (p := p) (q := Env) (e := e1) (e' := e2) (P := EndProc) (CC := Hole);
        auto with PiC.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
      destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
      simpl. auto.
      -- intros r H0.
         destruct (RoleEqDec p r) as [eq |_]; [exfalso; apply H0; auto|reflexivity].
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl; auto.
    - eapply CommEStep with (p := p) (q := q) (e := e1) (e' := e2) (CC := Hole);
        auto with PiC.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. eauto.
      -- intros r n.
         destruct (RoleEqDec p r) as [e |_]; [exfalso; apply n; auto|].
         destruct (RoleEqDec q r).
         --- subst. destruct (PrinEqDec q p) as [e |_]; [exfalso; apply H0; auto|].
             destruct (PrinEqDec q q) as [_|neq]; [|exfalso; apply neq; auto].
             reflexivity.
         --- destruct (InPrinList r (ThreadNames C)) eqn:e.
             destruct (PrinEqDec p0 p) as [eq |_].
             apply InPrinListSpec2 in e. exfalso; apply n. transitivity p0; auto.
             apply f_equal; auto.
             destruct (PrinEqDec p0 q) as [eq |_].
             apply InPrinListSpec2 in e. exfalso; apply n0.
             transitivity p0; auto. apply f_equal; auto.
             reflexivity.
             reflexivity.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. auto.
    - eapply CommVStep with (p := p) (q := q) (v := v) (CC := Hole) (CC' := Hole); auto.
      -- intro e; apply H0; apply PrinToRoleInj; auto.
      -- destruct (RoleEqDec  p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec  p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. reflexivity.
      -- destruct (RoleEqDec p q) as [e |_];
           [exfalso; apply H0; apply PrinToRoleInj; auto|].
         destruct (RoleEqDec q q) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec q p) as [e |_]; [exfalso; apply H0; auto|].
         destruct (PrinEqDec q q) as [_|n]; [|exfalso; apply n; auto].
         simpl. reflexivity.
      -- intros r n1 n2.
         destruct (RoleEqDec p r) as [e |_]; [exfalso; apply n1; auto|].
         destruct (RoleEqDec q r) as [e |_]; [exfalso; apply n2; auto|].
         destruct (InPrinList r (ThreadNames C)) eqn:er.
         destruct (PrinEqDec p0 p) as [e |_]; [exfalso; apply n1|].
         apply InPrinListSpec2 in er; transitivity p0; auto.
         apply f_equal; auto.
         destruct (PrinEqDec p0 q) as [e |_]; [exfalso; apply n2|].
         apply InPrinListSpec2 in er; transitivity p0; auto.
         apply f_equal; auto.
         rewrite <- ThreadNamesExprSubst. rewrite er.
         
         
         
      
      


        

End Choreography.
