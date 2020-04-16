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
  | SwapIfIf' : forall p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22',
      p <> q ->
      C11 ≡' C11' -> C12 ≡' C12' -> C21 ≡' C21' -> C22 ≡' C22' ->
      CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) ≡'
          CIf q e2 (CIf p e1 C11' C21') (CIf p e1 C12' C22')
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

  Lemma SwapIfIf : forall p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22',
      p <> q ->
      C11 ≡ C11' -> C12 ≡ C12' -> C21 ≡ C21' -> C22 ≡ C22' ->
      CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) ≡
          CIf q e2 (CIf p e1 C11' C21') (CIf p e1 C12' C22').
  Proof.
    intros p e1 q e2 C11 C11' C12 C12' C21 C21' C22 C22' neq equiv1;
      revert p e1 q e2 C12 C12' C21 C21' C22 C22' neq;
      induction equiv1; eauto with Chor.
      intros p e1 q e2 C12 C12' C21 C21' C22 C22' neq equiv2;
      revert p e1 q e2 C21 C21' C22 C22' neq;
      induction equiv2; eauto with Chor.
      intros p e1 q e2 C21 C21' C22 C22' neq equiv3;
      revert p e1 q e2 C22 C22' neq;
      induction equiv3; eauto with Chor.
      intros p e1 q e2 C22 C22' neq equiv4;
      revert p e1 q e2 neq; 
      induction equiv4;
      intros p e1 q e2 neq;
      eauto with Chor.
  Qed.
  Hint Resolve SendContext IfContext DefContext SwapSendSend SwapSendIf SwapIfSend SwapIfIf : Chor.


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

  Inductive RChorStep : Redex -> list Prin -> Chor -> Chor -> Prop :=
  | DoneEStep : forall (p : Prin) (e1 e2 : Expr),
      ExprStep e1 e2 -> RChorStep (RDone p e1 e2) nil (CDone p e1) (CDone p e2)
  | SendEStep : forall (p q : Prin) (B : list Prin),
      ~ In p B -> ~ In q B -> p <> q ->
      forall (e1 e2 : Expr) (C : Chor),
        ExprStep e1 e2 -> RChorStep (RSendE p e1 e2 q) B (CSend p e1 q C) (CSend p e2 q C)
  | SendIStep : forall (p q : Prin) (e : Expr) (C1 C2 : Chor) (B : list Prin) (R : Redex),
      RChorStep R (p :: q :: B) C1 C2 ->
      RChorStep R B (CSend p e q C1) (CSend p e q C2)
  | SendVStep : forall (p q : Prin) (v : Expr) (C : Chor) (B : list Prin),
      ~ In p B -> ~ In q B -> p <> q ->
      ExprVal v ->
      RChorStep (RSendV p v q) B (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
  | IfEStep : forall (p : Prin) (e1 e2 : Expr) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      ExprStep e1 e2 ->
      RChorStep (RIfE p e1 e2) B (CIf p e1 C1 C2) (CIf p e2 C1 C2)
  | IfIStep : forall (p : Prin) (e : Expr) (C1 C2 C3 C4 : Chor) (B : list Prin) (R : Redex),
      RChorStep R (p :: B) C1 C3 ->
      RChorStep R (p :: B) C2 C4 ->
      RChorStep R B (CIf p e C1 C2) (CIf p e C3 C4)
  | IfTrueStep : forall (p : Prin) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      RChorStep (RIfTT p) B (CIf p tt C1 C2) C1
  | IfFalseStep : forall (p : Prin) (C1 C2 : Chor) (B : list Prin),
      ~ In p B ->
      RChorStep (RIfFF p) B (CIf p ff C1 C2) C2
  | DefStep : forall (C1 C2 : Chor),
      RChorStep RDef nil (CDef C1 C2) (C2 [c| DefSubst C1; ExprChorIdSubst]).
  Hint Constructors RChorStep : Chor.

  Ltac RStepRearrangeHelper :=
      match goal with
      | [i : ~ In ?p ?B1, ext : forall q, In q ?B1 <-> In q ?B2 |- ~ In ?p ?B2 ] =>
        let H := fresh in intro H; rewrite <- ext in H; apply i; exact H
      end.

  Lemma RStepRearrange : forall R B1 C1 C2,
      RChorStep R B1 C1 C2 -> forall B2, (forall q, In q B1 <-> In q B2) -> RChorStep R B2 C1 C2.
  Proof.
    intros R B1 C1 C2 step; induction step; intros B2 ext.
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
      forall C1 C2, ~RChorStep R B C1 C2.
  Proof.
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
    inversion H.
  Qed.

  Corollary NoDoneIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RDone p e1 e2) B C1 C2.
  Proof.
    intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply RODone.
  Qed.
  Corollary NoSendEIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2 q, ~RChorStep (RSendE p e1 e2 q) B C1 C2.
  Proof.
    intros p B H q e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendE.
  Qed.
  Corollary NoSendVIStepInList : forall p B,
      In p B ->
      forall v q C1 C2, ~RChorStep (RSendV p v q) B C1 C2.
  Proof.
    intros p B H v q C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendV.
  Qed.
  Corollary NoIfEIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RIfE p e1 e2) B C1 C2.
  Proof.
   intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfE.
  Qed.
  Corollary NoIfTTStepInList : forall p B,
      In p B ->
      forall C1 C2, ~RChorStep (RIfTT p) B C1 C2.
  Proof.
   intros p B H C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfTT.
  Qed.
  Corollary NoIfFFStepInList : forall p B,
      In p B ->
      forall C1 C2, ~RChorStep (RIfFF p) B C1 C2.
  Proof.
   intros p B H C1 C2; apply NoIStepInList with (p := p); auto; apply ROIfFF.
  Qed.    
  
  Hint Resolve RStepRearrange NoDoneIStepInList : Chor.
  Hint Resolve NoSendEIStepInList NoSendVIStepInList : Chor.
  Hint Resolve NoIfEIStepInList NoIfTTStepInList NoIfFFStepInList: Chor.

  Inductive ChorStepMany : list Prin -> Chor -> Chor -> Prop :=
  | ChorManyZero : forall B C, ChorStepMany B C C
  | ChorManyPlus : forall R B C1 C2 C3, RChorStep R B C1 C2 -> ChorStepMany B C2 C3 -> ChorStepMany B C1 C3.
  Hint Constructors ChorStepMany : Chor.

  Theorem ChorManyOne : forall (R : Redex) (B : list Prin) (C1 C2 : Chor),
      RChorStep R B C1 C2 -> ChorStepMany B C1 C2.
  Proof.
    intros R B C1 C2 step.
    eapply ChorManyPlus; [exact step | apply ChorManyZero].
  Qed.
  Hint Resolve ChorManyOne : Chor.

  Program Fixpoint ChorStepManyTrans (B : list Prin) (C1 C2 C3 : Chor)
           (r1 : ChorStepMany B C1 C2)
           (r2 : ChorStepMany B C2 C3) {struct r1} : ChorStepMany B C1 C3 :=
   match r1 with
   | ChorManyZero B C => r2
   | ChorManyPlus R B C1' C2' _ s1 r3 =>
     ChorManyPlus _ _ _ _ _ s1  (ChorStepManyTrans _ _ _ _ r3 r2)
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


  Theorem Equiv'Simulation : forall C1 C2, C1 ≡' C2 -> forall R B C1',
        RChorStep R B C1 C1' -> exists C2', RChorStep R B C2 C2' /\ C1' ≡ C2'.
  Proof.
    intros C1 C2 equiv; induction equiv; intros R B Cstep step;
      eauto with Chor; inversion step; eauto with Chor; subst.
    - exists (CSend p e2 q C2); split; auto with Chor.
    - destruct (IHequiv _ _ _ H6) as [C3' HC3'].
      destruct (HC3') as [step' equivC3].
      exists (CSend p e q C3'); split; auto with Chor.
    - exists (CIf p e2 C12 C22); split; auto with Chor.
    - destruct (IHequiv1 _ _ _ H6) as [C12' HC12'];
        destruct HC12' as [stepC12' equivC12'].
      destruct (IHequiv2 _ _ _ H7) as [C22' HC22'];
        destruct HC22' as [stepC22' equivC22'].
      exists (CIf p e C12' C22'); split; auto with Chor.
    - exists C12; split; auto with Chor.
    - exists C22; split; auto with Chor.
    - exists (C22 [c| DefSubst C12; ExprChorIdSubst]); split; auto with Chor.
      apply EquivStableSubst; auto with Chor.
      intro n; unfold DefSubst; destruct n; auto with Chor.
    - exists (CSend r e2 s (CSend p e3 q C2)); split; auto with Chor.
    - inversion H10; subst.
      -- exists (CSend r e3 s (CSend p e1 q C2)); split; eauto with Chor.
         apply SendEStep; auto; ListHelper.
      -- destruct (IHequiv _ _ _ H11) as [C4' HC4'];
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
    - inversion H8; subst.
      -- inversion H9; subst.
         exists (CSend q e3 r (CIf p e1 C1' C2')); split; auto with Chor.
         apply SendEStep; auto; try ListHelper.
         exfalso. apply NoSendEIStepInList in H14; auto. left; reflexivity.
      -- inversion H9; subst.
         1: apply NoSendEIStepInList in H10; [destruct H10 | left; reflexivity].
         2: apply NoSendVIStepInList in H10; [destruct H10 | left; reflexivity].
         destruct (IHequiv1 _ _ _ H10) as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv2 _ _ _ H11) as [C4' HC4']; destruct HC4' as [stepC4' equivC4'].
         exists (CSend q e2 r (CIf p e1 C3' C4')); split; auto with Chor.
         apply SendIStep. apply IfIStep.
         all: apply RStepRearrange with (B1 := q :: r :: p :: B); auto.
         all: intros q0; split; intros i.
         2,4: destruct i as [eq | i];
           [right; right; left
           | destruct i as [eq | i];
             [left
             | destruct i as [eq | i];
               [right; left
               | right; right; right]]]; auto.
         all: destruct i as [eq | i];
           [right; left; exact eq
           | destruct i as [eq | i];
             [ right; right; left; exact eq
             | destruct i as [eq | i];
               [ left; exact eq
               | right; right; right; exact i]]].
      -- inversion H9; subst;
           [apply NoSendVIStepInList in H14; [destruct H14 | left; reflexivity] |].
         exists (CIf p e1 C1' C2' [c| ChorIdSubst; SendSubst r e2]); split; auto with Chor.
         apply SendVStep; auto; try ListHelper.
         simpl. unfold SendSubst at 3.
         destruct (PrinEqDec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq|].
         fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
         apply IfContext; apply EquivStableSubst; auto with Chor.
    - exists (CSend q e2 r C1'); split; auto with Chor.
    - exists (CSend q e2 r C2'); split; auto with Chor.
    - exists (CIf p e1 (CSend q e3 r C1') (CSend q e3 r C2')); split; auto with Chor.
    - inversion H8; subst.
      -- exists (CIf p e3 (CSend q e2 r C1') (CSend q e2 r C2')); split; auto with Chor.
         apply IfEStep; auto; ListHelper.
      -- destruct (IHequiv1 _ _ _ H9) as [C5' H5']; destruct H5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ H10) as [C6' H6']; destruct H6' as [stepC6' equivC6'].
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
    - exists (CIf q e2 (CIf p e3 C11' C21') (CIf p e3 C12' C22')); split; auto with Chor.
    - inversion H7; subst.
      -- inversion H8; subst.
         2: { apply NoIfEIStepInList in H12; [destruct H12| left; reflexivity]. }
         exists (CIf q e3 (CIf p e1 C11' C21') (CIf p e1 C12' C22')); split; auto with Chor.
         apply IfEStep; auto. ListHelper.
      -- inversion H8; subst.
         apply NoIfEIStepInList in H9; [destruct H9| left; reflexivity].
         2: apply NoIfTTStepInList in H10; [destruct H10 | left; reflexivity].
         2: apply NoIfFFStepInList in H10; [destruct H10 | left; reflexivity].
         destruct (IHequiv1 _ _ _ H9) as [C0' HC0'];
           destruct HC0' as [stepC0' equivC0'].
         destruct (IHequiv2 _ _ _ H10) as [C5' HC5'];
           destruct HC5' as [stepC5' equivC5'].
         destruct (IHequiv3 _ _ _ H11) as [C3' HC3'];
           destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv4 _ _ _ H12) as [C6' HC6'];
           destruct HC6' as [stepC6' equivC6'].
         exists (CIf q e2 (CIf p e1 C0' C3') (CIf p e1 C5' C6')); split; auto with Chor.
         apply IfIStep; apply IfIStep; eauto with Chor.
         all: apply RStepRearrange with (B1 := q :: p :: B); auto.
         all: intros t; split; intros i.
         all: destruct i as [eq | i];
           [(* t = p *) right; left; exact eq
                      | destruct i as [eq | i];
                        [ (* t = q *) left; exact eq
                                    | right; right; exact i]].
      -- inversion H8; subst;
           [apply NoIfTTStepInList in H10; [destruct H10 | left; reflexivity] |].
         exists (CIf p e1 C11' C21'); split; auto with Chor.
         apply IfTrueStep; ListHelper.
      -- inversion H8; subst;
           [apply NoIfFFStepInList in H10; [destruct H10 | left; reflexivity] |].
         exists (CIf p e1 C12' C22'); split; auto with Chor.
         apply IfFalseStep; ListHelper.
    - exists (CIf q e2 C11' C12'); split; auto with Chor.
    - exists (CIf q e2 C21' C22'); split; auto with Chor.
  Qed.

  Theorem EquivSimulation : forall C1 C2, C1 ≡ C2 -> forall C1' R B, RChorStep R B C1 C1' -> exists C2',
          RChorStep R B C2 C2' /\ C1' ≡ C2'.
  Proof.
    intros C1 C2 H.
    induction H; intros C1' R B step.
    apply Equiv'Simulation with (C1 := C1); auto.
    destruct (Equiv'Simulation _ _ H _ _ _ step) as [C2' HC2'].
    destruct HC2' as [stepC2' equivC2'].
    destruct (IHchorEquiv _ _ _ stepC2') as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
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
      -> exists R C2', C2 ≡ C2' /\ RChorStep R nil C1 C2'.
  Proof.
    intros C1 C2 stdstep; induction stdstep.
    all:try ( eexists; eexists; split; [reflexivity | constructor; auto]).
    rename H into equiv1; rename H0 into equiv2;
      destruct IHstdstep as [R H]; destruct H as [C2'' H]; destruct H as [equiv2' step].
    destruct (EquivSimulation _ C1 (chorEquivSym _ _ equiv1) _ _ _ step) as [C2''' H];
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

  Lemma RStepOnTop : forall (R : Redex) (B : list Prin) (C1 C2 : Chor),
      RChorStep R B C1 C2 ->
      exists C1' C2', C1 ≡ C1' /\ C2 ≡ C2' /\ RChorStep R B C1' C2' /\ RedexOnTop R C1'.
  Proof.
    intros R B C1 C2 step; induction step.
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
             intro eq; apply H10; left; symmetry; exact eq.
             intro eq; apply H10; right; left; symmetry; exact eq.
         --- transitivity (CSend p e q C2'); auto with Chor.
             rewrite <- H7; apply SwapIfSend; auto with Chor.
             intro eq; apply H10; left; symmetry; exact eq.
             intro eq; apply H10; right; left; symmetry; exact eq.
         --- constructor; auto.
             intro i; apply H10; right; right; exact i.
      -- exists (CIf p0 tt (CSend p e q C0) (CSend p e q C3));
           exists (CSend p e q C0);
           rewrite H4 in *;
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H1. apply SwapIfSend; auto with Chor.
             intro eq; apply H6; left; symmetry; exact eq.
             intro eq; apply H6; right; left; symmetry; exact eq.
         --- apply IfTrueStep. intro i; apply H6; right; right; exact i.
      -- exists (CIf p0 ff (CSend p e q C0) (CSend p e q C3));
           exists (CSend p e q C3);
           rewrite H4 in *; 
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H1. apply SwapIfSend; auto with Chor.
             intro eq; apply H6; left; symmetry; exact eq.
             intro eq; apply H6; right; left; symmetry; exact eq.
         --- apply IfFalseStep. intro i; apply H6; right; right; exact i.
      -- exists (CSend p0 e0 q0 (CSend p e q C));
           exists (CSend p0 e1 q0 (CSend p e q C));
           split; [| split; [| split]]; rewrite H3; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H4. apply SwapSendSend; auto with Chor.
             intro eq; apply H10; left; auto.
             intro eq; apply H10; right; left; auto.
             intro eq; apply H12; left; exact eq.
             intro eq; apply H12; right; left; exact eq.
         --- transitivity (CSend p e q C2'); auto with Chor.
             rewrite <- H11. apply SwapSendSend; auto with Chor.
             intro eq; apply H10; left; exact eq.
             intro eq; apply H10; right; left; exact eq.
             intro eq; apply H12; left; exact eq.
             intro eq; apply H12; right; left; exact eq.
         --- apply SendEStep; auto;
               intro i; [apply H10 | apply H12]; right; right; exact i.
      -- exists (CSend p0 e0 q0 (CSend p e q C));
           exists (CSend p e q C [c| ChorIdSubst; SendSubst q0 e0]);
           split; [| split; [| split]]; rewrite H2; auto with Chor StdChor.
         --- transitivity (CSend p e q C1'); auto with Chor.
             rewrite <- H3. apply SwapSendSend; auto with Chor.
             intro eq; apply H7; left; exact eq.
             intro eq; apply H7; right; left; exact eq.
             intro eq; apply H9; left; exact eq.
             intro eq; apply H9; right; left; exact eq.
         --- transitivity (CSend p e q C2'); auto with Chor.
             rewrite <- H10. simpl. unfold SendSubst at 2.
             destruct (PrinEqDec p1 p) as [eq | _];
               [exfalso; apply H9; left; symmetry; exact eq|].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
             assert (C [c|ChorIdSubst; SendSubst p1 e0]
                     = C [c|SendUpChorSubst ChorIdSubst q;
                            ChorUpExprSubst (SendSubst p1 e0) q]).
             apply ChorSubstExt.
             intro n; symmetry; apply SendUpChorIdSubst.
             intros p5 n; symmetry; apply UpSendSubst.
             intro eq; apply H9; right; left; symmetry; exact eq.
             rewrite H13; auto with Chor.
         --- apply SendVStep; auto with Chor.
             intro i; apply H7; right; right; exact i.
             intro i; apply H9; right; right; exact i.
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
      -- exists (CIf p0 e0 (CIf p e C0 C6) (CIf p e C5 C7));
           exists (CIf p0 e1 (CIf p e C0 C6) (CIf p e C5 C7));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H3; rewrite <- H7.
             apply SwapIfIf; auto with Chor.
             intro eq; apply H23; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H11; rewrite <- H20.
             apply SwapIfIf; auto with Chor.
             intro eq; apply H23; left; exact eq.
         --- apply IfEStep; auto with Chor.
             intro i; apply H23; right; exact i.
      -- exists (CIf p0 tt (CIf p e C0 C6) (CIf p e C5 C7));
           exists (CIf p e C0 C6);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H1; rewrite <- H3. apply SwapIfIf; auto with Chor.
             intro eq; apply H14; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H6; rewrite <- H12; auto with Chor.
         --- apply IfTrueStep. intro i; apply H14; right; exact i.
      -- exists (CIf p0 ff (CIf p e C0 C6) (CIf p e C5 C7));
           exists (CIf p e C5 C7);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H1; rewrite <- H3. apply SwapIfIf; auto with Chor.
             intro eq; apply H14; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H6; rewrite <- H12; auto with Chor.
         --- apply IfFalseStep. intro i; apply H14; right; exact i.
      -- exists (CSend p0 e0 p1 (CIf p e C C0));
           exists (CSend p0 e1 p1 (CIf p e C C0));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H4; rewrite <- H9. apply SwapSendIf; auto with Chor.
             intro eq; apply H26; left; exact eq.
             intro eq; apply H28; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H16; rewrite <- H27. apply SwapSendIf; auto with Chor.
             intro eq; apply H26; left; exact eq.
             intro eq; apply H28; left; exact eq.
         --- apply SendEStep; auto.
             intro i; apply H26; right; exact i.
             intro i; apply H28; right; exact i.
      -- exists (CSend p0 e0 p1 (CIf p e C C0));
           exists (CIf p e C C0 [c|ChorIdSubst; SendSubst p1 e0]);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e C1' C2'); auto with Chor.
             rewrite <- H3; rewrite <- H7. apply SwapSendIf; auto with Chor.
             intro eq; apply H21; left; exact eq.
             intro eq; apply H23; left; exact eq.
         --- transitivity (CIf p e C3' C4'); auto with Chor.
             rewrite <- H14; rewrite <- H24.
             simpl. unfold SendSubst at 3.
             destruct (PrinEqDec p1 p) as [eq | _];
               [exfalso; apply H23; left; symmetry; exact eq |].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec. reflexivity.
         --- apply SendVStep; auto.
             intro i; apply H21; right; exact i.
             intro i; apply H23; right; exact i.
  Qed.

  Lemma RStepOnTopToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Prin),
      RedexOnTop R C1 ->
      RChorStep R B C1 C2 ->
      StdChorStep C1 C2.
  Proof.
    intros C1 C2 R B ontop rstep; induction rstep; inversion ontop;
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
  Theorem RStepToStd : forall (C1 C2 : Chor) (R : Redex) (B : list Prin),
      RChorStep R B C1 C2 -> StdChorStep C1 C2.
  Proof.
    intros C1 C2 R B rstep.
    apply RStepOnTop in rstep;
      destruct rstep as [C1' H]; destruct H as [C2' H];
      destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [rstep ontop].
    apply StdEquivStep with (C1' := C1') (C2' := C2'); auto.
    apply RStepOnTopToStd with (R := R) (B := B); auto.
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

  Hint Resolve PrinOrderRefl PrinOrderAntisym PrinOrderTrans : Chor.
  Instance PrinOrderReflexive : Reflexive PrinOrder := PrinOrderRefl.
  Instance PrinOrderTransitive : Transitive PrinOrder := PrinOrderTrans.
  
  Module Import PrinSort := Sort PrinOrderM.

  Reserved Infix "⭆" (at level 15).
  Inductive NormStep : Chor -> Chor -> Prop :=
  | SendContextStep : forall p e q C1 C2,
      C1 ⭆ C2 ->
      CSend p e q C1 ⭆ CSend p e q C2
  | IfContextStep1 : forall p e C11 C12 C2,
      C11 ⭆ C12 -> CIf p e C11 C2 ⭆ CIf p e C12 C2
  | IfContextStep2 : forall p e C1 C21 C22,
      C21 ⭆ C22 -> CIf p e C1 C21 ⭆ CIf p e C1 C22
  | DefContextStep1 : forall C11 C12 C2,
      C11 ⭆ C12 ->
      CDef C11 C2 ⭆ CDef C12 C2
  | DefContextStep2 : forall C1 C21 C22,
      C21 ⭆ C22 ->
      CDef C1 C21 ⭆ CDef C1 C22
  | SwapSendSendStep : forall (p q r s : Prin) (C : Chor) (e1 e2 : Expr),
      p <> r -> q <> r -> p <> s -> q <> s ->
      r ≤p p -> (* Orienting the rule *)
      CSend p e1 q (CSend r e2 s C) ⭆ CSend r e2 s (CSend p e1 q C)
  | SwapSendIfStep : forall p e1 q e2 r C1 C2,
      p <> q -> p <> r ->
      CIf p e1 (CSend q e2 r C1) (CSend q e2 r C2) ⭆ CSend q e2 r (CIf p e1 C1 C2)
  | SwapIfIfStep : forall p e1 q e2 C11 C12 C21 C22,
      p <> q ->
      q ≤p p ->
      CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) ⭆
          CIf q e2 (CIf p e1 C11 C21) (CIf p e1 C12 C22)
  where "C1 ⭆ C2" := (NormStep C1 C2).
  Hint Constructors NormStep : Chor.

  Lemma NormStepEquiv' : forall C1 C2 : Chor, C1 ⭆ C2 -> C1 ≡' C2.
  Proof.
    intros C1 C2 step; induction step; auto with Chor.
  Qed.

  
    
  Reserved Infix "⭆*" (at level 15).
  Inductive NormSteps : Chor -> Chor -> Prop :=
  | ZeroNormSteps : forall C : Chor, C ⭆* C
  | ExtraNormStep : forall {C1 C2 C3}, C1 ⭆ C2 -> C2 ⭆* C3 -> C1 ⭆* C3
  where "C1 ⭆* C2" := (NormSteps C1 C2).
  Hint Constructors NormSteps : Chor.

  Instance NormStepsRefl : Reflexive NormSteps := ZeroNormSteps.
  Instance NormStepsTrans : Transitive NormSteps.
  Proof.
    unfold Transitive; intros C1 C2 C3 steps1; revert C3; induction steps1;
      intros C4 steps2.
    exact steps2. apply IHsteps1 in steps2. apply @ExtraNormStep with (C2 := C2); auto.
  Qed.
  Hint Resolve NormStepsRefl NormStepsTrans : Chor.

  Definition NormStepsOne : forall {C1 C2 : Chor}, C1 ⭆ C2 -> C1 ⭆* C2 :=
    fun {C1 C2} step => ExtraNormStep step (ZeroNormSteps C2).
  Hint Resolve NormStepsOne : Chor.

  Lemma SendContextSteps : forall C1 C2 : Chor,
      C1 ⭆* C2 -> forall p e q, CSend p e q C1 ⭆* CSend p e q C2.
  Proof.
    intros C1 C2 steps; induction steps; intros p e q; auto with Chor.
    transitivity (CSend p e q C2).
    apply NormStepsOne; auto with Chor.
    apply IHsteps.
  Qed.
  Lemma IfContextSteps : forall C1 C1' C2 C2' p e,
      C1 ⭆* C1' -> C2 ⭆* C2' -> CIf p e C1 C2 ⭆* CIf p e C1' C2'.
  Proof.
    intros C1 C1' C2 C2' p e steps1 steps2.
    revert C2 C2' steps2; induction steps1; intros C4 C4' steps4;
      [|revert C1 C2 C3 H steps1 IHsteps1]; induction steps4; auto with Chor;
       try (intros C1 C2 C3 step1 steps1 IHsteps1).
    - transitivity (CIf p e C C2); auto with Chor.
    - transitivity (CIf p e C2 C); auto with Chor.
    - rename H into steps12. intros C0 C4 C5 step04 steps45 IHsteps05.
      specialize (IHsteps4 C0 C4 C5 step04 steps45 IHsteps05).
      transitivity (CIf p e C0 C2); auto with Chor.
  Qed.
  Lemma DefContextSteps : forall C1 C1' C2 C2',
      C1 ⭆* C1' -> C2 ⭆* C2' -> CDef C1 C2 ⭆* CDef C1' C2'.
  Proof.
    intros C1 C1' C2 C2' steps1; revert C2 C2'; induction steps1;
      intros C4 C4' steps4; [|revert C1 C2 C3 H steps1 IHsteps1];
        induction steps4; auto with Chor.
    - transitivity (CDef C C2); auto with Chor.
    - intros C1 C2 C3 step1 steps1 IHsteps1. transitivity (CDef C2 C); auto with Chor.
    - intros C0 C4 C5 step1 steps1 IHsteps1.
      specialize (IHsteps4 C0 C4 C5 step1 steps1 IHsteps1).
      transitivity (CDef C0 C2); auto with Chor.
  Qed.
  Hint Resolve SendContextSteps IfContextSteps DefContextSteps : Chor.

  Lemma NormStepsEquiv : forall C1 C2 : Chor, C1 ⭆* C2 -> C1 ≡ C2.
  Proof.
    intros C1 C2 steps; induction steps; auto with Chor.
    apply NormStepEquiv' in H; eauto with Chor.
  Qed.
  
  Lemma Equiv'NormSteps : forall C1 C2 : Chor, C1 ≡' C2 -> exists C3, C1 ⭆* C3 /\ C2 ⭆* C3.
  Proof.
    intros C1 C2 equiv; induction equiv; auto.
    - exists (CDone p e); split; auto with Chor.
    - exists (CVar n); split; auto with Chor.
    - destruct IHequiv as [C3 IH]; destruct IH as [steps1 steps2].
      exists (CSend p e q C3); split; auto with Chor.
    - destruct IHequiv1 as [C13 IH1]; destruct IH1 as [steps11 steps12].
      destruct IHequiv2 as [C23 IH2]; destruct IH2 as [steps21 steps22].
      exists (CIf p e C13 C23); split; auto with Chor.
    - destruct IHequiv1 as [C13 IH1]; destruct IH1 as [steps11 steps12].
      destruct IHequiv2 as [C23 IH2]; destruct IH2 as [steps21 steps22].
      exists (CDef C13 C23); split; auto with Chor.
    - destruct IHequiv as [C3 IH]; destruct IH as [steps1 steps2].
      destruct (PrinOrderTotal p r).
      exists (CSend p e1 q (CSend r e2 s C3)); split; eauto with Chor.
      exists (CSend r e2 s (CSend p e1 q C3)); split; eauto with Chor.
    - destruct IHequiv1 as [C13 IH1]; destruct IH1 as [steps11 steps12].
      destruct IHequiv2 as [C23 IH2]; destruct IH2 as [steps21 steps22].
      exists (CSend q e2 r (CIf p e1 C13 C23)); split; eauto with Chor.
    - destruct IHequiv1 as [C13 IH1]; destruct IH1 as [steps11 steps12].
      destruct IHequiv2 as [C23 IH2]; destruct IH2 as [steps21 steps22].
      exists (CSend q e2 r (CIf p e1 C13 C23)); split; eauto with Chor.
    - destruct IHequiv1 as [C13 IH1]; destruct IH1 as [steps11 steps12].
      destruct IHequiv2 as [C23 IH2]; destruct IH2 as [steps21 steps22].
      destruct IHequiv3 as [C33 IH3]; destruct IH3 as [steps31 steps32].
      destruct IHequiv4 as [C43 IH4]; destruct IH4 as [steps41 steps42].
      destruct (PrinOrderTotal p q).
      exists (CIf p e1 (CIf q e2 C13 C23) (CIf q e2 C33 C43)); split; auto with Chor.
      apply @ExtraNormStep with (C2 := CIf p e1 (CIf q e2 C11' C12') (CIf q e2 C21' C22'));
        auto with Chor.
      exists (CIf q e2 (CIf p e1 C13 C33) (CIf p e1 C23 C43)); split; auto with Chor.
      apply @ExtraNormStep with (C2 := CIf q e2 (CIf p e1 C11 C21) (CIf p e1 C12 C22));
        auto with Chor.
  Qed.

  (* Theorem WeakDiamond : forall C1 C2 C3 : Chor, *)
  (*     C1 ⭆ C2 -> C1 ⭆ C3 -> *)
  (*     exists C4, C2 ⭆* C4 /\ C3 ⭆* C4. *)
  (* Proof. *)
  (*   intros C1 C2 C3 step1; revert C3; induction step1; *)
  (*     intros C3 step3; inversion step3; subst. *)
  (*   - apply IHstep1 in H4. destruct H4 as [C5 H]; destruct H as [step1' step2']. *)
  (*     exists (CSend p e q C5); split; auto with Chor. *)
  (*   - inversion step1; subst. *)
  (*     -- exists (CSend r e2 s (CSend p e q C0)); split; auto with Chor. *)
  (*     -- assert (r0 ≤p p) by (transitivity r; auto). *)
  (*        destruct (PrinEqDec q r0); subst; [| destruct (PrinEqDec q s0); subst]. *)
  (*        --- exists (CSend r e2 s (CSend p e r0 (CSend r0 e0 s0 C0))); split; auto with Chor. *)
  (*            transitivity (CSend p e r0 (CSend r e2 s (CSend r0 e0 s0 C0))); *)
  (*              auto with Chor. *)
  (*            apply NormStepsOne. apply SendContextStep. apply SwapSendSendStep; auto. *)
  (*        exists (CSend r0 e0 s0 (CSend r e2 s (CSend p e q C0))); split; auto with Chor. *)
  (*        --- transitivity (CSend r0 e0 s0 (CSend p e q (CSend r e2 s C0))); auto with Chor. *)
  (*            apply NormStepsOne. apply SwapSendSendStep; auto. *)
  (*            intro eq; subst. apply H5; apply PrinOrderAntisym; auto. *)
  (*            intro eq; subst. apply H3; apply PrinOrderAntisym; auto. *)
      

  
  Definition NormalForm : Chor -> Prop := fun C1 => forall C2, C1 ⭆* C2 -> C1 = C2.

  Lemma NormalFormSend : forall p e q C, NormalForm (CSend p e q C) -> NormalForm C.
  Proof.
    intros p e q C NF. unfold NormalForm; intros C2 steps; induction steps; auto.
    unfold NormalForm in NF.
    assert (CSend p e q C1 = CSend p e q C2) as eq
        by (apply NF; apply NormStepsOne; apply SendContextStep; auto);
      inversion eq; subst; clear eq.
    apply IHsteps. unfold NormalForm; auto.
  Qed.
  
  Lemma NormalFormIf : forall p e C1 C2,
      NormalForm (CIf p e C1 C2) -> NormalForm C1 /\ NormalForm C2.
  Proof.
    intros p e C1 C2 NF; unfold NormalForm; split; intros C3 steps; induction steps; auto.
    - unfold NormalForm in NF.
      assert (CIf p e C1 C2 = CIf p e C0 C2) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply IHsteps; unfold NormalForm; auto.
    - unfold NormalForm in NF.
      assert (CIf p e C1 C0 = CIf p e C1 C2) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply IHsteps; unfold NormalForm; auto.
  Qed.

  Lemma NormalFormDef : forall C1 C2,
      NormalForm (CDef C1 C2) -> NormalForm C1 /\ NormalForm C2.
  Proof.
    intros C1 C2 NF; unfold NormalForm; split; intros C3 steps; induction steps; auto.
    - unfold NormalForm in NF.
      assert (CDef C1 C2 = CDef C0 C2) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply IHsteps; unfold NormalForm; auto.
    - unfold NormalForm in NF.
      assert (CDef C1 C0 = CDef C1 C2) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply IHsteps; unfold NormalForm; auto.
  Qed.
  Hint Resolve NormalFormSend NormalFormIf NormalFormDef : Chor.

  Lemma NormalFormNoStep : forall C, NormalForm C -> forall C', ~ (C ⭆ C').
  Proof.
    intros C NF C' step; induction step; auto with Chor.
    all: try (apply IHstep; unfold NormalForm in *; intros C0 steps; auto with Chor).
    - assert (CSend p e q C1 = CSend p e q C0) as eq by (apply NF; auto with Chor);
        inversion eq; subst; clear eq; reflexivity.
    - assert (CIf p e C11 C2 = CIf p e C0 C2) as eq by (apply NF; auto with Chor);
        inversion eq; subst; clear eq; reflexivity.
    - assert (CIf p e C1 C21 = CIf p e C1 C0) as eq by (apply NF; auto with Chor);
        inversion eq; subst; clear eq; reflexivity.
    - assert (CDef C11 C2 = CDef C0 C2) as eq by (apply NF; auto with Chor);
        inversion eq; subst; clear eq; reflexivity.
    - assert (CDef C1 C21 = CDef C1 C0) as eq by (apply NF; auto with Chor);
        inversion eq; subst; clear eq; reflexivity.
    - unfold NormalForm in NF.
      assert (CSend p e1 q (CSend r e2 s C) = CSend r e2 s (CSend p e1 q C)) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply H2; auto.
    - unfold NormalForm in NF.
      assert (CIf p e1 (CSend q e2 r C1) (CSend q e2 r C2) =
              CSend q e2 r (CIf p e1 C1 C2)) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
    - unfold NormalForm in NF.
      assert (CIf p e1 (CIf q e2 C11 C12) (CIf q e2 C21 C22) =
              CIf q e2 (CIf p e1 C11 C21) (CIf p e1 C12 C22)) as eq
          by (apply NF; auto with Chor); inversion eq; subst; clear eq.
      apply H; auto.
  Qed.

  Lemma NoStepNormalForm : forall C, (forall C', ~ (C ⭆ C')) -> NormalForm C.
  Proof.
    unfold NormalForm; intros C nostep C2 steps; induction steps; auto.
    exfalso; apply (nostep C2); auto.
  Qed.

  Fixpoint InsertSend (p : Prin) (e : Expr) (q : Prin) (C : Chor) : Chor :=
    match C with
    | CDone r e' => CSend p e q (CDone r e')
    | CVar n => CSend p e q (CVar n)
    | CSend r e' s C2 => if PrinOrderDec p r
                        then CSend p e q (CSend r e' s C2)
                        else if PrinEqDec q r
                             then CSend p e q (CSend r e' s C2)
                             else if PrinEqDec q s
                                  then CSend p e q (CSend r e' s C2)
                                  else if PrinEqDec p s
                                       then CSend p e q (CSend r e' s C2)
                                       else CSend r e' s (InsertSend p e q C2)
    | CIf r e' C1 C2 =>
      CSend p e q (CIf r e' C1 C2)
    | CDef C1 C2 => CSend p e q (CDef C1 C2)
    end.

  Lemma InsertSendLeq : forall p e q r e' s C C',
      InsertSend p e q C = CSend r e' s C' -> r ≤p p.
  Proof.
    intros p e q r e' s C; revert r e' s; induction C; simpl; intros r e' s C' eq;
      inversion eq; auto with Chor.
    destruct (PrinOrderDec p p0); inversion H0; auto with Chor.
    destruct (PrinEqDec q p0); inversion H0; auto with Chor.
    destruct (PrinEqDec q p1); inversion H0; auto with Chor.
    destruct (PrinEqDec p p1); inversion H0; auto with Chor.
    subst.
    destruct (PrinOrderTotal r p); auto.
    exfalso; apply n; auto.
  Qed.

  Lemma BoundInsertSend : forall C p e q r e' s t e'' v C',
      NormalForm (CSend p e q C) -> 
      InsertSend r e' s C = CSend t e'' v C' -> p ≤p t \/ p = v \/ q = t \/ q = v \/ t = r.
  Proof.
    intro C; induction C; intros t expr v r e' s w e'' y C' NF eq;
      try (inversion eq; subst; auto with Chor; fail); simpl in eq.
    destruct (PrinOrderDec r p); [inversion eq; subst; eauto with Chor|].
    destruct (PrinEqDec s p); [inversion eq; subst; eauto with Chor|].
    destruct (PrinEqDec s p0); [inversion eq; subst; eauto with Chor|].
    destruct (PrinEqDec r p0); [inversion eq; subst; eauto with Chor|].
    inversion eq; subst.
    destruct (PrinOrderDec t w); [auto with Chor |].
    destruct (PrinEqDec t y);[auto with Chor|].
    destruct (PrinEqDec v w);[auto with Chor|].
    destruct (PrinEqDec v y);[auto with Chor|].
    destruct (PrinEqDec t w);[subst; left; reflexivity|].
    exfalso. eapply NormalFormNoStep in NF. apply NF. eapply SwapSendSendStep; auto.
    destruct (PrinOrderTotal w t); auto. exfalso; apply n3; auto.
  Qed.
  
  Ltac InsertSendNormHelper :=
    match goal with
    | [ H : ?C ⭆* ?C' |- _] =>
      let C'' := fresh "C" in
      remember C as C''; induction H; subst; auto;
      match goal with
      | [H' : C ⭆ ?C'' |- _ ] =>
        inversion H'; subst;
        match goal with
        | [ NF : NormalForm ?C''', H'' : ?C''' ⭆ ?C'''' |- _ ] =>
          exfalso; eapply NormalFormNoStep in NF; eauto with Chor
        | [ H'' : ?a <> ?a |- _ ] =>
          exfalso; apply H''; auto
        end
      end
    end.
  Lemma InsertSendNorm : forall C, NormalForm C -> forall p e q, NormalForm (InsertSend p e q C).
  Proof.
    intro C; induction C; simpl; intros NFC r e' s; unfold NormalForm; intros C' steps.
    - remember (CSend r e' s (CDone p e)) as C. induction steps; auto; subst.
      inversion H; subst. inversion H5; subst.
    - remember (CSend r e' s (CVar n)) as C. induction steps; auto; subst.
      inversion H; subst. inversion H5; subst.
    - specialize (IHC (NormalFormSend _ _ _ _ NFC)).
      destruct (PrinOrderDec r p); [|destruct (PrinEqDec s p);
                                     [|destruct (PrinEqDec s p0);
                                       [|destruct (PrinEqDec r p0)]]];
      auto with Chor; subst.
      all: try InsertSendNormHelper.
      -- remember (CSend r e' s (CSend p e p0 C)) as C''.
         induction steps as [| C1 C2 C3 step steps']; auto; subst.
         inversion step; subst.
         exfalso; apply NormalFormNoStep with (C' := C0) in NFC; auto.
         assert (p = r). apply PrinOrderAntisym; auto.
         exfalso; apply H7; auto.
      -- remember (CSend p e p0 (InsertSend r e' s C)) as C''.
         revert p e p0 r e' s C HeqC'' IHC NFC n n0 n1 n2.
         induction steps; intros p e p0 r e' s C' HeqC'' IHC NFC n n0 n1 n2; auto;
           subst.
         inversion H; subst.
         specialize (IHC r e' s);
           exfalso; eapply NormalFormNoStep in IHC; eauto with Chor.
         symmetry in H3. eapply BoundInsertSend in H3; [|exact NFC].
         repeat (destruct H3 as [H3 | H3];
                 try (match goal with
                      | [H : ~ ?P, H' : ?P |- _] => exfalso; apply H; exact H'
                      end)).
         exfalso; apply H4. apply PrinOrderAntisym; auto.
         subst. exfalso; apply n. auto.
    - remember (CSend r e' s (CIf p e C1 C2)) as C. induction steps; auto; subst.
      inversion H; subst. inversion H5; subst.
      all: try (exfalso; apply NormalFormNoStep in H5; auto; fail).
    - remember (CSend r e' s (CDef C1 C2)) as C. induction steps; auto; subst.
      inversion H; subst. inversion H5; subst.
      all: try (exfalso; apply NormalFormNoStep in H5; auto; fail).
  Qed.      

  Lemma InsertSendSteps : forall p e q C, CSend p e q C ⭆* InsertSend p e q C.
  Proof.
    intros p e q C; revert p e q; induction C; intros r expr s; simpl;
      auto with Chor.
    destruct (PrinOrderDec r p); auto with Chor.
    destruct (PrinEqDec s p); auto with Chor.
    destruct (PrinEqDec s p0); auto with Chor.
    destruct (PrinEqDec r p0); auto with Chor.
    specialize (IHC r expr s).
    destruct (PrinOrderTotal r p); [exfalso; apply n; auto|].
    transitivity (CSend p e p0 (CSend r expr s C)); auto with Chor.
    apply NormStepsOne. apply SwapSendSendStep; auto.
    intro eq; subst; apply n; reflexivity.
  Qed.
  
  Fixpoint InsertIf (p : Prin) (e : Expr) (C1 C2 : Chor) : Chor :=
    match C1 with
    | CDone _ _ => CIf p e C1 C2
    | CVar _ => CIf p e C1 C2
    | CSend q e' r C1' =>
      match C2 with
      | CSend q' e'' r' C2' =>
        if PrinEqDec q q'
        then if PrinEqDec r r'
             then if PrinEqDec p q
                  then CIf p e C1 C2
                  else if PrinEqDec p r
                       then CIf p e C1 C2
                       else if ExprEqDec e' e''
                            then CSend q e' r' (InsertIf p e C1' C2')
                            else CIf p e C1 C2
             else CIf p e C1 C2
        else CIf p e C1 C2
      | _ => CIf p e C1 C2
      end
    | CIf q e' C11 C12 =>
      if PrinOrderDec p q
      then CIf p e C1 C2
      else match C2 with
           | CIf q' e'' C21 C22 =>
             if PrinEqDec q q'
             then if ExprEqDec e' e''
                  then CIf q e' (InsertIf p e C11 C21) (InsertIf p e C12 C22)
                  else CIf p e C1 C2
             else CIf p e C1 C2
           | _ => CIf p e C1 C2
           end
    | CDef _ _ => CIf p e C1 C2
    end.
  Lemma BoundInsertIf1 : forall C1 C2 p e q r e' t e'' v C',
      NormalForm (CSend p e q C1) -> NormalForm (CSend p e q C2) ->
      InsertIf r e' C1 C2 = CSend t e'' v C' -> p ≤p t \/ p = v \/ q = t \/ q = v.
  Proof.
    intro C1; induction C1; simpl; intros C2 s e0 q r e' t e'' v C' H H0 H1.
    all: try (inversion H1; fail).
    - destruct C2; try (inversion H1; fail).
      destruct (PrinEqDec p p1); try (inversion H1; fail).
      destruct (PrinEqDec p0 p2); try (inversion H1; fail).
      destruct (PrinEqDec r p); try (inversion H1; fail).
      destruct (PrinEqDec r p0); try (inversion H1; fail).
      destruct (ExprEqDec e e1); try (inversion H1; fail).
      inversion H1; subst.
      destruct (PrinOrderTotal s t); auto.
      destruct (PrinEqDec s v); auto.
      destruct (PrinEqDec q t); auto.
      destruct (PrinEqDec q v); auto.
      destruct (PrinEqDec s t); subst; auto.
      exfalso. apply (NormalFormNoStep _ H0 (CSend t e'' v (CSend s e0 q C2))); auto.
      apply SwapSendSendStep; auto.
    - destruct (PrinOrderDec r p); try (inversion H1 ;fail).
      destruct C2; try (inversion H1; fail).
      destruct (PrinEqDec p p0); try (inversion H1; fail).
      destruct (ExprEqDec e e1); try (inversion H1; fail).
  Qed. 

  Lemma BoundInsertIf2 : forall {C1 C2 C3 C4 p e q e' r s e'' C5 C6},
      NormalForm (CIf p e C1 C2) ->
      NormalForm (CIf p e C3 C4) ->
      CSend q e' r C5 = InsertIf s e'' C1 C3 ->
      CSend q e' r C6 = InsertIf s e'' C2 C4 ->
      q = p \/ r = p.
  Proof.
    intro C1; induction C1; simpl; intros C2 C3 C4 t e0 q e' r s e'' C5 C6 NF1 NF2 eq1 eq2.
    all: try (inversion eq1; fail).
    - destruct C3; try (inversion eq1; fail).
      destruct (PrinEqDec p p1); try (inversion eq1; fail).
      destruct (PrinEqDec p0 p2); try (inversion eq1; fail).
      destruct (PrinEqDec s p); try (inversion eq1; fail).
      destruct (PrinEqDec s p0); try (inversion eq1; fail).
      destruct (ExprEqDec e e1); try (inversion eq1; fail).
      subst.
      destruct C2; simpl in *; try (inversion eq2; fail).
      -- destruct C4; try (inversion eq2; fail).
         destruct (PrinEqDec p p3); try (inversion eq2; fail).
         destruct (PrinEqDec p0 p4); try (inversion eq2; fail).
         destruct (PrinEqDec s p); try (inversion eq2; fail).
         destruct (PrinEqDec s p0); try (inversion eq2; fail).
         destruct (ExprEqDec e e2); try (inversion eq2; fail).
         subst.
         inversion eq1; inversion eq2; subst.
         destruct (PrinEqDec p3 t); auto.
         destruct (PrinEqDec p4 t); auto.
         exfalso. eapply NormalFormNoStep in NF2; apply NF2.
         apply SwapSendIfStep; auto.
      -- destruct (PrinOrderDec s p); try (inversion eq2; fail).
         destruct C4; try (inversion eq2; fail).
         destruct (PrinEqDec p p0); try (inversion eq2; fail).
         destruct (ExprEqDec e e2); try (inversion eq2; fail).
    - destruct (PrinOrderDec s p); try (inversion eq1; fail).
      destruct C3; try (inversion eq1; fail).
      destruct (PrinEqDec p p0); try (inversion eq1; fail).
      destruct (ExprEqDec e e1); try (inversion eq1; fail).
  Qed.

  Lemma BoundInsertIf3 : forall {C1 C2 C3 C4 p e q e' s e'' C5 C6 C7 C8},
      NormalForm (CIf p e C1 C2) ->
      NormalForm (CIf p e C3 C4) ->
      CIf q e' C5 C6 = InsertIf s e'' C1 C3 ->
      CIf q e' C7 C8 = InsertIf s e'' C2 C4 ->
      p ≤p q \/ s = q.
  Proof.
    intros C1 C2 C3 C4 p e q e' s e'' C5 C6 C7 C8 NF1 NF2 eq1 eq2.
    destruct C1; simpl in *; try (inversion eq1; subst; auto; fail).
    - destruct C3; simpl in *; try (inversion eq1; subst; auto; fail).
      destruct (PrinEqDec p0 p2); try (inversion eq1; subst; auto; fail).
      destruct (PrinEqDec p1 p3); try (inversion eq1; subst; auto; fail).
      destruct (PrinEqDec s p0); try (inversion eq1; subst; auto; fail).
      destruct (PrinEqDec s p1); try (inversion eq1; subst; auto; fail).
      destruct (ExprEqDec e0 e1); try (inversion eq1; subst; auto; fail).
    - destruct (PrinOrderDec s p0); try (inversion eq1; subst; auto; fail).
      destruct C3; simpl in *; try (inversion eq1; subst; auto; fail).
      destruct (PrinEqDec p0 p1); try (inversion eq1; subst; auto; fail).
      destruct (ExprEqDec e0 e1); try (inversion eq1; subst; auto; fail).
      inversion eq1; subst.
      destruct C2; simpl in *; try (inversion eq2; subst; auto; fail).
      -- destruct C4; try (inversion eq2; subst; auto; fail).
         destruct (PrinEqDec p0 p3); try (inversion eq2; subst; auto; fail).
         destruct (PrinEqDec p2 p4); try (inversion eq2; subst; auto; fail).
         destruct (PrinEqDec s p0); try (inversion eq2; subst; auto; fail).
         destruct (PrinEqDec s p2); try (inversion eq2; subst; auto; fail).
         destruct (ExprEqDec e0 e2); try (inversion eq2; subst; auto; fail).
      -- destruct (PrinOrderDec s p0); try (inversion eq2; subst; auto; fail).
         destruct C4; try (inversion eq2; subst; auto; fail).
         destruct (PrinEqDec p0 p2); try (inversion eq2; subst; auto; fail).
         destruct (ExprEqDec e0 e2); try (inversion eq2; subst; auto; fail).
         inversion eq2; subst.
         destruct (PrinOrderDec p p2); auto.
         exfalso. apply NormalFormNoStep with (C' := CIf p2 e2 (CIf p e C1_1 C2_1) (CIf p e C1_2 C2_2)) in NF1. apply NF1.
         apply SwapIfIfStep; auto.
         intro eq; subst; apply n1; reflexivity.
         destruct (PrinOrderTotal p2 p); auto. exfalso; apply n1; auto.
  Qed.
         
         
  Lemma InsertIfNormalize : forall p e C1 C2,
      NormalForm C1 -> NormalForm C2 ->
      NormalForm (InsertIf p e C1 C2).
  Proof.
    intros p e C1; revert p e; induction C1; simpl; intros q expr C2 NFC1 NFC2.
    - unfold NormalForm; intros C0 steps. inversion steps; auto.
      exfalso. inversion H; subst.
      all: apply NormalFormNoStep in H8; auto.
    - unfold NormalForm; intros C0 steps. inversion steps; auto.
      exfalso. inversion H; subst.
      all: apply NormalFormNoStep in H8; auto.
    - revert p e p0 C1 IHC1 NFC1 NFC2; induction C2; intros r expr' t C1 IHC1 NFC1 NFC2;
        simpl.
      all: try (unfold NormalForm; intros C0 steps; inversion steps; auto;
                exfalso; inversion H; subst; apply NormalFormNoStep in H8; auto; fail).
      destruct (PrinEqDec r p);
        [destruct (PrinEqDec t p0);
         [destruct (PrinEqDec q r);
          [| destruct (PrinEqDec q t);
             [| destruct (ExprEqDec expr' e)]]|]|].
      1,2,4,5,6: unfold NormalForm; intros C0 steps; inversion steps; auto;
        inversion H; subst; try (exfalso; apply NormalFormNoStep in H8; auto; fail).
      1,2,4,5,6: try match goal with
                     | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                     end.
      2:{ exfalso; apply n1; reflexivity. }
      subst.
      unfold NormalForm. intros C0 steps; inversion steps; auto.
      inversion H; subst.
      exfalso; apply NormalFormNoStep in H8; auto.
      apply IHC1; [apply NormalFormSend in NFC1 | apply NormalFormSend in NFC2]; auto.
      symmetry in H6; eapply BoundInsertIf1 in H6; eauto.
      repeat (destruct H6 as [H6 | H6]; subst).
      all: try match goal with
               | [H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
               end.
      exfalso; apply H7. apply PrinOrderAntisym; auto.
    - destruct (PrinOrderDec q p).
      unfold NormalForm; intros C0 steps; inversion steps; auto.
      inversion H; subst; try (exfalso; apply NormalFormNoStep in H8; auto; fail).
      exfalso; apply H11; apply PrinOrderAntisym; auto.
      destruct C2.
      all: try (unfold NormalForm; intros C0 steps; inversion steps; auto;
                inversion H; subst; exfalso; apply NormalFormNoStep in H8; auto; fail).
      destruct (PrinEqDec p p0); [destruct (ExprEqDec e e0)|]; subst.
      2,3: unfold NormalForm; intros C0 steps; inversion steps; auto;
        inversion H; subst; try (exfalso; apply NormalFormNoStep in H8; auto; fail).
      2: { exfalso; apply n0; reflexivity. }
      2: { exfalso; apply n0; reflexivity. }
      destruct (NormalFormIf _ _ _ _ NFC1) as [NFC1_1 NFC1_2].
      destruct (NormalFormIf _ _ _ _ NFC2) as [NFC2_1 NFC2_2].
      assert (NormalForm (InsertIf q expr C1_1 C2_1)) by (apply IHC1_1; auto).
      assert (NormalForm (InsertIf q expr C1_2 C2_2)) by (apply IHC1_2; auto).
      unfold NormalForm; intros C0 step. inversion step; auto.
      inversion H1; subst.
      -- exfalso; apply NormalFormNoStep in H10; auto.
      -- exfalso; apply NormalFormNoStep in H10; auto.
      -- destruct (BoundInsertIf2 NFC1 NFC2 H8 H9); subst;
           match goal with
           | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
           end.
      -- destruct (BoundInsertIf3 NFC1 NFC2 H8 H9); subst.
         exfalso; apply H10; apply PrinOrderAntisym; auto.
         exfalso; apply n; auto.
    - unfold NormalForm; intros C0 steps. inversion steps; auto.
      exfalso. inversion H; subst.
      all: apply NormalFormNoStep in H8; auto.
  Qed.      

  Lemma InsertIfSteps : forall p e C1 C2, CIf p e C1 C2 ⭆* InsertIf p e C1 C2.
  Proof.
    intros p e C1; revert p e; induction C1; intros r expr C2; simpl; eauto with Chor.
    - destruct C2; auto with Chor.
      destruct (PrinEqDec p p1); auto with Chor.
      destruct (PrinEqDec p0 p2); auto with Chor.
      destruct (PrinEqDec r p); auto with Chor.
      destruct (PrinEqDec r p0); auto with Chor.
      destruct (ExprEqDec e e0); auto with Chor.
      subst; eauto with Chor.
    - destruct (PrinOrderDec r p); auto with Chor.
      destruct C2; auto with Chor.
      destruct (PrinEqDec p p0); auto with Chor.
      destruct (ExprEqDec e e0); auto with Chor.
      subst. apply @ExtraNormStep with (C2 := CIf p0 e0 (CIf r expr C1_1 C2_1)
                                                 (CIf r expr C1_2 C2_2));
               auto with Chor.
      apply SwapIfIfStep; auto.
      intro H; subst; apply n; reflexivity.
      destruct (PrinOrderTotal p0 r); auto; exfalso; apply n; auto.
  Qed.
    
  Fixpoint Normalize (C : Chor) : Chor :=
    match C with
    | CDone p e => CDone p e
    | CVar n => CVar n
    | CSend p e q C1 => InsertSend p e q (Normalize C1)
    | CIf q e C1 C2 => InsertIf q e (Normalize C1) (Normalize C2)
    | CDef C1 C2 => CDef (Normalize C1) (Normalize C2)
    end.

  Theorem NormalizeSpec : forall C : Chor, NormalForm (Normalize C).
  Proof.
    intro C; induction C; simpl; auto.
    - unfold NormalForm. intros C2 H. inversion H; auto.
      inversion H0.
    - unfold NormalForm. intros C2 H. inversion H; auto. inversion H0.
    - apply InsertSendNorm; auto.
    - apply InsertIfNormalize; auto.
    - unfold NormalForm. intros C0 H.
      inversion H; auto.
      inversion H0; subst.
      all: apply NormalFormNoStep in H7; auto; destruct H7.
  Qed.

  Theorem NormalizeSteps : forall C : Chor, C ⭆* Normalize C.
  Proof.
    intro C; induction C; simpl; auto with Chor.
    - transitivity (CSend p e p0 (Normalize C)); auto with Chor.
      apply InsertSendSteps.
    - transitivity (CIf p e (Normalize C1) (Normalize C2)); auto with Chor.
      apply InsertIfSteps.
  Qed.

  Theorem Equiv'Normalize : forall C1 C2 : Chor, C1 ≡' C2 -> Normalize C1 = Normalize C2.
  Proof.
    intros C1 C2 equiv; induction equiv; simpl; auto.
    all: try (rewrite IHequiv; auto; fail).
    all: try (rewrite IHequiv1; rewrite IHequiv2; auto; fail).
    - rewrite IHequiv. remember (Normalize C2) as C.
      clear C1 C2 equiv HeqC IHequiv.
      induction C; simpl;
      repeat match goal with
             | [|- ?a = ?a ] => reflexivity
             | [H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
             | [n : ?a <> ?b, l1 : ?a ≤p ?b, l2 : ?b ≤p ?a |- _ ] =>
               exfalso; apply n; apply PrinOrderAntisym; auto
             | [n1 : ?a ≰p ?b, n2 : ?b ≰p ?a |- _ ] =>
               exfalso; destruct (PrinOrderTotal a b); auto
             | [ |- context[PrinOrderDec ?a ?b]] => destruct (PrinOrderDec a b); subst
             | [ |- context[PrinEqDec ?a ?b]] => destruct (PrinEqDec a b); subst
             | [ |- context[ExprEqDec ?a ?a]] => destruct (ExprEqDec a b); subst
             end.
  Abort.      
  
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
    - apply InIf2; apply InIf3; apply IHequiv3; exact H8.
    - apply InIf3; apply InIf3; apply IHequiv4; exact H8.
    - apply InIf3; apply InIf2; apply IHequiv3; exact H8.
    - apply InIf3; apply InIf3; apply IHequiv4; exact H8.
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
    | q :: l' => PC.Par (PC.EChoiceL q PC.EndProc) (DoCommsLeft l' P)
    end.

  Fixpoint DoCommsRight (l : list Prin) (P : PC.Proc) : PC.Proc :=
    match l with
    | nil => PC.EChoiceR Env P
    | q :: l' => PC.Par (PC.EChoiceR q PC.EndProc) (DoCommsRight l' P)
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
      match P2 with
      | PC.Par P21 P22 => PC.Par (MergeProcs p P11 P21) (MergeProcs p P12 P22)
      |_ => PC.IChoice p P1 P2
      end
      (* PC.IChoice p P1 P2 *)
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

  Theorem PiCalcInBStep : forall (C1 C2 : Chor) (R : Redex) (B : list Prin),
      RChorStep R B C1 C2 -> forall p l, In p B -> EPP' C1 p l = EPP' C2 p l.
  Proof.
    intros C1 C2 R B step; induction step; simpl;
      intros r l i; try (inversion i; fail).
    - destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H; rewrite <- e; auto|].
      destruct (PrinEqDec r q) as [e |_]; [exfalso; apply H0; rewrite <- e; auto|].
      reflexivity.
    - destruct (PrinEqDec r p). rewrite IHstep; auto. left; auto.
      destruct (PrinEqDec r q). rewrite IHstep; auto. right; left; auto.
      apply IHstep; right; right; auto.
    - destruct (PrinEqDec r p) as [e |_]; [exfalso; apply H; rewrite <- e; auto|].
      destruct (PrinEqDec r q) as [e |_]; [exfalso; apply H0; rewrite <- e; auto|].
      

  
  Theorem PiCalcSimulation : forall (C1 C2 : Chor) (R : Redex) (B : list Prin),
      RChorStep R B C1 C2 -> PiManyStep (FullEPP C1) (FullEPP C2).
  Proof.
    intros C1 C2 R B step; induction step; unfold FullEPP; simpl.
    - unfold EPP; simpl; apply PiOneStep.
      apply CommEStep with (p := p) (q := Env) (e := e1) (e' := e2) (P := EndProc) (CC := Hole);
        auto.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. reflexivity.
      -- intros r nrp. destruct (RoleEqDec p r) as [e |_]; [exfalso; apply nrp; auto|].
         destruct (RoleEqDec r Env); auto.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. reflexivity.
    - apply PiOneStep.
      eapply CommEStep with (p := p) (q := q) (e := e1) (e' := e2) (CC := Hole); auto.
      -- destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         simpl. unfold EPP. simpl.
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
      -- intros r n. destruct (RoleEqDec p r) as [e |_]; [exfalso; apply n; auto|].
         destruct (RoleEqDec q r); auto.
         unfold EPP; simpl.
         destruct (PrinEqDec q p) as [eq |_]; [exfalso; apply H1; auto|].
         destruct (PrinEqDec q q) as [_|neq]; [|exfalso; apply neq; auto].
         reflexivity.
         destruct (InPrinList r (ThreadNames C)) eqn:eq.
         apply InPrinListSpec2 in eq.
         unfold EPP; simpl.
         destruct (PrinEqDec p0 p) as [ e|_];
           [exfalso; apply n; transitivity p0; [apply eq| apply f_equal; exact e]|].
         destruct (PrinEqDec p0 q) as [ e|_];
           [exfalso; apply n0; transitivity p0; [apply f_equal; auto| auto]|].
         reflexivity.
         reflexivity.
      -- unfold EPP; simpl.
         destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         destruct (PrinEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
    -          
         
    

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
      MergeProcs p (DoCommsLeft l P) (DoCommsLeft l Q) ≡π DoCommsLeft l (MergeProcs p P Q).
  Proof.
    intros p l; revert p; induction l; intros p P Q.
    - simpl; destruct (PC.RoleEqDec Env Env) as [_ | neq];
        [reflexivity|exfalso; apply neq; reflexivity].
    - simpl.
  Abort.
  (* Qed. *)


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
    destruct equivQ; auto with PiC.
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
      C1 ≡' C2 -> forall (p : Prin) (l : list Prin), EPP' C1 p l ≡π EPP' C2 p l.
  Proof.
    intros C1 C2 equiv'; induction equiv'; intros t l; unfold EPP; simpl in *; auto with PiC.
    all: try (rewrite IHequiv'1; rewrite IHequiv'2; reflexivity).
    all: repeat match goal with
                | [ H1 : ?a <> ?c, H2 : ?b = ?a, H3 : ?b = ?c |- _ ] =>
                  exfalso; apply H1; transitivity b; [symmetry; exact H2 | exact H3]
                | [ |- context[PrinEqDec ?a ?b] ] =>
                  destruct (PrinEqDec a b); simpl
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity
                end; auto with PiC.
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
    
    
    rewrite MergeCommsLeft. rewrite MergeCommsRight.
    rewrite IHequiv'3. rewrite IHequiv'4. reflexivity.
    rewrite MergeCommsLeft. rewrite MergeCommsRight. rewrite IHequiv'3. rewrite IHequiv'4.
    reflexivity.
    Abort.
      
End Choreography.
