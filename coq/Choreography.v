Require Export Expression.
Require Import Coq.Arith.Arith.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.

Module Choreography (E : Expression).
  Import E.

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
  (* | sswapdefsend1 : forall C1 q e r C2, *)
  (*     q ∉TN C1 -> r ∉TN C1 -> *)
  (*     CDef C1 (CSend q e r C2) ≡ CSend q e r (CDef C1 C2) *)
  (* | sSwapDefSend2 : forall C1 q e r C2, *)
  (*     q ∉TN C1 -> r ∉TN C1 -> *)
  (*     CSend q e r (CDef C1 C2) ≡ CDef C1 (CSend q e r C2) *)
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

  Instance chorEquiv'Refl : Reflexive chorEquiv' := Equiv'Refl.
  Hint Resolve Equiv'Refl : Chor.
  
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
  (* Hint Resolve chorEquivTransitive : Chor. *)

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
  | RSendE : Prin -> Expr -> Expr -> Redex
  | RSendV : Prin -> Expr -> Redex
  | RDef.
  

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
  | DoneEStep : forall (p : Prin) (B : list Prin),
      ~ In p B ->
      forall e1 e2 : Expr, ExprStep e1 e2 -> RChorStep (RDone p e1 e2) B (CDone p e1) (CDone p e2)
  | SendEStep : forall (p q : Prin) (B : list Prin),
      ~ In p B -> ~ In q B ->
      forall (e1 e2 : Expr) (C : Chor),
        ExprStep e1 e2 -> RChorStep (RSendE p e1 e2) B (CSend p e1 q C) (CSend p e2 q C)
  | SendIStep : forall (p q : Prin) (e : Expr) (C1 C2 : Chor) (B : list Prin) (R : Redex),
      RChorStep R (p :: q :: B) C1 C2 ->
      RChorStep R B (CSend p e q C1) (CSend p e q C2)
  | SendVStep : forall (p q : Prin) (v : Expr) (C : Chor) (B : list Prin),
      ~ In p B -> ~ In q B ->
      ExprVal v ->
      RChorStep (RSendV p v) B (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
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
  | CDefStep : forall (C1 C2 : Chor) (B : list Prin),
      RChorStep RDef B (CDef C1 C2) (C2 [c| DefSubst C1; ExprChorIdSubst]).
  Hint Constructors RChorStep : Chor.

  Lemma RStepStrengthening : forall R B1 C1 C2,
      RChorStep R B1 C1 C2 -> forall B2, (forall q, In q B2 -> In q B1) -> RChorStep R B2 C1 C2.
  Proof.
    intros R B1 C1 C2 step; induction step; intros B2 sub; eauto with Chor.
    - apply SendEStep; auto.
    - apply SendIStep; auto. apply IHstep.
      intros q0 i; destruct i as [eq | i];
        [left | right; destruct i as [eq | i]; [left | right]]; auto.
    - apply SendVStep; auto.
    - apply IfIStep; [apply IHstep1 | apply IHstep2]; intros q i.
      all: destruct i; [left | right]; auto.
  Qed.

  Inductive RedexOf : Prin -> Redex -> Prop :=
  | RODone : forall p e1 e2, RedexOf p (RDone p e1 e2)
  | ROIfE : forall p e1 e2, RedexOf p (RIfE p e1 e2)
  | ROIfTT : forall p, RedexOf p (RIfTT p)
  | ROIfFF : forall p, RedexOf p (RIfFF p)
  | ROSendE : forall p e1 e2, RedexOf p (RSendE p e1 e2)
  | ROSendV : forall p v, RedexOf p (RSendV p v).

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
  Qed.

  Corollary NoDoneIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RDone p e1 e2) B C1 C2.
  Proof.
    intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply RODone.
  Qed.
  Corollary NoSendEIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~RChorStep (RSendE p e1 e2) B C1 C2.
  Proof.
    intros p B H e1 e2 C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendE.
  Qed.
  Corollary NoSendVIStepInList : forall p B,
      In p B ->
      forall v C1 C2, ~RChorStep (RSendV p v) B C1 C2.
  Proof.
    intros p B H v C1 C2; apply NoIStepInList with (p := p); auto; apply ROSendV.
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
  
  Hint Resolve RStepStrengthening NoDoneIStepInList : Chor.
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
      eauto with Chor; inversion step; eauto with Chor.
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
    - exists C12; rewrite <- H2; split; auto with Chor.
    - exists C22; rewrite <- H2; split; auto with Chor.
    - exists (C22 [c| DefSubst C12; ExprChorIdSubst]); split; auto with Chor.
      apply EquivStableSubst; auto with Chor.
      intro n; unfold DefSubst; destruct n; auto with Chor.
    - exists (CSend r e2 s (CSend p e3 q C2)); split; auto with Chor.
    - rewrite <- H6 in *; clear R0 H4 B0 H5 p0 H3 e H7 q0 H8 C0 H9 Cstep H6.
      inversion H10.
      -- rewrite H4 in *; rewrite <- H6 in *; rewrite H3 in *; rewrite <- H8 in *.
         clear R H6 B0 H7 p0 H3 e0 H4 q0 H5 C H9 C3 H8.
         exists (CSend r e3 s (CSend p e1 q C2)); split; eauto with Chor.
         apply SendEStep; auto; ListHelper.
      -- destruct (IHequiv _ _ _ H11) as [C4' HC4'];
           destruct HC4' as [stepC4' equivC4'].
         exists (CSend r e2 s (CSend p e1 q C4')); split; auto with Chor.
         apply SendIStep. apply SendIStep.
         eapply RStepStrengthening;
           [exact stepC4'|].
         intros q1 H13.
           destruct H13;
           [ right; right; left
           | destruct H12; [right; right; right; left
                           | destruct H12; [left
                                           | destruct H12; [right; left
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
         rewrite H14; reflexivity.
         rewrite H14. apply SendVStep; auto; ListHelper.
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
        rewrite H13.
        apply SendVStep; auto with Chor.
    - exists (CSend q e2 r (CIf p e3 C1' C2')); split; auto with Chor.
    - clear R0 H3 B0 H4 p0 H1 e H2 C0 H6 C3 H7.
      inversion H8.
      -- rewrite H1 in *; rewrite H2 in *; rewrite <- H7 in *; rewrite <- H4 in *;
           clear B0 H6 p0 H1 e0 H2 q0 H3 C H10 C4 H7 R H4.
         inversion H9. 
         rewrite <- H7 in *;
           clear p0 H1 e0 H2 e4 H3 B0 H6 q0 H4 C H10 C5 H7.
         exists (CSend q e3 r (CIf p e1 C1' C2')); split; auto with Chor.
         apply SendEStep; auto; try ListHelper.
         exfalso. apply NoSendEIStepInList in H14; auto. left; reflexivity.
      -- rewrite <- H4 in *; clear R0 H2 B0 H3 p0 H1 e H6 q0 H7 C0 H10 C4 H4.
         inversion H9.
         1: rewrite <- H4 in H11; rewrite H1 in H11;
           apply NoSendEIStepInList in H11; [destruct H11 | left; reflexivity].
         2: { rewrite <- H4 in H11. rewrite H1 in H11.
              apply NoSendVIStepInList in H11; [destruct H11 | left; reflexivity]. }
         rewrite <- H4 in *; clear R0 H2 B0 H3 p0 H1 e H6 q0 H7 C0 H10 C5 H4.
         destruct (IHequiv1 _ _ _ H11) as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv2 _ _ _ H12) as [C4' HC4']; destruct HC4' as [stepC4' equivC4'].
         exists (CSend q e2 r (CIf p e1 C3' C4')); split; auto with Chor.
         apply SendIStep. apply IfIStep.
         all: apply RStepStrengthening with (B1 := q :: r :: p :: B); auto.
         all: intros q0 i; destruct i as [eq | i];
           [right; right; left
           | destruct i as [eq | i];
             [left
             | destruct i as [eq | i];
               [right; left
               | right; right; right]]]; auto.
      -- rewrite H1 in *; rewrite H2 in *;  rewrite <- H4 in *; rewrite <- H7 in *;
           clear R H3 B0 H4 p0 H1 v H2 q0 H7 C H10 C4 H6.
         inversion H9;
           [apply NoSendVIStepInList in H14; [destruct H14 | left; reflexivity] |].
         rewrite <- H10 in *; clear p0 H1 v H2 B0 H6 q0 H3 C H4 C5 H10.
         exists (CIf p e1 C1' C2' [c| ChorIdSubst; SendSubst r e2]); split; auto with Chor.
         apply SendVStep; auto; try ListHelper.
         simpl. unfold SendSubst at 3.
         destruct (PrinEqDec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq|].
         fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
         apply IfContext; apply EquivStableSubst; auto with Chor.
    - exists (CSend q e2 r C1'); split; auto with Chor.
    - exists (CSend q e2 r C2'); split; auto with Chor.
    - exists (CIf p e1 (CSend q e3 r C1') (CSend q e3 r C2')); split; auto with Chor.
    - clear R0 H2 B0 H3 p0 H1 e H5 q0 H6 C0 H7. inversion H8.
      -- rewrite H1 in *; rewrite H2 in *; clear B0 H5 p0 H1 e0 H2 C0 H7 C4 H9.
         exists (CIf p e3 (CSend q e2 r C1') (CSend q e2 r C2')); split; auto with Chor.
         apply IfEStep; auto; ListHelper.
      -- destruct (IHequiv1 _ _ _ H10) as [C5' H5']; destruct H5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ H11) as [C6' H6']; destruct H6' as [stepC6' equivC6'].
         exists (CIf p e1 (CSend q e2 r C5') (CSend q e2 r C6')); split; auto with Chor.
         apply IfIStep; auto; apply SendIStep;
           apply RStepStrengthening with (B1 := p :: q :: r ::B); auto.
         all: intros t i; destruct i as [eq | i];
           [right; left; apply eq (* t = q *)
           | destruct i as [eq | i];
             [right; right; left; apply eq (* t = r *)
             |destruct i as [eq | i];
              [left; apply eq (* t = p *)
              | right; right; right; exact i]]].
      -- rewrite <- H6 in *; rewrite H1 in *; rewrite <- H5 in *;
           clear B0 H3 p0 H1 e1 H6 C0 H7 C4 H9 C3 H5.
         exists (CSend q e2 r C1'); split; auto with Chor.
         apply IfTrueStep; ListHelper.
      -- rewrite <- H6 in *; rewrite H1 in *; rewrite <- H5 in *;
           clear B0 H3 p0 H1 e1 H6 C0 H7 C4 H9 C3 H5.
         exists (CSend q e2 r C2'); split; auto with Chor.
         apply IfFalseStep; ListHelper.
    - exists (CIf p e1 (C1'[c| ChorIdSubst; SendSubst r e2])
             (C2'[c|ChorIdSubst; SendSubst r e2])); split; auto with Chor.
      simpl; unfold SendSubst at 1.
      destruct (PrinEqDec r p) as [eq | _];
        [exfalso; apply H0; symmetry; exact eq|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec; auto with Chor.
    - exists (CIf q e2 (CIf p e3 C11' C21') (CIf p e3 C12' C22')); split; auto with Chor.
    - clear R0 H2 B0 H3 p0 H0 e H1 C1 H5 C2 H6.
      inversion H7.
      -- rewrite H0 in *; rewrite H1 in *; rewrite <- H2 in *; rewrite <- H5 in *;
           clear B0 H3 p0 H0 e0 H1 C1 H6 C2 H9 C3 H5.
         inversion H8.
         2: { apply NoIfEIStepInList in H13; [destruct H13| left; reflexivity]. }
         rewrite <- H6 in *; clear p0 H0 e0 H1 e4 H5 B0 H3 C1 H9 C2 H12 C4 H6.
         exists (CIf q e3 (CIf p e1 C11' C21') (CIf p e1 C12' C22')); split; auto with Chor.
         apply IfEStep; auto. ListHelper.
      -- rewrite <- H5 in *; clear R0 H2 B0 H3 p0 H0 e H1 C1 H6 C2 H9 C3 H5.
         inversion H8.
         1: {rewrite <- H2 in *; rewrite H0 in *; apply NoIfEIStepInList in H10;
             [destruct H10| left; reflexivity]. }
         2: { rewrite <- H1 in H10; rewrite H0 in H10;
              apply NoIfTTStepInList in H10; [destruct H10 | left; reflexivity]. }
         2: { rewrite <- H1 in H10; rewrite H0 in H10;
              apply NoIfFFStepInList in H10; [destruct H10 | left; reflexivity]. }
         destruct (IHequiv1 _ _ _ H10) as [C0' HC0'];
           destruct HC0' as [stepC0' equivC0'].
         destruct (IHequiv2 _ _ _ H11) as [C5' HC5'];
           destruct HC5' as [stepC5' equivC5'].
         destruct (IHequiv3 _ _ _ H12) as [C3' HC3'];
           destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv4 _ _ _ H13) as [C6' HC6'];
           destruct HC6' as [stepC6' equivC6'].
         exists (CIf q e2 (CIf p e1 C0' C3') (CIf p e1 C5' C6')); split; auto with Chor.
         apply IfIStep; apply IfIStep; eauto with Chor.
         all: apply RStepStrengthening with (B1 := q :: p :: B); auto.
         all: intros t i; destruct i as [eq | i];
           [(* t = p *) right; left; exact eq
                      | destruct i as [eq | i];
                        [ (* t = q *) left; exact eq
                                    | right; right; exact i]].
      -- rewrite <- H1 in *; rewrite H0 in *; rewrite <- H5 in *; rewrite <- H3 in *;
           clear R H1 B0 H2 p0 H0 e2 H5 C1 H6 C2 H9 C3 H3.
         inversion H8;
           [apply NoIfTTStepInList in H11; [destruct H11 | left; reflexivity] |].
         exists (CIf p e1 C11' C21'); split; auto with Chor.
         apply IfTrueStep; ListHelper.
         rewrite <- H3 in *; apply IfContext; apply Equiv'; auto.
      -- rewrite <- H1 in *; rewrite H0 in *; rewrite <- H5 in *; rewrite <- H3 in *;
           clear R H1 B0 H2 p0 H0 e2 H5 C1 H6 C2 H9 C3 H3.
         inversion H8;
           [apply NoIfFFStepInList in H11; [destruct H11 | left; reflexivity] |].
         exists (CIf p e1 C12' C22'); split; auto with Chor.
         apply IfFalseStep; ListHelper.
         rewrite <- H3 in *; apply IfContext; apply Equiv'; auto.
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
      
  (* Reserved Infix "∈TN" (at level 25). *)
  (* Inductive InThreadNames : Prin -> Chor -> Prop := *)
  (*   ItnDone : forall p e, p ∈TN CDone p e *)
  (* | ItnSender : forall p e q C, *)
  (*     p ∈TN CSend p e q C *)
  (* | ItnReceiver : forall p e q C, *)
  (*     q ∈TN CSend p e q C *)
  (* | ItnContinuation : forall p e q C r, *)
  (*     r ∈TN C -> *)
  (*     r ∈TN CSend p e q C *)
  (* | ItnIfDiscriminate : forall p e C1 C2, *)
  (*     p ∈TN CIf p e C1 C2 *)
  (* | ItnIfBranch1 : forall p e C1 C2 q, *)
  (*     q ∈TN C1 -> *)
  (*     q ∈TN CIf p e C1 C2 *)
  (* | ItnIfBranch2 : forall p e C1 C2 q, *)
  (*     q ∈TN C2 -> *)
  (*     q ∈TN CIf p e C1 C2 *)
  (* | ItnDefined : forall p C1 C2, *)
  (*     p ∈TN C1 -> *)
  (*     p ∈TN CDef C1 C2 *)
  (* | ItnBody : forall p C1 C2, *)
  (*     p ∈TN C2 -> *)
  (*     p ∈TN CDef C1 C2 *)
  (* where "p ∈TN C" := (InThreadNames p C). *)
  (* Hint Constructors InThreadNames : Chor. *)

  (* Reserved Infix "∉TN" (at level 29). *)
  (* Inductive NotInThreadNames : Prin -> Chor -> Prop := *)
  (*   NitnDone : forall p q e, *)
  (*     p <> q -> *)
  (*     p ∉TN CDone q e *)
  (* | NitnVar : forall p n, *)
  (*     p ∉TN CVar n *)
  (* | NitnSend : forall p q e r C, *)
  (*     p <> q -> *)
  (*     p <> r -> *)
  (*     p ∉TN C -> *)
  (*     p ∉TN CSend q e r C *)
  (* | NitnIf : forall p q e C1 C2, *)
  (*     p <> q -> *)
  (*     p ∉TN C1 -> *)
  (*     p ∉TN C2 -> *)
  (*     p ∉TN CIf q e C1 C2 *)
  (* | NitnDef : forall p C1 C2, *)
  (*     p ∉TN C1 -> *)
  (*     p ∉TN C2 -> *)
  (*     p ∉TN CDef C1 C2 *)
  (* where "p ∉TN C" := (NotInThreadNames p C). *)
  (* Hint Constructors NotInThreadNames : Chor. *)

  (* Theorem LNotInThreadNames : forall p C, p ∉TN C <-> ~ (p ∈TN C). *)
  (* Proof. *)
  (*   intros p C; split; intro H. *)
  (*   - induction H; intro H'; inversion H'; auto. *)
  (*   - induction C as [q e | n | q e r C | q e C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2]; *)
  (*       auto with Chor. *)
  (*     -- constructor; intro H'; apply H; rewrite H'; auto with Chor. *)
  (*     -- constructor; [ | | apply IHC]; intro H'; apply H; auto with Chor. *)
  (*        all: rewrite H'; auto with Chor. *)
  (*     -- constructor; [ | apply IHC1 | apply IHC2]; intro H'; apply H; auto with Chor. *)
  (*        rewrite H'; auto with Chor. *)
  (*     -- constructor; [apply IHC1 | apply IHC2]; intro H'; apply H; auto with Chor. *)
  (* Qed. *)
  
End Choreography.
