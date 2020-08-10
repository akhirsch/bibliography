Require Export Expression.
Require Export Locations.
(* Require Import PiCalc. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Sorted Orders Coq.Sorting.Mergesort Permutation.
Require Import Program.Tactics.
Require Import Coq.Structures.Orders.

Module Choreography (Import E : Expression) (L : Locations).

  Inductive Chor : Set :=
    CDone : L.t -> Expr -> Chor
  | CVar : nat -> Chor
  | CSend : L.t -> Expr -> L.t -> Chor -> Chor
  | CIf : L.t -> Expr -> Chor -> Chor -> Chor
  | CDef : Chor -> Chor -> Chor.
  Hint Constructors Chor : Chor.
  Ltac ChorInduction C := let p := fresh "p" in
                          let e := fresh "e" in
                          let x := fresh "x" in
                          let q := fresh "q" in
                          let C1 := fresh "C" in
                          let C2 := fresh "C" in
                          let IHC := fresh "IH" C in
                          let IHC1 := fresh "IH" C1 in
                          let IHC2 := fresh "IH" C2 in
                          induction C as [p e| x | p e q C IHC | p e C1 IHC1 C2 IHC2 |C1 IHC1 C2 IHC2].
  Ltac ChorDestruct C := let p := fresh "p" in
                          let e := fresh "e" in
                          let x := fresh "x" in
                          let q := fresh "q" in
                          let C1 := fresh "C" in
                          let C2 := fresh "C" in
                          destruct C as [p e| x | p e q C | p e C1 C2 |C1 C2].

  Inductive ChorVal : Chor -> Prop :=
    VDone : forall (p : L.t) (v : Expr), ExprVal v -> ChorVal (CDone p v).

  Definition ChorUpRename : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S n => S (ξ n)
            end.
  Definition ChorUpExprRename : (L.t -> nat -> nat) -> L.t -> L.t -> nat -> nat :=
    fun ξ p q => if L.eq_dec p q
              then ExprUpRename (ξ q)
              else ξ q.
  
  Fixpoint ChorRename (C : Chor) (ξₖ : nat -> nat) (ξₑ : L.t -> nat -> nat) : Chor :=
    match C with
    | CDone p e => CDone p (e ⟨e| (ξₑ p)⟩)
    | CVar n => CVar (ξₖ n)
    | CSend p e q C => CSend p (e ⟨e| (ξₑ p)⟩) q (ChorRename C ξₖ (ChorUpExprRename ξₑ q))
    | CIf p e C1 C2 => CIf p (e ⟨e| (ξₑ p)⟩) (ChorRename C1 ξₖ ξₑ) (ChorRename C2 ξₖ ξₑ)
    | CDef C1 C2 => CDef (ChorRename C1 (ChorUpRename ξₖ) ξₑ) (ChorRename C2 (ChorUpRename ξₖ) ξₑ)
    end.
  Notation "C ⟨c| x1 ; x2 ⟩" := (ChorRename C x1 x2) (at level 20).

  Definition ChorIdRename : nat -> nat := fun n => n.
  Definition ChorIdExprRename : L.t -> nat -> nat := fun _ n => n.
  
  Lemma ChorUpIdRename : forall n, ChorUpRename ChorIdRename n = ChorIdRename n.
  Proof.
    intros n; destruct n; unfold ChorUpRename; unfold ChorIdRename; reflexivity.
  Qed.

  Lemma ChorUpIdExprRename : forall p q n, ChorUpExprRename ChorIdExprRename p q n
                                    = ChorIdExprRename p n.
  Proof.
    intros p q n; destruct n; unfold ChorUpExprRename; unfold ChorIdExprRename.
    all: destruct (L.eq_dec p q) as [_|neq]; simpl; reflexivity.
  Qed.

  Lemma ChorUpRenameExt : forall (ξ1 ξ2 : nat -> nat),
      (forall n : nat, ξ1 n = ξ2 n) ->
      forall n : nat, ChorUpRename ξ1 n = ChorUpRename ξ2 n.
  Proof.
    intros ξ1 ξ2 eq n; unfold ChorUpRename; destruct n; auto.
  Qed.

  Lemma ChorUpExprRenameExt : forall (ξ1 ξ2 : L.t -> nat -> nat),
      (forall (p : L.t) (n : nat), ξ1 p n = ξ2 p n) ->
      forall (p q : L.t) (n : nat), ChorUpExprRename ξ1 p q n = ChorUpExprRename ξ2 p q n.
  Proof.
    intros ξ1 ξ2 eq p q n. unfold ChorUpExprRename. unfold ExprUpRename.
    destruct (L.eq_dec p q); auto.
    destruct n; auto.
  Qed.

  Lemma ChorRenameExtensional : forall (ξₖ₁ ξₖ₂ : nat -> nat) (ξₑ₁ ξₑ₂ : L.t -> nat -> nat),
      (forall n : nat, ξₖ₁ n = ξₖ₂ n) -> (forall (p : L.t) (n : nat), ξₑ₁ p n = ξₑ₂ p n) ->
      forall (C : Chor), C ⟨c| ξₖ₁; ξₑ₁ ⟩ = C ⟨c| ξₖ₂; ξₑ₂⟩.
  Proof.
    intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2 C; revert ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; ChorInduction C;
      intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; simpl.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
    - rewrite eq1; auto.
    - rewrite IHC with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ChorUpExprRename ξₑ₂ q); auto.
      rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      apply ChorUpExprRenameExt; auto.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      rewrite IHC0 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC1 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
    - rewrite IHC0 with (ξₖ₂ := ChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC1 with (ξₖ₂ := ChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      all: apply ChorUpRenameExt; auto.
  Qed.

  Lemma ChorRenameFusion : forall (C : Chor) (ξc1 ξc2 : nat -> nat) (ξe1 ξe2 : L.t -> nat -> nat),
      (C ⟨c| ξc1; ξe1⟩)⟨c| ξc2; ξe2⟩ = C ⟨c| fun n => ξc2 (ξc1 n); fun p n => ξe2 p (ξe1 p n)⟩.
  Proof.
    intro C; ChorInduction C; intros ξc1 ξc2 ξe1 ξe2; simpl.
    - rewrite ExprRenameFusion; reflexivity.
    - reflexivity.
    - rewrite IHC. unfold ChorUpExprRename. unfold ExprUpRename.
      rewrite ExprRenameFusion.
      erewrite ChorRenameExtensional;[reflexivity | simpl; reflexivity |].
      intros p1 n.
      simpl. destruct (L.eq_dec q p1); auto.
      destruct n; auto.
    - rewrite IHC0; rewrite IHC1; rewrite ExprRenameFusion; auto.
    - rewrite IHC0. rewrite IHC1. unfold ChorUpRename.
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

  Definition ChorUpExprSubst : (L.t -> nat -> Expr) -> L.t -> L.t -> nat -> Expr :=
    fun σ p q n =>
      if L.eq_dec p q then
        match n with
        | 0 => ExprVar 0
        | S n => (σ q n) ⟨e| S ⟩
        end
      else σ q n.
  Definition SendUpChorSubst (σk : nat -> Chor) (p : L.t) : nat -> Chor :=
    fun n => (σk n)⟨c| ChorIdRename; fun q m => if L.eq_dec p q
                                          then S m
                                          else m⟩.

  Fixpoint ChorSubst (C : Chor) (σₖ : nat -> Chor) (σₑ : L.t -> nat -> Expr) : Chor :=
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

  Lemma ChorUpExprSubstExt : forall (σ1 σ2 : L.t -> nat -> Expr),
      (forall (p : L.t) (n : nat), σ1 p n = σ2 p n) ->
      forall (p q : L.t) (n : nat), ChorUpExprSubst σ1 p q n = ChorUpExprSubst σ2 p q n.
  Proof.
    intros σ1 σ2 eq p q n; unfold ChorUpExprSubst; destruct n; auto; repeat (rewrite eq);
      reflexivity.
  Qed.

  Lemma ChorSubstExt : forall (σk1 σk2 : nat -> Chor) (σe1 σe2 : L.t -> nat -> Expr),
      (forall n : nat, σk1 n = σk2 n) ->
      (forall (p : L.t) (n : nat), σe1 p n = σe2 p n) ->
      forall C, C [c| σk1; σe1] = C [c| σk2; σe2].
  Proof.
    intros σk1 σk2 σe1 σe2 eqk eqe C; revert σk1 σk2 σe1 σe2 eqk eqe;
      ChorInduction C; intros σk1 σk2 σe1 σe2 eqk eqe; simpl; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC with (σk2 := SendUpChorSubst σk2 q) (σe2 := ChorUpExprSubst σe2 q); auto.
      intro n; unfold SendUpChorSubst; rewrite eqk; reflexivity.
      apply ChorUpExprSubstExt; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC0 with (σk2 := σk2) (σe2 := σe2); auto.
      rewrite IHC1 with (σk2 := σk2) (σe2 := σe2); auto.
    - rewrite IHC0 with (σk2 := ChorUpSubst σk2) (σe2 := σe2); auto.
      rewrite IHC1 with (σk2 := ChorUpSubst σk2) (σe2 := σe2); auto.
      all: apply ChorUpSubstExt; auto.
  Qed.
  
  Definition ChorIdSubst : nat -> Chor := fun n => CVar n.
  Definition ExprChorIdSubst : L.t -> nat -> Expr := fun _ n => ExprVar n.
  
  Lemma ExprChorIdSubstFibre : forall (p : L.t),
      ExprChorIdSubst p = ExprIdSubst.
  Proof.
    intros p. unfold ExprChorIdSubst. unfold ExprIdSubst. reflexivity.
  Qed.

  Lemma ChorUpIdExprSubst : forall p q n, ExprChorIdSubst p n
                                   = ChorUpExprSubst ExprChorIdSubst q p n.
  Proof.
    intros p q n; unfold ChorUpExprSubst; unfold ExprChorIdSubst;
      destruct (L.eq_dec q p); destruct n; auto; rewrite ExprRenameVar; reflexivity.
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
    intro C; ChorInduction C; unfold ChorIdSubst; simpl.
    all: try (rewrite ExprChorIdSubstFibre).
    all: try (rewrite ExprIdentitySubstSpec).
    all: try auto.
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      -- rewrite IHC; auto.
      -- symmetry; apply ChorUpIdExprSubst. 
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto;
        rewrite IHC0.
      rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto;
        rewrite IHC1.
      reflexivity.
    - rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      rewrite IHC0.
      rewrite ChorSubstExt with (σk2 := ChorIdSubst) (σe2 := ExprChorIdSubst); auto.
      rewrite IHC1; reflexivity.
      all: symmetry; apply ChorUpIdSubst.
  Qed.
      
  Theorem ChorRenameSpec : forall (C : Chor) (ξₖ : nat -> nat) (ξₑ : L.t -> nat -> nat),
      C ⟨c| ξₖ; ξₑ ⟩ = C[c| (fun n => CVar (ξₖ n)); (fun p n => ExprVar (ξₑ p n))].
  Proof.
    intro C; ChorInduction C; intros ξₖ ξₑ; simpl; try reflexivity.
    all: repeat (rewrite ExprRenameSpec).
    all: try (repeat (rewrite IHC)).
    all: try (rewrite IHC0; rewrite IHC1).
    all: try reflexivity.
    - unfold ChorUpExprSubst.
      symmetry.
      rewrite ChorSubstExt with (σk2 := fun n : nat => CVar (ξₖ n)) (σe2 := fun r n => ExprVar (ChorUpExprRename ξₑ q r n)); auto.
      unfold ChorUpExprRename; unfold ExprUpRename.
      intros r n; destruct n; auto; destruct (L.eq_dec q r); auto.
      rewrite ExprRenameVar. reflexivity.
    - rewrite ChorSubstExt with (σk2 := ChorUpSubst (fun n : nat => CVar (ξₖ n)))
                                (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C0); auto.
      rewrite ChorSubstExt with (σk2 := ChorUpSubst (fun n : nat => CVar (ξₖ n)))
                                (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C1); auto.
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
  | SwapSendSend' : forall (p q r s : L.t) (C1 C2 : Chor) (e1 e2 : Expr),
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
  Lemma SendContext : forall (p q : L.t) (e : Expr) (C C' : Chor),
      C ≡ C' ->
      CSend p e q C ≡ CSend p e q C'.
  Proof.
    intros p q e C C' equiv; revert p q e; induction equiv; intros p q e; eauto with Chor.
  Qed.
  Lemma IfContext : forall (p : L.t) (e : Expr) (C1 C1' C2 C2' : Chor),
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

  Lemma SwapSendSend : forall (p q r s : L.t) (C1 C2 : Chor) (e1 e2 : Expr),
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


  Lemma Equiv'StableRename : forall (ξc : nat -> nat) (ξe : L.t -> nat -> nat) (C1 C2 : Chor),
      C1 ≡' C2 -> C1 ⟨c| ξc; ξe ⟩ ≡' C2 ⟨c| ξc; ξe⟩.
  Proof.
    intros ξc ξe C1 C2 equiv; revert ξc ξe; induction equiv; intros ξc ξe;
      simpl; eauto with Chor.
    - unfold ChorUpExprRename at 1.
      destruct (L.eq_dec q r) as [e | _]; [exfalso; apply H0; exact e |].
      unfold ChorUpExprRename at 3.
      destruct (L.eq_dec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e |].
      apply SwapSendSend'; auto.
      rewrite ChorRenameExtensional with (ξₖ₂ := ξc)
                                         (ξₑ₂ := ChorUpExprRename (ChorUpExprRename ξe s) q);
        auto.
      intros t n; unfold ChorUpExprRename.
      destruct (L.eq_dec s t) as [es | ns].
      destruct (L.eq_dec q t) as [eq | nq];
        [exfalso; apply H2; transitivity t; auto|].
      unfold ExprUpRename; destruct n; reflexivity.
      destruct (L.eq_dec q t); auto.
    - unfold ChorUpExprRename at 3.
      destruct (L.eq_dec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply SwapSendIf'; auto.
    - unfold ChorUpExprRename at 1.
      destruct (L.eq_dec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply SwapIfSend'; auto.
  Qed.

  Lemma EquivStableRename : forall (ξc : nat -> nat) (ξe : L.t -> nat -> nat) (C1 C2 : Chor),
      C1 ≡ C2 -> C1 ⟨c| ξc; ξe ⟩ ≡ C2 ⟨c| ξc; ξe⟩.
  Proof.
    intros ξc ξe C1 C2 equiv; induction equiv.
    - apply Equiv'; apply Equiv'StableRename; auto.
    - transitivity (C2 ⟨c| ξc; ξe⟩); auto.
      apply Equiv'; apply Equiv'StableRename; auto.
  Qed.

  Lemma Equiv'StableSubst : forall (σc1 σc2 : nat -> Chor) (σe : L.t -> nat -> Expr) (C1 C2 : Chor),
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
        destruct (L.eq_dec q r) as [e | _]; [exfalso; apply H0; exact e|].
      unfold ChorUpExprSubst at 3;
        destruct (L.eq_dec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e|].
      apply SwapSendSend; auto.
      rewrite ChorSubstExt with (σk2 := SendUpChorSubst (SendUpChorSubst σc1 s) q)
                                (σe2 := ChorUpExprSubst (ChorUpExprSubst σe s) q).
      -- apply IHequiv; intro n;
         unfold SendUpChorSubst; apply EquivStableRename;
           apply EquivStableRename; auto.
      -- intro n; unfold SendUpChorSubst.
         repeat (rewrite ChorRenameFusion). apply ChorRenameExtensional.
         reflexivity.
         intros t m. destruct (L.eq_dec s t).
         destruct (L.eq_dec q t) as [e' | _];
           [exfalso; apply H2; transitivity t; auto| reflexivity].
         reflexivity.
      --intros t n. unfold ChorUpExprSubst.
        destruct (L.eq_dec s t); [| reflexivity].
        destruct (L.eq_dec q t) as [e' | _];
          [exfalso; apply H2; transitivity t; auto | reflexivity].
    - unfold ChorUpExprSubst at 3.
      destruct (L.eq_dec r p) as [e | _];
        [exfalso; apply H0; symmetry; exact e |].
      apply SwapSendIf; auto with Chor; [apply IHequiv1 | apply IHequiv2].
      all: unfold SendUpChorSubst; intro n; apply EquivStableRename; auto.
    - unfold ChorUpExprSubst at 1.
      destruct (L.eq_dec r p) as [e |_]; [exfalso; apply H0; symmetry; exact e |].
      apply SwapIfSend; auto; [apply IHequiv1 | apply IHequiv2]; intro n.
      all: unfold SendUpChorSubst; apply EquivStableRename; auto.
  Qed.
  Hint Resolve Equiv'StableSubst : Chor.
  Lemma EquivStableSubst : forall (σc1 σc2 : nat -> Chor) (σe : L.t -> nat -> Expr) (C1 C2 : Chor),
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
  | RDone : L.t -> Expr -> Expr -> Redex
  | RIfE : L.t -> Expr -> Expr -> Redex
  | RIfTT : L.t -> Redex
  | RIfFF : L.t -> Redex
  | RSendE : L.t -> Expr -> Expr -> L.t -> Redex
  | RSendV : L.t -> Expr -> L.t -> Redex
  | RDef.
  Hint Constructors Redex : Chor.
  

  Definition SendSubst (p : L.t) (v : Expr) : L.t -> nat -> Expr :=
    fun q n =>
      if L.eq_dec p q
      then match n with
           | 0 => v
           | S m => ExprVar m
           end
      else ExprVar n.

  Lemma UpSendSubst : forall (p q : L.t) (v : Expr),
      p <> q ->
      forall r n, ChorUpExprSubst (SendSubst p v) q r n = SendSubst p v r n.
  Proof.
    intros p q v H r n.
    unfold ChorUpExprSubst; unfold SendSubst.
    destruct (L.eq_dec q r);
      destruct (L.eq_dec p r); auto.
    exfalso; apply H; transitivity r; auto.
    destruct n; auto. rewrite ExprRenameVar; auto.
  Qed.
  
  Definition DefSubst (C1 : Chor) : nat -> Chor :=
    fun n => match n with
          | 0 => CDef C1 C1
          | S m => CVar m
          end.

  Inductive RChorStep : Redex -> list L.t -> Chor -> Chor -> Prop :=
  | DoneEStep : forall (p : L.t) (e1 e2 : Expr),
      ExprStep e1 e2 -> RChorStep (RDone p e1 e2) nil (CDone p e1) (CDone p e2)
  | SendEStep : forall (p q : L.t) (B : list L.t),
      ~ In p B -> ~ In q B -> p <> q ->
      forall (e1 e2 : Expr) (C : Chor),
        ExprStep e1 e2 -> RChorStep (RSendE p e1 e2 q) B (CSend p e1 q C) (CSend p e2 q C)
  | SendIStep : forall (p q : L.t) (e : Expr) (C1 C2 : Chor) (B : list L.t) (R : Redex),
      RChorStep R (p :: q :: B) C1 C2 ->
      RChorStep R B (CSend p e q C1) (CSend p e q C2)
  | SendVStep : forall (p q : L.t) (v : Expr) (C : Chor) (B : list L.t),
      ~ In p B -> ~ In q B -> p <> q ->
      ExprVal v ->
      RChorStep (RSendV p v q) B (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
  | IfEStep : forall (p : L.t) (e1 e2 : Expr) (C1 C2 : Chor) (B : list L.t),
      ~ In p B ->
      ExprStep e1 e2 ->
      RChorStep (RIfE p e1 e2) B (CIf p e1 C1 C2) (CIf p e2 C1 C2)
  | IfIStep : forall (p : L.t) (e : Expr) (C1 C2 C3 C4 : Chor) (B : list L.t) (R : Redex),
      RChorStep R (p :: B) C1 C3 ->
      RChorStep R (p :: B) C2 C4 ->
      RChorStep R B (CIf p e C1 C2) (CIf p e C3 C4)
  | IfTrueStep : forall (p : L.t) (C1 C2 : Chor) (B : list L.t),
      ~ In p B ->
      RChorStep (RIfTT p) B (CIf p tt C1 C2) C1
  | IfFalseStep : forall (p : L.t) (C1 C2 : Chor) (B : list L.t),
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
    - assert (B2 = nil) by
        (destruct B2 as [| p0 B2]; auto;
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
        by (destruct B2 as [|p B2]; auto;
            assert (In p nil) as H0
                by (apply ext; left; reflexivity);
            inversion H0).
      rewrite H. apply DefStep.
  Qed.

  Inductive RedexOf : L.t -> Redex -> Prop :=
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

  Inductive ChorStepMany : list L.t -> Chor -> Chor -> Prop :=
  | ChorManyZero : forall B C, ChorStepMany B C C
  | ChorManyPlus : forall R B C1 C2 C3, RChorStep R B C1 C2 -> ChorStepMany B C2 C3 -> ChorStepMany B C1 C3.
  Hint Constructors ChorStepMany : Chor.

  Theorem ChorManyOne : forall (R : Redex) (B : list L.t) (C1 C2 : Chor),
      RChorStep R B C1 C2 -> ChorStepMany B C1 C2.
  Proof.
    intros R B C1 C2 step.
    eapply ChorManyPlus; [exact step | apply ChorManyZero].
  Qed.
  Hint Resolve ChorManyOne : Chor.

  Program Fixpoint ChorStepManyTrans (B : list L.t) (C1 C2 C3 : Chor)
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
    | [H : ~ In ?p (?p :: _) |- _ ] =>
      exfalso; apply H; left; reflexivity
    | [H : ~ In ?p (_ :: ?p :: _) |- _ ] =>
      exfalso; apply H; right; left; reflexivity
    | [H : ~ In ?r (?p :: ?q :: ?B) |- ~ In ?r ?B] =>
      let H' := fresh in intro H'; apply H; right; right; exact H'
    | [H : ~ In ?r (?p :: ?B) |- ~ In ?r ?B ] =>
      let H' := fresh in intro H'; apply H; right; exact H'
    | [H : ~ In ?r (?p :: _) |- ?r <> ?p ] =>
      let H' := fresh H in intro H'; apply H; left; auto
    | [H : ~ In ?r (?p :: _) |- ?p <> ?r ] =>
      let H' := fresh H in intro H'; apply H; left; auto
    | [H : ~ In ?r (_ :: ?p :: _) |- ?p <> ?r ] =>
      let H' := fresh H in intro H'; apply H; right; left; auto                                                      
    | [H : ~ In ?r (_ :: ?p :: _) |- ?r <> ?p ] =>
      let H' := fresh H in intro H'; apply H; right; left; auto                                                      
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
         simpl; unfold SendSubst at 2; destruct (L.eq_dec s p) as [eq | _];
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
        unfold SendSubst at 1; destruct (L.eq_dec q r) as [eq | _];
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
         destruct (L.eq_dec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq|].
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
      destruct (L.eq_dec r p) as [eq | _];
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
  | StdDoneEStep : forall (p : L.t) (e1 e2 : Expr),
      ExprStep e1 e2
      -> StdChorStep (CDone p e1) (CDone p e2)
  | StdSendEStep : forall (p q : L.t) (e1 e2 : Expr) (C : Chor),
      ExprStep e1 e2
      -> p <> q
      -> StdChorStep (CSend p e1 q C) (CSend p e2 q C)
  | StdSendVStep : forall (p q : L.t) (v : Expr) (C : Chor),
      ExprVal v
      -> p <> q
      -> StdChorStep (CSend p v q C) (C [c| ChorIdSubst; SendSubst q v])
  | StdIfEStep : forall (p : L.t) (e1 e2 : Expr) (C1 C2 : Chor),
      ExprStep e1 e2
      -> StdChorStep (CIf p e1 C1 C2) (CIf p e2 C1 C2)
  | StdIfTrueStep : forall (p : L.t) (C1 C2 : Chor),
      StdChorStep (CIf p tt C1 C2) C1
  | StdIfFalseStep : forall (p : L.t) (C1 C2 : Chor),
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

  Lemma RStepOnTop : forall (R : Redex) (B : list L.t) (C1 C2 : Chor),
      RChorStep R B C1 C2 ->
      exists C1' C2', C1 ≡ C1' /\ C2 ≡ C2' /\ RChorStep R B C1' C2' /\ RedexOnTop R C1'.
  Proof.
    intros R B C1 C2 step; induction step.
    all: try(eexists; eexists; split; [|split; [|split]]; eauto with Chor StdChor; fail).
    - destruct IHstep as [C1' H]; destruct H as [C2' H]; destruct H as [equiv1 H];
        destruct H as [equiv2 H]; destruct H as [step' ontop].
      destruct R; inversion ontop; subst.
      all: inversion step'; subst; try (rename t into r); try (rename t0 into s).
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
      -- exists (CIf r e0 (CSend p e q C0) (CSend p e q C3)).
         exists (CIf r e1 (CSend p e q C0) (CSend p e q C3)).
         split; [|split;[|split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CIf r e0 C0 C3)); auto with Chor.
             apply SwapIfSend; auto with Chor; ListHelper. 
         --- transitivity (CSend p e q (CIf r e1 C0 C3)); auto with Chor.
             apply SwapIfSend; auto with Chor; ListHelper.
         --- constructor; auto; ListHelper.
      -- exists (CIf r tt (CSend p e q C2') (CSend p e q C3));
           exists (CSend p e q C2');
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CIf r tt C2' C3)); auto with Chor. apply SwapIfSend; auto with Chor; ListHelper. 
         --- apply IfTrueStep; ListHelper. 
      -- exists (CIf r ff (CSend p e q C0) (CSend p e q C2'));
           exists (CSend p e q C2');
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CIf r ff C0 C2')); auto with Chor.
             apply SwapIfSend; auto with Chor; ListHelper. 
         --- apply IfFalseStep; ListHelper. 
      -- exists (CSend r e0 s (CSend p e q C));
           exists (CSend r e1 s (CSend p e q C));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CSend r e0 s C)); auto with Chor.
             apply SwapSendSend; auto with Chor; ListHelper.
         --- transitivity (CSend p e q (CSend r e1 s C)); auto with Chor.
              apply SwapSendSend; auto with Chor; ListHelper.
         --- apply SendEStep; auto; ListHelper.
      -- exists (CSend r e0 s (CSend p e q C));
           exists (CSend p e q C [c| ChorIdSubst; SendSubst s e0]);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CSend p e q (CSend r e0 s C)); auto with Chor.
             apply SwapSendSend; auto with Chor; ListHelper.
         ---  simpl. unfold SendSubst at 1.
             destruct (L.eq_dec s p) as [eq | _]; [subst; ListHelper|].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
             assert (C [c|ChorIdSubst; SendSubst s e0]
                     = C [c|SendUpChorSubst ChorIdSubst q;
                            ChorUpExprSubst (SendSubst s e0) q]) as H
             by (apply ChorSubstExt;
                 [intro n; symmetry; apply SendUpChorIdSubst
                 |intros p5 n; symmetry; apply UpSendSubst; ListHelper]).
             rewrite <- H; auto with Chor.
         --- apply SendVStep; auto with Chor; ListHelper.
    - destruct IHstep1 as [C1' H]; destruct H as [C3' H]; destruct H as [equiv1 H];
        destruct H as [equiv3 H]; destruct H as [step13 ontop1].
      destruct IHstep2 as [C2' H]; destruct H as [C4' H]; destruct H as [equiv2 H];
        destruct H as [equiv4 H]; destruct H as [step24 ontop2].
      destruct R; inversion ontop1; inversion ontop2; subst; inversion step13; subst; inversion step24; subst.
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
      all: try (rename t into r); try (rename t0 into s).
      -- exists (CIf r e0 (CIf p e C0 C6) (CIf p e C5 C7));
           exists (CIf r e1 (CIf p e C0 C6) (CIf p e C5 C7));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e (CIf r e0 C0 C5) (CIf r e0 C6 C7)); auto with Chor.
             apply SwapIfIf; auto with Chor; ListHelper.
         --- transitivity (CIf p e (CIf r e1 C0 C5) (CIf r e1 C6 C7)); auto with Chor.
             apply SwapIfIf; auto with Chor; ListHelper.
         --- apply IfEStep; auto with Chor; ListHelper.
      -- exists (CIf r tt (CIf p e C3' C4') (CIf p e C5 C7));
           exists (CIf p e C3' C4');
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e (CIf r tt C3' C5) (CIf r tt C4' C7)); auto with Chor; apply SwapIfIf; auto with Chor; ListHelper.
         --- apply IfTrueStep; ListHelper. 
      -- exists (CIf r ff (CIf p e C0 C6) (CIf p e C3' C4'));
           exists (CIf p e C3' C4');
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e (CIf r ff C0 C3') (CIf r ff C6 C4')); auto with Chor; apply SwapIfIf; auto with Chor; ListHelper.
         --- apply IfFalseStep; ListHelper. 
      -- exists (CSend r e0 s (CIf p e C C0));
           exists (CSend r e1 s (CIf p e C C0));
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e (CSend r e0 s C) (CSend r e0 s C0)); auto with Chor.
             apply SwapSendIf; auto with Chor; ListHelper.
         --- transitivity (CIf p e (CSend r e1 s C) (CSend r e1 s C0)); auto with Chor.
             apply SwapSendIf; auto with Chor; ListHelper.
         --- apply SendEStep; auto; ListHelper.
      -- exists (CSend r e0 s (CIf p e C C0));
           exists (CIf p e C C0 [c|ChorIdSubst; SendSubst s e0]);
           split; [| split; [| split]]; auto with Chor StdChor.
         --- transitivity (CIf p e (CSend r e0 s C) (CSend r e0 s C0)); auto with Chor.
             apply SwapSendIf; auto with Chor; ListHelper.
         --- transitivity (CIf p e (C [c|ChorIdSubst; SendSubst s e0]) (C0 [c|ChorIdSubst; SendSubst s e0])); auto with Chor.
             simpl. unfold SendSubst at 3.
             destruct (L.eq_dec s p) as [eq | _]; 
               [subst; ListHelper |].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec. reflexivity.
         --- apply SendVStep; auto; ListHelper.
  Qed.

  Lemma RStepOnTopToStd : forall (C1 C2 : Chor) (R : Redex) (B : list L.t),
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
  Theorem RStepToStd : forall (C1 C2 : Chor) (R : Redex) (B : list L.t),
      RChorStep R B C1 C2 -> StdChorStep C1 C2.
  Proof.
    intros C1 C2 R B rstep.
    apply RStepOnTop in rstep;
      destruct rstep as [C1' H]; destruct H as [C2' H];
      destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [rstep ontop].
    apply StdEquivStep with (C1' := C1') (C2' := C2'); auto.
    apply RStepOnTopToStd with (R := R) (B := B); auto.
  Qed.
  
  Fixpoint ThreadNames (C : Chor) : list L.t :=
    match C with
    | CDone p _ => p :: nil
    | CVar _ => nil
    | CSend p _ q C' => p :: q :: (ThreadNames C')
    | CIf p _ C1 C2 => p :: (ThreadNames C1) ++ (ThreadNames C2)
    | CDef C1 C2 => (ThreadNames C1) ++ (ThreadNames C2)
    end.

  Reserved Infix "∈TN" (at level 20).
  Inductive InThreadNames : L.t -> Chor -> Prop :=
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
    intros p C; revert p; ChorInduction C; intro r; split; intro i; simpl in *.
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
    all: try (constructor; rewrite IHC0; auto; fail).
    all: try (constructor; rewrite IHC1; auto; fail).
    - right; rewrite <- IHC; auto.
    - apply in_or_app; left; rewrite <- IHC0; exact H1.
    - apply in_or_app; right; rewrite <- IHC1; exact H1.
    - apply in_or_app; left; rewrite <- IHC0; exact H1.
    - apply in_or_app; right; rewrite <- IHC1; exact H1.
  Qed.             

  Lemma ThreadNamesInvariant' : forall C1 C2 : Chor,
      C1 ≡' C2 -> forall p : L.t, p ∈TN C1 <-> p ∈TN C2.
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
      C1 ≡ C2 -> forall p : L.t, p ∈TN C1 <-> p ∈TN C2.
  Proof.
    intros C1 C2 equiv; induction equiv.
    - intro p; apply ThreadNamesInvariant'; auto.
    - intro p. apply ThreadNamesInvariant' with (p := p) in H. rewrite H.
      apply IHequiv.
  Qed.
      
End Choreography.
