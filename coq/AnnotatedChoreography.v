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

(*
  An intermediate language between 
*)

Module AnnotatedChoreography (Import E : Expression) (L : Locations).

  Definition Loc : Set := L.t.
  
  Inductive AnnChor : Set :=
    ADone : Loc -> Expr -> AnnChor
  | AVar : nat -> AnnChor
  | ASend : Loc -> Expr -> Loc -> AnnChor -> AnnChor
  | AIf : nat -> Loc -> Expr -> AnnChor -> AnnChor -> AnnChor
  | ASyncL : Loc -> Loc -> AnnChor -> AnnChor (* Annotated SYNChronize, not Asynchronous! *)
  | ASyncR : Loc -> Loc -> AnnChor -> AnnChor
  | ADef : AnnChor -> AnnChor -> AnnChor.
  Hint Constructors AnnChor : AChor.

  Ltac AChorInduction C := let p := fresh "p" in
                          let e := fresh "e" in
                          let x := fresh "x" in
                          let q := fresh "q" in
                          let C1 := fresh "C1" in
                          let C2 := fresh "C2" in
                          let IHC := fresh "IH" C in
                          let IHC1 := fresh "IH" C1 in
                          let IHC2 := fresh "IH" C2 in
                          let n := fresh "n" in
                          induction C as [p e| x | p e q C IHC | n p e C1 IHC1 C2 IHC2 | p q C IHC | p q C IHC |C1 IHC1 C2 IHC2].
  Ltac ChorDestruct C := let p := fresh "p" in
                          let e := fresh "e" in
                          let x := fresh "x" in
                          let q := fresh "q" in
                          let C1 := fresh "C1" in
                          let C2 := fresh "C2" in
                          destruct C as [p e| x | p e q C | p e C1 C2 |p q C |p q C|C1 C2].
    Definition AChorUpRename : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S n => S (ξ n)
            end.
  Definition AChorUpExprRename : (Loc -> nat -> nat) -> Loc -> Loc -> nat -> nat :=
    fun ξ p q => if L.eq_dec p q
              then ExprUpRename (ξ q)
              else ξ q.

  Fixpoint AChorRename (C : AnnChor) (ξₖ : nat -> nat) (ξₑ : Loc -> nat -> nat) : AnnChor :=
    match C with
    | ADone p e => ADone p (e ⟨e| (ξₑ p)⟩)
    | AVar n => AVar (ξₖ n)
    | ASend p e q C => ASend p (e ⟨e| (ξₑ p)⟩) q (AChorRename C ξₖ (AChorUpExprRename ξₑ q))
    | AIf n p e C1 C2 => AIf n p (e ⟨e| (ξₑ p)⟩) (AChorRename C1 ξₖ ξₑ) (AChorRename C2 ξₖ ξₑ)
    | ASyncL p q C1 => ASyncL p q (AChorRename C1 ξₖ ξₑ)
    | ASyncR p q C1 => ASyncR p q (AChorRename C1 ξₖ ξₑ)
    | ADef C1 C2 => ADef (AChorRename C1 (AChorUpRename ξₖ) ξₑ) (AChorRename C2 (AChorUpRename ξₖ) ξₑ)
    end.
  Notation "C ⟨ac| x1 ; x2 ⟩" := (AChorRename C x1 x2) (at level 20).

  Definition AChorIdRename : nat -> nat := fun n => n.
  Definition AChorIdExprRename : Loc -> nat -> nat := fun _ n => n.
  
  Lemma AChorUpIdRename : forall n, AChorUpRename AChorIdRename n = AChorIdRename n.
  Proof using.
    intros n; destruct n; unfold AChorUpRename; unfold AChorIdRename; reflexivity.
  Qed.

  Lemma AChorUpIdExprRename : forall p q n, AChorUpExprRename AChorIdExprRename p q n
                                    = AChorIdExprRename p n.
  Proof using.
    intros p q n; destruct n; unfold AChorUpExprRename; unfold AChorIdExprRename.
    all: destruct (L.eq_dec p q) as [_|neq]; simpl; reflexivity.
  Qed.

  Lemma AChorUpRenameExt : forall (ξ1 ξ2 : nat -> nat),
      (forall n : nat, ξ1 n = ξ2 n) ->
      forall n : nat, AChorUpRename ξ1 n = AChorUpRename ξ2 n.
  Proof using.
    intros ξ1 ξ2 eq n; unfold AChorUpRename; destruct n; auto.
  Qed.

  Lemma AChorUpExprRenameExt : forall (ξ1 ξ2 : Loc -> nat -> nat),
      (forall (p : Loc) (n : nat), ξ1 p n = ξ2 p n) ->
      forall (p q : Loc) (n : nat), AChorUpExprRename ξ1 p q n = AChorUpExprRename ξ2 p q n.
  Proof using.
    intros ξ1 ξ2 eq p q n. unfold AChorUpExprRename. unfold ExprUpRename.
    destruct (L.eq_dec p q); auto.
    destruct n; auto.
  Qed.

  Lemma AChorRenameExtensional : forall (ξₖ₁ ξₖ₂ : nat -> nat) (ξₑ₁ ξₑ₂ : Loc -> nat -> nat),
      (forall n : nat, ξₖ₁ n = ξₖ₂ n) -> (forall (p : Loc) (n : nat), ξₑ₁ p n = ξₑ₂ p n) ->
      forall (C : AnnChor), C ⟨ac| ξₖ₁; ξₑ₁ ⟩ = C ⟨ac| ξₖ₂; ξₑ₂⟩.
  Proof using.
    intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2 C; revert ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; AChorInduction C;
      intros ξₖ₁ ξₖ₂ ξₑ₁ ξₑ₂ eq1 eq2; simpl.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
    - rewrite eq1; auto.
    - rewrite IHC with (ξₖ₂ := ξₖ₂) (ξₑ₂ := AChorUpExprRename ξₑ₂ q); auto.
      rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      apply AChorUpExprRenameExt; auto.
    - rewrite ExprRenameExt with (ξ2 := ξₑ₂ p); auto.
      rewrite IHC1 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC2 with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
    - rewrite IHC with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
    - rewrite IHC with (ξₖ₂ := ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
    - rewrite IHC1 with (ξₖ₂ := AChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      rewrite IHC2 with (ξₖ₂ := AChorUpRename ξₖ₂) (ξₑ₂ := ξₑ₂); auto.
      all: apply AChorUpRenameExt; auto.
  Qed.

  Lemma AChorRenameFusion : forall (C : AnnChor) (ξc1 ξc2 : nat -> nat) (ξe1 ξe2 : Loc -> nat -> nat),
      (C ⟨ac| ξc1; ξe1⟩)⟨ac| ξc2; ξe2⟩ = C ⟨ac| fun n => ξc2 (ξc1 n); fun p n => ξe2 p (ξe1 p n)⟩.
  Proof using.
    intro C; AChorInduction C; intros ξc1 ξc2 ξe1 ξe2; simpl.
    - rewrite ExprRenameFusion; reflexivity.
    - reflexivity.
    - rewrite IHC. unfold AChorUpExprRename. unfold ExprUpRename.
      rewrite ExprRenameFusion.
      erewrite AChorRenameExtensional;[reflexivity | simpl; reflexivity |].
      intros p1 n.
      simpl. destruct (L.eq_dec q p1); auto.
      destruct n; auto.
    - rewrite IHC1; rewrite IHC2; rewrite ExprRenameFusion; auto.
    - rewrite IHC; auto.
    - rewrite IHC; auto.
    - rewrite IHC1. rewrite IHC2. unfold AChorUpRename.
      rewrite AChorRenameExtensional with (ξₖ₂ := fun n => match n with
                                                      | 0 => 0
                                                      | S n0 => S (ξc2 (ξc1 n0))
                                                      end)
                                         (ξₑ₂ := fun p n => ξe2 p (ξe1 p n)).
      rewrite AChorRenameExtensional with (ξₖ₂ := fun n => match n with
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
      
  Definition AChorUpSubst : (nat -> AnnChor) -> nat -> AnnChor :=
    fun σ n =>
      match n with
      | 0 => AVar 0
      | S n => (σ n) ⟨ac| S ; fun _ => ExprIdRenaming⟩
      end.
  Definition AChorUpExprSubst : (Loc -> nat -> Expr) -> Loc -> Loc -> nat -> Expr :=
    fun σ p q n =>
      if L.eq_dec p q then
        match n with
        | 0 => ExprVar 0
        | S n => (σ q n) ⟨e| S ⟩
        end
      else σ q n.
  Definition SendUpAChorSubst (σk : nat -> AnnChor) (p : Loc) : nat -> AnnChor :=
    fun n => (σk n)⟨ac| AChorIdRename; fun q m => if L.eq_dec p q
                                            then S m
                                            else m⟩.

  Fixpoint AChorSubst (C : AnnChor) (σₖ : nat -> AnnChor) (σₑ : Loc -> nat -> Expr) : AnnChor :=
    match C with
    | ADone p e => ADone p (e [e| (σₑ p)])
    | AVar n => σₖ n
    | ASend p e q C => ASend p (e [e| (σₑ p)]) q (AChorSubst C (SendUpAChorSubst σₖ q) (AChorUpExprSubst σₑ q))
    | AIf n p e C1 C2 => AIf n p (e [e| (σₑ p)]) (AChorSubst C1 σₖ σₑ) (AChorSubst C2 σₖ σₑ)
    | ASyncL p q C => ASyncL p q (AChorSubst C σₖ σₑ)
    | ASyncR p q C => ASyncR p q (AChorSubst C σₖ σₑ)
    | ADef C1 C2 => ADef (AChorSubst C1 (AChorUpSubst σₖ) σₑ) (AChorSubst C2 (AChorUpSubst σₖ) σₑ)
    end.
  Notation "C [ac| s1 ; s2 ]" := (AChorSubst C s1 s2) (at level 20).

    Lemma AChorUpSubstExt : forall (σ1 σ2 : nat -> AnnChor),
      (forall n : nat, σ1 n = σ2 n) ->
      forall n : nat, AChorUpSubst σ1 n = AChorUpSubst σ2 n.
  Proof using.
    intros σ1 σ2 eq n; unfold AChorUpSubst.
    destruct n; auto; rewrite eq; reflexivity.
  Qed.

  Lemma AChorUpExprSubstExt : forall (σ1 σ2 : Loc -> nat -> Expr),
      (forall (p : Loc) (n : nat), σ1 p n = σ2 p n) ->
      forall (p q : Loc) (n : nat), AChorUpExprSubst σ1 p q n = AChorUpExprSubst σ2 p q n.
  Proof using.
    intros σ1 σ2 eq p q n; unfold AChorUpExprSubst; destruct n; auto; repeat (rewrite eq);
      reflexivity.
  Qed.

  Lemma AChorSubstExt : forall (σk1 σk2 : nat -> AnnChor) (σe1 σe2 : Loc -> nat -> Expr),
      (forall n : nat, σk1 n = σk2 n) ->
      (forall (p : Loc) (n : nat), σe1 p n = σe2 p n) ->
      forall C, C [ac| σk1; σe1] = C [ac| σk2; σe2].
  Proof using.
    intros σk1 σk2 σe1 σe2 eqk eqe C; revert σk1 σk2 σe1 σe2 eqk eqe;
      AChorInduction C; intros σk1 σk2 σe1 σe2 eqk eqe; simpl; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC with (σk2 := SendUpAChorSubst σk2 q) (σe2 := AChorUpExprSubst σe2 q); auto.
      intro n; unfold SendUpAChorSubst; rewrite eqk; reflexivity.
      apply AChorUpExprSubstExt; auto.
    - rewrite ExprSubstExt with (σ2 := σe2 p); auto.
      rewrite IHC1 with (σk2 := σk2) (σe2 := σe2); auto.
      rewrite IHC2 with (σk2 := σk2) (σe2 := σe2); auto.
    - erewrite IHC; eauto.
    - erewrite IHC; eauto.
    - rewrite IHC1 with (σk2 := AChorUpSubst σk2) (σe2 := σe2); auto.
      rewrite IHC2 with (σk2 := AChorUpSubst σk2) (σe2 := σe2); auto.
      all: apply AChorUpSubstExt; auto.
  Qed.
  
  Definition AChorIdSubst : nat -> AnnChor := fun n => AVar n.
  Definition ExprAChorIdSubst : Loc -> nat -> Expr := fun _ n => ExprVar n.
  
  Lemma ExprAChorIdSubstFibre : forall (p : Loc),
      ExprAChorIdSubst p = ExprIdSubst.
  Proof using.
    intros p. unfold ExprAChorIdSubst. unfold ExprIdSubst. reflexivity.
  Qed.

  Lemma AChorUpIdExprSubst : forall p q n, ExprAChorIdSubst p n
                                   = AChorUpExprSubst ExprAChorIdSubst q p n.
  Proof using.
    intros p q n; unfold AChorUpExprSubst; unfold ExprAChorIdSubst;
      destruct (L.eq_dec q p); destruct n; auto; rewrite ExprRenameVar; reflexivity.
  Qed.
  
  Lemma AChorUpIdSubst : forall n, AChorIdSubst n = AChorUpSubst AChorIdSubst n.
  Proof using.
    unfold AChorUpSubst; unfold AChorIdSubst; destruct n;
      [|unfold ExprIdRenaming; simpl]; reflexivity.
  Qed.

  Lemma SendUpAChorIdSubst : forall p n, SendUpAChorSubst AChorIdSubst p n = AChorIdSubst n.
  Proof using.
    intros p n. unfold AChorIdSubst; unfold SendUpAChorSubst.
    simpl. unfold AChorIdRename. auto.
  Qed.

  Lemma AChorSubstIdSpec : forall (C : AnnChor), C [ac| AChorIdSubst; ExprAChorIdSubst] = C.
  Proof using.
    intro C; AChorInduction C; unfold AChorIdSubst; simpl.
    all: try (rewrite ExprAChorIdSubstFibre).
    all: try (rewrite ExprIdentitySubstSpec).
    all: try auto.
    - rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto.
      -- rewrite IHC; auto.
      -- symmetry; apply AChorUpIdExprSubst. 
    - rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto;
        rewrite IHC1.
      rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto;
        rewrite IHC2.
      reflexivity.
    - rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto;
        rewrite IHC; reflexivity.
    - rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto;
        rewrite IHC; reflexivity.
    - rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto.
      rewrite IHC1.
      rewrite AChorSubstExt with (σk2 := AChorIdSubst) (σe2 := ExprAChorIdSubst); auto.
      rewrite IHC2; reflexivity.
      all: symmetry; apply AChorUpIdSubst.
  Qed.
      
  Theorem AChorRenameSpec : forall (C : AnnChor) (ξₖ : nat -> nat) (ξₑ : Loc -> nat -> nat),
      C ⟨ac| ξₖ; ξₑ ⟩ = C[ac| (fun n => AVar (ξₖ n)); (fun p n => ExprVar (ξₑ p n))].
  Proof using.
    intro C; AChorInduction C; intros ξₖ ξₑ; simpl; try reflexivity.
    all: repeat (rewrite ExprRenameSpec).
    all: try (repeat (rewrite IHC)).
    all: try (rewrite IHC0; rewrite IHC1).
    all: try reflexivity.
    - unfold AChorUpExprSubst.
      symmetry.
      rewrite AChorSubstExt with (σk2 := fun n : nat => AVar (ξₖ n)) (σe2 := fun r n => ExprVar (AChorUpExprRename ξₑ q r n)); auto.
      unfold AChorUpExprRename; unfold ExprUpRename.
      intros r n; destruct n; auto; destruct (L.eq_dec q r); auto.
      rewrite ExprRenameVar. reflexivity.
    - rewrite <- IHC1. rewrite <- IHC2. reflexivity.
    - rewrite IHC1; rewrite IHC2.
      rewrite AChorSubstExt with (σk2 := AChorUpSubst (fun n : nat => AVar (ξₖ n)))
                                (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C1); auto.
      rewrite AChorSubstExt with (σk2 := AChorUpSubst (fun n : nat => AVar (ξₖ n)))
                                 (σe2 := fun p n => ExprVar (ξₑ p n)) (C := C2); auto.
      all: unfold AChorUpSubst; unfold AChorUpRename; destruct n; cbn; reflexivity.
  Qed.
  
  Reserved Notation " C1 ≡a' C2" (at level 30).
  Inductive AchorEquiv' : AnnChor -> AnnChor -> Prop :=
    ADoneRefl : forall p e, ADone p e ≡a' ADone p e
  | AVarRefl : forall n, AVar n ≡a' AVar n
  | ASendContext' : forall p e q C1 C2,
      C1 ≡a' C2 ->
      ASend p e q C1 ≡a' ASend p e q C2
  | AIfContext' : forall n p e C11 C12 C21 C22,
      C11 ≡a' C12 -> C21 ≡a' C22 -> AIf n p e C11 C21 ≡a' AIf n p e C12 C22
  | ASyncLContext' : forall p q C1 C2,
      C1 ≡a' C2 ->
      ASyncL p q C1 ≡a' ASyncL p q C2
  | ASyncRContext' : forall p q C1 C2,
      C1 ≡a' C2 ->
      ASyncR p q C1 ≡a' ASyncR p q C2
  | ADefContext' : forall C11 C12 C21 C22,
      C11 ≡a' C12 ->
      C21 ≡a' C22 ->
      ADef C11 C21 ≡a' ADef C12 C22
  | ASwapSendSend' : forall (p q r s : Loc) (C1 C2 : AnnChor) (e1 e2 : Expr),
      (* if the two sends share any principals, swapping them would change things from
         one principal's point-of-view *)          
      p <> r -> q <> r -> p <> s -> q <> s ->
      C1 ≡a' C2 ->
      ASend p e1 q (ASend r e2 s C1) ≡a' ASend r e2 s (ASend p e1 q C2)
  | ASwapSendIf' : forall n p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡a' C1' -> C2 ≡a' C2' ->
      AIf n p e1 (ASend q e2 r C1) (ASend q e2 r C2) ≡a' ASend q e2 r (AIf n p e1 C1' C2')
  | ASwapIfSend' : forall n p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡a' C1' -> C2 ≡a' C2' ->
      ASend q e2 r (AIf n p e1 C1 C2) ≡a' AIf n p e1 (ASend q e2 r C1') (ASend q e2 r C2')
  | ASwapSendSyncL' : forall p q r e s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASend p e q (ASyncL r s C) ≡a' ASyncL r s (ASend p e q C')
  | ASwapSyncLSend' : forall p q r e s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncL p q (ASend r e s C) ≡a' ASend r e s (ASyncL p q C')
  | ASwapSendSyncR' : forall p q r e s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASend p e q (ASyncR r s C) ≡a' ASyncR r s (ASend p e q C')
  | ASwapSyncRSend' : forall p q r e s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncR p q (ASend r e s C) ≡a' ASend r e s (ASyncR p q C')
  | ASwapIfIf' : forall p m e1 n q e2 C11 C11' C12 C12' C21 C21' C22 C22',
      p <> q ->
      C11 ≡a' C11' -> C12 ≡a' C12' -> C21 ≡a' C21' -> C22 ≡a' C22' ->
      AIf m p e1 (AIf n q e2 C11 C12) (AIf n q e2 C21 C22) ≡a'
          AIf n q e2 (AIf m p e1 C11' C21') (AIf m p e1 C12' C22')
  | ASwapIfSyncL' : forall p m e q r C1 C1' C2 C2',
      p <> q -> p <> r -> C1 ≡a' C1' -> C2 ≡a' C2' ->
      AIf m p e (ASyncL q r C1) (ASyncL q r C2) ≡a' ASyncL q r (AIf m p e C1' C2')
  | ASwapSyncLIf' : forall p q r m e C1 C1' C2 C2',
      p <> r -> q <> r -> C1 ≡a' C1' -> C2 ≡a' C2' ->
      ASyncL p q (AIf m r e C1 C2) ≡a' AIf m r e (ASyncL p q C1') (ASyncL p q C2')
  | ASwapIfSyncR' : forall p m e q r C1 C1' C2 C2',
      p <> q -> p <> r -> C1 ≡a' C1' -> C2 ≡a' C2' ->
      AIf m p e (ASyncR q r C1) (ASyncR q r C2) ≡a' ASyncR q r (AIf m p e C1' C2')
  | ASwapSyncRIf' : forall p q r m e C1 C1' C2 C2',
      p <> r -> q <> r -> C1 ≡a' C1' -> C2 ≡a' C2' ->
      ASyncR p q (AIf m r e C1 C2) ≡a' AIf m r e (ASyncR p q C1') (ASyncR p q C2')
  | ASwapSyncLSyncL' : forall p q r s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncL p q (ASyncL r s C) ≡a' ASyncL r s (ASyncL p q C')
  | ASwapSyncLSyncR' : forall p q r s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncL p q (ASyncR r s C) ≡a' ASyncR r s (ASyncL p q C')
  | ASwapSyncRSyncL' : forall p q r s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncR p q (ASyncL r s C) ≡a' ASyncL r s (ASyncR p q C')
  | ASwapSyncRSyncR' : forall p q r s C C',
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a' C' ->
      ASyncR p q (ASyncR r s C) ≡a' ASyncR r s (ASyncR p q C')
  where "C1 ≡a' C2" := (AchorEquiv' C1 C2).
  Hint Constructors AchorEquiv' : AChor.

  Fixpoint AEquiv'Refl (C : AnnChor) : C ≡a' C :=
    match C with
    | ADone p e =>
      ADoneRefl p e
    | AVar n =>
      AVarRefl n
    | ASend p e q C =>
      ASendContext' p e q C C (AEquiv'Refl C)
    | AIf n p e C1 C2 =>
      AIfContext' n p e C1 C1 C2 C2 (AEquiv'Refl C1) (AEquiv'Refl C2)
    | ASyncL p q C =>
      ASyncLContext' p q C C (AEquiv'Refl C)
    | ASyncR p q C =>
      ASyncRContext' p q C C (AEquiv'Refl C)
    | ADef C1 C2 =>
      ADefContext' C1 C1 C2 C2 (AEquiv'Refl C1) (AEquiv'Refl C2)
    end.
  Hint Resolve AEquiv'Refl : AChor.
  Instance AchorEquiv'Refl : Reflexive AchorEquiv' := AEquiv'Refl.
  
  Theorem AEquiv'Sym : forall (C1 C2 : AnnChor), C1 ≡a' C2 -> C2 ≡a' C1.
  Proof using.
    intros C1 C2 equiv; induction equiv; eauto with AChor.
  Qed.
  Hint Resolve AEquiv'Sym : AChor.

  Instance AchorEquiv'Sym : Symmetric AchorEquiv' := AEquiv'Sym.

  Reserved Infix "≡a" (at level 30).
  Inductive AchorEquiv : AnnChor -> AnnChor -> Prop :=
    AEquiv' : forall C1 C2, C1 ≡a' C2 -> C1 ≡a C2
  | ATransEquiv : forall C1 C2 C3, C1 ≡a' C2 -> C2 ≡a C3 -> C1 ≡a C3
  where "C1 ≡a C2" := (AchorEquiv C1 C2).
  Hint Constructors AchorEquiv : AChor.

  Instance AchorEquivRefl : Reflexive AchorEquiv.
  Proof using.
    unfold Reflexive; intro C; apply AEquiv'; reflexivity.
  Defined.
  Hint Resolve AchorEquivRefl : AChor.

  Lemma AchorEquivTransitive : forall C1 C2 C3 : AnnChor, C1 ≡a C2 -> C2 ≡a C3 -> C1 ≡a C3.
  Proof using.
    intros C1 C2 C3 equiv; revert C3; induction equiv; intros C3' equiv'.
    - eapply ATransEquiv; eauto.
    - specialize (IHequiv C3' equiv'). eapply ATransEquiv; eauto.
  Qed.
  Instance AchorEquivTrans : Transitive AchorEquiv := AchorEquivTransitive.

  Instance AchorEquivSym : Symmetric AchorEquiv.
  Proof using.
    unfold Symmetric; intros C1 C2 equiv; induction equiv; auto with AChor.
    - transitivity C2; auto with AChor.
  Qed.
  Hint Resolve AchorEquivSym : AChor.

  (* Smart constructors for ≡a *)
  Lemma ASendContext : forall (p q : Loc) (e : Expr) (C C' : AnnChor),
      C ≡a C' ->
      ASend p e q C ≡a ASend p e q C'.
  Proof using.
    intros p q e C C' equiv; revert p q e; induction equiv; intros p q e; eauto with AChor.
  Qed.
  Lemma AIfContext : forall (n : nat) (p : Loc) (e : Expr) (C1 C1' C2 C2' : AnnChor),
      C1 ≡a C1' -> C2 ≡a C2' ->
      AIf n p e C1 C2 ≡a AIf n p e C1' C2'.
  Proof using.
    intros n p e C1 C1' C2 C2' equiv; revert n p e C2 C2'; induction equiv;
      intros n p e C2' C2'' equiv'; revert n p e; induction equiv'; intros n p e;
        eauto with AChor.
  Qed.
  Lemma ASyncLContext : forall (p q : Loc) (C C' : AnnChor),
      C ≡a C' ->
      ASyncL p q C ≡a ASyncL p q C'.
  Proof using.
    intros p q C C' equiv; revert p q; induction equiv; intros p q; eauto with AChor.
  Qed.
  Lemma ASyncRContext : forall (p q : Loc) (C C' : AnnChor),
      C ≡a C' ->
      ASyncR p q C ≡a ASyncR p q C'.
  Proof using.
    intros p q C C' equiv; revert p q; induction equiv; intros p q; eauto with AChor.
  Qed.
  Lemma ADefContext : forall (C1 C1' C2 C2' : AnnChor),
      C1 ≡a C1' -> C2 ≡a C2' ->
      ADef C1 C2 ≡a ADef C1' C2'.
  Proof using.
    intros C1 C1' C2 C2' equiv; revert C2 C2'; induction equiv;
      intros C4 C4' equiv'; induction equiv'; eauto with AChor.
  Qed.

  Lemma ASwapSendSend : forall (p q r s : Loc) (C1 C2 : AnnChor) (e1 e2 : Expr),
      p <> r -> q <> r -> p <> s -> q <> s ->
      C1 ≡a C2 ->
      ASend p e1 q (ASend r e2 s C1) ≡a ASend r e2 s (ASend p e1 q C2).
  Proof using.
    intros p q r s C1 C2 e1 e2 neq1 neq2 neq3 neq4 equiv;
      revert p q r s e1 e2 neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e1 e2 neq1 neq2 neq3 neq4;
      auto with AChor.
    transitivity (ASend p e1 q (ASend r e2 s C2)); auto with AChor.
  Qed.

  Lemma ASwapIfSend : forall n p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡a C1' -> C2 ≡a C2' ->
      ASend q e2 r (AIf n p e1 C1 C2) ≡a AIf n p e1 (ASend q e2 r C1') (ASend q e2 r C2').
  Proof using.
    intros n p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1;
      revert p e1 q e2 r C2 C2' neq1 neq2;
      induction equiv1;
      intros p e1 q e2 r C0 C0' neq1 neq2 equiv2;
      revert p e1 q e2 r neq1 neq2;
      induction equiv2;
      intros p e1 q e2 r neq1 neq2;
      eauto with AChor.
  Qed.

  Lemma ASwapSendIf : forall n p e1 q e2 r C1 C1' C2 C2',
      p <> q -> p <> r ->
      C1 ≡a C1' -> C2 ≡a C2' ->
      AIf n p e1 (ASend q e2 r C1) (ASend q e2 r C2) ≡a ASend q e2 r (AIf n p e1 C1' C2').
  Proof using.
    intros n p e1 q e2 r C1 C1' C2 C2' neq1 neq2 equiv1;
      revert n p e1 q e2 r C2 C2' neq1 neq2;
      induction equiv1;
      intros n p e1 q e2 r C0 C0' neq1 neq2 equiv2;
      revert n p e1 q e2 r neq1 neq2;
      induction equiv2;
      intros n p e1 q e2 r neq1 neq2;
      eauto with AChor.
    transitivity (AIf n p e1 (ASend q e2 r C2) (ASend q e2 r C4));
      eauto with AChor.
  Qed.

  Lemma ASwapSendSyncL : forall (p q r s : Loc) (e : Expr) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASend p e q (ASyncL r s C) ≡a ASyncL r s (ASend p e q C').
  Proof using.
    intros p q r s e C C' neq1 neq2 neq3 neq4 equiv;
      revert p q r s e neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e neq1 neq2 neq3 neq4;
      eauto with AChor.
  Qed.
  Lemma ASwapSyncLSend : forall (p q r s : Loc) (e : Expr) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncL p q (ASend r e s C) ≡a ASend r e s (ASyncL p q C').
  Proof using.
    intros p q r s e C C' neq1 neq2 neq3 neq4 equiv;
      revert p q r s e neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e neq1 neq2 neq3 neq4;
      eauto with AChor.
  Qed.

  Lemma ASwapSendSyncR : forall (p q r s : Loc) (e : Expr) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASend p e q (ASyncR r s C) ≡a ASyncR r s (ASend p e q C').
  Proof using.
    intros p q r s e C C' neq1 neq2 neq3 neq4 equiv;
      revert p q r s e neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e neq1 neq2 neq3 neq4;
      eauto with AChor.
  Qed.
  Lemma ASwapSyncRSend : forall (p q r s : Loc) (e : Expr) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncR p q (ASend r e s C) ≡a ASend r e s (ASyncR p q C').
  Proof using.
    intros p q r s e C C' neq1 neq2 neq3 neq4 equiv;
      revert p q r s e neq1 neq2 neq3 neq4;
      induction equiv;
      intros p q r s e neq1 neq2 neq3 neq4;
      eauto with AChor.
  Qed.

  Lemma ASwapIfIf : forall n p e1 m q e2 C11 C11' C12 C12' C21 C21' C22 C22',
      p <> q ->
      C11 ≡a C11' -> C12 ≡a C12' -> C21 ≡a C21' -> C22 ≡a C22' ->
      AIf n p e1 (AIf m q e2 C11 C12) (AIf m q e2 C21 C22) ≡a
          AIf m q e2 (AIf n p e1 C11' C21') (AIf n p e1 C12' C22').
  Proof using.
    intros n p e1 m q e2 C11 C11' C12 C12' C21 C21' C22 C22' neq equiv1;
      revert n p e1 m q e2 C12 C12' C21 C21' C22 C22' neq;
      induction equiv1; eauto with AChor.
      intros n p e1 m q e2 C12 C12' C21 C21' C22 C22' neq equiv2;
      revert n p e1 m q e2 C21 C21' C22 C22' neq;
      induction equiv2; eauto with AChor.
      intros n p e1 m q e2 C21 C21' C22 C22' neq equiv3;
      revert n p e1 m q e2 C22 C22' neq;
      induction equiv3; eauto with AChor.
      intros n p e1 m q e2 C22 C22' neq equiv4;
      revert n p e1 m q e2 neq; 
      induction equiv4;
      intros p e1 q e2 neq;
      eauto with AChor.
  Qed.

  Lemma ASwapIfSyncL : forall (m : nat) (p q r : Loc) (e : Expr) (C1 C1' C2 C2' : AnnChor),
      p <> q -> p <> r -> C1 ≡a C1' -> C2 ≡a C2' ->
      AIf m p e (ASyncL q r C1) (ASyncL q r C2) ≡a ASyncL q r (AIf m p e C1' C2').
  Proof using.
    intros m p q r e C1 C1' C2 C2' neq1 neq2 equiv1;
      revert m p q r e C2 C2' neq1 neq2;
      induction equiv1;
      eauto with AChor.
    intros m p q r e C3 C3' neq1 neq2 equiv2;
      revert m p q r e neq1 neq2; induction equiv2; eauto with AChor.
  Qed.

  Lemma ASwapSyncLIf : forall (p q r : Loc) (n : nat) (e : Expr) (C1 C1' C2 C2' : AnnChor),
      p <> r -> q <> r -> C1 ≡a C1' -> C2 ≡a C2' ->
      ASyncL p q (AIf n r e C1 C2) ≡a AIf n r e (ASyncL p q C1') (ASyncL p q C2').
  Proof using.
    intros m p q r e C1 C1' C2 C2' neq1 neq2 equiv1;
      revert m p q r e C2 C2' neq1 neq2;
      induction equiv1;
      eauto with AChor.
    intros m p q r e C3 C3' neq1 neq2 equiv2;
      revert m p q r e neq1 neq2; induction equiv2; eauto with AChor.
  Qed.
  Lemma ASwapIfSyncR : forall (p q r : Loc) (n : nat) (e : Expr) (C1 C1' C2 C2' : AnnChor),
      p <> q -> p <> r -> C1 ≡a C1' -> C2 ≡a C2' ->
      AIf n p e (ASyncR q r C1) (ASyncR q r C2) ≡a ASyncR q r (AIf n p e C1' C2').
  Proof using.
    intros m p q r e C1 C1' C2 C2' neq1 neq2 equiv1;
      revert m p q r e C2 C2' neq1 neq2;
      induction equiv1;
      eauto with AChor.
    intros m p q r e C3 C3' neq1 neq2 equiv2;
      revert m p q r e neq1 neq2; induction equiv2; eauto with AChor.
  Qed.

  Lemma ASwapSyncRIf : forall (p q r : Loc) (n : nat) (e : Expr) (C1 C1' C2 C2' : AnnChor),
      p <> r -> q <> r -> C1 ≡a C1' -> C2 ≡a C2' ->
      ASyncR p q (AIf n r e C1 C2) ≡a AIf n r e (ASyncR p q C1') (ASyncR p q C2').
  Proof using.
    intros m p q r e C1 C1' C2 C2' neq1 neq2 equiv1;
      revert m p q r e C2 C2' neq1 neq2;
      induction equiv1;
      eauto with AChor.
    intros m p q r e C3 C3' neq1 neq2 equiv2;
      revert m p q r e neq1 neq2; induction equiv2; eauto with AChor.
  Qed.
    
  Lemma ASwapSyncLSyncL : forall (p q r s : Loc) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncL p q (ASyncL r s C) ≡a ASyncL r s (ASyncL p q C').
  Proof using.
    intros p q r s C1 C1' neq1 neq2 neq3 neq4 equiv;
      revert p q r s neq1 neq2 neq3 neq4;
      induction equiv;
      eauto with AChor.
  Qed.
  Lemma ASwapSyncLSyncR : forall (p q r s : Loc) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncL p q (ASyncR r s C) ≡a ASyncR r s (ASyncL p q C').
  Proof using.
    intros p q r s C1 C1' neq1 neq2 neq3 neq4 equiv;
      revert p q r s neq1 neq2 neq3 neq4;
      induction equiv;
      eauto with AChor.
  Qed.
  Lemma ASwapSyncRSyncL : forall (p q r s : Loc) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncR p q (ASyncL r s C) ≡a ASyncL r s (ASyncR p q C').
  Proof using.
    intros p q r s C1 C1' neq1 neq2 neq3 neq4 equiv;
      revert p q r s neq1 neq2 neq3 neq4;
      induction equiv;
      eauto with AChor.
  Qed.

  Lemma ASwapSyncRSyncR : forall (p q r s : Loc) (C C' : AnnChor),
      p <> r -> p <> s -> q <> r -> q <> s -> C ≡a C' ->
      ASyncR p q (ASyncR r s C) ≡a ASyncR r s (ASyncR p q C').
  Proof using.
    intros p q r s C1 C1' neq1 neq2 neq3 neq4 equiv;
      revert p q r s neq1 neq2 neq3 neq4;
      induction equiv;
      eauto with AChor.
  Qed.
  Hint Resolve ASendContext AIfContext ADefContext ASwapSendSend ASwapSendIf ASwapIfSend ASwapIfIf ASyncLContext
       ASyncRContext ASwapSendSyncL ASwapSyncLSend ASwapSendSyncR ASwapSyncRSend ASwapIfSyncL ASwapSyncLIf
       ASwapIfSyncR ASwapSyncRIf ASwapSyncLSyncL ASwapSyncLSyncR  ASwapSyncRSyncL ASwapSyncRSyncR : AChor.


  Lemma AEquiv'StableRename : forall (ξc : nat -> nat) (ξe : Loc -> nat -> nat) (C1 C2 : AnnChor),
      C1 ≡a' C2 -> C1 ⟨ac| ξc; ξe ⟩ ≡a' C2 ⟨ac| ξc; ξe⟩.
  Proof using.
    intros ξc ξe C1 C2 equiv; revert ξc ξe; induction equiv; intros ξc ξe;
      simpl; eauto with AChor.
    - unfold AChorUpExprRename at 1.
      destruct (L.eq_dec q r) as [e | _]; [exfalso; apply H0; exact e |].
      unfold AChorUpExprRename at 3.
      destruct (L.eq_dec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e |].
      apply ASwapSendSend'; auto.
      rewrite AChorRenameExtensional with (ξₖ₂ := ξc)
                                         (ξₑ₂ := AChorUpExprRename (AChorUpExprRename ξe s) q);
        auto.
      intros t n; unfold AChorUpExprRename.
      destruct (L.eq_dec s t) as [es | ns].
      destruct (L.eq_dec q t) as [eq | nq];
        [exfalso; apply H2; transitivity t; auto|].
      unfold ExprUpRename; destruct n; reflexivity.
      destruct (L.eq_dec q t); auto.
    - unfold AChorUpExprRename at 3.
      destruct (L.eq_dec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply ASwapSendIf'; auto.
    - unfold AChorUpExprRename at 1.
      destruct (L.eq_dec r p) as [e | _]; [exfalso; apply H0; symmetry; exact e|].
      apply ASwapIfSend'; auto.
  Qed.

  Lemma AEquivStableRename : forall (ξc : nat -> nat) (ξe : Loc -> nat -> nat) (C1 C2 : AnnChor),
      C1 ≡a C2 -> C1 ⟨ac| ξc; ξe ⟩ ≡a C2 ⟨ac| ξc; ξe⟩.
  Proof using.
    intros ξc ξe C1 C2 equiv; induction equiv.
    - apply AEquiv'; apply AEquiv'StableRename; auto.
    - transitivity (C2 ⟨ac| ξc; ξe⟩); auto.
      apply AEquiv'; apply AEquiv'StableRename; auto.
  Qed.

  Lemma AEquiv'StableSubst : forall (σc1 σc2 : nat -> AnnChor) (σe : Loc -> nat -> Expr) (C1 C2 : AnnChor),
      (forall n : nat, σc1 n ≡a σc2 n) ->
      C1 ≡a' C2 ->
      C1 [ac| σc1; σe] ≡a C2 [ac| σc2; σe].
  Proof using.
    intros σc1 σc2 σe C1 C2 equivσ equiv; revert σc1 σc2 σe equivσ; induction equiv;
      intros σc1 σc2 σe equivσ; simpl; try (auto with AChor; fail).
    - assert (forall n, SendUpAChorSubst σc1 q n ≡a SendUpAChorSubst σc2 q n) as equivSendUpσ
        by (unfold SendUpAChorSubst; intro n; apply AEquivStableRename; auto).
      specialize (IHequiv (SendUpAChorSubst σc1 q) (SendUpAChorSubst σc2 q)
                          (AChorUpExprSubst σe q) equivSendUpσ).
      inversion IHequiv; auto with AChor.
    - apply ADefContext.
      apply IHequiv1; intro n; unfold AChorUpSubst; destruct n; 
        [reflexivity | apply AEquivStableRename; auto].
      apply IHequiv2; intro n; unfold AChorUpSubst; destruct n;
        [reflexivity | apply AEquivStableRename; auto].
    - unfold AChorUpExprSubst at 1;
        destruct (L.eq_dec q r) as [e | _]; [exfalso; apply H0; exact e|].
      unfold AChorUpExprSubst at 3;
        destruct (L.eq_dec s p) as [e | _]; [exfalso; apply H1; symmetry; exact e|].
      apply ASwapSendSend; auto.
      rewrite AChorSubstExt with (σk2 := SendUpAChorSubst (SendUpAChorSubst σc1 s) q)
                                 (σe2 := AChorUpExprSubst (AChorUpExprSubst σe s) q).
      -- apply IHequiv; intro n;
         unfold SendUpAChorSubst; apply AEquivStableRename;
           apply AEquivStableRename; auto.
      -- intro n; unfold SendUpAChorSubst.
         repeat (rewrite AChorRenameFusion). apply AChorRenameExtensional.
         reflexivity.
         intros t m. destruct (L.eq_dec s t).
         destruct (L.eq_dec q t) as [e' | _];
           [exfalso; apply H2; transitivity t; auto| reflexivity].
         reflexivity.
      --intros t n. unfold AChorUpExprSubst.
        destruct (L.eq_dec s t); [| reflexivity].
        destruct (L.eq_dec q t) as [e' | _];
          [exfalso; apply H2; transitivity t; auto | reflexivity].
    - unfold AChorUpExprSubst at 3.
      destruct (L.eq_dec r p) as [e | _];
        [exfalso; apply H0; symmetry; exact e |].
      apply ASwapSendIf; auto with AChor; [apply IHequiv1 | apply IHequiv2].
      all: unfold SendUpAChorSubst; intro m; apply AEquivStableRename; auto.
    - unfold AChorUpExprSubst at 1.
      destruct (L.eq_dec r p) as [e |_]; [exfalso; apply H0; symmetry; exact e |].
      apply ASwapIfSend; auto; [apply IHequiv1 | apply IHequiv2]; intro m.
      all: unfold SendUpAChorSubst; apply AEquivStableRename; auto.
    - apply ASwapSendSyncL; auto; apply IHequiv; intro n; unfold SendUpAChorSubst;
      apply AEquivStableRename; auto.
    - apply ASwapSyncLSend; auto; apply IHequiv; intro n; unfold SendUpAChorSubst;
      apply AEquivStableRename; auto.
    - apply ASwapSendSyncR; auto; apply IHequiv; intro n; unfold SendUpAChorSubst;
      apply AEquivStableRename; auto.
    - apply ASwapSyncRSend; auto; apply IHequiv; intro n; unfold SendUpAChorSubst;
      apply AEquivStableRename; auto.
  Qed.
  Hint Resolve AEquiv'StableSubst : AChor.
  Lemma AEquivStableSubst : forall (σc1 σc2 : nat -> AnnChor) (σe : Loc -> nat -> Expr) (C1 C2 : AnnChor),
      (forall n : nat, σc1 n ≡a σc2 n) ->
      C1 ≡a C2 ->
      C1 [ac| σc1; σe] ≡a C2 [ac| σc2; σe].
  Proof using.
    intros σc1 σc2 σe C1 C2 equivσ equiv. induction equiv.
    - apply AEquiv'StableSubst; auto. 
    - transitivity (C2 [ac| σc1; σe]); auto with AChor.
  Qed.
  Hint Resolve AEquivStableSubst : AChor.

  Inductive ARedex : Set :=
  | ARDone : Loc -> Expr -> Expr -> ARedex
  | ARIfE : nat -> Loc -> Expr -> Expr -> ARedex
  | ARIfTT : nat -> Loc -> ARedex
  | ARIfFF : nat -> Loc -> ARedex
  | ARSendE : Loc -> Expr -> Expr -> Loc -> ARedex
  | ARSendV : Loc -> Expr -> Loc -> ARedex
  | ARSyncL : Loc -> Loc -> ARedex
  | ARSyncR : Loc -> Loc -> ARedex
  | ARDef.
  Hint Constructors ARedex : AChor.
  
  Definition ASendSubst (p : Loc) (v : Expr) : Loc -> nat -> Expr :=
    fun q n =>
      if L.eq_dec p q
      then match n with
           | 0 => v
           | S m => ExprVar m
           end
      else ExprVar n.

  Lemma AUpSendSubst : forall (p q : Loc) (v : Expr),
      p <> q ->
      forall r n, AChorUpExprSubst (ASendSubst p v) q r n = ASendSubst p v r n.
  Proof using.
    intros p q v H r n.
    unfold AChorUpExprSubst; unfold ASendSubst.
    destruct (L.eq_dec q r);
      destruct (L.eq_dec p r); auto.
    exfalso; apply H; transitivity r; auto.
    destruct n; auto. rewrite ExprRenameVar; auto.
  Qed.
  
  Definition DefSubst (C1 : AnnChor) : nat -> AnnChor :=
    fun n => match n with
          | 0 => ADef C1 C1
          | S m => AVar m
          end.

  Inductive ARChorStep : ARedex -> list Loc -> AnnChor -> AnnChor -> Prop :=
  | ADoneEStep : forall (p : Loc) (e1 e2 : Expr),
      ExprStep e1 e2 -> ARChorStep (ARDone p e1 e2) nil (ADone p e1) (ADone p e2)
  | ASendEStep : forall (p q : Loc) (B : list Loc),
      ~ In p B -> ~ In q B -> p <> q ->
      forall (e1 e2 : Expr) (C : AnnChor),
        ExprStep e1 e2 -> ARChorStep (ARSendE p e1 e2 q) B (ASend p e1 q C) (ASend p e2 q C)
  | ASendIStep : forall (p q : Loc) (e : Expr) (C1 C2 : AnnChor) (B : list Loc) (R : ARedex),
      ARChorStep R (p :: q :: B) C1 C2 ->
      ARChorStep R B (ASend p e q C1) (ASend p e q C2)
  | ASendVStep : forall (p q : Loc) (v : Expr) (C : AnnChor) (B : list Loc),
      ~ In p B -> ~ In q B -> p <> q ->
      ExprVal v ->
      ARChorStep (ARSendV p v q) B (ASend p v q C) (C [ac| AChorIdSubst; ASendSubst q v])
  | AIfEStep : forall (p : Loc) (n : nat) (e1 e2 : Expr) (C1 C2 : AnnChor) (B : list Loc),
      ~ In p B ->
      ExprStep e1 e2 ->
      ARChorStep (ARIfE n p e1 e2) B (AIf n p e1 C1 C2) (AIf n p e2 C1 C2)
  | AIfIStep : forall (p : Loc) (n : nat) (e : Expr) (C1 C2 C3 C4 : AnnChor) (B : list Loc) (R : ARedex),
      ARChorStep R (p :: B) C1 C3 ->
      ARChorStep R (p :: B) C2 C4 ->
      ARChorStep R B (AIf n p e C1 C2) (AIf n p e C3 C4)
  | AIfTrueStep : forall (p : Loc) (n : nat) (C1 C2 : AnnChor) (B : list Loc),
      ~ In p B ->
      ARChorStep (ARIfTT n p) B (AIf n p tt C1 C2) C1
  | AIfFalseStep : forall (p : Loc) (n : nat) (C1 C2 : AnnChor) (B : list Loc),
      ~ In p B ->
      ARChorStep (ARIfFF n p) B (AIf n p ff C1 C2) C2
  | ADefStep : forall (C1 C2 : AnnChor),
      ARChorStep ARDef nil (ADef C1 C2) (C2 [ac| DefSubst C1; ExprAChorIdSubst])
  | ASyncLStep : forall (p q : Loc) (C : AnnChor) (B : list Loc),
      ~ In p B -> ~ In q B ->
      ARChorStep (ARSyncL p q) B (ASyncL p q C) C
  | ASyncRStep : forall (p q : Loc) (C : AnnChor) (B : list Loc),
      ~ In p B -> ~ In q B ->
      ARChorStep (ARSyncR p q) B (ASyncR p q C) C
  | ASyncLIStep : forall (p q : Loc) (C1 C2 : AnnChor) (B : list Loc) (R : ARedex),
      ARChorStep R (p :: q :: B) C1 C2 ->
      ARChorStep R B (ASyncL p q C1) (ASyncL p q C2)
  | ASyncRIStep : forall (p q : Loc) (C1 C2 : AnnChor) (B : list Loc) (R : ARedex),
      ARChorStep R (p :: q :: B) C1 C2 ->
      ARChorStep R B (ASyncR p q C1) (ASyncR p q C2).
  Hint Constructors ARChorStep : AChor.

  Ltac RStepRearrangeHelper :=
      match goal with
      | [i : ~ In ?p ?B1, ext : forall q, In q ?B1 <-> In q ?B2 |- ~ In ?p ?B2 ] =>
        let H := fresh in intro H; rewrite <- ext in H; apply i; exact H
      end.

  Lemma ARStepRearrange : forall R B1 C1 C2,
      ARChorStep R B1 C1 C2 -> forall B2, (forall q, In q B1 <-> In q B2) -> ARChorStep R B2 C1 C2.
  Proof using.
    intros R B1 C1 C2 step; induction step; intros B2 ext.
    all: try (constructor; try RStepRearrangeHelper; auto with AChor; fail).
    - assert (B2 = nil) by
        (destruct B2 as [| p0 B2]; auto;
          assert (In p0 nil) as H0
              by (apply ext; left; reflexivity);
          inversion H0).
      subst.
      clear ext; auto with AChor.
    - apply ASendIStep. apply IHstep.
      intros r; split.
      all:intro i; destruct i as [eq | i];
        [ left; exact eq
        | destruct i as [eq | i];
          [ right; left; exact eq
          | right; right; apply ext; auto]].
    - apply AIfIStep; [apply IHstep1 | apply IHstep2].
      all: intros q; split.
      all: intro i; destruct i as [eq | i]; [left; exact eq | right; apply ext; auto].
    - assert (B2 = nil)
        by (destruct B2 as [|p B2]; auto;
            assert (In p nil) as H0
                by (apply ext; left; reflexivity);
            inversion H0).
      rewrite H. apply ADefStep.
    - apply ASyncLIStep. apply IHstep. intro r; split; intro i. all: destruct i as [eq|i]; [subst; left; auto | right]; destruct i; [subst; left; auto | right; apply ext; auto].
    - apply ASyncRIStep. apply IHstep. intro r; split; intro i. all: destruct i as [eq|i]; [subst; left; auto | right]; destruct i; [subst; left; auto | right; apply ext; auto].
  Qed.

  Inductive ARedexOf : Loc -> ARedex -> Prop :=
  | ARODone : forall p e1 e2, ARedexOf p (ARDone p e1 e2)
  | AROIfE : forall n p e1 e2, ARedexOf p (ARIfE n p e1 e2)
  | AROIfTT : forall n p, ARedexOf p (ARIfTT n p)
  | AROIfFF : forall n p, ARedexOf p (ARIfFF n p)
  | AROSendE1 : forall p e1 e2 q, ARedexOf p (ARSendE p e1 e2 q)
  | AROSendE2 : forall p e1 e2 q, ARedexOf q (ARSendE p e1 e2 q)
  | AROSendV1 : forall p v q, ARedexOf p (ARSendV p v q)
  | AROSendV2 : forall p v q, ARedexOf q (ARSendV p v q)
  | AROSyncL1 : forall p q, ARedexOf p (ARSyncL p q)
  | AROSyncL2 : forall p q, ARedexOf q (ARSyncL p q)
  | AROSyncR1 : forall p q, ARedexOf p (ARSyncR p q)
  | AROSyncR2 : forall p q, ARedexOf q (ARSyncR p q).

  Lemma ANoIStepInList : forall p B R,
      In p B ->
      ARedexOf p R ->
      forall C1 C2, ~ARChorStep R B C1 C2.
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

  Corollary ANoDoneIStepInList : forall p B,
      In p B ->
      forall e1 e2 C1 C2, ~ARChorStep (ARDone p e1 e2) B C1 C2.
  Proof using.
    intros p B H e1 e2 C1 C2; apply ANoIStepInList with (p := p); auto; apply ARODone.
  Qed.
  Corollary ANoSendEIStepInList1 : forall p B,
      In p B ->
      forall e1 e2 C1 C2 q, ~ARChorStep (ARSendE p e1 e2 q) B C1 C2.
  Proof using.
    intros p B H q e1 e2 C1 C2; apply ANoIStepInList with (p := p); auto; apply AROSendE1.
  Qed.
  Corollary ANoSendEIStepInList2 : forall B q,
      In q B ->
      forall p e1 e2 C1 C2, ~ARChorStep (ARSendE p e1 e2 q) B C1 C2.
  Proof using.
    intros B q H p e1 e2 C1 C2; apply ANoIStepInList with (p := q); auto; apply AROSendE2.
  Qed.
  Corollary ANoSendVIStepInList1 : forall p B,
      In p B ->
      forall v q C1 C2, ~ARChorStep (ARSendV p v q) B C1 C2.
  Proof using.
    intros p B H v q C1 C2; apply ANoIStepInList with (p := p); auto; apply AROSendV1.
  Qed.
  Corollary ANoSendVIStepInList2 : forall B q,
      In q B ->
      forall p v C1 C2, ~ARChorStep (ARSendV p v q) B C1 C2.
  Proof using.
    intros B q H p v C1 C2; apply ANoIStepInList with (p := q); auto; apply AROSendV2.
  Qed.
  Corollary ANoIfEIStepInList : forall p B,
      In p B ->
      forall n e1 e2 C1 C2, ~ARChorStep (ARIfE n p e1 e2) B C1 C2.
  Proof using.
   intros p B H n e1 e2 C1 C2; apply ANoIStepInList with (p := p); auto; apply AROIfE.
  Qed.
  Corollary ANoIfTTStepInList : forall p B,
      In p B ->
      forall n C1 C2, ~ARChorStep (ARIfTT n p) B C1 C2.
  Proof using.
   intros p B H C1 C2; apply ANoIStepInList with (p := p); auto; apply AROIfTT.
  Qed.
  Corollary ANoIfFFStepInList : forall p B,
      In p B ->
      forall n C1 C2, ~ARChorStep (ARIfFF n p) B C1 C2.
  Proof using.
   intros p B H C1 C2; apply ANoIStepInList with (p := p); auto; apply AROIfFF.
  Qed.
  Corollary ANoASyncLStepInList1 : forall p B,
      In p B ->
      forall q C1 C2, ~ARChorStep (ARSyncL p q) B C1 C2.
  Proof using.
   intros p B H q C1 C2; apply ANoIStepInList with (p := p); auto; constructor.
  Qed. 
  Corollary ANoASyncLStepInList2 : forall B q,
      In q B ->
      forall p C1 C2, ~ARChorStep (ARSyncL p q) B C1 C2.
  Proof using.
   intros B q H p C1 C2; apply ANoIStepInList with (p := q); auto; constructor.
  Qed. 
  Corollary ANoASyncRStepInList1 : forall p B,
      In p B ->
      forall q C1 C2, ~ARChorStep (ARSyncR p q) B C1 C2.
  Proof using.
   intros p B H q C1 C2; apply ANoIStepInList with (p := p); auto; constructor.
  Qed. 
  Corollary ANoASyncRStepInList2 : forall B q,
      In q B ->
      forall p C1 C2, ~ARChorStep (ARSyncR p q) B C1 C2.
  Proof using.
   intros B q H p C1 C2; apply ANoIStepInList with (p := q); auto; constructor.
  Qed. 

  Hint Resolve ARStepRearrange ANoDoneIStepInList : AChor.
  Hint Resolve ANoSendEIStepInList1 ANoSendVIStepInList1 ANoSendEIStepInList2 ANoSendVIStepInList2 : AChor.
  Hint Resolve ANoIfEIStepInList ANoIfTTStepInList ANoIfFFStepInList: AChor.
  Hint Resolve ANoASyncLStepInList1 ANoASyncLStepInList2 ANoASyncRStepInList1 ANoASyncRStepInList2 : AChor.

  Inductive AChorStepMany : list Loc -> AnnChor -> AnnChor -> Prop :=
  | AChorManyZero : forall B C, AChorStepMany B C C
  | AChorManyPlus : forall R B C1 C2 C3, ARChorStep R B C1 C2 -> AChorStepMany B C2 C3 -> AChorStepMany B C1 C3.
  Hint Constructors AChorStepMany : AChor.

  Theorem AChorManyOne : forall (R : ARedex) (B : list Loc) (C1 C2 : AnnChor),
      ARChorStep R B C1 C2 -> AChorStepMany B C1 C2.
  Proof using.
    intros R B C1 C2 step.
    eapply AChorManyPlus; [exact step | apply AChorManyZero].
  Qed.
  Hint Resolve AChorManyOne : AChor.

  Program Fixpoint AChorStepManyTrans (B : list Loc) (C1 C2 C3 : AnnChor)
           (r1 : AChorStepMany B C1 C2)
           (r2 : AChorStepMany B C2 C3) {struct r1} : AChorStepMany B C1 C3 :=
   match r1 with
   | AChorManyZero B C => r2
   | AChorManyPlus R B C1' C2' _ s1 r3 =>
     AChorManyPlus _ _ _ _ _ s1  (AChorStepManyTrans _ _ _ _ r3 r2)
   end.
  Hint Resolve AChorStepManyTrans : AChor.

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
  Hint Resolve ConsNotIn NotInCons : AChor.

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


  Theorem AEquiv'Simulation : forall C1 C2, C1 ≡a' C2 -> forall R B C1',
        ARChorStep R B C1 C1' -> exists C2', ARChorStep R B C2 C2' /\ C1' ≡a C2'.
  Proof using.
    intros C1 C2 equiv; induction equiv; intros R B Cstep step;
      eauto with AChor; inversion step; eauto with AChor; subst.
    all: try (eexists; split; eauto with AChor; fail).
    - destruct (IHequiv _ _ _ H6) as [C3' HC3'].
      destruct (HC3') as [step' equivC3].
      exists (ASend p e q C3'); split; auto with AChor.
    - destruct (IHequiv1 _ _ _ H7) as [C12' HC12'];
        destruct HC12' as [stepC12' equivC12'].
      destruct (IHequiv2 _ _ _ H8) as [C22' HC22'];
        destruct HC22' as [stepC22' equivC22'].
      exists (AIf n p e C12' C22'); split; auto with AChor.
    - specialize (IHequiv _ _ _ H5). destruct IHequiv as [C2' HC2']; destruct HC2' as [stepC2' equivC2'].
      exists (ASyncL p q C2'); split; auto with AChor.
    - specialize (IHequiv _ _ _ H5). destruct IHequiv as [C2' HC2']; destruct HC2' as [stepC2' equivC2'].
      exists (ASyncR p q C2'); split; auto with AChor.
    - exists (C22 [ac| DefSubst C12; ExprAChorIdSubst]); split; auto with AChor.
      apply AEquivStableSubst; auto with AChor.
      intro n; unfold DefSubst; destruct n; auto with AChor.
    - exists (ASend r e2 s (ASend p e3 q C2)); split; auto with AChor.
    - inversion H10; subst.
      -- exists (ASend r e3 s (ASend p e1 q C2)); split; eauto with AChor.
         apply ASendEStep; auto; ListHelper.
      -- destruct (IHequiv _ _ _ H11) as [C4' HC4'];
           destruct HC4' as [stepC4' equivC4'].
         exists (ASend r e2 s (ASend p e1 q C4')); split; auto with AChor.
         apply ASendIStep. apply ASendIStep.
         eapply ARStepRearrange;
           [exact stepC4'|].
         intros q1; split; intros H13.
         all: destruct H13;
           [ right; right; left
           | destruct H3; [right; right; right; left
                           | destruct H3; [left
                                           | destruct H3; [right; left
                                                           | right; right; right; right]]]];
           auto.
      -- exists (ASend p e1 q (C2 [ac| AChorIdSubst; ASendSubst s e2]));
           split; auto with AChor.
         assert ((ASend p e1 q (C2 [ac| AChorIdSubst; ASendSubst s e2]))
                 = (ASend p e1 q C2) [ac| AChorIdSubst; ASendSubst s e2]).
         simpl; unfold ASendSubst at 2; destruct (L.eq_dec s p) as [eq | _];
           [exfalso; apply H1; symmetry; exact eq |].
         fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
         assert (C2 [ac|AChorIdSubst; ASendSubst s e2] =
                 C2 [ac| SendUpAChorSubst AChorIdSubst q; AChorUpExprSubst (ASendSubst s e2) q])
           by (apply AChorSubstExt;
               [ intro n; symmetry; apply SendUpAChorIdSubst
               | symmetry; apply AUpSendSubst; auto]).
         rewrite H3; reflexivity.
         rewrite H3. apply ASendVStep; auto; ListHelper.
    - exists (ASend r e2 s C2 [ac| AChorIdSubst; ASendSubst q e1]).
        split; auto with AChor.
        simpl.
        unfold ASendSubst at 1; destruct (L.eq_dec q r) as [eq | _];
          [exfalso; apply H0; exact eq|]; fold ExprIdSubst; rewrite ExprIdentitySubstSpec.
        apply ASendIStep.
        assert (C2 [ac| SendUpAChorSubst AChorIdSubst s; AChorUpExprSubst (ASendSubst q e1) s]
                = C2 [ac| AChorIdSubst; ASendSubst q e1])
          by (apply AChorSubstExt; [intro n; apply SendUpAChorIdSubst
                                  | apply AUpSendSubst; auto]).
        rewrite H3.
        apply ASendVStep; auto with AChor.
    - inversion H9; subst.
      -- inversion H10; subst.
         exists (ASend q e3 r (AIf n p e1 C1' C2')); split; auto with AChor.
         apply ASendEStep; auto; try ListHelper.
         exfalso. apply ANoSendEIStepInList1 in H14; auto. left; reflexivity.
      -- inversion H10; subst.
         1: apply ANoSendEIStepInList1 in H8; [destruct H8 | left; reflexivity].
         2: apply ANoSendVIStepInList1 in H8; [destruct H8 | left; reflexivity].
         destruct (IHequiv1 _ _ _ H8) as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv2 _ _ _ H11) as [C4' HC4']; destruct HC4' as [stepC4' equivC4'].
         exists (ASend q e2 r (AIf n p e1 C3' C4')); split; auto with AChor.
         apply ASendIStep. apply AIfIStep.
         all: apply ARStepRearrange with (B1 := q :: r :: p :: B); auto.
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
      -- inversion H10; subst;
           [apply ANoSendVIStepInList1 in H14; [destruct H14 | left; reflexivity] |].
         exists (AIf n p e1 C1' C2' [ac| AChorIdSubst; ASendSubst r e2]); split; auto with AChor.
         apply ASendVStep; auto; try ListHelper.
         simpl. unfold ASendSubst at 3.
         destruct (L.eq_dec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq|].
         fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
         apply AIfContext; apply AEquivStableSubst; auto with AChor.
    - exists (AIf n p e1 (ASend q e3 r C1') (ASend q e3 r C2')); split; auto with AChor.
    - inversion H8; subst.
      -- exists (AIf n p e3 (ASend q e2 r C1') (ASend q e2 r C2')); split; auto with AChor.
         apply AIfEStep; auto; ListHelper.
      -- destruct (IHequiv1 _ _ _ H10) as [C5' H5']; destruct H5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ H11) as [C6' H6']; destruct H6' as [stepC6' equivC6'].
         exists (AIf n p e1 (ASend q e2 r C5') (ASend q e2 r C6')); split; auto with AChor.
         apply AIfIStep; auto; apply ASendIStep;
           apply ARStepRearrange with (B1 := p :: q :: r ::B); auto.
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
      -- exists (ASend q e2 r C1'); split; auto with AChor.
         apply AIfTrueStep; ListHelper.
      -- exists (ASend q e2 r C2'); split; auto with AChor.
         apply AIfFalseStep; ListHelper.
    - exists (AIf n p e1 (C1'[ac| AChorIdSubst; ASendSubst r e2])
             (C2'[ac|AChorIdSubst; ASendSubst r e2])); split; auto with AChor.
      simpl; unfold ASendSubst at 1.
      destruct (L.eq_dec r p) as [eq | _];
        [exfalso; apply H0; symmetry; exact eq|].
      fold ExprIdSubst; rewrite ExprIdentitySubstSpec; auto with AChor.
    - exists (ASyncL r s (ASend p e2 q C')); split; auto with AChor.
    - inversion H10; subst.
      exists (ASend p e q C'); split; auto with AChor; apply ASyncLStep; intro i; [apply H9 | apply H11]; right; right; auto.
      specialize (IHequiv _ _ _ H9); destruct IHequiv as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
      exists (ASyncL r s (ASend p e q C0')); split; auto with AChor. apply ASyncLIStep. apply ASendIStep.
      apply ARStepRearrange with (B1 := r :: s :: p :: q :: B); auto.
      intros q0; split; intro i.
      all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
        destruct i as [eq | i]; subst; [right; right; right; left; reflexivity|];
          destruct i as [eq | i]; subst; [left; reflexivity|];
            destruct i as [eq | i]; subst; [right; left; reflexivity|];
              right; right; right; right; exact i.
    - exists (ASyncL r s C' [ac|AChorIdSubst; ASendSubst q e]); split; eauto with AChor.
      apply ASyncLIStep; fold AChorSubst. apply ASendVStep; auto.
      intro i; destruct i as [eq | i]; [apply H; auto | destruct i as [eq | i]; [apply H0; auto | apply H9; auto]].
      intro i; destruct i as [eq | i]; [apply H1; auto | destruct i as [eq | i]; [apply H2; auto | apply H11; auto]].
    - exists (ASend r e s C'); split; auto with AChor.
    - inversion H9; subst.
      -- exists (ASend r e2 s (ASyncL p q C')); split; auto with AChor.
         apply ASendEStep; auto; intro i; [apply H10 | apply H12]; right; right; auto.
      -- specialize (IHequiv _ _ _ H11); destruct IHequiv as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASend r e s (ASyncL p q C0')); split; auto with AChor.
         apply ASendIStep; apply ASyncLIStep. eapply ARStepRearrange; eauto with AChor.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
           destruct i as [eq | i]; subst; [right; right; right; left; reflexivity|];
             destruct i as [eq | i]; subst; [left; reflexivity|];
               destruct i as [eq | i]; subst; [right; left; reflexivity|];
                 right; right; right; right; exact i.
      -- exists (ASyncL p q (C' [ac|AChorIdSubst; ASendSubst s e])); split; eauto with AChor.
         apply ASendVStep; auto; intro i; [apply H10 | apply H12]; right; right; auto.
    - exists (ASyncR r s (ASend p e2 q C')); split; eauto with AChor. apply ASyncRIStep.
      apply ASendEStep; auto; intro i; destruct i as [eq | i]; auto; destruct i as [eq | i]; auto.
    - inversion H10; subst.
      -- exists (ASend p e q C'); split; eauto with AChor.
         apply ASyncRStep; intro i; [apply H9 | apply H11]; right; right; auto.
      -- specialize (IHequiv _ _ _ H9); destruct IHequiv as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASyncR r s (ASend p e q C0')); split; eauto with AChor.
         apply ASyncRIStep; apply ASendIStep. eapply ARStepRearrange; eauto with AChor.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
           destruct i as [eq | i]; subst; [right; right; right; left; reflexivity|];
             destruct i as [eq | i]; subst; [left; reflexivity|];
               destruct i as [eq | i]; subst; [right; left; reflexivity|];
                 right; right; right; right; exact i.
    - exists (ASyncR r s C' [ac|AChorIdSubst; ASendSubst q e]); split; eauto with AChor.
      apply ASyncRIStep; fold AChorSubst. apply ASendVStep; auto.
      intro i; destruct i as [eq | i]; [apply H; auto | destruct i as [eq | i]; [apply H0; auto | apply H9; auto]].
      intro i; destruct i as [eq | i]; [apply H1; auto | destruct i as [eq | i]; [apply H2; auto | apply H11; auto]].
    - exists (ASend r e s C'); split; auto with AChor.
    - inversion H9; subst.
      -- exists (ASend r e2 s (ASyncR p q C')); split; auto with AChor.
         apply ASendEStep; auto; intro i; [apply H10 | apply H12]; right; right; auto.
      -- specialize (IHequiv _ _ _ H11); destruct IHequiv as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASend r e s (ASyncR p q C0')); split; auto with AChor.
         apply ASendIStep; apply ASyncRIStep. eapply ARStepRearrange; eauto with AChor.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
           destruct i as [eq | i]; subst; [right; right; right; left; reflexivity|];
             destruct i as [eq | i]; subst; [left; reflexivity|];
               destruct i as [eq | i]; subst; [right; left; reflexivity|];
                 right; right; right; right; exact i.
      -- exists (ASyncR p q (C' [ac|AChorIdSubst; ASendSubst s e])); split; eauto with AChor.
         apply ASendVStep; auto; intro i; [apply H10 | apply H12]; right; right; auto.
    - exists (AIf n q e2 (AIf m p e3 C11' C21') (AIf m p e3 C12' C22')); split; eauto with AChor.
      apply AIfIStep; apply AIfEStep; auto. all: intro i; destruct i as [eq | i]; [apply H; auto | apply H8; auto].
    - inversion H8; subst.
      -- inversion H9; subst.
         2: { apply ANoIfEIStepInList in H12; [destruct H12| left; reflexivity]. }
         exists (AIf n q e3 (AIf m p e1 C11' C21') (AIf m p e1 C12' C22')); split; auto with AChor.
         apply AIfEStep; auto. ListHelper.
      -- inversion H9; subst.
         apply ANoIfEIStepInList in H11; [destruct H11| left; reflexivity].
         2: apply ANoIfTTStepInList in H10; [destruct H10 | left; reflexivity].
         2: apply ANoIfFFStepInList in H10; [destruct H10 | left; reflexivity].
         destruct (IHequiv1 _ _ _ H10) as [C0' HC0'];
           destruct HC0' as [stepC0' equivC0'].
         destruct (IHequiv2 _ _ _ H11) as [C5' HC5'];
           destruct HC5' as [stepC5' equivC5'].
         destruct (IHequiv3 _ _ _ H12) as [C3' HC3'];
           destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv4 _ _ _ H13) as [C6' HC6'];
           destruct HC6' as [stepC6' equivC6'].
         exists (AIf n q e2 (AIf m p e1 C0' C3') (AIf m p e1 C5' C6')); split; auto with AChor.
         apply AIfIStep; apply AIfIStep; eauto with AChor.
         all: apply ARStepRearrange with (B1 := q :: p :: B); auto.
         all: intros t; split; intros i.
         all: destruct i as [eq | i];
           [(* t = p *) right; left; exact eq
                      | destruct i as [eq | i];
                        [ (* t = q *) left; exact eq
                                    | right; right; exact i]].
      -- inversion H9; subst;
           [apply ANoIfTTStepInList in H11; [destruct H11 | left; reflexivity] |].
         exists (AIf m p e1 C11' C21'); split; auto with AChor.
         apply AIfTrueStep; ListHelper.
      -- inversion H9; subst;
           [apply ANoIfFFStepInList in H11; [destruct H11 | left; reflexivity] |].
         exists (AIf m p e1 C12' C22'); split; auto with AChor.
         apply AIfFalseStep; ListHelper.
    - exists (AIf n q e2 C11' C12'); split; auto with AChor.
    - exists (AIf n q e2 C21' C22'); split; auto with AChor.
    - inversion H9; subst; inversion H10; subst.
      -- exists (AIf m p e C1' C2'); split; auto with AChor.
         apply ASyncLStep; intro i; [apply H7 | apply H8]; right; auto.
      -- apply ANoASyncLStepInList1 in H11; [destruct H11| left; auto].
      -- apply ANoASyncLStepInList1 in H7; [destruct H7 | left; auto].
      -- destruct (IHequiv1 _ _ _ H7) as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv2 _ _ _ H8) as [C4' HC4']; destruct HC4' as [stepC4' equivC4'].
         exists (ASyncL q r (AIf m p e C3' C4')); split; auto with AChor.
         apply ASyncLIStep; apply AIfIStep; eapply ARStepRearrange; eauto with AChor; intro q0; split; intro i.
         1,3: destruct i as [eq | i]; subst; [right; left; reflexivity|];
           destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
             destruct i as [eq | i]; subst; [ left; reflexivity | right; right; right; auto].
         all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
           destruct i as [eq | i]; subst; [left; reflexivity |];
             destruct i as [eq | i]; subst; [right; left; reflexivity| right; right; right; auto].
    - exists (AIf m r e C1' C2'); split; eauto with AChor.
      apply AIfIStep; apply ASyncLStep. 1,3: intro i; destruct i as [eq | i]; [apply H; auto | apply H7; exact i].
      all: intro i; destruct i as [eq | i]; [apply H0; auto | apply H8; exact i].
    - inversion H7; subst.
      -- exists (AIf m r e2 (ASyncL p q C1') (ASyncL p q C2')); split; eauto with AChor.
         apply AIfEStep; auto; intro i; apply H10; right; right; auto.
      -- destruct (IHequiv1 _ _ _ H10) as [C5' HC5']; destruct HC5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ H11) as [C6' HC6']; destruct HC6' as [stepC6' equivC6'].
         exists (AIf m r e (ASyncL p q C5') (ASyncL p q C6')); split; eauto with AChor.
         apply AIfIStep; apply ASyncLIStep; eapply ARStepRearrange; eauto with AChor; intro q0; split; intro i.
         1,3: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [left; auto |];
             destruct i as [eq|i]; [right; left; auto | right; right; right; auto].
         all: destruct i as [eq | i]; [right; left; auto |];
           destruct i as [eq | i]; [right; right; left; auto|];
             destruct i as [eq | i]; [left; auto | right; right; right; auto].
      -- exists (ASyncL p q C1'); split; eauto with AChor; apply AIfTrueStep; intro i; apply H10; right; right; auto.
      -- exists (ASyncL p q C2'); split; eauto with AChor; apply AIfFalseStep; intro i; apply H10; right; right; auto.
    - inversion H9; subst; inversion H10; subst.
      -- exists (AIf m p e C1' C2'); split; auto with AChor.
         apply ASyncRStep; intro i; [apply H7 | apply H8]; right; auto.
      -- apply ANoASyncRStepInList1 in H11; [destruct H11| left; auto].
      -- apply ANoASyncRStepInList1 in H7; [destruct H7 | left; auto].
      -- destruct (IHequiv1 _ _ _ H7) as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
         destruct (IHequiv2 _ _ _ H8) as [C4' HC4']; destruct HC4' as [stepC4' equivC4'].
         exists (ASyncR q r (AIf m p e C3' C4')); split; auto with AChor.
         apply ASyncRIStep; apply AIfIStep; eapply ARStepRearrange; eauto with AChor; intro q0; split; intro i.
         1,3: destruct i as [eq | i]; subst; [right; left; reflexivity|];
           destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
             destruct i as [eq | i]; subst; [ left; reflexivity | right; right; right; auto].
         all: destruct i as [eq | i]; subst; [right; right; left; reflexivity|];
           destruct i as [eq | i]; subst; [left; reflexivity |];
             destruct i as [eq | i]; subst; [right; left; reflexivity| right; right; right; auto].
    - exists (AIf m r e C1' C2'); split; eauto with AChor.
      apply AIfIStep; apply ASyncRStep. 1,3: intro i; destruct i as [eq | i]; [apply H; auto | apply H7; exact i].
      all: intro i; destruct i as [eq | i]; [apply H0; auto | apply H8; exact i].
    - inversion H7; subst.
      -- exists (AIf m r e2 (ASyncR p q C1') (ASyncR p q C2')); split; eauto with AChor.
         apply AIfEStep; auto; intro i; apply H10; right; right; auto.
      -- destruct (IHequiv1 _ _ _ H10) as [C5' HC5']; destruct HC5' as [stepC5' equivC5'].
         destruct (IHequiv2 _ _ _ H11) as [C6' HC6']; destruct HC6' as [stepC6' equivC6'].
         exists (AIf m r e (ASyncR p q C5') (ASyncR p q C6')); split; eauto with AChor.
         apply AIfIStep; apply ASyncRIStep; eapply ARStepRearrange; eauto with AChor; intro q0; split; intro i.
         1,3: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [left; auto |];
             destruct i as [eq|i]; [right; left; auto | right; right; right; auto].
         all: destruct i as [eq | i]; [right; left; auto |];
           destruct i as [eq | i]; [right; right; left; auto|];
             destruct i as [eq | i]; [left; auto | right; right; right; auto].
      -- exists (ASyncR p q C1'); split; eauto with AChor; apply AIfTrueStep; intro i; apply H10; right; right; auto.
      -- exists (ASyncR p q C2'); split; eauto with AChor; apply AIfFalseStep; intro i; apply H10; right; right; auto.
    - exists (ASyncL r s C'); split; eauto with AChor. apply ASyncLIStep; apply ASyncLStep.
      all: intro i; destruct i as [eq|i]; auto; destruct i; auto.
    - inversion H9; subst.
      -- exists (ASyncL p q C'); split; eauto with AChor.
         apply ASyncLStep; intro i; [apply H10 | apply H11]; right; right; auto.
      -- destruct (IHequiv _ _ _ H10) as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASyncL r s (ASyncL p q C0')); split; eauto with AChor.
         repeat (apply ASyncLIStep). eapply ARStepRearrange; eauto.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [right; right; right; left; auto |];
             destruct i as [eq | i]; [left; auto |];
               destruct i as [eq | i]; [right; left; auto | right; right; right; right; auto].
    - exists (ASyncR r s C'); split; eauto with AChor; apply ASyncRIStep; apply ASyncLStep.
      all: intro i; destruct i as [eq|i]; auto; destruct i; auto.
    - inversion H9; subst.
      -- exists (ASyncL p q C'); split; eauto with AChor.
         apply ASyncRStep; intro i; [apply H10 | apply H11]; right; right; auto.
      -- destruct (IHequiv _ _ _ H10) as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASyncR r s (ASyncL p q C0')); split; eauto with AChor.
         apply ASyncRIStep; apply ASyncLIStep. eapply ARStepRearrange; eauto.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [right; right; right; left; auto |];
             destruct i as [eq | i]; [left; auto |];
               destruct i as [eq | i]; [right; left; auto | right; right; right; right; auto].
    - exists (ASyncL r s C'); split; eauto with AChor. apply ASyncLIStep; apply ASyncRStep.
      all: intro i; destruct i as [eq|i]; auto; destruct i; auto.
    - inversion H9; subst.
      -- exists (ASyncR p q C'); split; eauto with AChor.
         apply ASyncLStep; intro i; [apply H10 | apply H11]; right; right; auto.
      -- destruct (IHequiv _ _ _ H10) as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASyncL r s (ASyncR p q C0')); split; eauto with AChor.
         apply ASyncLIStep; apply ASyncRIStep. eapply ARStepRearrange; eauto.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [right; right; right; left; auto |];
             destruct i as [eq | i]; [left; auto |];
               destruct i as [eq | i]; [right; left; auto | right; right; right; right; auto].
    - exists (ASyncR r s C'); split; eauto with AChor. apply ASyncRIStep; apply ASyncRStep.
      all: intro i; destruct i as [eq|i]; auto; destruct i; auto.
    - inversion H9; subst.
      -- exists (ASyncR p q C'); split; eauto with AChor.
         apply ASyncRStep; intro i; [apply H10 | apply H11]; right; right; auto.
      -- destruct (IHequiv _ _ _ H10) as [C0' HC0']; destruct HC0' as [stepC0' equivC0'].
         exists (ASyncR r s (ASyncR p q C0')); split; eauto with AChor.
         apply ASyncRIStep; apply ASyncRIStep. eapply ARStepRearrange; eauto.
         intro q0; split; intro i.
         all: destruct i as [eq | i]; [right; right; left; auto |];
           destruct i as [eq | i]; [right; right; right; left; auto |];
             destruct i as [eq | i]; [left; auto |];
               destruct i as [eq | i]; [right; left; auto | right; right; right; right; auto].
  Qed.

  Theorem AEquivSimulation : forall C1 C2, C1 ≡a C2 -> forall C1' R B, ARChorStep R B C1 C1' -> exists C2',
          ARChorStep R B C2 C2' /\ C1' ≡a C2'.
  Proof using.
    intros C1 C2 H.
    induction H; intros C1' R B step.
    apply AEquiv'Simulation with (C1 := C1); auto.
    destruct (AEquiv'Simulation _ _ H _ _ _ step) as [C2' HC2'].
    destruct HC2' as [stepC2' equivC2'].
    destruct (IHAchorEquiv _ _ _ stepC2') as [C3' HC3']; destruct HC3' as [stepC3' equivC3'].
    exists C3'; split; auto. transitivity C2'; auto.
  Qed.

  Inductive AStdChorStep : AnnChor -> AnnChor -> Prop :=
  | AStdDoneEStep : forall (p : Loc) (e1 e2 : Expr),
      ExprStep e1 e2
      -> AStdChorStep (ADone p e1) (ADone p e2)
  | AStdSendEStep : forall (p q : Loc) (e1 e2 : Expr) (C : AnnChor),
      ExprStep e1 e2
      -> p <> q
      -> AStdChorStep (ASend p e1 q C) (ASend p e2 q C)
  | AStdSendVStep : forall (p q : Loc) (v : Expr) (C : AnnChor),
      ExprVal v
      -> p <> q
      -> AStdChorStep (ASend p v q C) (C [ac| AChorIdSubst; ASendSubst q v])
  | AStdIfEStep : forall (n : nat) (p : Loc) (e1 e2 : Expr) (C1 C2 : AnnChor),
      ExprStep e1 e2
      -> AStdChorStep (AIf n p e1 C1 C2) (AIf n p e2 C1 C2)
  | AStdIfTrueStep : forall (n : nat) (p : Loc) (C1 C2 : AnnChor),
      AStdChorStep (AIf n p tt C1 C2) C1
  | AStdIfFalseStep : forall (n : nat) (p : Loc) (C1 C2 : AnnChor),
      AStdChorStep (AIf n p ff C1 C2) C2
  | AStdASyncLStep : forall (p q : Loc) (C : AnnChor),
      AStdChorStep (ASyncL p q C) C
  | AStdASyncRStep : forall (p q : Loc) (C : AnnChor),
      AStdChorStep (ASyncR p q C) C
  | AStdADefStep : forall (C1 C2 : AnnChor),
      AStdChorStep (ADef C1 C2) (C2 [ac| DefSubst C1; ExprAChorIdSubst])
  | AStdEquivStep : forall (C1 C1' C2 C2' : AnnChor),
      C1 ≡a C1'
      -> AStdChorStep C1' C2'
      -> C2 ≡a C2'
      -> AStdChorStep C1 C2.
  Hint Constructors AStdChorStep : AStdChor.

  Theorem AStdToARStep : forall (C1 C2 : AnnChor),
      AStdChorStep C1 C2
      -> exists R C2', C2 ≡a C2' /\ ARChorStep R nil C1 C2'.
  Proof using.
    intros C1 C2 stdstep; induction stdstep.
    all:try ( eexists; eexists; split; [reflexivity | constructor; auto]).
    rename H into equiv1; rename H0 into equiv2;
      destruct IHstdstep as [R H]; destruct H as [C2'' H]; destruct H as [equiv2' step].
    destruct (AEquivSimulation _ C1 (AchorEquivSym _ _ equiv1) _ _ _ step) as [C2''' H];
      destruct H as [step' equiv2''].
    exists R; exists C2'''; split; auto.
    transitivity C2'; auto. transitivity C2''; auto.
  Qed.

  Inductive ARedexOnTop : ARedex -> AnnChor -> Prop :=
  | ADoneOnTop : forall p e1 e2, ARedexOnTop (ARDone p e1 e2) (ADone p e1)
  | ASendEOnTop : forall p e1 e2 q C, ARedexOnTop (ARSendE p e1 e2 q) (ASend p e1 q C)
  | ASendVOnTop : forall p v q C, ARedexOnTop (ARSendV p v q) (ASend p v q C)
  | AIfEOnTop : forall n p e1 e2 C1 C2, ARedexOnTop (ARIfE n p e1 e2) (AIf n p e1 C1 C2)
  | AIfTTOnTop : forall n p C1 C2, ARedexOnTop (ARIfTT n p) (AIf n p tt C1 C2)
  | AIfFFOnTop : forall n p C1 C2, ARedexOnTop (ARIfFF n p) (AIf n p ff C1 C2)
  | ASyncLOnTop : forall p q C, ARedexOnTop (ARSyncL p q) (ASyncL p q C)
  | ASyncROnTop : forall p q C, ARedexOnTop (ARSyncR p q) (ASyncR p q C)
  | ADefOnTop : forall C1 C2, ARedexOnTop ARDef (ADef C1 C2).
  Hint Constructors ARedexOnTop : AStdChor.

  Lemma ARStepOnTop : forall (R : ARedex) (B : list Loc) (C1 C2 : AnnChor),
      ARChorStep R B C1 C2 ->
      exists C1' C2', C1 ≡a C1' /\ C2 ≡a C2' /\ ARChorStep R B C1' C2' /\ ARedexOnTop R C1'.
  Proof using.
    intros R B C1 C2 step; induction step.
    all: try(eexists; eexists; split; [|split; [|split]]; eauto with AChor AStdChor; fail).
    - destruct IHstep as [C1' H]; destruct H as [C2' H]; destruct H as [equiv1 H];
        destruct H as [equiv2 H]; destruct H as [step' ontop].
      destruct R; inversion ontop; subst.
      all: inversion step'; subst; try (rename l into r); try (rename l0 into s).
      all: try (match goal with
                | [H : ARChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e1 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?p ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      -- exists (AIf n r e0 (ASend p e q C0) (ASend p e q C3)).
         exists (AIf n r e1 (ASend p e q C0) (ASend p e q C3)).
         split; [|split;[|split]]; auto with AChor AStdChor.
         --- transitivity (ASend p e q (AIf n r e0 C0 C3)); auto with AChor.
             apply ASwapIfSend; auto with AChor; ListHelper. 
         --- transitivity (ASend p e q (AIf n r e1 C0 C3)); auto with AChor.
             apply ASwapIfSend; auto with AChor; ListHelper.
         --- constructor; auto; ListHelper.
      -- exists (AIf n r tt (ASend p e q C2') (ASend p e q C3));
           exists (ASend p e q C2');
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (ASend p e q (AIf n r tt C2' C3)); auto with AChor. apply ASwapIfSend; auto with AChor; ListHelper. 
         --- apply AIfTrueStep; ListHelper. 
      -- exists (AIf n r ff (ASend p e q C0) (ASend p e q C2'));
           exists (ASend p e q C2');
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (ASend p e q (AIf n r ff C0 C2')); auto with AChor.
             apply ASwapIfSend; auto with AChor; ListHelper. 
         --- apply AIfFalseStep; ListHelper. 
      -- exists (ASend r e0 s (ASend p e q C));
           exists (ASend r e1 s (ASend p e q C));
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (ASend p e q (ASend r e0 s C)); auto with AChor.
             apply ASwapSendSend; auto with AChor; ListHelper.
         --- transitivity (ASend p e q (ASend r e1 s C)); auto with AChor.
              apply ASwapSendSend; auto with AChor; ListHelper.
         --- apply ASendEStep; auto; ListHelper.
      -- exists (ASend r e0 s (ASend p e q C));
           exists (ASend p e q C [ac| AChorIdSubst; ASendSubst s e0]);
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (ASend p e q (ASend r e0 s C)); auto with AChor.
             apply ASwapSendSend; auto with AChor; ListHelper.
         ---  simpl. unfold ASendSubst at 1.
             destruct (L.eq_dec s p) as [eq | _]; [subst; ListHelper|].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec.
             assert (C [ac|AChorIdSubst; ASendSubst s e0]
                     = C [ac|SendUpAChorSubst AChorIdSubst q;
                            AChorUpExprSubst (ASendSubst s e0) q]) as H
             by (apply AChorSubstExt;
                 [intro n; symmetry; apply SendUpAChorIdSubst
                 |intros p5 n; symmetry; apply AUpSendSubst; ListHelper]).
             rewrite <- H; auto with AChor.
         --- apply ASendVStep; auto with AChor; ListHelper.
      -- exists (ASyncL r s (ASend p e q C2')); exists (ASend p e q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         --- transitivity (ASend p e q (ASyncL r s C2')); eauto with AChor. apply ASwapSendSyncL; auto with AChor.
             intro i; apply H3; left; auto. intro i; apply H5; left; auto.
             intro i; apply H3; right; left; auto. intro i; apply H5; right; left; auto.
         --- apply ASyncLStep; intro i; [apply H3 | apply H5]; right; right; auto.
      -- exists (ASyncR r s (ASend p e q C2')); exists (ASend p e q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         --- transitivity (ASend p e q (ASyncR r s C2')); eauto with AChor. apply ASwapSendSyncR; auto with AChor.
             intro i; apply H3; left; auto. intro i; apply H5; left; auto.
             intro i; apply H3; right; left; auto. intro i; apply H5; right; left; auto.
         --- apply ASyncRStep; intro i; [apply H3 | apply H5]; right; right; auto.
    - destruct IHstep1 as [C1' H]; destruct H as [C3' H]; destruct H as [equiv1 H];
        destruct H as [equiv3 H]; destruct H as [step13 ontop1].
      destruct IHstep2 as [C2' H]; destruct H as [C4' H]; destruct H as [equiv2 H];
        destruct H as [equiv4 H]; destruct H as [step24 ontop2].
      destruct R; inversion ontop1; subst; inversion ontop2; subst; inversion step13; subst; inversion step24; subst.
      all: try (match goal with
                | [H : ARChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      all: try (rename l into r); try (rename l0 into s).
      -- exists (AIf n0 r e0 (AIf n p e C0 C6) (AIf n p e C5 C7));
           exists (AIf n0 r e1 (AIf n p e C0 C6) (AIf n p e C5 C7));
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (AIf n p e (AIf n0 r e0 C0 C5) (AIf n0 r e0 C6 C7)); auto with AChor.
             apply ASwapIfIf; auto with AChor; ListHelper.
         --- transitivity (AIf n p e (AIf n0 r e1 C0 C5) (AIf n0 r e1 C6 C7)); auto with AChor.
             apply ASwapIfIf; auto with AChor; ListHelper.
         --- apply AIfEStep; auto with AChor; ListHelper.
      -- exists (AIf n0 r tt (AIf n p e C3' C4') (AIf n p e C5 C7));
           exists (AIf n p e C3' C4');
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (AIf n p e (AIf n0 r tt C3' C5) (AIf n0 r tt C4' C7)); auto with AChor; apply ASwapIfIf; auto with AChor; ListHelper.
         --- apply AIfTrueStep; ListHelper. 
      -- exists (AIf n0 r ff (AIf n p e C0 C6) (AIf n p e C3' C4'));
           exists (AIf n p e C3' C4');
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (AIf n p e (AIf n0 r ff C0 C3') (AIf n0 r ff C6 C4')); auto with AChor; apply ASwapIfIf; auto with AChor; ListHelper.
         --- apply AIfFalseStep; ListHelper. 
      -- exists (ASend r e0 s (AIf n p e C C0));
           exists (ASend r e1 s (AIf n p e C C0));
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (AIf n p e (ASend r e0 s C) (ASend r e0 s C0)); auto with AChor.
             apply ASwapSendIf; auto with AChor; ListHelper.
         --- transitivity (AIf n p e (ASend r e1 s C) (ASend r e1 s C0)); auto with AChor.
             apply ASwapSendIf; auto with AChor; ListHelper.
         --- apply ASendEStep; auto; ListHelper.
      -- exists (ASend r e0 s (AIf n p e C C0));
           exists (AIf n p e C C0 [ac|AChorIdSubst; ASendSubst s e0]);
           split; [| split; [| split]]; auto with AChor AStdChor.
         --- transitivity (AIf n p e (ASend r e0 s C) (ASend r e0 s C0)); auto with AChor.
             apply ASwapSendIf; auto with AChor; ListHelper.
         --- transitivity (AIf n p e (C [ac|AChorIdSubst; ASendSubst s e0]) (C0 [ac|AChorIdSubst; ASendSubst s e0])); auto with AChor.
             simpl. unfold ASendSubst at 3.
             destruct (L.eq_dec s p) as [eq | _]; 
               [subst; ListHelper |].
             fold ExprIdSubst. rewrite ExprIdentitySubstSpec. reflexivity.
         --- apply ASendVStep; auto; ListHelper.
      -- exists (ASyncL r s (AIf n p e C3' C4')); exists (AIf n p e C3' C4'); split; [|split; [|split]]; auto with AChor AStdChor.
         assert (p <> r) by (intro eq; apply H3; left; auto).
         assert (p <> s) by (intro eq; apply H5; left; auto).
         transitivity (AIf n p e (ASyncL r s C3') (ASyncL r s C4')); auto with AChor.
         apply ASyncLStep; intro i; [apply H3 | apply H5]; right; auto.
      -- exists (ASyncR r s (AIf n p e C3' C4')); exists (AIf n p e C3' C4'); split; [|split; [|split]]; auto with AChor AStdChor.
         assert (p <> r) by (intro eq; apply H3; left; auto).
         assert (p <> s) by (intro eq; apply H5; left; auto).
         transitivity (AIf n p e (ASyncR r s C3') (ASyncR r s C4')); auto with AChor.
         apply ASyncRStep; intro i; [apply H3 | apply H5]; right; auto.
    - destruct IHstep as [C1' H]; destruct H as [C2' H]; destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [step12 ontop1].
      destruct R; inversion ontop1; subst; inversion ontop1; subst; inversion step12; subst.
      all: try (match goal with
                | [H : ARChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?p ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?p ?q) (_ :: ?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | right; left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      all: try (rename l into r); try (rename l0 into s).
      all:  repeat match goal with
                   | [H : ~ In ?r (?p :: ?q :: ?B) |- _ ] =>
                     match goal with
                     | [ _ : p <> r, _ : q <> r, _ : ~ In r B |- _] => fail 1
                     | _ =>
                       assert (p <> r) by (intro eq; apply H; left; auto);
                         assert (q <> r) by (intro eq; apply H; right; left; auto);
                         assert (~ In r B) by (intro i; apply H; right; right; auto)
                     end
                   end.
      -- exists (AIf n r e (ASyncL p q C0) (ASyncL p q C3));
           exists (AIf n r e0 (ASyncL p q C0) (ASyncL p q C3)); split; [|split; [|split]];
             eauto with AChor AStdChor.
         --- transitivity (ASyncL p q (AIf n r e C0 C3)); eauto with AChor.
         --- transitivity (ASyncL p q (AIf n r e0 C0 C3)); eauto with AChor.
      -- exists (AIf n r tt (ASyncL p q C2') (ASyncL p q C3)); exists (ASyncL p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (AIf n r tt C2' C3)); eauto with AChor.
      -- exists (AIf n r ff (ASyncL p q C0) (ASyncL p q C2')); exists (ASyncL p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (AIf n r ff C0 C2')); eauto with AChor.
      -- exists (ASend r e s (ASyncL p q C)); exists (ASend r e0 s (ASyncL p q C));
           split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (ASend r e s C)); eauto with AChor.
         transitivity (ASyncL p q (ASend r e0 s C)); eauto with AChor.
      -- exists (ASend r e s (ASyncL p q C)); exists (ASyncL p q C [ac| AChorIdSubst; ASendSubst s e]);
           split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (ASend r e s C)); eauto with AChor.
         transitivity (ASyncL p q (C [ac| AChorIdSubst; ASendSubst s e])); auto with AChor.
      -- exists (ASyncL r s (ASyncL p q C2')); exists (ASyncL p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (ASyncL r s C2')); eauto with AChor.
      -- exists (ASyncR r s (ASyncL p q C2')); exists (ASyncL p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncL p q (ASyncR r s C2')); eauto with AChor.
    - destruct IHstep as [C1' H]; destruct H as [C2' H]; destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [step12 ontop1].
      destruct R; inversion ontop1; subst; inversion ontop1; subst; inversion step12; subst.
      all: try (match goal with
                | [H : ARChorStep (?RC ?q ?e1 ?e2 ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e ?r) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q ?e) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?p ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?p ?q) (_ :: ?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | right; left; reflexivity | constructor]
                | [H : ARChorStep (?RC ?q) (?q :: ?B') ?C1' ?C2' |- _] =>
                  apply ANoIStepInList with (p := q) in H;
                  [destruct H | left; reflexivity | constructor]
                end).
      all: try (rename l into r); try (rename l0 into s).
      all:  repeat match goal with
                   | [H : ~ In ?r (?p :: ?q :: ?B) |- _ ] =>
                     match goal with
                     | [ _ : p <> r, _ : q <> r, _ : ~ In r B |- _] => fail 1
                     | _ =>
                       assert (p <> r) by (intro eq; apply H; left; auto);
                         assert (q <> r) by (intro eq; apply H; right; left; auto);
                         assert (~ In r B) by (intro i; apply H; right; right; auto)
                     end
                   end.
      -- exists (AIf n r e (ASyncR p q C0) (ASyncR p q C3));
           exists (AIf n r e0 (ASyncR p q C0) (ASyncR p q C3)); split; [|split; [|split]];
             eauto with AChor AStdChor.
         --- transitivity (ASyncR p q (AIf n r e C0 C3)); eauto with AChor.
         --- transitivity (ASyncR p q (AIf n r e0 C0 C3)); eauto with AChor.
      -- exists (AIf n r tt (ASyncR p q C2') (ASyncR p q C3)); exists (ASyncR p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (AIf n r tt C2' C3)); eauto with AChor.
      -- exists (AIf n r ff (ASyncR p q C0) (ASyncR p q C2')); exists (ASyncR p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (AIf n r ff C0 C2')); eauto with AChor.
      -- exists (ASend r e s (ASyncR p q C)); exists (ASend r e0 s (ASyncR p q C));
           split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (ASend r e s C)); eauto with AChor.
         transitivity (ASyncR p q (ASend r e0 s C)); eauto with AChor.
      -- exists (ASend r e s (ASyncR p q C)); exists (ASyncR p q C [ac| AChorIdSubst; ASendSubst s e]);
           split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (ASend r e s C)); eauto with AChor.
         transitivity (ASyncR p q (C [ac| AChorIdSubst; ASendSubst s e])); auto with AChor.
      -- exists (ASyncL r s (ASyncR p q C2')); exists (ASyncR p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (ASyncL r s C2')); eauto with AChor.
      -- exists (ASyncR r s (ASyncR p q C2')); exists (ASyncR p q C2'); split; [|split; [|split]]; eauto with AChor AStdChor.
         transitivity (ASyncR p q (ASyncR r s C2')); eauto with AChor.
  Qed.

  Lemma ARStepOnTopToStd : forall (C1 C2 : AnnChor) (R : ARedex) (B : list Loc),
      ARedexOnTop R C1 ->
      ARChorStep R B C1 C2 ->
      AStdChorStep C1 C2.
  Proof using.
    intros C1 C2 R B ontop rstep; induction rstep; inversion ontop; subst;
      eauto with AChor AStdChor.
    - apply ANoSendEIStepInList1 in rstep; [destruct rstep| left; reflexivity].
    - apply ANoSendVIStepInList1 in rstep; [destruct rstep | left; reflexivity].
    - apply ANoIfEIStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - apply ANoIfTTStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - apply ANoIfFFStepInList in rstep1; [destruct rstep1 | left; reflexivity].
    - apply ANoASyncLStepInList1 in rstep; [destruct rstep | left; reflexivity].
    - apply ANoASyncRStepInList1 in rstep; [destruct rstep | left; reflexivity].
  Qed.
  Theorem ARStepToStd : forall (C1 C2 : AnnChor) (R : ARedex) (B : list Loc),
      ARChorStep R B C1 C2 -> AStdChorStep C1 C2.
  Proof using.
    intros C1 C2 R B rstep.
    apply ARStepOnTop in rstep;
      destruct rstep as [C1' H]; destruct H as [C2' H];
      destruct H as [equiv1 H]; destruct H as [equiv2 H]; destruct H as [rstep ontop].
    apply AStdEquivStep with (C1' := C1') (C2' := C2'); auto.
    apply ARStepOnTopToStd with (R := R) (B := B); auto.
  Qed.
  
  Fixpoint AnnThreadNames (C : AnnChor) : list Loc :=
    match C with
    | ADone p _ => p :: nil
    | AVar _ => nil
    | ASend p _ q C' => p :: q :: (AnnThreadNames C')
    | AIf _ p _ C1 C2 => p :: (AnnThreadNames C1) ++ (AnnThreadNames C2)
    | ASyncL p q C => p :: q :: AnnThreadNames C
    | ASyncR p q C => p :: q :: AnnThreadNames C
    | ADef C1 C2 => (AnnThreadNames C1) ++ (AnnThreadNames C2)
    end.

  Reserved Infix "∈ATN" (at level 20).
  Inductive InAnnThreadNames : Loc -> AnnChor -> Prop :=
  | AnnInDone : forall p e, p ∈ATN (ADone p e)
  | AnnInSend1 : forall p e q C', p ∈ATN (ASend p e q C')
  | AnnInSend2 : forall p e q C', q ∈ATN (ASend p e q C')
  | AnnInSend3 : forall r p e q C', r ∈ATN C' -> r ∈ATN (ASend p e q C')
  | AnnInIf1 : forall n p e C1 C2, p ∈ATN (AIf n p e C1 C2)
  | AnnInIf2 : forall n q p e C1 C2, q ∈ATN C1 -> q ∈ATN (AIf n p e C1 C2)
  | AnnInIf3 : forall n q p e C1 C2, q ∈ATN C2 -> q ∈ATN (AIf n p e C1 C2)
  | AnnInASyncL1 : forall p q C, p ∈ATN (ASyncL p q C)
  | AnnInASyncL2 : forall p q C, q ∈ATN (ASyncL p q C)
  | AnnInASyncL3 : forall p q r C, r ∈ATN C -> r ∈ATN (ASyncL p q C)
  | AnnInASyncR1 : forall p q C, p ∈ATN (ASyncR p q C)
  | AnnInASyncR2 : forall p q C, q ∈ATN (ASyncR p q C)
  | AnnInASyncR3 : forall p q r C, r ∈ATN C -> r ∈ATN (ASyncR p q C)
  | AnnInDef1 : forall p C1 C2, p ∈ATN C1 -> p ∈ATN (ADef C1 C2)
  | AnnInDef2 : forall p C1 C2, p ∈ATN C2 -> p ∈ATN (ADef C1 C2)
  where "p ∈ATN C" := (InAnnThreadNames p C).

  Lemma InAnnThreadNamesSpec : forall p C, p ∈ATN C <-> In p (AnnThreadNames C).
  Proof using.
    intros p C; revert p; AChorInduction C; intro r; split; intro i; simpl in *.
    all: try (match goal with
              | [H : ?r ∈ATN ?C |- _] => inversion H; subst
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

  Lemma AnnThreadNamesInvariant' : forall C1 C2 : AnnChor,
      C1 ≡a' C2 -> forall p : Loc, p ∈ATN C1 <-> p ∈ATN C2.
  Proof using.
    intros C1 C2 equiv; induction equiv; intros t; split; intros i; auto;
      repeat match goal with
             | [i : ?p ∈ATN (_ _) |- _] => inversion i; subst; clear i
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
    - apply AnnInIf2; apply AnnInIf3; apply IHequiv3; auto.
    - apply AnnInIf3; apply AnnInIf3; apply IHequiv4; auto.
    - apply AnnInIf3; apply AnnInIf2; apply IHequiv3; auto.
    - apply AnnInIf3; apply AnnInIf3; apply IHequiv4; auto.
  Qed.
    
  Lemma AnnThreadNamesInvariant : forall C1 C2 : AnnChor,
      C1 ≡a C2 -> forall p : Loc, p ∈ATN C1 <-> p ∈ATN C2.
  Proof using.
    intros C1 C2 equiv; induction equiv.
    - intro p; apply AnnThreadNamesInvariant'; auto.
    - intro p. apply AnnThreadNamesInvariant' with (p := p) in H. rewrite H.
      apply IHequiv.
  Qed.
      
End AnnotatedChoreography.
