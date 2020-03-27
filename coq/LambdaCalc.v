Require Export Expression.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Module LambdaCalc <: Expression.

  Inductive SimpleType : Set :=
    boolType : SimpleType
  | natType : SimpleType
  | ArrowT : SimpleType -> SimpleType -> SimpleType.

  Definition SimpleTypeEqDec : forall tau sigma : SimpleType, {tau = sigma} + {tau <> sigma}.
    decide equality.
  Qed.

  Inductive LC :=
  | var  : nat -> LC
  | ttLC : LC
  | ffLC : LC
  | zero : LC
  | succ : LC -> LC
  | fixP : LC -> LC
  | ite  : LC -> LC -> LC -> LC
  | app  : LC -> LC -> LC
  | abs  : SimpleType -> LC -> LC.

  Definition Expr := LC.
  Definition ExprEqDec : forall e1 e2 : Expr, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality. apply Nat.eq_dec. apply SimpleTypeEqDec.
  Qed.
  Definition ExprVar : nat -> Expr := var.

  Fixpoint LCClosedBelow (n : nat) (e : LC) : Prop :=
    match e with
    | var m => if m <? n then True else False
    | ttLC => True
    | ffLC => True
    | zero => True
    | succ e' => LCClosedBelow n e'
    | fixP e' => LCClosedBelow n e'
    | ite b e1 e2 => LCClosedBelow n b /\ LCClosedBelow n e1 /\ LCClosedBelow n e2
    | app e1 e2 => LCClosedBelow n e1 /\ LCClosedBelow n e2                                
    | abs τ e' => LCClosedBelow (S n) e'
    end.
  Definition ExprClosedBelow := LCClosedBelow.
  Definition ExprClosed := ExprClosedBelow 0.
  
  Inductive LCVal : LC -> Prop :=
  | ttVal  : LCVal ttLC
  | ffVal  : LCVal ffLC
  | zeroVal : LCVal zero
  | succVal : forall e : Expr, LCVal e -> LCVal (succ e)
  | AbsVal : forall (τ : SimpleType) (e : LC), LCClosedBelow 1 e -> LCVal (abs τ e).
  Definition ExprVal := LCVal.

  Lemma ExprValuesClosed : forall v : Expr, ExprVal v -> ExprClosed v.
  Proof.
    intros v val_v; induction val_v; unfold ExprClosed; simpl; auto.
  Qed.

  Definition ExprUpRename : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S n' => S (ξ n')
            end.
  
  Fixpoint ExprRename (e : Expr) (ξ : nat -> nat) : Expr :=
    match e with
    | var n => var (ξ n)
    | ttLC => ttLC
    | ffLC => ffLC
    | zero => zero
    | succ e' => succ (ExprRename e' ξ)
    | fixP e' => fixP (ExprRename e' ξ)
    | ite b e1 e2 => ite (ExprRename b ξ) (ExprRename e1 ξ) (ExprRename e2 ξ)
    | app e1 e2 => app (ExprRename e1 ξ) (ExprRename e2 ξ)
    | abs τ e => abs τ (ExprRename e (ExprUpRename ξ))
    end.
  Notation "e ⟨e| ξ ⟩" := (ExprRename e ξ) (at level 29).

  Lemma ExprRenameExt : forall (e : Expr) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n) -> e ⟨e| ξ1⟩ = e ⟨e| ξ2⟩.
  Proof.
    intro e; induction e; intros ξ1 ξ2 ext_eq; simpl; auto.
    1,2: rewrite IHe with (ξ2 := ξ2); auto.
    1,2: rewrite IHe1 with (ξ2 := ξ2); auto; rewrite IHe2 with (ξ2 := ξ2); auto.
    - rewrite IHe3 with (ξ2 := ξ2); auto.
    - rewrite IHe with (ξ2 := ExprUpRename ξ2); auto.
      intro n; unfold ExprUpRename; destruct n; auto.
  Qed.
  
  Definition ExprUpSubst : (nat -> Expr) -> nat -> Expr :=
    fun σ n => match n with
            | 0 => var 0
            | S n' => σ n' ⟨e| S ⟩
            end.
  Fixpoint ExprSubst (e : Expr) (σ : nat -> Expr) : Expr :=
    match e with
    | var n => σ n
    | ttLC => ttLC
    | ffLC => ffLC
    | zero => zero
    | succ e' => succ (ExprSubst e' σ)
    | fixP e' => fixP (ExprSubst e' σ)
    | ite b e1 e2 => ite (ExprSubst b σ) (ExprSubst e1 σ) (ExprSubst e2 σ)
    | app e1 e2 => app (ExprSubst e1 σ) (ExprSubst e2 σ)
    | abs τ e => abs τ (ExprSubst e (ExprUpSubst σ))
    end.
  Notation "e [e| σ ]" := (ExprSubst e σ) (at level 29).

  Lemma ExprSubstExt : forall (e : Expr) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n)
      -> e [e| σ1] = e [e| σ2].
  Proof.
    intro e; induction e; intros σ1 σ2 ext_eq; simpl; auto.
    1,2: rewrite IHe with (σ2 := σ2); auto.
    1,2: rewrite IHe1 with (σ2 := σ2); auto; rewrite IHe2 with (σ2 := σ2); auto.
    - rewrite IHe3 with (σ2 := σ2); auto.
    - rewrite IHe with (σ2 := ExprUpSubst σ2); auto.
      intro n; unfold ExprUpSubst; destruct n; simpl; auto.
      rewrite ext_eq; reflexivity.
  Qed.
  
  Lemma ExprRenameSpec : forall (e : Expr) (ξ : nat -> nat),
      e ⟨e| ξ⟩ = e [e| fun n => ExprVar (ξ n)].
  Proof.
    intros e; induction e; intro ξ; simpl; auto.
    1,2: rewrite IHe; reflexivity.
    1,2: rewrite IHe1; rewrite IHe2; try (rewrite IHe3); reflexivity.
    rewrite IHe. unfold ExprUpSubst. unfold ExprUpRename.
    erewrite ExprSubstExt; [reflexivity |].
    intro n; destruct n; simpl; auto.
  Qed.

  Definition ExprSubstVar : forall n σ, (ExprVar n) [e| σ] = σ n := fun n σ => eq_refl.
  Lemma ExprRenameVar : forall n ξ, (ExprVar n) ⟨e| ξ ⟩ = ExprVar (ξ n).
  Proof.
    intros n ξ.
    rewrite ExprRenameSpec. rewrite ExprSubstVar. reflexivity.
  Qed.
  
  Lemma ExprRenameFusion : forall (e : Expr) (ξ1 ξ2 : nat -> nat),
      (e ⟨e| ξ1⟩) ⟨e| ξ2⟩ = e ⟨e| fun n => ξ2 (ξ1 n)⟩.
  Proof.
    intro e; induction e; intros ξ1 ξ2; simpl; auto.
    1,2,5: rewrite IHe; try (reflexivity).
    2,3: rewrite IHe1; rewrite IHe2; try (rewrite IHe3); reflexivity.
    rewrite ExprRenameExt with (ξ2 := ExprUpRename (fun n => ξ2 (ξ1 n))); auto.
    intro n; unfold ExprUpRename; destruct n; simpl; auto.
  Qed.
  
  Definition ExprIdSubst : nat -> Expr := fun n => ExprVar n.

  Lemma ExprIdentitySubstSpec : forall (e : Expr), e [e| ExprIdSubst] = e.
  Proof.
    intro e; induction e; simpl; auto.
    3,4: rewrite IHe1; rewrite IHe2; try (rewrite IHe3); reflexivity.
    1,2: rewrite IHe; auto.
    rewrite <- IHe at 2. erewrite ExprSubstExt; [reflexivity |].
    intro n; unfold ExprUpSubst; unfold ExprIdSubst; destruct n; auto.
  Qed.

  Definition ExprIdRenaming : nat -> nat := fun n => n.
  Lemma ExprIdRenamingSpec : forall (e : Expr), e ⟨e| ExprIdRenaming ⟩ = e.
  Proof.
    intro e; induction e; simpl; auto.
    3,4: rewrite IHe1; rewrite IHe2; try (rewrite IHe3); reflexivity.
    1,2: rewrite IHe; reflexivity.
    rewrite <- IHe at 2. erewrite ExprRenameExt; [reflexivity |].
    intro n; unfold ExprUpRename; unfold ExprIdRenaming; destruct n; auto.
  Qed.
    
  Lemma ExprUpSubstId : forall n, ExprIdSubst n = (ExprUpSubst ExprIdSubst) n.
  Proof.
    intros n; unfold ExprUpSubst; destruct n.
    - unfold ExprIdSubst; reflexivity.
    - unfold ExprIdSubst. rewrite ExprRenameVar. reflexivity.
  Qed.
  Lemma ExprUpRenamingId : forall n, ExprIdRenaming n = ExprUpRename ExprIdRenaming n.
  Proof.
    intros n; unfold ExprUpRename; destruct n; unfold ExprIdRenaming; reflexivity.
  Qed.

  Definition tt := ttLC.
  Definition ff := ffLC.
  Lemma ttValue : ExprVal tt. Proof. constructor. Qed.
  Lemma ffValue : ExprVal ff. Proof. constructor. Qed.

  Definition LCStepSubst : Expr -> (nat -> Expr) :=
    fun e n => match n with
            | 0 => e
            | S n' => ExprVar n'
            end.
  
  Inductive LCStep : Expr -> Expr -> Prop :=
  | succStep : forall (e1 e2 : Expr),
      LCStep e1 e2
      -> LCStep (succ e1) (succ e2)
  | iteEStep : forall (b1 b2 e1 e2 : Expr),
      LCStep b1 b2
      -> LCStep (ite b1 e1 e2) (ite b2 e1 e2)
  | iteTTStep : forall (e1 e2 : Expr),
      LCStep (ite tt e1 e2) e1
  | iteFFStep : forall (e1 e2 : Expr),
      LCStep (ite ff e1 e2) e2
  | fixPStep : forall (e : Expr),
      LCStep (fixP e) (app e (fixP e))
  | appAbsStep : forall (τ : SimpleType) (e1 e2 : Expr),
      ExprVal e2
      -> LCStep (app (abs τ e1) e2) (ExprSubst e1 (LCStepSubst e2))
  | appFStep : forall e1 e1' e2 : Expr,
      LCStep e1 e1'
      -> LCStep (app e1 e2) (app e1' e2)
  | appArgStep : forall e1 e2 e2' : Expr,
      LCStep e2 e2'
      -> LCStep (app e1 e2) (app e1 e2').
  Hint Constructors LCStep : LC.
  Definition ExprStep := LCStep.

End LambdaCalc.
