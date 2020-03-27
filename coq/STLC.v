Require Export Expression.
Require Export TypedExpression.
Require Export LambdaCalc.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Module STLC <: (TypedExpression LambdaCalc).
  Include LambdaCalc.

  Definition ExprTyp := SimpleType.
  Definition ExprTypEqDec := SimpleTypeEqDec.
  Definition bool := boolType.

  Reserved Notation "Γ ⊢e e ::: τ" (at level 30).
  Inductive LCTyping : (nat -> ExprTyp) -> Expr -> ExprTyp -> Prop :=
  | ttTyping : forall (Γ : nat -> ExprTyp), Γ ⊢e tt ::: bool
  | ffTyping : forall (Γ : nat -> ExprTyp), Γ ⊢e ff ::: bool
  | iteTyping : forall (Γ : nat -> ExprTyp) (b e1 e2 : Expr) (τ : ExprTyp),
      Γ ⊢e b ::: bool
      -> Γ ⊢e e1 ::: τ
      -> Γ ⊢e e2 ::: τ
      -> Γ ⊢e (ite b e1 e2) ::: τ
  | zeroTyping : forall (Γ : nat -> ExprTyp),
      Γ ⊢e zero ::: natType
  | succTyping : forall (Γ : nat -> ExprTyp) (e : Expr),
      Γ ⊢e e ::: natType
      -> Γ ⊢e succ e ::: natType
  | fixTyping : forall (Γ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
      Γ ⊢e e ::: ArrowT τ τ
      -> Γ ⊢e fixP e ::: τ
  | varTyping : forall (Γ : nat -> ExprTyp) (n : nat), Γ ⊢e (var n) ::: (Γ n)
  | appTyping : forall (Γ : nat -> ExprTyp) (e1 e2 : Expr) (τ1 τ2 : ExprTyp),
      Γ ⊢e e1 ::: (ArrowT τ1 τ2)
      -> Γ ⊢e e2 ::: τ1
      -> Γ ⊢e (app e1 e2) ::: τ2
  | absTyping : forall (Γ : nat -> ExprTyp) (e : Expr) (τ1 τ2 : ExprTyp),
      (fun n => match n with
             | 0 => τ1
             | S n' => Γ n'
             end) ⊢e e ::: τ2
      -> Γ ⊢e (abs τ1 e) ::: (ArrowT τ1 τ2)
  where "Γ ⊢e e ::: τ" := (LCTyping Γ e τ).
  Hint Constructors LCTyping : LC.
  Definition ExprTyping := LCTyping.
  Definition ExprVarTyping := varTyping.

  Theorem ExprTypingExt : forall (Γ Δ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
      (forall n, Γ n = Δ n) ->
      Γ ⊢e e ::: τ ->
      Δ ⊢e e ::: τ.
  Proof.
    intros Γ Δ e τ ext_eq typing; revert Δ ext_eq; induction typing; intros Δ ext_eq;
      auto with LC.
    rewrite ext_eq; constructor.
    econstructor; [apply IHtyping1 | apply IHtyping2]; auto.
    econstructor; apply IHtyping; auto.
    intro n; destruct n; simpl; auto.
  Qed.

  Theorem ExprTypingUnique : forall (Γ : nat -> ExprTyp) (e : Expr) (τ σ : ExprTyp),
      Γ ⊢e e ::: τ ->
      Γ ⊢e e ::: σ ->
      τ = σ.
  Proof.
    intros Γ e τ σ typing1; revert σ; induction typing1;
      intros σ typing2; inversion typing2; auto.
    - apply IHtyping1 in H1; inversion H1; reflexivity.
    - apply IHtyping1_1 in H2; inversion H2; reflexivity.
    - rewrite IHtyping1 with (σ := τ3); auto.
  Qed.

  Theorem ExprWeakening : forall (Γ Δ : nat -> ExprTyp) (ξ : nat -> nat) (e : Expr) (τ : ExprTyp),
      (forall n, Γ n = Δ (ξ n)) ->
      Γ ⊢e e ::: τ ->
      Δ ⊢e e ⟨e| ξ⟩ ::: τ.
  Proof.
    intros Γ Δ ξ e τ weak typing; revert Δ ξ weak; induction typing;
      intros Δ ξ weak; simpl; auto with LC.
    - rewrite weak; auto with LC.
    - apply appTyping with (τ1 := τ1); auto.
    - apply absTyping; apply IHtyping;
        intro n; unfold ExprUpRename; destruct n; simpl; auto.
  Qed.

  Definition ExprClosedBelowTyping : forall (Γ Δ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp) (n : nat),
      ExprClosedBelow n e -> (forall m, m < n -> Γ m = Δ m) -> Γ ⊢e e ::: τ -> Δ ⊢e e ::: τ.
  Proof.
    intros Γ Δ e τ n e_cb ext_eq typing; revert Δ n e_cb ext_eq; induction typing;
      try (rename n into n'); intros Δ n e_cb ext_eq; simpl in e_cb; eauto with LC.
    - destruct e_cb as [b_cb H]; destruct H as [e1_cb e2_cb].
      apply iteTyping;
        [ apply IHtyping1 with (n := n)
        | apply IHtyping2 with (n := n)
        | apply IHtyping3 with (n := n)]; auto.
    - destruct (n' <? n) eqn:e ;[rewrite Nat.ltb_lt in e; clear e_cb | destruct e_cb].
      rewrite ext_eq; auto with LC.
    - destruct e_cb; apply appTyping with (τ1 := τ1).
      apply IHtyping1 with (n := n); auto.
      apply IHtyping2 with (n := n); auto.
    - apply absTyping; apply IHtyping with (n := S n); auto.
      intros m lt_n_m; destruct m; auto. apply ext_eq. apply Lt.lt_S_n; auto.
  Qed.

    Lemma ExprClosedTyping : forall (Γ Δ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
      ExprClosed e -> Γ ⊢e e ::: τ -> Δ ⊢e e ::: τ.
  Proof.
    intros Γ Δ e τ H H0. unfold ExprClosed in H.
    apply ExprClosedBelowTyping with (Γ := Γ) (n := 0); auto.
    intros m H1. inversion H1.
  Qed.
  Lemma ExprValueTyping : forall (Γ Δ : nat -> ExprTyp) (v : Expr) (τ : ExprTyp),
      ExprVal v -> Γ ⊢e v ::: τ -> Δ ⊢e v ::: τ.
  Proof.
    intros Γ Δ v τ H H0. apply ExprClosedTyping with (Γ := Γ); auto.
    apply ExprValuesClosed; auto.
  Qed.

  Lemma TrueTyping : forall (Γ : nat -> ExprTyp),
      Γ ⊢e tt ::: bool.
  Proof.
    intros Γ; constructor.
  Qed.
  Lemma FalseTyping : forall (Γ : nat -> ExprTyp),
      Γ ⊢e ff ::: bool.
  Proof.
    intros Γ; constructor.
  Qed.

    Definition ExprSubstTyping : (nat -> ExprTyp) -> (nat -> Expr) -> (nat -> ExprTyp) -> Prop :=
    fun Γ σ Δ => forall n : nat, Δ ⊢e (σ n) ::: (Γ n).
  Notation "Gamma ⊢es sigma ⊣ Delta"  := (ExprSubstTyping Gamma sigma Delta) (at level 30).
  Parameter ExprSubstType :
    forall (Γ Δ : nat -> ExprTyp) (sigma : nat -> Expr) (e : Expr) (τ : ExprTyp),
      Γ ⊢es sigma ⊣ Δ -> Γ ⊢e e ::: τ -> Δ ⊢e e [e| sigma ] ::: τ.
  Lemma ExprIdSubstTyping : forall (Γ : nat -> ExprTyp), Γ ⊢es ExprIdSubst ⊣ Γ.
  Proof.
    unfold ExprSubstTyping. intros Γ n. unfold ExprIdSubst. apply ExprVarTyping.
  Qed.                                                   

  Lemma ExprSubstLWeakening : forall (Γ Δ1 Δ2 : nat -> ExprTyp) (σ : nat -> Expr) (ξ : nat -> nat),
      (forall n, Δ1 n = Δ2 (ξ n)) ->
      Γ ⊢es σ ⊣ Δ1 ->
      Γ ⊢es fun n => (σ n) ⟨e|ξ⟩ ⊣ Δ2.
  Proof.
    intros Γ Δ1 Δ2 σ ξ subΔ typing.
    unfold ExprSubstTyping in *; intro n.
    eapply ExprWeakening; eauto.
  Qed.

  Lemma ExprSubstRWeakening : forall (Γ1 Γ2 Δ : nat -> ExprTyp) (σ : nat -> Expr) (ξ : nat -> nat),
      (forall n, Γ1 (ξ n) = Γ2 n) ->
      Γ1 ⊢es σ ⊣ Δ ->
      Γ2 ⊢es fun n => σ (ξ n) ⊣ Δ.
  Proof.
    intros Γ1 Γ2 Δ σ ξ subΓ typing.
    unfold ExprSubstTyping in *; intro n.
    rewrite <- subΓ. apply typing.
  Qed.
  
  Lemma ExprSubstTypeExpand : forall (Γ Δ : nat -> ExprTyp) (σ : nat -> Expr),
      Γ ⊢es σ ⊣ Δ ->
      forall τ : ExprTyp, ExprSubstTyping (fun n => match n with | 0 => τ | S n => Γ n end)
                                     (ExprUpSubst σ)
                                     (fun n => match n with |0 => τ | S n => Δ n end).
  Proof.
    intros Γ Δ σ typing τ.
    unfold ExprUpSubst.
    unfold ExprSubstTyping in *.
    intro m.
    unfold ExprUpSubst. destruct m; simpl.
    apply ExprVarTyping.
    apply ExprWeakening with (Γ := Δ); auto.
  Qed.
  
End STLC.
