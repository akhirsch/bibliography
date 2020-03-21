Require Export Expression.

Module Type TypedExpression (E : Expression).
  Import E.

  Parameter ExprTyp : Set.
  Parameter ExprTypEqDec : forall tau sigma : ExprTyp, {tau = sigma} + {tau <> sigma}.
  
  Parameter ExprTyping : (nat -> ExprTyp) -> Expr -> ExprTyp -> Prop.
  Notation "Gamma ⊢e e ::: tau" := (ExprTyping Gamma e tau) (at level 30).

  Parameter ExprVarTyping : forall (Γ : nat -> ExprTyp) (n : nat),
      Γ ⊢e (ExprVar n) ::: (Γ n).
  
  Parameter ExprTypingExt : forall (Γ Δ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
      (forall n, Γ n = Δ n) ->
      Γ ⊢e e ::: τ ->
      Δ ⊢e e ::: τ.

  Parameter ExprTypingUnique : forall (Γ : nat -> ExprTyp) (e : Expr) (τ σ : ExprTyp),
      Γ ⊢e e ::: τ ->
      Γ ⊢e e ::: σ ->
      τ = σ.

  Parameter ExprWeakening : forall (Γ Δ : nat -> ExprTyp) (ξ : nat -> nat) (e : Expr) (τ : ExprTyp),
      (forall n, Γ n = Δ (ξ n)) ->
      Γ ⊢e e ::: τ ->
      Δ ⊢e e ⟨e| ξ⟩ ::: τ.

  Parameter ExprClosedBelowTyping : forall (Γ Δ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp) (n : nat),
      ExprClosedBelow n e -> (forall m, m < n -> Γ m = Δ m) -> Γ ⊢e e ::: τ -> Δ ⊢e e ::: τ.
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
  
  Parameter bool : ExprTyp.
  Parameter TrueTyping : forall (Γ : nat -> ExprTyp),
      Γ ⊢e tt ::: bool.
  Parameter FalseTyping : forall (Γ : nat -> ExprTyp),
      Γ ⊢e ff ::: bool.

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
  
End TypedExpression.
