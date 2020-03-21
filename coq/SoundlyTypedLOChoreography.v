Require Export LOChoreography.
Require Export TypedLOChoreography.
Require Export Expression.
Require Export TypedExpression.
Require Export SoundlyTypedExpression.

Module SoundlyTypedChoreography (E : Expression) (TE : TypedExpression E) (STE : SoundlyTypedExpression E TE).
  Import E. Import TE. Import STE.
  Include (TypedChoreography E TE).

    Theorem Preservation :
    forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (C : Chor) (τ : ExprTyp) (p : Prin),
      Γ;; Δ ⊢c C ::: τ @ p -> forall (R : Redex) (B : list Prin) (C': Chor),
        RChorStep R B C C' -> Γ;; Δ ⊢c C' ::: τ @ p.
    Proof.
      apply RelativePreservation. intros Γ e τ H e' H0.
      apply ExprPreservation with (e1 := e); auto.
    Qed.

    Theorem Progress :
    forall (C : Chor) (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (τ : ExprTyp) (p : Prin),
      ChorClosed C -> Γ;; Δ ⊢c C ::: τ @ p ->
      ChorVal C \/ exists R C', RChorStep R nil C C'.
    Proof.
      apply RelativeProgress; auto.
      intros e τ Γ H H0; eapply ExprProgress; eauto.
      intros v Γ H H0; eapply BoolInversion; eauto.
    Qed.
End SoundlyTypedChoreography.


