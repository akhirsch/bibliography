Require Export Choreography.
Require Export TypedChoreography.
Require Export Expression.
Require Export TypedExpression.
Require Export SoundlyTypedExpression.

Module SoundlyTypedChoreography (E : Expression) (TE : TypedExpression E) (STE : SoundlyTypedExpression E TE) (L : Locations).
  Import E. Import TE. Import STE.
  Include (TypedChoreography L E TE).

    Theorem Preservation :
    forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (C : Chor) (τ : ExprTyp) (p : L.t),
      Γ;; Δ ⊢c C ::: τ @ p -> forall (R : Redex) (B : list L.t) (C': Chor),
        RChorStep R B C C' -> Γ;; Δ ⊢c C' ::: τ @ p.
    Proof.
      apply RelativePreservation. intros Γ e τ H e' H0.
      apply ExprPreservation with (e1 := e); auto.
    Qed.

    Theorem Progress :
    forall (C : Chor) (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (τ : ExprTyp) (p : L.t),
      ChorClosed C -> Γ;; Δ ⊢c C ::: τ @ p ->
      ChorVal C \/ exists R C', RChorStep R nil C C'.
    Proof.
      apply RelativeProgress; auto.
      intros e τ Γ H H0; eapply ExprProgress; eauto.
      intros v Γ H H0; eapply BoolInversion; eauto.
    Qed.
End SoundlyTypedChoreography.


