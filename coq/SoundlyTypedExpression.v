Require Export Expression.
Require Export TypedExpression.

Module Type SoundlyTypedExpression (E : Expression) (TE : TypedExpression E).
  Import E.
  Import TE.

  Parameter BoolInversion : forall (Γ : nat -> ExprTyp) (v : Expr),
      Γ ⊢e v ::: bool ->
      ExprVal v ->
      {v = tt} + {v = ff}.
  
  Parameter ExprPreservation : forall (Γ : nat -> ExprTyp) (e1 e2 : Expr) (τ : ExprTyp),
      Γ ⊢e e1 ::: τ -> ExprStep e1 e2 -> Γ ⊢e e2 ::: τ.
  Parameter ExprProgress : forall (Γ : nat -> ExprTyp) (e1 : Expr) (τ : ExprTyp),
      Γ ⊢e e1 ::: τ -> ExprClosed e1 -> ExprVal e1 \/ exists e2, ExprStep e1 e2.
End SoundlyTypedExpression.                                  
