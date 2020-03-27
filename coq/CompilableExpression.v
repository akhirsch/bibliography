Require Export Expression.
Require Export TypedExpression.
Require Export MPST.

Module Type CompilableExpression (E : Expression) (TE : TypedExpression E).
  Import E. Import TE.

  Parameter ExprRole : MPST.Role.
  (* 
   * Session, 
   * type 
   *)
  Parameter ExprTypeCompile : nat -> ExprTyp -> MPST.SessionType.
  (* 
   * Session the main computation is taking place in, 
   * Principal receiving the expression, 
   * expression 
   *)
  Parameter ExprCompile : nat -> MPST.Role -> Expr -> MPST.PiCalc.
  Parameter ExprCompileTyping : forall (e : Expr) (s : nat) (p : MPST.Role) (Θ : nat)
                                  (Γ1 : nat -> ExprTyp)
                                  (Γ2 : MPST.Chan -> MPST.SessionType) (τ : ExprTyp),
      Γ1 ⊢e e ::: τ ->
      MPST.ProcessTyping Θ
                         (fun χ => if MPST.ChanEqDec χ (MPST.Session s ExprRole)
                                then MPST.SendT p (ExprTypeCompile s τ) MPST.EndType
                                else Γ2 χ)
                         (ExprCompile s p e).
  Parameter ExprCompileCorr : forall (e1 e2 : Expr) (s : nat) (p : MPST.Role),
      ExprStep e1 e2 ->
      MPST.PiRed (ExprCompile s p e1) (ExprCompile s p e2).
End CompilableExpression.
