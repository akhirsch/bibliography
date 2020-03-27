Require Export Expression.
Require Export TypedExpression.
Require Export SoundlyTypedExpression.
Require Export LambdaCalc.
Require Export STLC.

Module STLCSound <: (SoundlyTypedExpression LambdaCalc STLC).
  Import LambdaCalc.
  Import STLC.
  Theorem BoolInversion : forall (Γ : nat -> ExprTyp) (v : Expr),
      Γ ⊢e v ::: bool ->
      ExprVal v ->
      {v = tt} + {v = ff}.
  Proof.
    intros Γ v H H0.
    destruct v; auto; exfalso; inversion H0; inversion H.
  Qed.

  Theorem LCStepSubstTyping : forall (Γ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
      Γ ⊢e e ::: τ
      -> (fun n => match n with
               | 0 => τ
               | S n' => Γ n'
               end) ⊢es (LCStepSubst e) ⊣ Γ.
  Proof.
    intros Γ e τ H. unfold ExprSubstTyping.
    intro n. unfold LCStepSubst. destruct n; auto with LC.
  Qed.


  Theorem ExprPreservation : forall (Γ : nat -> ExprTyp) (e1 e2 : Expr) (τ : ExprTyp),
      Γ ⊢e e1 ::: τ -> ExprStep e1 e2 -> Γ ⊢e e2 ::: τ.
  Proof.
    intros Γ e1 e2 τ typing step; revert Γ τ typing; induction step;
      try (rename τ into σ); intros Γ τ typing; inversion typing; auto.
    all: try (constructor; auto; fail).
    - apply appTyping with (τ1 := τ); auto.
    - inversion H3; eapply ExprSubstType; [exact (LCStepSubstTyping Γ e2 τ1 H5)|auto].
    - apply appTyping with (τ1 := τ1); auto.
    - apply appTyping with (τ1 := τ1); auto.
  Qed.

  Theorem ExprProgress : forall (Γ : nat -> ExprTyp) (e1 : Expr) (τ : ExprTyp),
      Γ ⊢e e1 ::: τ -> ExprClosed e1 -> ExprVal e1 \/ exists e2, ExprStep e1 e2.
  Proof.
    intros Γ e1 τ typing; induction typing; simpl; intros closed; try (inversion closed).
    all: try (left; constructor; auto; fail).
    2: { unfold ExprClosed in *. simpl in closed. specialize (IHtyping closed).
         destruct IHtyping as [H|H];
           [left; constructor |right; destruct H as [e2 He2]; exists (succ e2); constructor];
           auto with LC. }
    all: right.
    - unfold ExprClosed in IHtyping1; specialize (IHtyping1 H).
      destruct IHtyping1 as [b_val | b_step].
      destruct b; inversion typing1; inversion b_val;
        [exists e1 | exists e2]; constructor; auto.
      destruct b_step as [b2 b_step]; exists (ite b2 e1 e2); constructor; auto.
    - exists (app e (fixP e)); constructor.
    - rename H into closed1; rename H0 into closed2;
        unfold ExprClosed in *; specialize (IHtyping1 closed1);
          specialize (IHtyping2 closed2).
      rename e1 into f; rename e2 into arg.
      destruct IHtyping1 as [f_val | f_step]; [| destruct f_step as [f' f_step]].
      -- destruct IHtyping2 as [arg_val | arg_step];
           [| destruct arg_step as [arg' arg_step]].
         destruct f; inversion typing1; inversion f_val; eexists; constructor; auto.
         exists (app f arg'); constructor; auto.
      -- exists (app f' arg); constructor; auto.
  Qed.
End STLCSound.
