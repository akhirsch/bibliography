Module Type Expression.
  Parameter Expr : Set.
  Parameter ExprEqDec : forall e1 e2 : Expr, {e1 = e2} + {e1 <> e2}.
  Parameter ExprVar : nat -> Expr.

  Parameter ExprVal : Expr -> Prop.
  Parameter ExprClosedBelow : nat -> Expr -> Prop.
  Definition ExprClosed := ExprClosedBelow 0.
  Parameter ExprValuesClosed : forall v : Expr, ExprVal v -> ExprClosed v.

  Parameter ExprSubst : Expr -> (nat -> Expr) -> Expr.
  Parameter ExprRename : Expr -> (nat -> nat) -> Expr.
  Notation "e [e| sigma ]" := (ExprSubst e sigma) (at level 29).
  Notation "e ⟨e| xi ⟩" := (ExprRename e xi) (at level 29).
  Parameter ExprRenameSpec : forall (e : Expr) (ξ : nat -> nat),
      e ⟨e| ξ⟩ = e [e| fun n => ExprVar (ξ n)].
  Parameter ExprSubstVar : forall n σ, (ExprVar n ) [e| σ] = σ n.
  Lemma ExprRenameVar : forall n ξ, (ExprVar n) ⟨e| ξ ⟩ = ExprVar (ξ n).
  Proof.
    intros n ξ.
    rewrite ExprRenameSpec. rewrite ExprSubstVar. reflexivity.
  Qed.

  Parameter ExprRenameFusion : forall (e : Expr) (ξ1 ξ2 : nat -> nat),
      (e ⟨e| ξ1⟩) ⟨e| ξ2⟩ = e ⟨e| fun n => ξ2 (ξ1 n)⟩.                        
  
  Definition ExprUpSubst : (nat -> Expr) -> nat -> Expr :=
    fun σ n =>
      match n with
      | 0 => ExprVar 0
      | S n => (σ n) ⟨e| S ⟩
      end.

  Definition ExprUpRename : (nat -> nat) -> nat -> nat :=
    fun ξ n =>
      match n with
      | 0 => 0
      | S n => S (ξ n)
      end.

  Parameter ExprSubstExt : forall (e : Expr) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n) -> e [e| σ1] = e [e| σ2].
  Parameter ExprRenameExt :forall (e : Expr) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n) -> e ⟨e| ξ1 ⟩= e ⟨e| ξ2⟩.
  
  Definition ExprIdSubst : nat -> Expr := fun n => ExprVar n.
  Parameter ExprIdentitySubstSpec : forall (e : Expr), e [e| ExprIdSubst] = e.
  Definition ExprIdRenaming : nat -> nat := fun n => n.
  Parameter ExprIdRenamingSpec : forall (e : Expr), e ⟨e| ExprIdRenaming ⟩ = e.
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

  Parameter tt ff : Expr.
  Parameter ttValue : ExprVal tt.
  Parameter ffValue : ExprVal ff.
  
  Parameter ExprStep : Expr -> Expr -> Prop.
End Expression.
