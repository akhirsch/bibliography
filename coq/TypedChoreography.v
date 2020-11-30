Require Export Expression.
Require Export TypedExpression.
Require Export Choreography.

Module TypedChoreography (L : Locations) (E : Expression) (TE : TypedExpression E).
  Import E.
  Import TE.
  Include (Choreography E L).

  Reserved Notation "G ;; D ⊢c C ::: tau @ p" (at level 30).
  Inductive ctyping : (Loc -> nat -> ExprTyp) -> (nat -> Loc * ExprTyp) -> Chor -> ExprTyp -> Loc -> Prop :=
  | TDone : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
              (p : Loc) (e : Expr) (tau : ExprTyp),
       (Γ p) ⊢e e ::: tau ->
  (* ------------------------------ *)
      Γ ;; Δ ⊢c Done p e ::: tau @ p
  | TVar : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp) (n : nat),
  (* ----------------------------- *)
      Γ ;; Δ ⊢c Var n ::: snd (Δ n) @ fst (Δ n)
  | TSend : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
              (p : Loc) (e : Expr) (τ : ExprTyp) (q : Loc) (C : Chor) (r : Loc) (sigma : ExprTyp),
      (Γ p) ⊢e e ::: τ ->
      (fun r n => if L.eq_dec q r
               then match n with
                    | 0 => τ
                    | S n => Γ r n
                    end
               else Γ r n);; Δ ⊢c C ::: sigma @ r ->
      p <> q ->
  (* --------------------------------------- *)
      Γ ;; Δ ⊢c (Send p e q C) ::: sigma @ r
  | TIf : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
            (p : Loc) (e : Expr) (C1 C2 : Chor) (q : Loc) (tau : ExprTyp),
      (Γ p) ⊢e e ::: bool ->
      Γ ;; Δ ⊢c C1 ::: tau @ q ->
      Γ ;; Δ ⊢c C2 ::: tau @ q ->
  (* --------------------------------- *)
      Γ;; Δ ⊢c If p e C1 C2 ::: tau @ q
  | TSync : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
              (p : Loc) (d : LRChoice) (q : Loc) (C : Chor) (τ : ExprTyp) (r : Loc),
      Γ ;; Δ ⊢c C ::: τ @ r ->
  (* ---------------------------------- *)
      Γ ;; Δ ⊢c Sync p d q C ::: τ @ r
  | TDefLocal : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
                  (p : Loc) (C1 C2 : Chor) (τ σ : ExprTyp) (q : Loc),
      Γ ;; Δ ⊢c C1 ::: τ @ p ->
      (fun r n =>
         if L.eq_dec p r
         then match n with
              | 0 => τ
              | S n => Γ r n
              end
         else Γ r n);; Δ ⊢c C2 ::: σ @ q ->
  (* ------------------------------------*)
      Γ ;; Δ ⊢c DefLocal p C1 C2 ::: σ @ q
  | TDefGlobal : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
                   (C1 C2 : Chor) (p q : Loc) (τ σ : ExprTyp),
      Γ;; (fun n =>
            match n with
            | 0 => (q, σ)
            | S n => Δ n
            end) ⊢c C1 ::: σ @ q ->
      Γ;; (fun n =>
            match n with
            | 0 => (q, σ)
            | S n => Δ n
            end) ⊢c C2 ::: τ @ p ->
  (* ---------------------------------------- *)
      Γ;; Δ ⊢c DefGlobal C1 C2 ::: τ @ p
  where "Gamma ;; Delta ⊢c C ::: tau @ p" := (ctyping Gamma Delta C tau p).
  Hint Constructors ctyping : Chor.


  Theorem TypeExprWeakening : forall (Γ1 Γ2 : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp)
                               (ξ : Loc -> nat -> nat),
      (forall p n, Γ1 p n = Γ2 p (ξ p n)) ->
      forall (τ : ExprTyp) (p : Loc) (C : Chor),
        Γ1;; Δ ⊢c C ::: τ @ p ->
        Γ2;; Δ ⊢c C⟨ce| ξ⟩ ::: τ @ p.
  Proof using.
    intros Γ1 Γ2 Δ ξ eqv τ p C typing; revert Γ2 ξ eqv; induction typing; intros Γ2 ξ eqv;
      cbn; repeat match goal with
                  | [ H : ?Γ ?p ⊢e ?e ::: ?t, eqv : forall p n, ?Γ p n = ?Γ2 p (?ξ p n) |- _] =>
                    lazymatch goal with
                    | [_ : Γ2 p ⊢e e ⟨e| ξ p ⟩ ::: t |- _ ] => fail
                    | _ => pose proof (ExprWeakening (Γ p) (Γ2 p) (ξ p) e t (eqv p) H)
                    end
                  end; auto with Chor.
    - apply TSend with (τ := τ); auto; apply IHtyping.
      intros p0 n; unfold ChorUpExprRename; unfold ExprUpRename;
        destruct (L.eq_dec q p0); destruct n; auto.
    - apply TDefLocal with (τ := τ); auto; apply IHtyping2.
      intros p0 n; unfold ChorUpExprRename; unfold ExprUpRename;
        destruct (L.eq_dec p p0); destruct n; auto.
    - apply TDefGlobal with (q := q) (σ := σ); auto.
  Qed.
      
  Theorem TypeChorWeakening : forall (Γ : Loc -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Loc * ExprTyp)
                                (ξ : nat -> nat),
      (forall n, Δ1 n = Δ2 (ξ n)) ->
      forall (τ : ExprTyp) (p : Loc) (C : Chor),
        Γ ;; Δ1 ⊢c C ::: τ @ p ->
        Γ ;; Δ2 ⊢c C ⟨c| ξ⟩ ::: τ @ p.
  Proof using.
    intros Γ Δ1 Δ2 ξ eqv τ p C typing; revert Δ2 ξ eqv; induction typing;
      intros Δ2 ξ eqv; cbn; eauto with Chor.
    - rewrite eqv; apply TVar.
    - apply TDefGlobal with (q := q) (σ := σ); auto with Chor.
      apply IHtyping1; intro n; unfold ChorUpRename; destruct n; auto.
      apply IHtyping2; intro n; unfold ChorUpRename; destruct n; auto.
  Qed.
  
  Theorem ChorTypingExt : forall (Γ1 Γ2 : Loc -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Loc * ExprTyp)
                            (C : Chor) (p : Loc) (τ : ExprTyp),
      (forall (p : Loc) (n : nat), Γ1 p n = Γ2 p n) ->
      (forall n : nat, Δ1 n = Δ2 n) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C p τ eqΓ eqΔ typing; revert Γ2 Δ2 eqΓ eqΔ; induction typing;
      intros Γ2 Δ2 eqΓ eqΔ;
      repeat match goal with
             | [ H : ?Γ ?p ⊢e ?e ::: ?t, eqv : forall p n, ?Γ p n = ?Γ2 p n |- _ ] =>
               lazymatch goal with
               | [_ : Γ2 p ⊢e e ::: t |- _ ] => fail
               | _ => pose proof (ExprTypingExt (Γ p) (Γ2 p) e t (eqv p) H)
               end
             end; auto with Chor.
    - rewrite eqΔ; auto with Chor.
    - apply TSend with (τ := τ); auto with Chor; apply IHtyping; auto.
      intros p0 n; destruct (L.eq_dec q p0); destruct n; auto.
    - apply TDefLocal with (τ := τ); auto with Chor; apply IHtyping2; auto.
      intros p0 n; destruct (L.eq_dec p p0); destruct n; auto.
    - apply TDefGlobal with (q := q) (σ := σ); auto with Chor;
        [apply IHtyping1 | apply IHtyping2]; auto; intro n; destruct n; auto.
  Qed.

  Definition ChorSubstTyping Γ Δ1 σ Δ2 :=
    (forall (n : nat), Γ;; Δ2 ⊢c (σ n) ::: (snd (Δ1 n)) @ (fst (Δ1 n))).

  Theorem ChorExprSubstTypingSpec : forall Γ1 σ Γ2 Δ C p τ,
      (forall q, Γ1 q ⊢es σ q ⊣ Γ2 q) -> Γ1 ;; Δ ⊢c C ::: τ @ p -> Γ2 ;; Δ ⊢c C [ce| σ] ::: τ @ p.
  Proof using.
    intros Γ1 σ Γ2 Δ C p τ eqv typing; revert σ Γ2 eqv; induction typing; intros σ' Γ2 eqv;
      cbn; repeat match goal with
                  | [ H : ?Γ ?p ⊢e ?e ::: ?t, eqv : forall q, ?Γ q ⊢es ?σ' q ⊣ ?Γ2 q |- _] =>
                    lazymatch goal with
                    | [ _ : Γ2 p ⊢e e [e|σ' p] ::: t |- _] => fail
                    | _ => pose proof (ExprSubstType (Γ p) (Γ2 p) (σ' p) e t (eqv p) H)
                    end
                  end; eauto with Chor.
    - apply TSend with (τ := τ); auto; apply IHtyping.
      intro q0; unfold ExprSubstTyping; intro n; unfold ChorUpExprSubst;
        destruct (L.eq_dec q q0); destruct n; auto.
      apply ExprVarTyping. apply ExprWeakening with (Γ := Γ2 q0); auto.
      all: apply eqv.
    - apply TDefLocal with (τ := τ); auto; apply IHtyping2; auto.
      intro q0; unfold ChorUpExprSubst; intro n;
        destruct (L.eq_dec p q0); destruct n; auto with Chor.
      apply ExprVarTyping. apply ExprWeakening with (Γ := Γ2 q0); auto.
      all: apply eqv.
  Qed.      
         

  Lemma TypingLocalUp :forall Γ Δ C τ p,
      Γ ;; Δ ⊢c C ::: τ @ p ->
      forall q σ, (fun r n => if L.eq_dec r q
                      then match n with
                           | 0 => σ
                           | S n => Γ r n
                           end
                      else Γ r n) ;; Δ ⊢c C ⟨ce| fun p n => if L.eq_dec q p then S n else n ⟩ ::: τ @ p.
  Proof using.
    intros Γ Δ C τ p H q σ.
    apply TypeExprWeakening with (Γ1 := Γ); auto.
    intros p0 n; destruct (L.eq_dec q p0); subst.
    destruct (L.eq_dec p0 p0) as [_ | neq]; [|destruct (neq eq_refl)]; auto.
    destruct (L.eq_dec p0 q) as [eq | _ ]; [destruct (n0 (eq_sym eq))|] ;auto.
  Qed.
  
  Theorem ChorSubstTypingSpec : forall Γ Δ1 σ Δ2,
      (ChorSubstTyping Γ Δ1 σ Δ2) ->
      forall (C : Chor) (τ : ExprTyp) (p : Loc),
        (Γ;; Δ1 ⊢c C ::: τ @ p) -> (Γ;; Δ2 ⊢c (C [c| σ]) ::: τ @ p).
  Proof.
    intros Γ Δ1 σ Δ2 styping C τ p typing; revert σ Δ2 styping; induction typing;
      try rename σ into ρ; intros σ Δ2 styping; cbn; auto with Chor.
    - apply TSend with (τ := τ); auto. apply IHtyping.
      unfold ChorSubstTyping. intro n. unfold ChorSubstTyping in styping.
      unfold ChorUpSubstForExpr. apply TypeExprWeakening with (Γ1 := Γ); auto.
      intros p0 n0; destruct (L.eq_dec q p0); auto.
    - apply TDefLocal with (τ := τ). apply IHtyping1; auto.
      unfold ChorUpSubstForExpr. apply IHtyping2. unfold ChorSubstTyping.
      intro n; apply TypeExprWeakening with (Γ1 := Γ); auto.
      intros p0 n0; destruct (L.eq_dec p p0); auto.
    - apply TDefGlobal with (σ := ρ) (q := q); auto.
      apply IHtyping1. unfold ChorSubstTyping; unfold ChorUpSubst.
      intro n. destruct n. apply TVar. apply TypeChorWeakening with (Δ1 := Δ2); auto.
      apply IHtyping2. unfold ChorSubstTyping; unfold ChorUpSubst.
      intro n. destruct n. apply TVar. apply TypeChorWeakening with (Δ1 := Δ2); auto.
  Qed.

  Lemma SendExprSubstTyping: forall (Γ : Loc -> nat -> ExprTyp) (p : Loc) (e : Expr) (τ : ExprTyp),
      (Γ p ⊢e e ::: τ) ->
      forall q, ((fun r n => if L.eq_dec p r
                     then match n with
                          | 0 => τ
                          | S n => Γ r n
                          end
                     else Γ r n) q) ⊢es SendExprSubst p e q ⊣ (Γ q).
  Proof using.
    intros Γ p e τ tpng q. unfold SendExprSubst.
    unfold ExprSubstTyping. intro n. destruct n; destruct (L.eq_dec p q); subst; auto.
    all: apply ExprVarTyping.
  Qed.

  Lemma DefSubstTyping : forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp) (C : Chor) (p : Loc) (τ : ExprTyp),
      Γ ;; (fun n => match n with
                  | 0 => (p, τ)
                  | S n => Δ n
                  end) ⊢c C ::: τ @ p ->
      ChorSubstTyping Γ (fun n => match n with
                               | 0 => (p, τ)
                               | S n => Δ n
                               end) (DefSubst C) Δ.
  Proof using.
    intros Γ Δ C p τ H. unfold ChorSubstTyping; unfold DefSubst.
    intro n; destruct n; cbn; auto; [|apply TVar].
    assert (ChorSubstTyping Γ (fun n => match n with
                                     | 0 => (p, τ)
                                     | S n0 => Δ n0
                                     end)
                            (fun n => match n with
                                   | 0 => LetGlobal ⟪new⟫ ← C fby C
                                   | S n0 => Var n0
                                   end) Δ); [|eapply ChorSubstTypingSpec; eauto].
    unfold ChorSubstTyping; intro n; destruct n.
    apply TDefGlobal with (q := p) (σ := τ); auto. apply TVar.
  Qed.

  Theorem ChorEquivTyping : forall (C1 C2 : Chor),
      C1 ≡ C2 ->
      forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp) (τ : ExprTyp) (p : Loc),
        Γ ;; Δ ⊢c C1 ::: τ @ p -> Γ ;; Δ ⊢c C2 ::: τ @ p.
  Proof using.
    intros C1 C2 equiv; induction equiv; intros Γ Δ τ p typ; auto with Chor;
      repeat match goal with
             | [ H : ?Γ ;; ?Δ ⊢c ?C ::: ?t @ ?p |- _ ] =>
               tryif let x := fresh "_" C in idtac
               then fail
               else inversion H; subst; clear H
             end; auto with Chor.
    all: repeat match goal with
                | [IH : forall G D t p, G ;; D ⊢c ?C1 ::: t @ p -> G ;; D ⊢c ?C2 ::: t @ p,
                     H : ?Γ ;; ?Δ ⊢c ?C1 ::: ?τ @ ?p |- _ ] =>
                  lazymatch goal with
                  | [_ : Γ ;; Δ ⊢c C2 ::: τ @ p |- _ ] => fail
                  | _ => pose proof (IH Γ Δ τ p H)
                  end
                end; eauto with Chor.
    - apply TSend with (τ := τ1); auto.
      destruct (L.eq_dec l2 l3) as [eq | _ ]; [destruct (H1 eq)|]; auto.
      apply TSend with (τ := τ0); auto.
      destruct (L.eq_dec l4 l1) as [eq|_]; [destruct (H0 (eq_sym eq))|]; auto.
      eapply ChorTypingExt; [| |exact H15]; auto.
      intros p0 n; cbn; destruct (L.eq_dec l4 p0); destruct (L.eq_dec l2 p0); subst;
        try match goal with [H : ?a <> ?a |- _] => destruct (H eq_refl) end;
        auto.
    - apply TIf. destruct (L.eq_dec l2 l3) as [eq|_]; [destruct (H0 eq)|auto].
      all: apply TSend with (τ := τ0); auto.
    - apply TSend with (τ := τ0); auto.
      apply TIf; auto.
      destruct (L.eq_dec l3 l1) as [eq | _ ]; [destruct (H0 (eq_sym eq))| auto].
      rewrite (ExprTypingUnique (Γ l2) e' τ0 τ1 H12 H11); auto.
  Qed.      

  Theorem RelativePreservation :
    (forall (Γ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
        Γ ⊢e e ::: τ
        -> forall e' : Expr, ExprStep e e'
                       -> Γ ⊢e e' ::: τ) ->
    forall (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp) (C : Chor) (τ : ExprTyp) (p : Loc),
      Γ;; Δ ⊢c C ::: τ @ p -> forall (R : Redex) (B : list Loc) (C': Chor),
        RChorStep R B C C' -> Γ;; Δ ⊢c C' ::: τ @ p.
  Proof.
    intros ExprPreservation Γ Δ C τ p typing; induction typing;
      intros R B C' step; inversion step; subst; clear step; auto.
    all: repeat match goal with
                | [ H : ?Γ ⊢e ?e ::: ?τ, H' : ExprStep ?e ?e' |- _ ] =>
                  lazymatch goal with
                  | [_ : Γ ⊢e e' ::: τ |- _ ] => fail
                  | _ => pose proof (ExprPreservation Γ e τ H e' H')
                  end
                end; eauto with Chor.
    - eapply ChorExprSubstTypingSpec; [apply SendExprSubstTyping|]; eauto.
      eapply ExprValueTyping; eauto.
    - inversion typing1; subst.
      eapply ChorExprSubstTypingSpec; [apply SendExprSubstTyping|]; eauto.
    - eapply ChorSubstTypingSpec; [apply DefSubstTyping|]; eauto.
  Qed.

  Theorem ChorValueTyping : forall (C : Chor) (τ : ExprTyp) (p : Loc),
      ChorVal C ->
       forall Γ1 Γ2 Δ1 Δ2, Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros C τ p H Γ1 Γ2 Δ1 Δ2 H0.
    inversion H. rewrite <- H2 in *; clear C H2.
    inversion H0; auto.
    apply TDone. eapply ExprValueTyping; eauto.
  Qed.

  Inductive ChorClosedBelow : (Loc -> nat) -> nat -> Chor -> Prop :=
  | DoneClosedBelow : forall n m p e, ExprClosedBelow (n p) e -> ChorClosedBelow n m (Done p e)
  | VarClosedBelow : forall n m k, lt k m -> ChorClosedBelow n m (Var k)
  | SendClosedBelow : forall p e q C n m,
      ExprClosedBelow (n p) e
      -> ChorClosedBelow (fun r => if L.eq_dec q r then S (n q) else n r) m C 
      -> ChorClosedBelow n m (Send p e q C)
  | SyncClosedBelow : forall n m p d q C,
      ChorClosedBelow n m C -> ChorClosedBelow n m (Sync p d q C)
  | IfClosedBelow : forall n m p e C1 C2,
    ExprClosedBelow (n p) e -> ChorClosedBelow n m C1 -> ChorClosedBelow n m C2
    -> ChorClosedBelow n m (If p e C1 C2)
  | DefLocalClosedBelow : forall n m l C1 C2,
      ChorClosedBelow n m C1 ->
      ChorClosedBelow (fun l' => if L.eq_dec l l' then S (n l) else n l') m C2 ->
      ChorClosedBelow n m (DefLocal l C1 C2)
  | DefGlobalClosedBelow : forall n m C1 C2,
      ChorClosedBelow n (S m) C1
      -> ChorClosedBelow n (S m) C2
      -> ChorClosedBelow n m (DefGlobal C1 C2).

  Lemma ChorClosedBelowTyping : forall (Γ1 Γ2 : Loc -> nat -> ExprTyp)
                                  (Δ1 Δ2 : nat -> Loc * ExprTyp)
                                  (C : Chor) (τ : ExprTyp) (p : Loc)
                                  (n : Loc -> nat) (m : nat),
      ChorClosedBelow n m C ->
      (forall (p : Loc) (k : nat), lt k (n p) -> Γ1 p k = Γ2 p k) ->
      (forall k : nat, lt k m -> Δ1 k = Δ2 k) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C τ p n m cb eqΓ eqΔ typ; revert Γ2 Δ2 n m cb eqΓ eqΔ;
      induction typ; try rename n into n'; intros Γ2 Δ2 n m cb eqΓ eqΔ;
        inversion cb; subst.
    - apply TDone; eapply ExprClosedBelowTyping; [| apply eqΓ|]; eauto.
    - rewrite eqΔ; auto; apply TVar.
    - eapply TSend; eauto.
      eapply ExprClosedBelowTyping; [| | exact H]; eauto.
      eapply IHtyp; eauto. cbn in *; intros p0 k l.
      destruct (L.eq_dec q p0); subst; auto. destruct k; auto. apply eqΓ.
      apply Lt.lt_S_n in l; auto.
    - apply TIf. eapply ExprClosedBelowTyping; [| apply eqΓ|]; eauto.
      eapply IHtyp1; eauto. eapply IHtyp2; eauto.
    - apply TSync; eapply IHtyp; eauto.
    - eapply TDefLocal. eapply IHtyp1; eauto.
      eapply IHtyp2; eauto. cbn in *; intros p0 k l.
      destruct (L.eq_dec p p0); subst; auto. destruct k; auto.
      apply eqΓ; apply Lt.lt_S_n in l; auto.
    - eapply TDefGlobal. eapply IHtyp1; eauto. 2: eapply IHtyp2; eauto.
      all: intros k l; destruct k; auto; apply eqΔ; apply Lt.lt_S_n in l; auto.
  Qed.

  Definition ChorClosed := ChorClosedBelow (fun _ => 0) 0.
  Lemma ChorClosedTyping : forall (Γ1 Γ2 : Loc -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Loc * ExprTyp)
                             (C : Chor) (τ : ExprTyp)(p : Loc),
      ChorClosed C -> Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C τ p H H0.
    unfold ChorClosed in H.
    apply ChorClosedBelowTyping with (Γ1 := Γ1) (Δ1 := Δ1) (n := fun _ => 0) (m := 0); auto.
    intros p0 k H1; inversion H1.
    intros k H1; inversion H1.
  Qed.
  Lemma ChorValuesClosed : forall C : Chor, ChorVal C -> ChorClosed C.
  Proof.
    intros C H. induction H. unfold ChorClosed. apply DoneClosedBelow.
    apply ExprValuesClosed in H. unfold ExprClosed in H. exact H.
  Qed.
  
  Theorem RelativeProgress :
    (forall (e : Expr) (τ : ExprTyp) (Γ : nat -> ExprTyp),
        Γ ⊢e e ::: τ -> ExprClosed e ->
        ExprVal e \/ exists e' : Expr, ExprStep e e') ->
    (forall (v : Expr) (Γ : nat -> ExprTyp),
        Γ ⊢e v ::: bool -> ExprVal v -> {v = tt} + {v = ff}) ->
    forall (C : Chor) (Γ : Loc -> nat -> ExprTyp) (Δ : nat -> Loc * ExprTyp) (τ : ExprTyp) (p : Loc),
      ChorClosed C -> Γ;; Δ ⊢c C ::: τ @ p ->
      ChorVal C \/ exists R C', RChorStep R nil C C'.
  Proof.
    intros ExprProgress BoolInversion C Γ Δ τ p cc typ; revert cc; induction typ; intro cc;
      inversion cc; subst.
    2: inversion H2.
    2-6: right.
    - destruct (ExprProgress e tau (Γ p) ltac:(assumption) ltac:(assumption));
        [left; constructor; auto | right].
      destruct H0 as [e' step]; exists (RDone p e e'); exists (Done p e'); auto with Chor.
    - destruct (ExprProgress e τ (Γ p) ltac:(assumption) ltac:(assumption))
        as [eval | [e' step]];
        eexists; eexists; eauto with Chor.
    - destruct (ExprProgress e bool (Γ p) ltac:(assumption) ltac:(assumption))
        as [eval | [e' step]];
        [destruct (BoolInversion e (Γ p) ltac:(assumption) eval); subst|].
      all: eexists; eexists; eauto with Chor.
    - eexists; eexists; eauto with Chor.
    - destruct (IHtyp1 ltac:(assumption)) as [cval | [R [C' step]]].
      inversion cval; subst. inversion typ1; subst.
      all: eexists; eexists; eauto with Chor.
    - exists RDefGlobal; eexists; eauto with Chor.
  Qed.
      
End TypedChoreography.

