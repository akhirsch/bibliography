Require Export Expression.
Require Export TypedExpression.
Require Export Choreography.

Module TypedChoreography (L : Locations) (E : Expression) (TE : TypedExpression E).
  Import E.
  Import TE.
  Include (Choreography E L).

  Reserved Notation "G ;; D ⊢c C ::: tau @ p" (at level 30).
  Inductive ctyping : (L.t -> nat -> ExprTyp) -> (nat -> L.t * ExprTyp) -> Chor -> ExprTyp -> L.t -> Prop :=
  | TDone : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp)
              (p : L.t) (e : Expr) (tau : ExprTyp),
       (Γ p) ⊢e e ::: tau ->
  (* ------------------------------ *)
      Γ ;; Δ ⊢c CDone p e ::: tau @ p
  | TVar : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (n : nat),
  (* ----------------------------- *)
      Γ ;; Δ ⊢c CVar n ::: snd (Δ n) @ fst (Δ n)
  | TSend : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp)
              (p : L.t) (e : Expr) (τ : ExprTyp) (q : L.t) (C : Chor) (r : L.t) (sigma : ExprTyp),
      (Γ p) ⊢e e ::: τ ->
      (fun r n => if L.eq_dec q r
               then match n with
                    | 0 => τ
                    | S n => Γ r n
                    end
               else Γ r n);; Δ ⊢c C ::: sigma @ r ->
      p <> q ->
  (* --------------------------------------- *)
      Γ ;; Δ ⊢c (CSend p e q C) ::: sigma @ r
  | TIf : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp)
            (p : L.t) (e : Expr) (C1 C2 : Chor) (q : L.t) (tau : ExprTyp),
      (Γ p) ⊢e e ::: bool ->
      Γ ;; Δ ⊢c C1 ::: tau @ q ->
      Γ ;; Δ ⊢c C2 ::: tau @ q ->
  (* --------------------------------- *)
      Γ;; Δ ⊢c CIf p e C1 C2 ::: tau @ q
  | TDef : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp)
             (C1 C2 : Chor) (p q : L.t) (τ σ : ExprTyp),
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
      Γ;; Δ ⊢c CDef C1 C2 ::: τ @ p
  where "Gamma ;; Delta ⊢c C ::: tau @ p" := (ctyping Gamma Delta C tau p).
  Hint Constructors ctyping : Chor.


  Theorem ChorWeakening : forall (Γ1 Γ2 : L.t -> nat -> ExprTyp) (Δ1 Δ2 : nat -> L.t * ExprTyp)
                            (ξe : L.t -> nat -> nat) (ξc : nat -> nat),
      (forall p n, Γ1 p n = Γ2 p (ξe p n)) ->
      (forall n, Δ1 n = Δ2 (ξc n)) ->
      forall (τ : ExprTyp) (r : L.t) (C : Chor),
        Γ1;; Δ1 ⊢c C ::: τ @ r ->
        Γ2;; Δ2 ⊢c C⟨c| ξc; ξe⟩ ::: τ @ r.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r C; revert Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r;
      ChorInduction C; intros Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r typing; simpl; inversion typing.
    - apply TDone. apply ExprWeakening with (Γ := Γ1 p).
      rewrite <- H4; apply subΓ.
      rewrite H4; auto.
    - rewrite subΔ. apply TVar; auto.
    - inversion typing.
      rewrite <- H4 in *; subst.
      unfold ChorUpExprRename. unfold ExprUpRename.
      rename τ0 into σ; apply TSend with (τ := σ);
        [apply ExprWeakening with (Γ := Γ1 p); auto| |]; auto.
      apply IHC with (Γ1 := fun (r : L.t) (n : nat) => if L.eq_dec q r then match n with
                                                                         | 0 => σ
                                                                         |S n0 => Γ1 r n0
                                                                         end
                                                  else Γ1 r n) (Δ1 := Δ1); auto.
      intros s n.
      destruct (L.eq_dec q s); simpl.
      destruct n; auto.
      auto.
    - apply TIf; [eapply ExprWeakening; eauto | eapply IHC0; eauto | eapply IHC1; eauto].
    - eapply TDef. eapply IHC0; eauto.
      intro n; simpl. unfold ChorUpRename. destruct n; auto.
      eapply IHC1; eauto.
      intro n; simpl. unfold ChorUpRename. destruct n; auto.
  Qed.
  
  Theorem ChorTypingExt : forall (Γ1 Γ2 : L.t -> nat -> ExprTyp) (Δ1 Δ2 : nat -> L.t * ExprTyp)
                            (C : Chor) (p : L.t) (τ : ExprTyp),
      (forall (p : L.t) (n : nat), Γ1 p n = Γ2 p n) ->
      (forall n : nat, Δ1 n = Δ2 n) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C p τ eqΓ eqΔ typing; revert Γ1 Γ2 Δ1 Δ2 p τ eqΓ eqΔ typing;
      ChorInduction C; intros Γ1 Γ2 Δ1 Δ2 r τ eqΓ eqΔ typing.
    - inversion typing; apply TDone.
      apply ExprTypingExt with (Γ := Γ1 r); auto.
    - inversion typing. rewrite eqΔ; apply TVar.
    - inversion typing. apply TSend with (τ := τ0); [eapply ExprTypingExt; eauto | |auto].
      eapply IHC; [| auto | exact H8]; subst.
      intros p3 n; simpl. destruct (L.eq_dec q p3); auto.
      destruct n; auto.
    - inversion typing; subst.
      apply TIf; [eapply ExprTypingExt; eauto| eapply IHC0 | eapply IHC1]; eauto.
    - inversion typing; subst.
      eapply TDef; [eapply IHC0 | eapply IHC1].
      3: exact H3.
      all: eauto.
      all: intro n; simpl; destruct n; auto.
  Qed.

  Definition ChorSubstTyping Γ1 Δ1 σc σe Γ2 Δ2 :=
    (forall n : nat, Γ2;; Δ2 ⊢c (σc n) ::: (snd (Δ1 n)) @ (fst (Δ1 n))) /\
    (forall p : L.t, (Γ1 p) ⊢es (σe p) ⊣ (Γ2 p)).

  Theorem ChorSubstTypingSpec : forall Γ1 Δ1 σc σe Γ2 Δ2,
      (ChorSubstTyping Γ1 Δ1 σc σe Γ2 Δ2) -> forall (C : Chor) (τ : ExprTyp) (p : L.t),
          (Γ1;; Δ1 ⊢c C ::: τ @ p) -> (Γ2;; Δ2 ⊢c (C [c| σc; σe]) ::: τ @ p).
  Proof.
    intros Γ1 Δ1 σc σe Γ2 Δ2 substyping C;
      revert Γ1 Δ1 σc σe Γ2 Δ2 substyping;
      ChorInduction C;
      intros Γ1 Δ1 σc σe Γ2 Δ2 substyping τ r typing; simpl.
    all: unfold ChorSubstTyping in substyping; destruct substyping as [st1 st2].
    all: inversion typing; subst.
    - apply TDone; eapply ExprSubstType; eauto.
    - apply st1.
    - eapply TSend; auto. simpl. eapply ExprSubstType; eauto.
      apply IHC with (Γ1 := fun r n => if L.eq_dec q r then match n with
                                                          | 0 => τ0
                                                          | S n0 => Γ1 r n0
                                                          end else Γ1 r n)
      (Δ1 := Δ1); [unfold ChorSubstTyping; split |]; auto.
      -- intros n.
         unfold SendUpChorSubst. eapply ChorWeakening; eauto.
         intros p1 m; destruct (L.eq_dec q p1); reflexivity.
      -- unfold ChorUpExprSubst. intro p2. eapply ExprSubstRWeakening.
         intro n; reflexivity.
         unfold ExprSubstTyping. intro n; simpl.
         destruct (L.eq_dec q p2). destruct n. apply ExprVarTyping.
         apply ExprWeakening with (Γ := Γ2 p2); auto.
         apply st2. apply st2.
    - apply TIf; 
        [ eapply ExprSubstType; eauto | eapply IHC0; eauto | eapply IHC1; eauto];
        unfold ChorSubstTyping; split; auto.

    - eapply TDef; [eapply IHC0; eauto | eapply IHC1; eauto];
        unfold ChorSubstTyping; split; eauto;
          unfold ChorUpSubst.
      all: intro n; destruct n; [apply TVar | eapply ChorWeakening; eauto].
  Qed.

  Lemma SendSubstTyping : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp)
                            (p : L.t) (e : Expr) (τ : ExprTyp),
      Γ p ⊢e e ::: τ ->
      ChorSubstTyping (fun r n => if L.eq_dec p r
                               then match n with
                                    | 0 => τ
                                    | S n => Γ r n
                                    end
                               else Γ r n) Δ ChorIdSubst (SendSubst p e) Γ Δ.
  Proof.
    intros Γ Δ p e τ typ.
    unfold ChorSubstTyping; split; auto.
    - intro n; unfold ChorIdSubst; auto with Chor.
    - intro q. unfold ExprSubstTyping.
      unfold SendSubst; destruct (L.eq_dec p q); intro m;
        [rewrite <- e0; destruct m; auto|]; apply ExprVarTyping.
  Qed.

  Lemma DefSubstTyping : forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (C : Chor)
    (σ : ExprTyp) (p : L.t),
      (Γ;; fun n =>
            match n with
            | 0 => (p, σ)
            | S n => Δ n
            end ⊢c C ::: σ @ p) ->
      ChorSubstTyping Γ (fun n =>
                           match n with
                           | 0 => (p, σ)
                           | S n => Δ n
                           end) (DefSubst C) ExprChorIdSubst Γ Δ.
  Proof.
    intros Γ Δ C σ p H.
    unfold ChorSubstTyping; split.
    unfold DefSubst; intro n; destruct n; eauto with Chor.
    intro p0; unfold ExprChorIdSubst. fold ExprIdSubst. apply ExprIdSubstTyping.
  Qed.    

  Theorem ChorEquiv'Typing : forall (C1 C2 : Chor),
      C1 ≡' C2 ->
      forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (τ : ExprTyp) (p : L.t),
        Γ;; Δ ⊢c C1 ::: τ @ p -> Γ;; Δ ⊢c C2 ::: τ @ p.
  Proof.
    intros C1 C2 equiv; induction equiv; intros Γ Δ τ Alice typ; auto with Chor.
    - inversion typ. clear Γ0 H1 Δ0 H2 p0 H e0 H0 q0 H4 C H5 sigma H3 r H6.
      rename τ0 into σ. rename H7 into ltyp. rename H8 into Ctyp.
      apply TSend with (τ := σ); auto.
    - inversion typ; apply TIf; auto.
    - inversion typ; eapply TDef; eauto.
    - inversion typ; clear Γ0 H5 Δ0 H6 p0 H3 e H4 q0 H8 C H9 sigma H7 r0 H10;
        rename τ0 into σ; rename H11 into ltyp1; rename H12 into ContTyp1.
      inversion ContTyp1. clear Γ0 H5 Δ0 H6 p0 H3 e H4 q0 H8 C H9 sigma H7 r0 H10;
        rename H11 into ltyp2; rename H12 into ContTyp2; rename τ0 into ρ.
      destruct (L.eq_dec q r) as [e | _]; [exfalso; apply H0; apply e | ].
      apply TSend with (τ := ρ); [apply ltyp2 | |]; auto.
      apply TSend with (τ := σ); auto.
      -- destruct (L.eq_dec s p) as [e | _]; [exfalso; apply H1; symmetry; apply e |].
         apply ltyp1.
      -- apply IHequiv in ContTyp2. eapply ChorTypingExt; [ | | exact ContTyp2]; auto.
         intros t n; simpl. destruct (L.eq_dec s t) as [e3 | n1].
         destruct (L.eq_dec q t) as [e4 | n2]; [exfalso; apply H2; transitivity t; auto|].
         destruct n; auto.
         destruct (L.eq_dec q t); auto.
    - inversion typ; clear Γ0 H4 Δ0 H5 p0 H1 e H2 C0 H3 C3 H7 tau H6 q0 H8;
        rename H9 into ltyp1; rename H10 into Btyp11; rename H11 into Btyp21.
      inversion Btyp11; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into σ; rename H9 into ltyp2; rename H10 into typC1.
      inversion Btyp21; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into ρ; rename H9 into ltyp3; rename H10 into typC2.
      apply TSend with (τ := σ); auto.
      apply TIf; [| apply IHequiv1 in typC1; auto |].
      destruct (L.eq_dec r p) as [eq | _ ]; [exfalso; apply H0; symmetry; exact eq| auto ].
      rewrite (ExprTypingUnique _ _ _ _ ltyp2 ltyp3); apply IHequiv2 in typC2; auto.
    - inversion typ; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into σ; rename H9 into ltyp1; rename H10 into typif.
      inversion typif; clear Γ0 H4 Δ0 H5 p0 H1 e H2 C0 H3 C3 H7 tau H6 q0 H8;
        rename H9 into ltyp2; rename H10 into typC1; rename H11 into typC2.
      destruct (L.eq_dec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq |].
      apply TIf; auto.
      all: apply TSend with (τ := σ); auto.
    - inversion typ; clear Γ0 H3 Δ0 H4 p0 H0 C1 H2 C2 H6 tau H5 q0 H7 e H1;
        rename H8 into ltyp1; rename H9 into typC1; rename H10 into typC2.
      inversion typC1; clear Γ0 H3 Δ0 H4 p0 H0 e H1 C1 H2 C2 H6 tau H5 q0 H7;
        rename H8 into ltyp2; rename H9 into typC11; rename H10 into typC12.
      inversion typC2; clear Γ0 H3 Δ0 H4 p0 H0 e H1 C1 H2 C2 H6 tau H5 q0 H7;
        rename H8 into ltyp3; rename H9 into typC21; rename H10 into typC22.
      auto with Chor. 
  Qed.

  Theorem ChorEquivTyping : forall (C1 C2 : Chor),
      C1 ≡ C2 ->
      forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (τ : ExprTyp) (p : L.t),
        Γ;; Δ ⊢c C1 ::: τ @ p -> Γ;; Δ ⊢c C2 ::: τ @ p.
  Proof.
    intros C1 C2 equiv; induction equiv; intros Γ Δ τ p typ.
    apply ChorEquiv'Typing with (C1 := C1); auto.
    apply ChorEquiv'Typing with (C2 := C2) in typ; auto.
  Qed.


  Theorem RelativePreservation :
    (forall (Γ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
        Γ ⊢e e ::: τ
        -> forall e' : Expr, ExprStep e e'
                       -> Γ ⊢e e' ::: τ) ->
    forall (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (C : Chor) (τ : ExprTyp) (p : L.t),
      Γ;; Δ ⊢c C ::: τ @ p -> forall (R : Redex) (B : list L.t) (C': Chor),
        RChorStep R B C C' -> Γ;; Δ ⊢c C' ::: τ @ p.
  Proof.
    intros ExprPreservation Γ Δ C τ p typing; induction typing;
      intros R B C' step; inversion step; subst; auto.
    - apply TDone; apply ExprPreservation with (e := e); auto.
    - apply TSend with (τ := τ); auto; apply ExprPreservation with (e := e); auto.
    - specialize (IHtyping _ _ _ H8). apply TSend with (τ := τ); auto.
    - eapply ChorSubstTypingSpec; [apply SendSubstTyping|]; eauto.
      apply ExprValueTyping with (Γ := Γ p); auto.
    - apply TIf; auto. apply ExprPreservation with (e := e); auto.
    - specialize (IHtyping1 _ _ _ H7). specialize (IHtyping2 _ _ _ H8).
      apply TIf; auto.
    - eapply ChorSubstTypingSpec; [apply DefSubstTyping|]; eauto.
  Qed.

  Theorem ChorValueTyping : forall (C : Chor) (τ : ExprTyp) (p : L.t),
      ChorVal C ->
       forall Γ1 Γ2 Δ1 Δ2, Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros C τ p H Γ1 Γ2 Δ1 Δ2 H0.
    inversion H. rewrite <- H2 in *; clear C H2.
    inversion H0; auto.
    apply TDone. eapply ExprValueTyping; eauto.
  Qed.

  Inductive ChorClosedBelow : (L.t -> nat) -> nat -> Chor -> Prop :=
  | DoneClosedBelow : forall n m p e, ExprClosedBelow (n p) e -> ChorClosedBelow n m (CDone p e)
  | CVarClosedBelow : forall n m k, k < m -> ChorClosedBelow n m (CVar k)
  | SendClosedBelow : forall p e q C n m,
      ExprClosedBelow (n p) e
      -> ChorClosedBelow (fun r => if L.eq_dec q r then S (n q) else n r) m C 
      -> ChorClosedBelow n m (CSend p e q C)
  | IfClosedBelow : forall n m p e C1 C2,
    ExprClosedBelow (n p) e -> ChorClosedBelow n m C1 -> ChorClosedBelow n m C2
    -> ChorClosedBelow n m (CIf p e C1 C2)
  | DefClosedBelow : forall n m C1 C2, ChorClosedBelow n (S m) C1
                         -> ChorClosedBelow n (S m) C2
                         -> ChorClosedBelow n m (CDef C1 C2).
  Lemma ChorClosedBelowTyping : forall (Γ1 Γ2 : L.t -> nat -> ExprTyp)
                                  (Δ1 Δ2 : nat -> L.t * ExprTyp)
                                  (C : Chor) (τ : ExprTyp) (p : L.t)
                                  (n : L.t -> nat) (m : nat),
      ChorClosedBelow n m C ->
      (forall (p : L.t) (k : nat), k < (n p) -> Γ1 p k = Γ2 p k) ->
      (forall k : nat, k < m -> Δ1 k = Δ2 k) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C; revert Γ1 Γ2 Δ1 Δ2; ChorInduction C;
      try (rename n into n');
      intros Γ1 Γ2 Δ1 Δ2 τ q' n m closedC eqΓ eqΔ typ; inversion closedC; inversion typ; subst.
    - apply TDone; apply ExprClosedBelowTyping with (Γ := Γ1 q') (n := n q'); auto.
    - rewrite eqΔ; auto; apply TVar.
    - apply TSend with (τ := τ0); auto.
      apply ExprClosedBelowTyping with (Γ := Γ1 p) (n := n p); auto.
      apply IHC with (Γ1 := fun r n => if L.eq_dec q r then match n with
                                                          | 0 => τ0
                                                          | S n0 => Γ1 r n0
                                                          end else Γ1 r n)
                     (Δ1 := Δ1) (n := fun r => if L.eq_dec q r then S (n q) else n r) (m := m); auto.
      intros p3 k lt_k_Sn. destruct (L.eq_dec q p3). destruct k; auto;
      apply eqΓ. rewrite <- e0. apply Lt.lt_S_n; auto. apply eqΓ; auto.
    - apply TIf. apply ExprClosedBelowTyping with (Γ := Γ1 p) (n := n p); auto.
      eapply IHC0; eauto. eapply IHC1; eauto.
    - apply TDef with (q := q) (σ := σ).
      eapply IHC0; eauto. intros k lt_k_Sm. simpl. destruct k; auto.
      apply eqΔ. apply Lt.lt_S_n; auto.
      eapply IHC1; eauto. intros k lt_k_Sm. simpl. destruct k; auto.
      apply eqΔ. apply Lt.lt_S_n; auto.
  Qed.

  Definition ChorClosed := ChorClosedBelow (fun _ => 0) 0.
  Lemma ChorClosedTyping : forall (Γ1 Γ2 : L.t -> nat -> ExprTyp) (Δ1 Δ2 : nat -> L.t * ExprTyp)
                             (C : Chor) (τ : ExprTyp)(p : L.t),
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
    forall (C : Chor) (Γ : L.t -> nat -> ExprTyp) (Δ : nat -> L.t * ExprTyp) (τ : ExprTyp) (p : L.t),
      ChorClosed C -> Γ;; Δ ⊢c C ::: τ @ p ->
      ChorVal C \/ exists R C', RChorStep R nil C C'.
  Proof.
    intros ExprProgress BoolInversion C; ChorInduction C; intros Γ Δ τ q' closedC typ;
      inversion typ; subst; inversion closedC; subst.
    2,3,4,5: right.
    - specialize (ExprProgress _ _ _ H5 H2).
      destruct ExprProgress as [eval | estep]; [left; apply VDone; auto
                                               | right; destruct estep as [e' estep]].
      exists (RDone q' e e');  exists (CDone q' e'); apply DoneEStep; auto.
    - inversion H2.
    - specialize (ExprProgress _ _ _ H7 H3); destruct ExprProgress as [eval | estep];
        [| destruct estep as [e' estep]].
      -- exists (RSendV p e q);  exists (C [c| ChorIdSubst; SendSubst q e]); auto with Chor.
      -- exists (RSendE p e e' q);  exists (CSend p e' q C); auto with Chor.
    - specialize (ExprProgress _ _ _ H7 H4); destruct ExprProgress as [eval | estep];
        [destruct (BoolInversion _ _ H7 eval) as [ett | eff] |
         destruct estep as [e' estep]].
      -- rewrite ett in *; exists (RIfTT p);  exists C0; auto with Chor.
      -- rewrite eff in *; exists (RIfFF p);  exists C1; auto with Chor.
      -- exists (RIfE p e e');  exists (CIf p e' C0 C1); auto with Chor.
    - exists RDef;  exists (C1 [c| DefSubst C0; ExprChorIdSubst]); auto with Chor.
  Qed.
      
End TypedChoreography.

