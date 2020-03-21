Require Export Expression.
Require Export TypedExpression.
Require Export Choreography.

Module TypedChoreography (E : Expression) (TE : TypedExpression E).
  Import E.
  Import TE.
  Include (Choreography E).

  Reserved Notation "G ;; D ⊢c C ::: tau @ p" (at level 30).
  Inductive ctyping : (Prin -> nat -> ExprTyp) -> (nat -> Prin * ExprTyp) -> Chor -> ExprTyp -> Prin -> Prop :=
  | TDone : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp)
              (p : Prin) (e : Expr) (tau : ExprTyp),
       (Γ p) ⊢e e ::: tau ->
  (* ------------------------------ *)
      Γ ;; Δ ⊢c CDone p e ::: tau @ p
  | TVar : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (n : nat),
  (* ----------------------------- *)
      Γ ;; Δ ⊢c CVar n ::: snd (Δ n) @ fst (Δ n)
  | TSend : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp)
              (p : Prin) (e : Expr) (τ : ExprTyp) (q : Prin) (C : Chor) (r : Prin) (sigma : ExprTyp),
      (Γ p) ⊢e e ::: τ ->
      (fun r n => if PrinEqDec q r
               then match n with
                    | 0 => τ
                    | S n => Γ r n
                    end
               else Γ r n);; Δ ⊢c C ::: sigma @ r ->
  (* --------------------------------------- *)
      Γ ;; Δ ⊢c (CSend p e q C) ::: sigma @ r
  | TIf : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp)
            (p : Prin) (e : Expr) (C1 C2 : Chor) (q : Prin) (tau : ExprTyp),
      (Γ p) ⊢e e ::: bool ->
      Γ ;; Δ ⊢c C1 ::: tau @ q ->
      Γ ;; Δ ⊢c C2 ::: tau @ q ->
  (* --------------------------------- *)
      Γ;; Δ ⊢c CIf p e C1 C2 ::: tau @ q
  | TDef : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp)
             (C1 C2 : Chor) (p q : Prin) (τ σ : ExprTyp),
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


  Theorem ChorWeakening : forall (Γ1 Γ2 : Prin -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Prin * ExprTyp)
                            (ξe : Prin -> nat -> nat) (ξc : nat -> nat),
      (forall p n, Γ1 p n = Γ2 p (ξe p n)) ->
      (forall n, Δ1 n = Δ2 (ξc n)) ->
      forall (τ : ExprTyp) (r : Prin) (C : Chor),
        Γ1;; Δ1 ⊢c C ::: τ @ r ->
        Γ2;; Δ2 ⊢c C⟨c| ξc; ξe⟩ ::: τ @ r.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r C; revert Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r;
      induction C; intros Γ1 Γ2 Δ1 Δ2 ξe ξc subΓ subΔ τ r typing; simpl; inversion typing.
    - apply TDone. apply ExprWeakening with (Γ := Γ1 p).
      rewrite <- H4; apply subΓ.
      rewrite H4; auto.
    - rewrite subΔ. apply TVar; auto.
    - inversion typing.
      rewrite <- H4 in *.
      clear sigma H3 Γ H1 Δ H2 p1 H e0 H0 p0 H4 C0 H5 r0 H6.
      unfold ChorUpExprRename. unfold ExprUpRename.
      rename τ0 into σ; apply TSend with (τ := σ);
        [apply ExprWeakening with (Γ := Γ1 p); auto|]; auto.
      apply IHC with (Γ1 := fun (r : Prin) (n : nat) => if PrinEqDec q r then match n with
                                                                         | 0 => σ
                                                                         |S n0 => Γ1 r n0
                                                                         end
                                                  else Γ1 r n) (Δ1 := Δ1); auto.
      intros s n.
      destruct (PrinEqDec q s); simpl.
      destruct n; auto.
      auto.
    - apply TIf; [eapply ExprWeakening; eauto | eapply IHC1; eauto | eapply IHC2; eauto].
    - eapply TDef. eapply IHC1; eauto.
      intro n; simpl. unfold ChorUpRename. destruct n; auto.
      eapply IHC2; eauto.
      intro n; simpl. unfold ChorUpRename. destruct n; auto.
  Qed.
  
  Theorem ChorTypingExt : forall (Γ1 Γ2 : Prin -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Prin * ExprTyp)
                            (C : Chor) (p : Prin) (τ : ExprTyp),
      (forall (p : Prin) (n : nat), Γ1 p n = Γ2 p n) ->
      (forall n : nat, Δ1 n = Δ2 n) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C p τ eqΓ eqΔ typing; revert Γ1 Γ2 Δ1 Δ2 p τ eqΓ eqΔ typing;
      induction C; intros Γ1 Γ2 Δ1 Δ2 r τ eqΓ eqΔ typing.
    - inversion typing; apply TDone.
      apply ExprTypingExt with (Γ := Γ1 r); auto.
    - inversion typing. rewrite eqΔ; apply TVar.
    - inversion typing. apply TSend with (τ := τ0); [eapply ExprTypingExt; eauto |].
      eapply IHC; [| auto | exact H8].
      intros p3 n; simpl. destruct (PrinEqDec p0 p3); auto.
      destruct n; auto.
    - inversion typing.
      apply TIf; [eapply ExprTypingExt; eauto| eapply IHC1 | eapply IHC2]; eauto.
    - inversion typing.
      eapply TDef; [eapply IHC1 | eapply IHC2].
      3: exact H3.
      all: eauto.
      all: intro n; simpl; destruct n; auto.
  Qed.

  Definition ChorSubstTyping Γ1 Δ1 σc σe Γ2 Δ2 :=
    (forall n : nat, Γ2;; Δ2 ⊢c (σc n) ::: (snd (Δ1 n)) @ (fst (Δ1 n))) /\
    (forall p : Prin, (Γ1 p) ⊢es (σe p) ⊣ (Γ2 p)).

  Theorem ChorSubstTypingSpec : forall Γ1 Δ1 σc σe Γ2 Δ2,
      (ChorSubstTyping Γ1 Δ1 σc σe Γ2 Δ2) -> forall (C : Chor) (τ : ExprTyp) (p : Prin),
          (Γ1;; Δ1 ⊢c C ::: τ @ p) -> (Γ2;; Δ2 ⊢c (C [c| σc; σe]) ::: τ @ p).
  Proof.
    intros Γ1 Δ1 σc σe Γ2 Δ2 substyping C;
      revert Γ1 Δ1 σc σe Γ2 Δ2 substyping;
      induction C;
      intros Γ1 Δ1 σc σe Γ2 Δ2 substyping τ r typing; simpl.
    all: unfold ChorSubstTyping in substyping; destruct substyping as [st1 st2].
    all: inversion typing.
    - apply TDone; eapply ExprSubstType; eauto.
    - apply st1.
    - eapply TSend. simpl. eapply ExprSubstType; eauto.
      apply IHC with (Γ1 := fun r n => if PrinEqDec p0 r then match n with
                                                          | 0 => τ0
                                                          | S n0 => Γ1 r n0
                                                          end else Γ1 r n)
      (Δ1 := Δ1); [unfold ChorSubstTyping; split |].
      -- intros n.
         unfold SendUpChorSubst. eapply ChorWeakening; eauto.
         intros p2 m; destruct (PrinEqDec p0 p2); reflexivity.
      -- unfold ChorUpExprSubst. intro p2. eapply ExprSubstRWeakening.
         intro n; reflexivity.
         unfold ExprSubstTyping. intro n; simpl.
         destruct (PrinEqDec p0 p2). destruct n. apply ExprVarTyping.
         apply ExprWeakening with (Γ := Γ2 p2); auto.
         apply st2. apply st2.
      -- apply H8.
    - apply TIf; 
        [ eapply ExprSubstType; eauto | eapply IHC1; eauto | eapply IHC2; eauto];
        unfold ChorSubstTyping; split; auto.

    - eapply TDef; [eapply IHC1; eauto | eapply IHC2; eauto];
        unfold ChorSubstTyping; split; eauto;
          unfold ChorUpSubst.
      all: intro n; destruct n; [apply TVar | eapply ChorWeakening; eauto].
  Qed.

  Lemma SendSubstTyping : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp)
                            (p : Prin) (e : Expr) (τ : ExprTyp),
      Γ p ⊢e e ::: τ ->
      ChorSubstTyping (fun r n => if PrinEqDec p r
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
      unfold SendSubst; destruct (PrinEqDec p q); intro m;
        [rewrite <- e0; destruct m; auto|]; apply ExprVarTyping.
  Qed.

  Lemma DefSubstTyping : forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (C : Chor)
    (σ : ExprTyp) (p : Prin),
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

  (* Lemma ChorTypingWithoutThread: forall (p : Prin) *)
  (*                                  (Γ1 Γ2 : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) *)
  (*                                  (C : Chor) *)
  (*                                  (τ : ExprTyp) (q : Prin), *)
  (*     (forall r n, p <> r -> Γ1 r n = Γ2 r n) -> *)
  (*     p ∉TN C -> *)
  (*     Γ1;; Δ ⊢c C ::: τ @ q -> *)
  (*     Γ2;; Δ ⊢c C ::: τ @ q. *)
  (* Proof. *)
  (*   intros p Γ1 Γ2 Δ C; revert p Γ1 Γ2 Δ; *)
  (*     induction C as [r e | n |r e s C IHC | r e C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2]; *)
  (*     intros p Γ1 Γ2 Δ τ q HΓ pnin typ1; inversion pnin; inversion typ1; auto with Chor. *)
  (*   - clear p0 H0 q0 H e0 H2 Γ H4 Δ0 H5 p1 H3 e1 H7 tau H6; inversion typ1. *)
  (*     rewrite <- H8 in *; clear H8. *)
  (*     apply TDone. apply ExprTypingExt with (Γ := Γ1 r); auto. *)
  (*   - clear p0 H2 q0 H e0 H0 r0 H1 C0 H4 Γ H9 Δ0 H10 p1 H7 e1 H8 q1 H12 C1 H13 sigma H11 r1 H14; *)
  (*     rename τ0 into σ. *)
  (*     apply TSend with (τ := σ); auto with Chor; *)
  (*       [eapply ExprTypingExt; [ | exact H15]; auto|]. *)
  (*     eapply IHC with (p := p); [ | | exact H16]; auto. *)
  (*     intros r0 n H; simpl; destruct (PrinEqDec s r0); destruct n; auto. *)
  (*   - clear p0 H2 q0 H e0 H0 C0 H1 C4 H4 Γ H10 Δ0 H11 p1 H7 e1 H8 C5 H9 C5 H13 tau H12 q1 H14 C3. *)
  (*     apply TIf; [eapply ExprTypingExt; [ | exact H15]; auto| |]. *)
  (*     apply IHC1 with (p := p) (Γ1 := Γ1); auto. *)
  (*     apply IHC2 with (p := p) (Γ1 := Γ1); auto. *)
  (*   - clear p0 H1 C0 H C3 H0 Γ H6 Δ0 H7 C4 H4 C5 H5 τ0 H9 p1 H10. *)
  (*     apply TDef with (q := q0)(σ := σ); eauto. *)
  (* Qed. *)

  Theorem ChorEquiv'Typing : forall (C1 C2 : Chor),
      C1 ≡' C2 ->
      forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (τ : ExprTyp) (p : Prin),
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
      destruct (PrinEqDec q r) as [e | _]; [exfalso; apply H0; apply e | ].
      apply TSend with (τ := ρ); [apply ltyp2 |].
      apply TSend with (τ := σ).
      -- destruct (PrinEqDec s p) as [e | _]; [exfalso; apply H1; symmetry; apply e |].
         apply ltyp1.
      -- apply IHequiv in ContTyp2. eapply ChorTypingExt; [ | | exact ContTyp2]; auto.
         intros t n; simpl. destruct (PrinEqDec s t) as [e3 | n1].
         destruct (PrinEqDec q t) as [e4 | n2]; [exfalso; apply H2; transitivity t; auto|].
         destruct n; auto.
         destruct (PrinEqDec q t); auto.
    - inversion typ; clear Γ0 H4 Δ0 H5 p0 H1 e H2 C0 H3 C3 H7 tau H6 q0 H8;
        rename H9 into ltyp1; rename H10 into Btyp11; rename H11 into Btyp21.
      inversion Btyp11; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into σ; rename H9 into ltyp2; rename H10 into typC1.
      inversion Btyp21; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into ρ; rename H9 into ltyp3; rename H10 into typC2.
      apply TSend with (τ := σ); auto.
      apply TIf; [| apply IHequiv1 in typC1; auto |].
      destruct (PrinEqDec r p) as [eq | _ ]; [exfalso; apply H0; symmetry; exact eq| auto ].
      rewrite (ExprTypingUnique _ _ _ _ ltyp2 ltyp3); apply IHequiv2 in typC2; auto.
    - inversion typ; clear Γ0 H3 Δ0 H4 p0 H1 e H2 q0 H6 C H7 sigma H5 r0 H8;
        rename τ0 into σ; rename H9 into ltyp1; rename H10 into typif.
      inversion typif; clear Γ0 H4 Δ0 H5 p0 H1 e H2 C0 H3 C3 H7 tau H6 q0 H8;
        rename H9 into ltyp2; rename H10 into typC1; rename H11 into typC2.
      destruct (PrinEqDec r p) as [eq | _]; [exfalso; apply H0; symmetry; exact eq |].
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
      forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (τ : ExprTyp) (p : Prin),
        Γ;; Δ ⊢c C1 ::: τ @ p -> Γ;; Δ ⊢c C2 ::: τ @ p.
  Proof.
    intros C1 C2 equiv; induction equiv; intros Γ Δ τ p typ.
    apply ChorEquiv'Typing with (C1 := C1); auto.
    apply ChorEquiv'Typing with (C2 := C2) in typ; auto.
  Qed.


  (* Lemma CDoneEquiv: forall (p : Prin) (e : Expr) (C : Chor), *)
  (*     CDone p e ≡ C -> C = CDone p e. *)
  (* Proof. *)
  (*   intros p e C2 equiv. remember (CDone p e) as C1. *)
  (*   induction equiv; inversion HeqC1. *)
  (*   - reflexivity. *)
  (*   - specialize (IHequiv1 HeqC1). rewrite HeqC1 in IHequiv1. *)
  (*     specialize (IHequiv2 IHequiv1). rewrite IHequiv2. rewrite IHequiv1. *)
  (*     reflexivity. *)
  (* Qed. *)

  (* Lemma CVarEquiv : forall (n : nat) (C : Chor), *)
  (*     CVar n ≡ C -> C = CVar n. *)
  (* Proof. *)
  (*   intros n C2 equiv; remember (CVar n) as C1. *)
  (*   induction equiv; inversion HeqC1; auto. *)
  (*   specialize (IHequiv1 HeqC1). rewrite HeqC1 in IHequiv1. *)
  (*   specialize (IHequiv2 IHequiv1). rewrite IHequiv1 in IHequiv2. rewrite IHequiv2. *)
  (*   reflexivity. *)
  (* Qed. *)
      
  Theorem RelativePreservation :
    (forall (Γ : nat -> ExprTyp) (e : Expr) (τ : ExprTyp),
        Γ ⊢e e ::: τ
        -> forall e' : Expr, ExprStep e e'
                       -> Γ ⊢e e' ::: τ) ->
    forall (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (C : Chor) (τ : ExprTyp) (p : Prin),
      Γ;; Δ ⊢c C ::: τ @ p -> forall (R : Redex) (B : list Prin) (C': Chor),
        RChorStep R B C C' -> Γ;; Δ ⊢c C' ::: τ @ p.
  Proof.
    intros ExprPreservation Γ Δ C τ p typing; induction typing;
      intros R B C' step; inversion step.
    - apply TDone; apply ExprPreservation with (e := e); auto.
    - apply TSend with (τ := τ); auto; apply ExprPreservation with (e := e); auto.
    - specialize (IHtyping _ _ _ H7). apply TSend with (τ := τ); auto.
    - eapply ChorSubstTypingSpec; [apply SendSubstTyping|]; eauto.
      apply ExprValueTyping with (Γ := Γ p); auto.
    - apply TIf; auto. apply ExprPreservation with (e := e); auto.
    - specialize (IHtyping1 _ _ _ H7). specialize (IHtyping2 _ _ _ H8).
      apply TIf; auto.
    - rewrite <- H3; auto.
    - rewrite <- H3; auto.
    - eapply ChorSubstTypingSpec; [apply DefSubstTyping|]; eauto.
  Qed.

  Theorem ChorValueTyping : forall (C : Chor) (τ : ExprTyp) (p : Prin),
      ChorVal C ->
       forall Γ1 Γ2 Δ1 Δ2, Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros C τ p H Γ1 Γ2 Δ1 Δ2 H0.
    inversion H. rewrite <- H2 in *; clear C H2.
    inversion H0; auto.
    apply TDone. eapply ExprValueTyping; eauto.
  Qed.

  Inductive ChorClosedBelow : (Prin -> nat) -> nat -> Chor -> Prop :=
  | DoneClosedBelow : forall n m p e, ExprClosedBelow (n p) e -> ChorClosedBelow n m (CDone p e)
  | CVarClosedBelow : forall n m k, k < m -> ChorClosedBelow n m (CVar k)
  | SendClosedBelow : forall p e q C n m,
      ExprClosedBelow (n p) e
      -> ChorClosedBelow (fun r => if PrinEqDec q r then S (n q) else n r) m C 
      -> ChorClosedBelow n m (CSend p e q C)
  | IfClosedBelow : forall n m p e C1 C2,
    ExprClosedBelow (n p) e -> ChorClosedBelow n m C1 -> ChorClosedBelow n m C2
    -> ChorClosedBelow n m (CIf p e C1 C2)
  | DefClosedBelow : forall n m C1 C2, ChorClosedBelow n (S m) C1
                         -> ChorClosedBelow n (S m) C2
                         -> ChorClosedBelow n m (CDef C1 C2).
  Lemma ChorClosedBelowTyping : forall (Γ1 Γ2 : Prin -> nat -> ExprTyp)
                                  (Δ1 Δ2 : nat -> Prin * ExprTyp)
                                  (C : Chor) (τ : ExprTyp) (p : Prin)
                                  (n : Prin -> nat) (m : nat),
      ChorClosedBelow n m C ->
      (forall (p : Prin) (k : nat), k < (n p) -> Γ1 p k = Γ2 p k) ->
      (forall k : nat, k < m -> Δ1 k = Δ2 k) ->
      Γ1;; Δ1 ⊢c C ::: τ @ p -> Γ2;; Δ2 ⊢c C ::: τ @ p.
  Proof.
    intros Γ1 Γ2 Δ1 Δ2 C; revert Γ1 Γ2 Δ1 Δ2; induction C;
      try (rename n into n');
      intros Γ1 Γ2 Δ1 Δ2 τ q n m closedC eqΓ eqΔ typ; inversion closedC; inversion typ.
    - apply TDone; apply ExprClosedBelowTyping with (Γ := Γ1 q) (n := n q); auto.
      rewrite <- H9; auto.
    - rewrite eqΔ; auto; apply TVar.
    - apply TSend with (τ := τ0).
      apply ExprClosedBelowTyping with (Γ := Γ1 p) (n := n p); auto.
      apply IHC with (Γ1 := fun r n => if PrinEqDec p0 r then match n with
                                                          | 0 => τ0
                                                          | S n0 => Γ1 r n0
                                                          end else Γ1 r n)
                     (Δ1 := Δ1) (n := fun r => if PrinEqDec p0 r then S (n p0) else n r) (m := m); auto.
      intros p3 k lt_k_Sn. destruct (PrinEqDec p0 p3). destruct k; auto;
      apply eqΓ. rewrite <- e2; apply Lt.lt_S_n; auto. apply eqΓ; auto.
    - apply TIf. apply ExprClosedBelowTyping with (Γ := Γ1 p) (n := n p); auto.
      eapply IHC1; eauto. eapply IHC2; eauto.
    - apply TDef with (q := q0) (σ := σ).
      eapply IHC1; eauto. intros k lt_k_Sm. simpl. destruct k; auto.
      apply eqΔ. apply Lt.lt_S_n; auto.
      eapply IHC2; eauto. intros k lt_k_Sm. simpl. destruct k; auto.
      apply eqΔ. apply Lt.lt_S_n; auto.
  Qed.

  Definition ChorClosed := ChorClosedBelow (fun _ => 0) 0.
  Lemma ChorClosedTyping : forall (Γ1 Γ2 : Prin -> nat -> ExprTyp) (Δ1 Δ2 : nat -> Prin * ExprTyp)
                             (C : Chor) (τ : ExprTyp)(p : Prin),
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
    forall (C : Chor) (Γ : Prin -> nat -> ExprTyp) (Δ : nat -> Prin * ExprTyp) (τ : ExprTyp) (p : Prin),
      ChorClosed C -> Γ;; Δ ⊢c C ::: τ @ p ->
      ChorVal C \/ exists R C', RChorStep R nil C C'.
  Proof.
    intros ExprProgress BoolInversion C; induction C; intros Γ Δ τ q closedC typ;
      inversion typ; inversion closedC.
    2,3,4,5: right.
    - specialize (ExprProgress _ _ _ H5 H9).
      destruct ExprProgress as [eval | estep]; [left; apply VDone; auto
                                               | right; destruct estep as [e' estep]].
      rewrite <- H4;
        exists (RDone p e e');  exists (CDone p e'); apply DoneEStep; auto.
    - inversion H7.
    - specialize (ExprProgress _ _ _ H7 H13); destruct ExprProgress as [eval | estep];
        [| destruct estep as [e' estep]].
      -- exists (RSendV p e);  exists (C [c| ChorIdSubst; SendSubst p0 e]); auto with Chor.
      -- exists (RSendE p e e');  exists (CSend p e' p0 C); auto with Chor.
    - specialize (ExprProgress _ _ _ H7 H15); destruct ExprProgress as [eval | estep];
        [destruct (BoolInversion _ _ H7 eval) as [ett | eff] |
         destruct estep as [e' estep]].
      -- rewrite ett in *; exists (RIfTT p);  exists C1; auto with Chor.
      -- rewrite eff in *; exists (RIfFF p);  exists C2; auto with Chor.
      -- exists (RIfE p e e');  exists (CIf p e' C1 C2); auto with Chor.
    - exists RDef;  exists (C2 [c| DefSubst C1; ExprChorIdSubst]); auto with Chor.
  Qed.
      
End TypedChoreography.

