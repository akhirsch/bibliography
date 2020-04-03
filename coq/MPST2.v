Require Import Coq.Logic.JMeq.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.

Require Export Expression.
Require Export TypedExpression.
Require Export SoundlyTypedExpression.

Module MPST (E : Expression) (TE : TypedExpression E) (STE : SoundlyTypedExpression E TE).
  Import E.
  Import TE.
  Import STE.
  
  Parameter Role : Set.
  Parameter RoleEqDec : forall p q : Role, {p = q} + {p <> q}.
  Hint Resolve RoleEqDec : PiC.

  Definition IdRenaming : nat -> nat := fun n => n.
  Definition RenamingUp : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S m => S (ξ m)
            end.

    Lemma RenamingUpExt : forall (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> forall n, RenamingUp ξ1 n = RenamingUp ξ2 n.
  Proof.
    intros ξ1 ξ2 ext_eq n; destruct n; simpl; auto.
  Qed.
  Hint Resolve RenamingUpExt : PiC.
  Hint Rewrite RenamingUpExt : PiC.

  Lemma IdRenamingUp : forall n, RenamingUp IdRenaming n = IdRenaming n.
  Proof.
    intro n; destruct n; auto.
  Qed.
  Hint Resolve IdRenamingUp : PiC.
  Hint Rewrite IdRenamingUp : PiC.

  Inductive GSType' : Set :=
    GEndType : GSType'
  | GSendType : Role -> ExprTyp -> GSType -> GSType'
  | GRecvType : Role -> ExprTyp -> GSType -> GSType'
  | GEChoiceType : Role -> GSType -> GSType'
  | GIChoiceType : Role -> GSType -> GSType -> GSType'
  with GSType : Set :=
    Gμ : GSType' -> GSType
  | GSTypeVar : nat -> GSType
  | GPlain : GSType' -> GSType.
  Hint Constructors GSType : PiC.
  Hint Constructors GSType' : PiC.

  Section GSTypeInd.
    Variable P : GSType' -> Prop.
    Variable Q : GSType -> Prop.

    Variable EndCase : P (GEndType).
    Variable VarCase : forall n, Q (GSTypeVar n).
    Variable SendCase : forall p τ T, Q T -> P (GSendType p τ T).
    Variable RecvCase : forall p τ T, Q T -> P (GRecvType p τ T).
    Variable EChoiceCase : forall p T, Q T -> P (GEChoiceType p T).
    Variable IChoiceCase : forall p T1 T2, Q T1 -> Q T2 -> P (GIChoiceType p T1 T2).
    Variable μCase : forall T, P T -> Q (Gμ T).
    Variable PlainCase : forall T, P T -> Q (GPlain T).

    Fixpoint GSTypeInd (T : GSType) : Q T :=
      match T with
      | Gμ T' => μCase T' (GSType'Ind T')
      | GSTypeVar n => VarCase n
      | GPlain T' => PlainCase T' (GSType'Ind T')
      end
    with GSType'Ind (T' : GSType') : P T' :=
           match T' with
           | GEndType => EndCase
           | GSendType p τ T => SendCase p τ T (GSTypeInd T)
           | GRecvType p τ T => RecvCase p τ T (GSTypeInd T)
           | GEChoiceType p T => EChoiceCase p T (GSTypeInd T)
           | GIChoiceType p T1 T2 => IChoiceCase p T1 T2 (GSTypeInd T1) (GSTypeInd T2)
           end.
  End GSTypeInd.

  Fixpoint GSTypeRename (T : GSType) (ξ : nat -> nat) : GSType :=
    match T with
    | Gμ T' => Gμ (GSType'Rename T' (RenamingUp ξ))
    | GSTypeVar n => GSTypeVar (ξ n)
    | GPlain T' => GPlain (GSType'Rename T' ξ)
    end
  with GSType'Rename (T : GSType') (ξ : nat -> nat) : GSType' :=
         match T with
         | GEndType => GEndType
         | GSendType p τ T => GSendType p τ (GSTypeRename T ξ)
         | GRecvType p τ T => GRecvType p τ (GSTypeRename T ξ)
         | GEChoiceType p T => GEChoiceType p (GSTypeRename T ξ)
         | GIChoiceType p T1 T2 => GIChoiceType p (GSTypeRename T1 ξ) (GSTypeRename T2 ξ)
         end.
  Notation "T ⟨gst| ξ ⟩" := (GSTypeRename T ξ) (at level 15).
  Notation "T ⟨gst'| ξ ⟩" := (GSType'Rename T ξ) (at level 15).

  Lemma GSTypeRenameExt : forall (T : GSType) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> T ⟨gst| ξ1⟩ = T ⟨gst| ξ2⟩.
  Proof.
    intro T;
      induction T using GSTypeInd
        with (P := fun T' =>
                     forall ξ1 ξ2 : nat -> nat, (forall n, ξ1 n = ξ2 n) -> T' ⟨gst'|ξ1⟩ = T' ⟨gst'|ξ2⟩);
      intros ξ1 ξ2 ext_eq; simpl; auto.
    1,2,3,6: rewrite IHT with (ξ2 := ξ2); auto.
    - rewrite IHT1 with (ξ2 := ξ2); [rewrite IHT2 with (ξ2 := ξ2)|]; auto.
    - rewrite IHT with (ξ2 := RenamingUp ξ2); [reflexivity| apply RenamingUpExt; auto].
  Qed.
  Hint Resolve GSTypeRenameExt : PiC.
  Hint Rewrite GSTypeRenameExt : PiC.

  Lemma GSType'RenameExt : forall (T : GSType') (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> T ⟨gst'| ξ1⟩ = T ⟨gst'| ξ2⟩.
  Proof.
    intro T;
      induction T using GSType'Ind
        with (Q := fun T => forall ξ1 ξ2 : nat -> nat, (forall n, ξ1 n = ξ2 n) -> T ⟨gst|ξ1⟩ = T ⟨gst|ξ2⟩);
      intros ξ1 ξ2 ext_eq; simpl; auto.
    1,2,3,6: rewrite IHT with (ξ2 := ξ2); auto.
    - rewrite IHT with (ξ2 := ξ2); [rewrite IHT0 with (ξ2 := ξ2)|]; auto.
    - rewrite IHT with (ξ2 := RenamingUp ξ2); [reflexivity| apply RenamingUpExt; auto].
  Qed.

  Lemma GSTypeRenameId : forall (T : GSType), T ⟨gst| IdRenaming⟩ = T.
  Proof.
    intro T; induction T using GSTypeInd
               with (P := fun T' => T' ⟨gst'| IdRenaming⟩ = T'); simpl; auto.
    1,2,3,6: rewrite IHT; reflexivity.
    - rewrite IHT1; rewrite IHT2; reflexivity.
    - rewrite GSType'RenameExt with (ξ2 := IdRenaming);
        [rewrite IHT; reflexivity | exact IdRenamingUp].
  Qed.
  Lemma GSType'RenameId : forall (T : GSType'), T ⟨gst'| IdRenaming⟩ = T.
  Proof.
    intro T; induction T using GSType'Ind
               with (Q := fun T' => T' ⟨gst| IdRenaming⟩ = T'); simpl; auto.
    1,2,3,6: rewrite IHT; reflexivity.
    - rewrite IHT; rewrite IHT0; reflexivity.
    - rewrite GSType'RenameExt with (ξ2 := IdRenaming);
        [rewrite IHT; reflexivity | exact IdRenamingUp].
  Qed.

  Definition GSTypeSubstUp : (nat -> GSType) -> nat -> GSType :=
    fun σ n => match n with
            | 0 => GSTypeVar 0
            | S n' => σ n' ⟨gst| S⟩
            end.
  
  Fixpoint GSTypeSubst (T : GSType) (σ : nat -> GSType) :=
    match T with
    | Gμ T' => Gμ (GSType'Subst T' (GSTypeSubstUp σ))
    | GSTypeVar n => σ n
    | GPlain T' => GPlain (GSType'Subst T' σ)
    end
  with GSType'Subst (T' : GSType') (σ : nat -> GSType) :=
    match T' with
    | GEndType => GEndType
    | GSendType p τ T => GSendType p τ (GSTypeSubst T σ)
    | GRecvType p τ T => GRecvType p τ (GSTypeSubst T σ)
    | GEChoiceType p T => GEChoiceType p (GSTypeSubst T σ)
    | GIChoiceType p T1 T2 => GIChoiceType p (GSTypeSubst T1 σ) (GSTypeSubst T2 σ)
    end.
  Notation "P [gst| σ ]" := (GSTypeSubst P σ) (at level 15).
  Notation "P [gst'| σ ]" := (GSType'Subst P σ) (at level 15).

  Lemma GSTypeSubstExt : forall (T : GSType) (σ1 σ2 : nat -> GSType),
      (forall n, σ1 n = σ2 n)
      -> T [gst| σ1] = T [gst| σ2].
  Proof.
    intro T; induction T using GSTypeInd
               with (P :=
                       fun T' =>
                         forall (σ1 σ2  : nat -> GSType),
                           (forall n, σ1 n = σ2 n)
                           -> T' [gst'| σ1] = T' [gst'| σ2]);
    intros σ1 σ2 ext_eq; simpl; auto with PiC.
    1,2,3,6: rewrite IHT with (σ2 := σ2); auto.
    rewrite IHT1 with (σ2 := σ2); auto; rewrite IHT2 with (σ2 := σ2); auto.
    rewrite IHT with (σ2 := GSTypeSubstUp σ2); [reflexivity|].
    intro n; unfold GSTypeSubstUp; destruct n; simpl; [| rewrite ext_eq]; reflexivity.
  Qed.    
  Lemma GSType'SubstExt : forall (T : GSType') (σ1 σ2 : nat -> GSType),
      (forall n, σ1 n = σ2 n)
      -> T [gst'| σ1] = T [gst'| σ2].
  Proof.
    intro T; induction T using GSType'Ind
               with (Q :=
                       fun T' =>
                         forall (σ1 σ2  : nat -> GSType),
                           (forall n, σ1 n = σ2 n)
                           -> T' [gst| σ1] = T' [gst| σ2]);
    intros σ1 σ2 ext_eq; simpl; auto with PiC.
    1,2,3,6: rewrite IHT with (σ2 := σ2); auto.
    rewrite IHT with (σ2 := σ2); auto; rewrite IHT0 with (σ2 := σ2); auto.
    rewrite IHT with (σ2 := GSTypeSubstUp σ2); [reflexivity|].
    intro n; unfold GSTypeSubstUp; destruct n; simpl; [| rewrite ext_eq]; reflexivity.
  Qed.

  
  
  Inductive SType : Set :=
    EndType : SType
  | STypeVar : nat -> SType
  | μ : SType -> SType
  | SendType : Role -> ExprTyp -> SType -> SType
  | RecvType : Role -> ExprTyp -> SType -> SType
  | EChoiceType : Role -> SType -> SType
  | IChoiceType : Role -> SType -> SType -> SType.
  Hint Constructors SType : PiC.
  
  Fixpoint STypeRename (T : SType) (ξ : nat -> nat) : SType :=
    match T with
    | EndType => EndType
    | STypeVar n => STypeVar (ξ n)
    | μ T => μ (STypeRename T (RenamingUp ξ))
    | SendType p τ T => SendType p τ (STypeRename T ξ)
    | RecvType p τ T => RecvType p τ (STypeRename T ξ)
    | EChoiceType p T => EChoiceType p (STypeRename T ξ)
    | IChoiceType p T1 T2 => IChoiceType p (STypeRename T1 ξ) (STypeRename T2 ξ)
    end.
  Notation "T ⟨st| ξ ⟩" := (STypeRename T ξ) (at level 15).

  Lemma STypeRenameExt : forall (T : SType) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> T ⟨st| ξ1⟩ = T ⟨st| ξ2⟩.
  Proof.
    intros T; induction T; intros ξ1 ξ2 ext_eq; simpl; auto with PiC.
    2,3,4: rewrite IHT with (ξ2 := ξ2); auto.
    - rewrite IHT with (ξ2 := RenamingUp ξ2);
        [reflexivity| apply RenamingUpExt; exact ext_eq].
    - rewrite IHT1 with (ξ2 := ξ2); auto; rewrite IHT2 with (ξ2 := ξ2); auto.
  Qed.
  Hint Resolve STypeRenameExt : PiC.
  Hint Rewrite STypeRenameExt : PiC.

  Lemma STypeRenameId : forall (T : SType), T ⟨st| IdRenaming⟩ = T.
  Proof.
    intro T; induction T; simpl; auto with PiC.
    rewrite STypeRenameExt with (ξ2 := IdRenaming); [| exact IdRenamingUp].
    1,2,3,4: rewrite IHT; reflexivity.
    rewrite IHT1; rewrite IHT2; reflexivity.
  Qed.
  Hint Resolve STypeRenameId : PiC.
  Hint Rewrite STypeRenameId : PiC.

  Definition STypeSubstUp : (nat -> SType) -> nat -> SType :=
    fun σ n => match n with
            | 0 => STypeVar 0
            | S n' => σ n' ⟨st| S ⟩
            end.

  Lemma STypeSubstUpExt : forall (σ1 σ2 : nat -> SType),
      (forall n, σ1 n = σ2 n)
      -> forall n, STypeSubstUp σ1 n = STypeSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; unfold STypeSubstUp; destruct n; [|rewrite ext_eq]; reflexivity.
  Qed.

  Fixpoint STypeSubst (T : SType) (σ : nat -> SType) : SType :=
    match T with
    | EndType => EndType
    | STypeVar n => σ n
    | μ T => μ (STypeSubst T (STypeSubstUp σ))
    | SendType p τ T => SendType p τ (STypeSubst T σ)
    | RecvType p τ T => RecvType p τ (STypeSubst T σ)
    | EChoiceType p T => EChoiceType p (STypeSubst T σ)
    | IChoiceType p T1 T2 => IChoiceType p (STypeSubst T1 σ) (STypeSubst T2 σ)
    end.
  Notation "T [st| σ ]" := (STypeSubst T σ) (at level 15).

  Lemma STypeSubstExt : forall (T : SType) (σ1 σ2 : nat -> SType),
      (forall n, σ1 n = σ2 n)
      -> T [st| σ1] = T [st| σ2].
  Proof.
    intro T; induction T; intros σ1 σ2 ext_eq; simpl; auto with PiC.
    2,3,4: rewrite IHT with (σ2 := σ2); [reflexivity | exact ext_eq].
    - rewrite IHT with (σ2 := STypeSubstUp σ2);
        [reflexivity | apply STypeSubstUpExt; exact ext_eq].
    - rewrite IHT1 with (σ2 := σ2); [| exact ext_eq];
        rewrite IHT2 with (σ2 := σ2); [reflexivity| exact ext_eq].
  Qed.
  Hint Resolve STypeSubstExt : PiC.
  Hint Rewrite STypeSubstExt : PiC.

  Definition IdSTypeSubst : nat -> SType := STypeVar.
  Lemma IdSTypeSubstUp : forall n, STypeSubstUp IdSTypeSubst n = IdSTypeSubst n.
  Proof.
    intro n; unfold STypeSubstUp; unfold IdSTypeSubst; destruct n; simpl; reflexivity.
  Qed.
    
  Lemma STypeSubstId : forall (T : SType), T[st| IdSTypeSubst] = T.
  Proof.
    intro T; induction T; simpl; auto with PiC.
    rewrite STypeSubstExt with (σ2 := IdSTypeSubst); [| exact IdSTypeSubstUp].
    1,2,3,4: rewrite IHT; reflexivity.
    rewrite IHT1; rewrite IHT2; reflexivity.
  Qed.
  Hint Resolve STypeSubstId : PiC.
  Hint Rewrite STypeSubstId : PiC.

  Inductive Plain : SType -> Prop :=
    EndPlain : Plain EndType
  | SendPlain : forall p τ T, Plain (SendType p τ T)
  | RecvPlain : forall p τ T, Plain (RecvType p τ T)
  | EChoicePlain : forall p T, Plain (EChoiceType p T)
  | IChoicePlain : forall p T1 T2, Plain (IChoiceType p T1 T2).

  Lemma PlainRename : forall (T : SType) (ξ : nat -> nat),
      Plain T -> Plain (T ⟨st| ξ⟩).
  Proof.
    intro T; induction T; intros ξ nvT; simpl; auto; inversion nvT; constructor; auto.
  Qed.
  
  Lemma PlainSubst : forall (T : SType) (σ : nat -> SType),
      Plain T -> Plain (T [st| σ]).
  Proof.
    intro T; induction T; intros σ nvT; simpl; auto; inversion nvT; constructor; auto.
  Qed.

  Inductive GuardedType : SType -> Prop :=
    EndGood : GuardedType EndType
  | VarGood : forall n, GuardedType (STypeVar n)
  | μGood : forall {T}, Plain T -> GuardedType T -> GuardedType (μ T)
  | SendGood : forall (p : Role) (τ : ExprTyp) {T : SType},
      GuardedType T -> GuardedType (SendType p τ T)
  | RecvGood : forall (p : Role) (τ : ExprTyp) {T : SType},
      GuardedType T -> GuardedType (RecvType p τ T)
  | EChoiceGood : forall (p : Role) {T : SType}, GuardedType T -> GuardedType (EChoiceType p T)
  | IChoiceGood : forall (p : Role) {T1 T2 : SType},
      GuardedType T1 -> GuardedType T2 -> GuardedType (IChoiceType p T1 T2).

  Lemma GuardedTypeRename : forall (T : SType) (ξ : nat -> nat),
      GuardedType T -> GuardedType (T ⟨st| ξ⟩).
  Proof.
    intro T; induction T; simpl; intros ξ gtT; auto; inversion gtT; constructor; auto.
    apply PlainRename; auto.
  Qed.
    
  Lemma GuardedTypeSubst : forall (T : SType) (σ : nat -> SType),
      GuardedType T -> (forall n, GuardedType (σ n)) -> GuardedType (T [st| σ]).
  Proof.
    intro T; induction T; simpl; intros σ gtT gtσ; inversion gtT; auto;
      constructor; auto.
    apply PlainSubst; auto.
    apply IHT; auto. intro n; unfold STypeSubstUp; destruct n; [constructor|].
    apply GuardedTypeRename; auto.
  Qed.

  Fixpoint FlattenGSType (T : GSType) : SType :=
    match T with
    | Gμ T' => μ (FlattenGSType' T')
    | GSTypeVar n => STypeVar n
    | GPlain T' => FlattenGSType' T'
    end
  with FlattenGSType' (T' : GSType') : SType :=
         match T' with
         | GEndType => EndType
         | GSendType p τ T => SendType p τ (FlattenGSType T)
         | GRecvType p τ T => RecvType p τ (FlattenGSType T)
         | GEChoiceType p T => EChoiceType p (FlattenGSType T)
         | GIChoiceType p T1 T2 => IChoiceType p (FlattenGSType T1) (FlattenGSType T2)
         end.

  Lemma FlattenGSTypeGuarded : forall (T : GSType), GuardedType (FlattenGSType T).
  Proof.
    intro T; induction T using GSTypeInd with (P := fun T' => GuardedType (FlattenGSType' T')
                                                          /\ Plain (FlattenGSType' T'));
    simpl; try split; try (constructor; auto; fail).
    all: destruct IHT; auto; constructor; auto.
  Qed.

  Program Fixpoint ReflectGuardedType (T : SType) (G : GuardedType T) : GSType :=
    match T with
    | EndType => GPlain (GEndType)
    | STypeVar n => GSTypeVar n
    | μ T' => Gμ (ReflectGuardedPlainType T' _ _)
    | SendType p τ T' => GPlain (GSendType p τ (ReflectGuardedType T' _))
    | RecvType p τ T' => GPlain (GRecvType p τ (ReflectGuardedType T' _))
    | EChoiceType p T' => GPlain (GEChoiceType p (ReflectGuardedType T' _))
    | IChoiceType p T'1 T'2 => GPlain (GIChoiceType p
                                                   (ReflectGuardedType T'1 _)
                                                   (ReflectGuardedType T'2 _))
    end
  with ReflectGuardedPlainType (T : SType) (G: GuardedType T) (P : Plain T) : GSType' :=
         match T with
         | EndType => GEndType
         | STypeVar n => _
         | μ T' => _
         | SendType p τ T' => GSendType p τ (ReflectGuardedType T' _)
         | RecvType p τ T' => GRecvType p τ (ReflectGuardedType T' _)
         | EChoiceType p T' => GEChoiceType p (ReflectGuardedType T' _)
         | IChoiceType p T'1 T'2 => GIChoiceType p
                                                (ReflectGuardedType T'1 _)
                                                (ReflectGuardedType T'2 _)
         end.
  Next Obligation.
    exfalso. inversion P.
  Defined.
  Next Obligation.
    exfalso; inversion P.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.
  Next Obligation.
    inversion G; auto.
  Defined.

  Definition σμ (T : SType) : nat -> SType :=
    fun n => match n with
          | 0 => μ T
          | S n' => STypeVar n
          end.
            
  Reserved Infix "≡st" (at level 16).
  CoInductive STypeEquiv : SType -> SType -> Prop :=
  | EndEquiv : EndType ≡st EndType
  | VarEquiv : forall n, STypeVar n ≡st STypeVar n
  | SendEquiv : forall (p : Role) (τ : ExprTyp) {T1 T2 : SType},
      T1 ≡st T2 -> (SendType p τ T1) ≡st (SendType p τ T2)
  | RecvEquiv : forall (p : Role) (τ : ExprTyp) {T1 T2 : SType},
      T1 ≡st T2 -> (RecvType p τ T1) ≡st (RecvType p τ T2)
  | EChoiceEquiv : forall (p : Role) {T1 T2 : SType},
      T1 ≡st T2 -> (EChoiceType p T1) ≡st (EChoiceType p T2)
  | IChoiceEquiv : forall (p : Role) {S1 S2 T1 T2 : SType},
      S1 ≡st S2 -> T1 ≡st T2 -> (IChoiceType p S1 T1) ≡st (IChoiceType p S2 T2)
  | μEquivL : forall {S T : SType}, (S [st| σμ S]) ≡st T -> (μ S) ≡st T
  | μEquivR : forall {S T : SType}, S ≡st (T [st| σμ T]) -> S ≡st (μ T)
  where "T1 ≡st T2" := (STypeEquiv T1 T2).

  CoFixpoint STypeEquivRefl (T : SType) : T ≡st T :=
    match T with
    | EndType => EndEquiv
    | STypeVar n => VarEquiv n
    | μ T => μEquivL (μEquivR (STypeEquivRefl _))
    | SendType p τ T => SendEquiv p τ (STypeEquivRefl T)
    | RecvType p τ T => RecvEquiv p τ (STypeEquivRefl T)
    | EChoiceType p T => EChoiceEquiv p (STypeEquivRefl T)
    | IChoiceType p T1 T2 => IChoiceEquiv p (STypeEquivRefl T1) (STypeEquivRefl T2)
    end.

  CoFixpoint STypeEquivSym {T1 T2 : SType} (equiv12 : T1 ≡st T2) : T2 ≡st T1 :=
    match equiv12 with
    | EndEquiv => EndEquiv
    | VarEquiv n => VarEquiv n
    | SendEquiv p τ pf => SendEquiv p τ (STypeEquivSym pf)
    | RecvEquiv p τ pf => RecvEquiv p τ (STypeEquivSym pf)
    | EChoiceEquiv p pf => EChoiceEquiv p (STypeEquivSym pf)
    | IChoiceEquiv p pf1 pf2 => IChoiceEquiv p (STypeEquivSym pf1) (STypeEquivSym pf2)
    | μEquivL pf => μEquivR (STypeEquivSym pf)
    | μEquivR pf => μEquivL (STypeEquivSym pf)
    end.

  Definition gσμ (T : GSType') : nat -> GSType :=
    fun n => match n with
          | 0 => Gμ T
          | S n' => GSTypeVar n
          end.

  Reserved Infix "≡gst" (at level 16).
  Reserved Infix "≡gst'" (at level 16).
  CoInductive GSTypeEquiv : GSType -> GSType -> Prop :=
  | GVarEquiv : forall n, GSTypeVar n ≡gst GSTypeVar n
  | GμEquivL : forall {T1 : GSType'} {T2 : GSType},
      (GPlain (T1 [gst'| gσμ T1])) ≡gst T2 -> (Gμ T1) ≡gst T2
  | GμEquivR : forall {T1 : GSType} {T2 : GSType'},
      T1 ≡gst GPlain (T2 [gst'| gσμ T2]) -> T1 ≡gst (Gμ T2)
  | GPlainEquiv : forall {T1 T2 : GSType'},
      T1 ≡gst' T2 -> GPlain T1 ≡gst GPlain T2
  where "T1 ≡gst T2" := (GSTypeEquiv T1 T2)
  with GSType'Equiv : GSType' -> GSType' -> Prop :=
  | GEndEquiv : GEndType ≡gst' GEndType
  | GSendEquiv : forall (p : Role) (τ : ExprTyp) {T1 T2 : GSType},
      T1 ≡gst T2 -> (GSendType p τ T1) ≡gst' (GSendType p τ T2)
  | GRecvEquiv : forall (p : Role) (τ : ExprTyp) {T1 T2 : GSType},
      T1 ≡gst T2 -> (GRecvType p τ T1) ≡gst' (GRecvType p τ T2)
  | GEChoiceEquiv : forall (p : Role) {T1 T2 : GSType},
      T1 ≡gst T2 -> (GEChoiceType p T1) ≡gst' (GEChoiceType p T2)
  | GIChoiceEquiv : forall (p : Role) {S1 S2 T1 T2 : GSType},
      S1 ≡gst S2 -> T1 ≡gst T2 -> (GIChoiceType p S1 T1) ≡gst' (GIChoiceType p S2 T2)
  where "T1 ≡gst' T2" := (GSType'Equiv T1 T2).

  Lemma SigmaMuGuarded : forall (T1 : SType),
      GuardedType T1 -> Plain T1 -> forall n, GuardedType (σμ T1 n).
  Proof.
    intros T1 GT1 PT1 n; unfold σμ; destruct n; [constructor; auto| constructor].
  Qed.
  
  Lemma SigmaMuConnection : forall (T1 : SType) (G : GuardedType T1) (P : Plain T1), 
      ReflectGuardedType (T1 [st| σμ T1])
                         (GuardedTypeSubst T1 (σμ T1) G (SigmaMuGuarded T1 G P))
      = (GSTypeSubst (ReflectGuardedType T1 G) (gσμ (ReflectGuardedPlainType T1 G P))).
  Proof.
    intro T1; induction T1; intros G P; try (inversion G; inversion P; fail); auto.
    simpl. fold ReflectGuardedType.
  Admitted.
                                          
  Program CoFixpoint GuardedTypeEquiv1 (T1 T2 : SType)
          (G1 : GuardedType T1) (G2 : GuardedType T2)
          (equiv : T1 ≡st T2)
    : (ReflectGuardedType T1 G1) ≡gst (ReflectGuardedType T2 G2)
    := match equiv with
      | EndEquiv => GPlainEquiv GEndEquiv
      | VarEquiv n => GVarEquiv n
      | @SendEquiv p τ T1 T2 equiv' =>
        GPlainEquiv (GuardedPlainTypeEquiv1 _ _ _ _
                                            (SendPlain _ _ T1)
                                            (SendPlain _ _ T2)
                                            equiv)
      | @RecvEquiv p τ T1 T2 equiv' =>
        GPlainEquiv (GuardedPlainTypeEquiv1 _ _ G1 G2
                                            (RecvPlain _ _ T1)
                                            (RecvPlain _ _ T2)
                                            equiv)
      | @EChoiceEquiv p T1 T2 equiv' =>
        GPlainEquiv (GuardedPlainTypeEquiv1 _ _ G1 G2
                                            (EChoicePlain _ T1)
                                            (EChoicePlain _ T2)
                                            equiv)
      | @IChoiceEquiv p S1 S2 T1 T2 equiv'1 equiv'2 =>
        GPlainEquiv (GuardedPlainTypeEquiv1 _ _ G1 G2
                                            (IChoicePlain _ S1 T1)
                                            (IChoicePlain _ S2 T2)
                                            equiv)
      | @μEquivL T1' _ equiv' =>
        @GμEquivL
            (ReflectGuardedPlainType T1' _ _)
            (ReflectGuardedType T2 _)
            (GuardedTypeEquiv1 _ _ _ _  equiv')
      | @μEquivR _ T2' equiv' =>
        @GμEquivR
          (ReflectGuardedType T1 _)
          (ReflectGuardedPlainType T2' _ _)
          (GuardedTypeEquiv1 _ _ _ _ equiv')
      end
  with GuardedPlainTypeEquiv1 (T1 T2 : SType)
                             (G1 : GuardedType T1) (G2 : GuardedType T2)
                             (P1 : Plain T1) (P2 : Plain T2)
                             (equiv : T1 ≡st T2)
       : (ReflectGuardedPlainType T1 G1 P1) ≡gst' (ReflectGuardedPlainType T2 G2 P2)
       := match equiv with
         | EndEquiv => GEndEquiv
         | VarEquiv n => _
         | SendEquiv p τ equiv' => GSendEquiv p τ (GuardedTypeEquiv1 _ _ _ _ equiv')
         | RecvEquiv p τ equiv' => GRecvEquiv p τ (GuardedTypeEquiv1 _ _ _ _ equiv')
         | EChoiceEquiv p equiv' => GEChoiceEquiv p (GuardedTypeEquiv1 _ _ _ _ equiv')
         | IChoiceEquiv p equiv'1 equiv'2 =>
           GIChoiceEquiv p (GuardedTypeEquiv1 _ _ _ _ equiv'1)
                         (GuardedTypeEquiv1 _ _ _ _ equiv'2)
                                                          
         | μEquivL equiv' => _
         | μEquivR equiv' => _
         end.
  Next Obligation.
    inversion P1.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion P1.
  Defined.
  Next Obligation.
    inversion P2.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    inversion G1; auto.
  Defined.
  Next Obligation.
    apply GuardedTypeSubst. inversion G1; auto.
    unfold σμ. intro n; destruct n; constructor; auto;
    inversion G1; auto.
  Defined.
  Next Obligation.
  Admitted.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    inversion G2; auto.
  Defined.
  Next Obligation.
    apply GuardedTypeSubst. inversion G2; auto.
    unfold σμ; intro n; destruct n; constructor; auto; inversion G2; auto.
  Defined.
  Next Obligation.
  Admitted.

  Program CoFixpoint GSTypeEquivTrans {T1 T2 T3 : GSType}
          (equiv12 : T1 ≡gst T2) (equiv23 : T2 ≡gst T3) : T1 ≡gst T3 :=
    match equiv12 with
    | GVarEquiv n => equiv23
    | GμEquivL equiv' =>
      match equiv' with
      | GVarEquiv n => GμEquivL equiv23
      | GμEquivL equiv'' => _
      | GμEquivR equiv'' =>
        match equiv'' with
        | GVarEquiv n => _
        | GμEquivL x => _
        | GμEquivR x => _
        | GPlainEquiv equiv'''' =>
          match equiv23 with
          | GVarEquiv n => _
          | GμEquivL equiv''' =>
            match equiv''' with
            | GVarEquiv n => _
            | GμEquivL x => _
            | GμEquivR equiv'''' =>
              match equiv'''' with
              | GVarEquiv n => _
              | GμEquivL  x => _
              | GμEquivR  x => _
              | GPlainEquiv equiv''''' => GμEquivL (GμEquivR (GSTypeEquivTrans equiv''
                                                                              _))
              end
            | GPlainEquiv x => GμEquivL (GSTypeEquivTrans _ equiv''')
            end
          | GμEquivR equiv''' => GμEquivR (GSTypeEquivTrans _ equiv''')
          | GPlainEquiv x => _
          end
        end
      | GPlainEquiv equiv'' => GμEquivL (GSTypeEquivTrans _ equiv23)
      end
    | GμEquivR equiv12' =>
      match equiv23 with
      | GVarEquiv n => _
      | GμEquivL equiv23' =>
        match equiv12' with
        | GVarEquiv n => _
        | GμEquivL equiv12'' => GμEquivL (GSTypeEquivTrans equiv12'' equiv23')
        | GμEquivR x => _
        | GPlainEquiv equiv12'' =>
          match equiv23' with
          | GVarEquiv n => _
          | GμEquivL x => _
          | GμEquivR equiv23'' => GμEquivR (GSTypeEquivTrans _ equiv23'')
          | GPlainEquiv equiv23'' => GPlainEquiv (GSType'EquivTrans _ equiv23'')
          end
        end
      | GμEquivR equiv23' =>
        match equiv23' with
        | GVarEquiv n => _
        | GμEquivL equiv23'' => GμEquivR (GSTypeEquivTrans _ equiv23'')
        | GμEquivR x => _
        | GPlainEquiv x => _
        end
      | GPlainEquiv x => _
      end
    | GPlainEquiv equiv12' =>
      match equiv23 with
      | GVarEquiv n => _
      | GμEquivL x => _
      | GμEquivR equiv23' => GμEquivR (GSTypeEquivTrans equiv12 equiv23')
      | GPlainEquiv equiv23' => GPlainEquiv (GSType'EquivTrans equiv12' equiv23')
      end
    end
  with GSType'EquivTrans {T1 T2 T3 : GSType'}
                         (equiv12 : T1 ≡gst' T2) (equiv23 : T2 ≡gst' T3) : T1 ≡gst' T3 :=
         match equiv12 with
         | GEndEquiv => _
         | GSendEquiv p τ equiv12' =>
           match equiv23 with
           | GEndEquiv => _
           | GSendEquiv _ _ equiv23' => GSendEquiv p τ (GSTypeEquivTrans equiv12' equiv23')
           | GRecvEquiv p τ x => _
           | GEChoiceEquiv p x => _
           | GIChoiceEquiv p x x0 => _
           end
         | GRecvEquiv p τ equiv12' =>
           match equiv23 with
           | GEndEquiv => _
           | GSendEquiv p τ x => _
           | GRecvEquiv _ _ equiv23' => GRecvEquiv p τ (GSTypeEquivTrans equiv12' equiv23')
           | GEChoiceEquiv p x => _
           | GIChoiceEquiv p x x0 => _
           end
         | GEChoiceEquiv p equiv12' =>
           match equiv23 with
           | GEndEquiv => _
           | GSendEquiv p τ x => _
           | GRecvEquiv p τ  x => _
           | GEChoiceEquiv p equiv23' => GEChoiceEquiv p (GSTypeEquivTrans equiv12' equiv23')
           | GIChoiceEquiv p x x0 => _
           end
         | GIChoiceEquiv p equiv12' equiv12'' =>
           match equiv23 with
           | GEndEquiv => _
           | GSendEquiv p τ x => _
           | GRecvEquiv p τ x => _
           | GEChoiceEquiv p x => _
           | GIChoiceEquiv p equiv23' equiv23'' =>
             GIChoiceEquiv p (GSTypeEquivTrans equiv12' equiv23')
                           (GSTypeEquivTrans equiv12'' equiv23'')
           end
         end.
    
  Program CoFixpoint STypeEquivAllμX : forall T : SType, T ≡st μ (STypeVar 0) :=
    fun T => μEquivR (STypeEquivAllμX T).

  Theorem STypeEquivTransToTrivial :
    (forall {T1 T2 T3 : SType}, T1 ≡st T2 -> T2 ≡st T3 -> T1 ≡st T3) ->
  forall {T1 T2 : SType}, T1 ≡st T2.
  Proof.
    intros stetrans T1 T2. apply stetrans with (T2 := μ (STypeVar 0)). 
    apply STypeEquivAllμX. apply STypeEquivSym. apply STypeEquivAllμX.
  Qed.

  Theorem STypeEquivNotTrivial : ~ (EndType ≡st STypeVar 0).
  Proof.
    intro H. inversion H.
  Qed.

  Theorem STypeEquivNotTransitive : ~(forall T1 T2 T3 : SType, T1 ≡st T2 -> T2 ≡st T3 -> T1 ≡st T3).
  Proof.
    intro stetrans. apply STypeEquivNotTrivial. apply stetrans with (T2 := μ (STypeVar 0)).
    apply STypeEquivAllμX. apply STypeEquivSym. apply STypeEquivAllμX.
  Qed.

  Inductive CtxtStep : (Role -> SType) -> (Role -> SType) -> Prop :=
  | CtxtCommStep : forall Γ Γ' p q τ S T,
      Γ p = SendType q τ S
      -> Γ q  = RecvType p τ T
      -> Γ' p = S
      -> Γ' q = T
      -> (forall (r : Role), r <> p -> r <> q -> Γ r = Γ' r)
      -> CtxtStep Γ Γ'
  | CtxtChoiceStep1 : forall Γ Γ' p q S T1 T2,
      Γ p = EChoiceType q S
      -> Γ q = IChoiceType p T1 T2
      -> Γ' p = S
      -> Γ' q = T1
      -> (forall (r : Role), r <> p -> r <> q -> Γ r = Γ' r)
      -> CtxtStep Γ Γ'
  | CtxtChoiceStep2 : forall Γ Γ' p q S T1 T2,
      Γ p = EChoiceType q S
      -> Γ q = IChoiceType p T1 T2
      -> Γ' p = S
      -> Γ' q = T2
      -> (forall (r : Role), r <> p -> r <> q -> Γ r = Γ' r)
      -> CtxtStep Γ Γ'
  | CtxtμStep : forall Γ Γ' p S,
      Γ p = μ S
      -> Γ' p = S [st| σμ S]
      -> (forall (r : Role), r <> p -> Γ r = Γ' r)
      -> CtxtStep Γ Γ'.

  Lemma CtxtStepExt : forall Γ1 Γ2 Γ1' Γ2',
      (forall r : Role, Γ1 r = Γ1' r)
      -> (forall r : Role, Γ2 r = Γ2' r)
      -> CtxtStep Γ1 Γ2
      -> CtxtStep Γ1' Γ2'.
  Proof.
    intros Γ1 Γ2 Γ1' Γ2' ext_eq1 ext_eq2 step.
    revert Γ1' Γ2' ext_eq1 ext_eq2. induction step; intros Γ1' Γ2' ext_eq1 ext_eq2.
    - apply CtxtCommStep with (p := p) (q := q) (S := S) (T := T) (τ := τ).
      1,2: rewrite <- ext_eq1; auto.
      1,2: rewrite <- ext_eq2; auto.
      intros r neq1 neq2; rewrite <- ext_eq1; rewrite <- ext_eq2; apply H3; auto.
    - apply CtxtChoiceStep1 with (p := p) (q := q) (S := S) (T1 := T1) (T2 := T2).
      1,2: rewrite <- ext_eq1; auto.
      1,2: rewrite <- ext_eq2; auto.
      intros r neq1 neq2; rewrite <- ext_eq1; rewrite <- ext_eq2; apply H3; auto.
    - apply CtxtChoiceStep2 with (p := p) (q := q) (S := S) (T1 := T1) (T2 := T2).
      1,2: rewrite <- ext_eq1; auto.
      1,2: rewrite <- ext_eq2; auto.
      intros r neq1 neq2; rewrite <- ext_eq1; rewrite <- ext_eq2; apply H3; auto.
    - apply CtxtμStep with (p := p) (S := S).
      rewrite <- ext_eq1; auto.
      rewrite <- ext_eq2; auto.
      intros r neq; rewrite <- ext_eq1; rewrite <- ext_eq2; apply H1; auto.
  Qed.

  Inductive CtxtStepMany : (Role -> SType) -> (Role -> SType) -> Prop :=
    CtxtStepZero : forall Γ, CtxtStepMany Γ Γ
  | CtxtStepMore : forall Γ1 Γ2 Γ3, CtxtStep Γ1 Γ2 -> CtxtStepMany Γ2 Γ3 -> CtxtStepMany Γ1 Γ3.

  Inductive LiveContext : (Role -> SType) -> Prop :=
    mkLive : forall Γ : Role -> SType,
      (forall p q τ S, Γ p = SendType q τ S -> exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ')
      -> (forall p q τ S, Γ p = RecvType q τ S -> exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ')
      -> (forall p q S, Γ p = EChoiceType q S ->  exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ')
      -> (forall p q S1 S2, Γ p = IChoiceType q S1 S2 ->  exists Γ', Γ' p = S1 /\ CtxtStepMany Γ Γ')
      -> (forall p q S1 S2, Γ p = IChoiceType q S1 S2 ->  exists Γ', Γ' p = S2 /\ CtxtStepMany Γ Γ')
      -> (forall p S Γ', Γ p = μ S -> (forall r, p <> r -> Γ r = Γ' r) -> Γ' p = S [st| σμ S] -> LiveContext Γ')
      -> (forall Γ', CtxtStep Γ Γ' -> LiveContext Γ')
      -> LiveContext Γ.
          
  Definition LiveSend : forall Γ,
      LiveContext Γ
      -> forall p q τ S, Γ p = SendType q τ S -> exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x
      end.

  Definition LiveRecv : forall Γ,
      LiveContext Γ
      -> forall p q τ S, Γ p = RecvType q τ S -> exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x0
      end.

  Definition LiveEChoice : forall Γ,
      LiveContext Γ
      -> forall p q S, Γ p = EChoiceType q S ->  exists Γ', Γ' p = S /\ CtxtStepMany Γ Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x1
      end.

  Definition LiveIChoice1 : forall Γ,
      LiveContext Γ
      -> forall p q S1 S2, Γ p = IChoiceType q S1 S2 ->  exists Γ', Γ' p = S1 /\ CtxtStepMany Γ Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x2
      end.
  
  Definition LiveIChoice2 : forall Γ,
      LiveContext Γ
      -> forall p q S1 S2, Γ p = IChoiceType q S1 S2 ->  exists Γ', Γ' p = S2 /\ CtxtStepMany Γ Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x3
      end.

  Definition Liveμ : forall Γ,
      LiveContext Γ
      -> forall p S Γ', Γ p = μ S -> (forall r, p <> r -> Γ r = Γ' r) -> Γ' p = S [st| σμ S] -> LiveContext Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x4
      end.

  Definition LiveStep : forall Γ,
      LiveContext Γ
      -> forall Γ', CtxtStep Γ Γ' -> LiveContext Γ' :=
    fun Γ liveΓ =>
      match liveΓ with
      | mkLive Γ x x0 x1 x2 x3 x4 x5 => x5
      end.

  
