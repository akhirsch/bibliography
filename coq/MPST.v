Require Import Coq.Logic.JMeq.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Tactics.

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


  
  Fixpoint TypeToGType (T : SType) : option GSType :=
    match T with
    | EndType => Some (GPlain (GEndType))
    | STypeVar n => Some (GSTypeVar n)
    | μ T' =>
      match TypeToGType' T' with
      | Some T'' => Some (Gμ T'')
      | None => None
      end
    | SendType p τ T1 =>
      match TypeToGType T1 with
      | Some T2 => Some (GPlain (GSendType p τ T2))
      | None => None
      end
    | RecvType p τ T1 =>
      match TypeToGType T1 with
      | Some T2 => Some (GPlain (GRecvType p τ T2))
      | None => None
      end
    | EChoiceType p T1 =>
      match TypeToGType T1 with
      | Some T2 => Some (GPlain (GEChoiceType p T2))
      | None => None
      end
    | IChoiceType p T11 T21 =>
      match TypeToGType T11 with
      | Some T12 =>
        match TypeToGType T21 with
        | Some T22 => Some (GPlain (GIChoiceType p T12 T22))
        | None => None
        end
      | None => None
      end
    end
  with TypeToGType' (T' : SType) : option GSType' :=
         match T' with
         | EndType => Some GEndType
         | SendType p τ T1 =>
           match TypeToGType T1 with
           | Some T2 => Some (GSendType p τ T2)
           | None => None
           end
         | RecvType p τ T1 =>
           match TypeToGType T1 with
           | Some T2 => Some (GRecvType p τ T2)
           | None => None
           end
         | EChoiceType p T1 =>
           match TypeToGType T1 with
           | Some T2 => Some (GEChoiceType p T2)
           | None => None
           end
         | IChoiceType p T11 T21 =>
           match TypeToGType T11 with
           | Some T12 => match TypeToGType T21 with
                        | Some T22 => Some (GIChoiceType p T12 T22)
                        | None => None
                        end
           | None => None
           end
         | _ => None
         end.

  Lemma GuardedPlainTypeToGTypeMaster : forall (T : SType),
      GuardedType T -> (exists GT, TypeToGType T = Some GT)
                      /\ (Plain T -> exists GT', TypeToGType' T = Some GT').
  Proof.
    intro T; induction T; intros gT.
    all: split;[|intro pT]; simpl; try (eexists; eauto; fail).
    all: try (inversion pT; fail).
    all: inversion gT.
    all: repeat match goal with
                | [H: ?P, IH : ?P -> ?Q |- _] => specialize (IH H)
                | [H : ?P /\ ?Q |- _] => destruct H
                | [H : exists x, TypeToGType ?T = Some x |- _] =>
                  let GT := fresh "GT" in
                  let HGT := fresh "HGT" in 
                  destruct H as [GT HGT]
                | [H : exists x, TypeToGType' ?T = Some x |- _] =>
                  let GT := fresh "GT'" in
                  let HGT := fresh "HGT'" in 
                  destruct H as [GT HGT]
                end.
    all: try (rewrite HGT; eexists; eauto; fail).
    rewrite HGT'; eexists; eauto.
    all: rewrite HGT; rewrite HGT0; eexists; eauto.
  Qed.        
  
  Lemma GuardedTypeToGType : forall (T : SType),
      GuardedType T -> exists GT, TypeToGType T = Some GT.
  Proof.
    apply GuardedPlainTypeToGTypeMaster.
  Qed.

  Lemma GuardedPlainTypeToGType : forall (T : SType),
      GuardedType T -> Plain T -> exists GT', TypeToGType' T = Some GT'.
  Proof.
    apply GuardedPlainTypeToGTypeMaster.
  Qed.

  Lemma STypeThroughGTypeIdMaster : forall (T : SType),
      (forall GT : GSType, TypeToGType T = Some GT -> FlattenGSType GT = T)
      /\ (forall GT' : GSType', TypeToGType' T = Some GT' -> FlattenGSType' GT' = T).
  Proof.
    intro T; induction T; split.
    1,3,5,7,9,11,13: intros GT eq.
    8,9,10,11,12,13,14: intros GT' eq.
    all: simpl in *; try (inversion eq; simpl; auto; fail).
    all: try (destruct IHT; destruct (TypeToGType T); inversion eq).
    destruct (TypeToGType' T) eqn:e; inversion eq.
    simpl. rewrite (H0 g0 eq_refl). reflexivity.
    destruct (TypeToGType' T) eqn:e; inversion eq.
    simpl. rewrite (H0 g eq_refl). reflexivity.
    all: simpl.
    all: try (match goal with
              | [H : (forall g, Some ?g' = Some g -> FlattenGSType g = ?T) |- context[(FlattenGSType ?g')] ]
                => rewrite (H g' eq_refl)
              end; reflexivity).
    all: destruct (TypeToGType T1) eqn:e1; [|inversion eq].
    all: destruct (TypeToGType T2) eqn:e2; inversion eq; simpl in *.
    all: destruct IHT1; destruct IHT2.
    - rewrite (H g eq_refl); rewrite (H2 g0 eq_refl); reflexivity.
    - rewrite (H g eq_refl); rewrite (H2 g0 eq_refl); reflexivity.
  Qed.
  Lemma STypeThroughGTypeId : forall (T : SType) (GT : GSType),
      TypeToGType T = Some GT -> FlattenGSType GT = T.
  Proof.
    apply STypeThroughGTypeIdMaster.
  Qed.
  Lemma STypeThroughGType'Id : forall (T : SType) (GT : GSType'),
      TypeToGType' T = Some GT -> FlattenGSType' GT = T.
  Proof.
    apply STypeThroughGTypeIdMaster.
  Qed.

  Lemma TypeToGType'ImpliesTypeToGType : forall (T : SType) (GT' :GSType'),
      TypeToGType' T = Some GT' -> exists GT, TypeToGType T = Some GT.
  Proof.
    intro T; induction T; intros GT' HGT'; simpl in *; try (eexists; eauto; fail).
    all: try (destruct (TypeToGType T));
      repeat match goal with
             | [ H : None = Some _ |- _ ] => inversion H
             end; try (eexists; eauto; fail).
    destruct (TypeToGType T1); destruct (TypeToGType T2); try (inversion HGT'; fail).
    eexists; eauto.
  Qed.
  
  Lemma GTypeThroughSType : forall GT : GSType, TypeToGType (FlattenGSType GT) = Some GT.
  Proof.
    intro GT; induction GT using GSTypeInd
                with (P := fun GT' =>
                             (TypeToGType' (FlattenGSType' GT') = Some GT')
                             /\ (TypeToGType (FlattenGSType' GT') = Some (GPlain GT')));
    simpl; auto.
    all: try (rewrite IHGT); auto.
    - rewrite IHGT1; rewrite IHGT2; auto.
    - destruct IHGT. rewrite H. reflexivity.
    - destruct IHGT. exact H0.
  Qed.

  Lemma GType'ThroughSTypeMaster : forall (GT' : GSType'),
      TypeToGType' (FlattenGSType' GT') = Some GT'
      /\ TypeToGType (FlattenGSType' GT') = Some (GPlain GT').
  Proof.
    intro GT'; induction GT' using GSType'Ind
                 with (Q := fun GT => TypeToGType (FlattenGSType GT) = Some GT);
    simpl; auto.
    all: try (rewrite IHGT'); auto.
    - rewrite IHGT'0; auto.
    - destruct IHGT'. rewrite H. reflexivity.
    - destruct IHGT'. exact H0.
  Qed.

  Lemma GType'ThroughSType : forall (GT' : GSType'),
      TypeToGType' (FlattenGSType' GT') = Some GT'.
  Proof.
    apply GType'ThroughSTypeMaster.
  Qed.

  Lemma GTypeThroughSType' :  forall (GT' : GSType'),
      TypeToGType (FlattenGSType' GT') = Some (GPlain GT').
  Proof.
    apply GType'ThroughSTypeMaster.
  Qed.

  Lemma LiftTypeToGType' : forall (T : SType) (GT' : GSType'),
      TypeToGType' T = Some GT' -> TypeToGType T = Some (GPlain GT').
  Proof.
    intro T; induction T; simpl; intros GT' eq; try (inversion eq; reflexivity; fail).
    all: try (destruct (TypeToGType T); inversion eq; reflexivity).
    destruct (TypeToGType T1); [|inversion eq];
      destruct (TypeToGType T2); inversion eq; reflexivity.
  Qed.                                                 

  Lemma TypeToGTypeRenameMaster : forall (T : SType)(ξ : nat -> nat),
      (forall GT : GSType,
          TypeToGType T = Some GT
          -> TypeToGType (T ⟨st| ξ⟩) = Some (GT ⟨gst| ξ⟩))
      /\ (forall GT' : GSType',
            TypeToGType' T = Some GT'
            -> TypeToGType' (T ⟨st| ξ⟩) = Some (GT' ⟨gst'| ξ⟩)).
  Proof.
    intro T; induction T; intro ξ.
    all: split; [intro GT | intro GT']; intro eq; simpl in *; auto;
      try (inversion eq; simpl; auto; fail).
    all: try (specialize (IHT ξ); destruct IHT as [IHT IHT'];
              destruct (TypeToGType T) as [GT2|]; inversion eq;
              rewrite IHT with (GT := GT2); simpl; reflexivity).
    - destruct (IHT (RenamingUp ξ)) as [IHTξ IHT'ξ].
      destruct (TypeToGType' T) as [GT'|]; [|inversion eq].
      rewrite IHT'ξ with (GT'0 := GT'); [| reflexivity].
      inversion eq. simpl. reflexivity.
    - specialize (IHT1 ξ); destruct IHT1 as [IHT1 IHT1'].
      specialize (IHT2 ξ); destruct IHT2 as [IHT2 IHT2'].
      destruct (TypeToGType T1) as [GT1 |]; [|inversion eq];
        destruct (TypeToGType T2) as [GT2 |]; inversion eq.
      rewrite IHT1 with (GT := GT1); [|reflexivity].
      rewrite IHT2 with (GT := GT2); reflexivity.
    - specialize (IHT1 ξ); destruct IHT1 as [IHT1 IHT1'].
      specialize (IHT2 ξ); destruct IHT2 as [IHT2 IHT2'].
      destruct (TypeToGType T1) as [GT1 |]; [|inversion eq];
        destruct (TypeToGType T2) as [GT2 |]; inversion eq.
      rewrite IHT1 with (GT := GT1); [|reflexivity].
      rewrite IHT2 with (GT := GT2); reflexivity.
  Qed.
  Lemma TypeToGTypeRename : forall (T : SType)(ξ : nat -> nat) (GT : GSType),
      TypeToGType T = Some GT
      -> TypeToGType (T ⟨st| ξ⟩) = Some (GT ⟨gst| ξ⟩).
  Proof.
    apply TypeToGTypeRenameMaster.
  Qed.
  Lemma TypeToGType'Rename : forall (T : SType) (ξ : nat -> nat) (GT' : GSType'),
      TypeToGType' T = Some GT'
      -> TypeToGType' (T ⟨st| ξ⟩) = Some (GT' ⟨gst'| ξ⟩).
  Proof.
    apply TypeToGTypeRenameMaster.
  Qed.
      
  Lemma TypeToGTypeSubstMaster : forall (T : SType)(σ : nat -> SType) (gσ : nat -> GSType),
      (forall n, TypeToGType (σ n) = Some (gσ n))
      -> (forall GT : GSType, TypeToGType T = Some GT
         -> TypeToGType (T [st| σ]) = Some (GT [gst| gσ]))
      /\ (forall GT' : GSType', TypeToGType' T = Some GT'
         -> TypeToGType' (T [st| σ]) = Some (GT' [gst'| gσ])).
  Proof.
    intro T; induction T; intros σ gσ ext_eq.
    all: split; [intros GT eq | intros GT' eq].
    all: simpl in *; try (inversion eq; simpl; auto; fail).
    all: try (specialize (IHT σ gσ ext_eq); destruct IHT as [IHT IHT'];
              destruct (TypeToGType T) as [GT1 |]; inversion eq;
              rewrite IHT with (GT := GT1); simpl; reflexivity).
    2,3: specialize (IHT1 σ gσ ext_eq); destruct IHT1 as [IHT1 IHT1'];
      specialize (IHT2 σ gσ ext_eq); destruct IHT2 as [IHT2 IHT2'];
        destruct (TypeToGType T1) as [GT1 |]; [|inversion eq];
          destruct (TypeToGType T2) as [GT2|]; inversion eq;
            rewrite (IHT1 GT1); [|reflexivity]; rewrite (IHT2 GT2); simpl; reflexivity.
    specialize IHT with (σ := STypeSubstUp σ) (gσ := GSTypeSubstUp gσ).
    destruct IHT as [IHT IHT'].
    intro n; destruct n; unfold STypeSubstUp; unfold GSTypeSubstUp; auto.
    rewrite TypeToGTypeRename with (GT := gσ n); [reflexivity | apply ext_eq].
    destruct (TypeToGType' T) as [GT' |]; inversion eq.
    rewrite IHT' with (GT'0 := GT'); simpl; reflexivity.
  Qed.

  Lemma TypeToGTypeSubst : forall (T : SType)(σ : nat -> SType) (gσ : nat -> GSType) (GT : GSType),
      (forall n, TypeToGType (σ n) = Some (gσ n))
      -> TypeToGType T = Some GT
      -> TypeToGType (T [st| σ]) = Some (GT [gst| gσ]).
  Proof.
    intros T σ gσ GT H H0.
    apply TypeToGTypeSubstMaster; auto.
  Qed.
                                                      
  Lemma TypeToGType'Subst : forall (T : SType)(σ : nat -> SType) (gσ : nat -> GSType) (GT' : GSType'),
      (forall n, TypeToGType (σ n) = Some (gσ n))
      -> TypeToGType' T = Some GT'
      -> TypeToGType' (T [st| σ]) = Some (GT' [gst'| gσ]).
  Proof.
    intros T σ gσ GT' H H0.
    apply TypeToGTypeSubstMaster; auto.
  Qed.
  
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

  Ltac GuardedTypeEquiv1Tac :=
    repeat match goal with
           | [ |- ?a = ?a ] => reflexivity
           | [ H : TypeToGType _ = Some _ |- _ ] => simpl in H
           | [ H : match (TypeToGType ?T) with
                   | Some _ => _
                   | None => _
                   end = Some _ |- _] => destruct (TypeToGType T)
           | [ H: None = Some _ |- _] => inversion H
           | [ H : Some ?a = Some ?b |- _] =>
             match goal with
             | [_ : a = b |- _ ] => fail 1
             |  _ => inversion H;
                    assert (a = b) by (inversion H; auto)
             end
           end.

  Obligation Tactic := program_simpl; GuardedTypeEquiv1Tac.

  Program CoFixpoint GuardedTypeEquiv1 (T1 T2 : SType) (GT1 GT2 : GSType)
          (eq1 : TypeToGType T1 = Some GT1) (eq2 : TypeToGType T2 = Some GT2)
          (equiv : T1 ≡st T2) : GT1 ≡gst GT2 :=
  match equiv with
  | EndEquiv => GPlainEquiv (GEndEquiv)
  | VarEquiv n => GVarEquiv n
  | SendEquiv p τ equiv' =>
    match GT1 with
    | Gμ x => _
    | GSTypeVar x => _
    | GPlain GT1' =>
      match GT1' with
      | GEndType => _
      | GSendType _ _ GT1'' =>
        match GT2 with
        | Gμ x => _
        | GSTypeVar x => _
        | GPlain GT2' =>
          match GT2' with
          | GEndType => _
          | GSendType _ _ GT2'' =>
            GPlainEquiv (GSendEquiv p τ (GuardedTypeEquiv1 _ _ GT1'' GT2'' _ _ equiv'))
          | GRecvType x x0 x1 => _
          | GEChoiceType x x0 => _
          | GIChoiceType x x0 x1 => _
          end
        end
      | GRecvType x x0 x1 => _
      | GEChoiceType x x0 => _
      | GIChoiceType x x0 x1 => _
      end
    end
  | RecvEquiv p τ equiv' =>
    match GT1 with
    | Gμ x => _
    | GSTypeVar x => _
    | GPlain GT1' =>
      match GT1' with
      | GEndType => _
      | GSendType x x0 x1 => _
      | GRecvType _ _ GT1'' =>
        match GT2 with
        | Gμ x => _
        | GSTypeVar x => _
        | GPlain GT2' =>
          match GT2' with
          | GEndType => _
          | GSendType x x0 x1 => _
          | GRecvType _ _ GT2'' =>
            GPlainEquiv (GRecvEquiv p τ (GuardedTypeEquiv1 _ _ GT1'' GT2'' _ _ equiv'))
          | GEChoiceType x x0 => _
          | GIChoiceType x x0 x1 => _
          end
        end
      | GEChoiceType x x0 => _
      | GIChoiceType x x0 x1 => _
      end
    end
  | EChoiceEquiv p equiv' =>
    match GT1 with
    | Gμ x => _
    | GSTypeVar x => _
    | GPlain GT1' =>
      match GT1' with
      | GEndType => _
      | GSendType x x0 x1 => _
      | GRecvType x x0 x1 => _
      | GEChoiceType _ GT1'' =>
        match GT2 with
        | Gμ x => _
        | GSTypeVar x => _
        | GPlain GT2' =>
          match GT2' with
          | GEndType => _
          | GSendType x x0 x1 => _
          | GRecvType x x0 x1 => _
          | GEChoiceType _ GT2'' =>
            GPlainEquiv (GEChoiceEquiv p (GuardedTypeEquiv1 _ _ GT1'' GT2'' _ _ equiv'))
          | GIChoiceType x x0 x1 => _
          end
        end
      | GIChoiceType x x0 x1 => _
      end
    end
  | IChoiceEquiv p equiv'1 equiv'2 =>
    match GT1 with
    | Gμ x => _
    | GSTypeVar x => _
    | GPlain GT1' =>
      match GT1' with
      | GEndType => _
      | GSendType x x0 x1 => _
      | GRecvType x x0 x1 => _
      | GEChoiceType x x0 => _
      | GIChoiceType _ GT11 GT12 =>
        match GT2 with
        | Gμ x => _
        | GSTypeVar x => _
        | GPlain GT2' =>
          match GT2' with
          | GEndType => _
          | GSendType x x0 x1 => _
          | GRecvType x x0 x1 => _
          | GEChoiceType x x0 => _
          | GIChoiceType _ GT21 GT22 =>
            GPlainEquiv (GIChoiceEquiv p (GuardedTypeEquiv1 _ _ GT11 GT21 _ _ equiv'1)
                                       (GuardedTypeEquiv1 _ _ GT12 GT22 _ _ equiv'2))
          end
        end
      end
    end
  | @μEquivL T1' _ equiv' =>
    match (TypeToGType' T1') with
    | Some T1'' => @GμEquivL T1'' _ (GuardedTypeEquiv1 _ _ _ _ _ _ equiv')
    | None => _
    end
  | @μEquivR _ T2' equiv' =>
    match (TypeToGType' T2') with
    | Some T2'' =>  @GμEquivR _ T2'' (GuardedTypeEquiv1 _ _ _ _ _ _ equiv')
    | None => _
    end
  end.
  Next Obligation.
    rewrite <- H0; rewrite <- H1; rewrite <- H4; rewrite <- H5; reflexivity.
  Defined.
  Next Obligation.
    rewrite <- H0; rewrite <- H1; rewrite <- H4; rewrite <- H5; reflexivity.
  Defined.
  Next Obligation.
    rewrite <- H0; rewrite <- H3; reflexivity.
  Defined.
  Next Obligation.
    rewrite <- H0. rewrite <- H4. reflexivity.
  Defined.
  Next Obligation.
    simpl in eq1. destruct (TypeToGType' T1') as [GT1'|] eqn:e; inversion eq1.
    inversion Heq_anonymous.
    rewrite TypeToGTypeSubst with (gσ := gσμ GT1') (GT := GPlain GT1').
    simpl. reflexivity.
    intro n; unfold σμ; unfold gσμ; destruct n; auto.
    simpl. rewrite e. reflexivity.
    apply LiftTypeToGType'; auto.
  Defined.
  Next Obligation.
    simpl in eq1. destruct (TypeToGType' T1') as [GT1'|] eqn:e; inversion eq1.
    inversion Heq_anonymous. rewrite <- H1. reflexivity.
  Defined.
  Next Obligation.
    simpl in eq1. destruct (TypeToGType' T1'); [inversion Heq_anonymous | inversion eq1].
  Defined.
  Next Obligation.
    destruct (TypeToGType' T2') as [GT2'|] eqn:e; inversion eq2.
    inversion Heq_anonymous.
    rewrite TypeToGTypeSubst with (gσ := gσμ GT2') (GT := GPlain GT2').
    simpl; reflexivity.
    intro n; unfold σμ; unfold gσμ; destruct n; auto.
    simpl. rewrite e. reflexivity.
    apply LiftTypeToGType'; auto.
  Defined.
  Next Obligation.
    destruct (TypeToGType' T2'); inversion eq2.
    inversion Heq_anonymous. reflexivity.
  Defined.
  Next Obligation.
    destruct (TypeToGType' T2'); [inversion Heq_anonymous | inversion eq2].
  Defined.

  Program CoFixpoint GuardedTypeEquiv2 (T1 T2 : SType) (GT1 GT2 : GSType)
          (eq1 : TypeToGType T1 = Some GT1) (eq2 : TypeToGType T2 = Some GT2)
          (equiv : GT1 ≡gst GT2) : T1 ≡st T2 :=
    match equiv with
    | GVarEquiv n => VarEquiv n
    | @GμEquivL GT1' _ equiv' => μEquivL (GuardedTypeEquiv2 _ _ (GPlain (GT1' [gst'| gσμ GT1'])) _ _ _ equiv')
    | GμEquivR x => _
    | GPlainEquiv equiv' => GuardedTypeEquiv2' _ _ _ _ _ _ equiv'
    end
  with GuardedTypeEquiv2' (T1 T2 : SType) (GT1' GT2' : GSType')
          (eq1 : TypeToGType' T1 = Some GT1') (eq2 : TypeToGType' T2 = Some GT2')
          (equiv : GT1' ≡gst' GT2') : T1 ≡st T2 :=
         _.
  Next Obligation.
    destruct T1; simpl in eq1; inversion eq1. reflexivity.
    all: try (destruct (TypeToGType' T1); inversion eq1; fail).
    all: try (destruct (TypeToGType T1); inversion eq1; fail).
    destruct (TypeToGType T1_1); [|inversion eq1];
      destruct (TypeToGType T1_2); inversion eq1.
  Defined.
  Next Obligation.
    destruct T2; simpl in eq2; inversion eq2. reflexivity.
    all: try (destruct (TypeToGType' T2); inversion eq2; fail).
    all: try (destruct (TypeToGType T2); inversion eq2; fail).
    destruct (TypeToGType T2_1); [|inversion eq2];
      destruct (TypeToGType T2_2); inversion eq2.
  Defined.
  Next Obligation.
    unfold GuardedTypeEquiv2_obligation_3; simpl.
    unfold eq_rec_r. simpl.
    rewrite TypeToGTypeSubst with (gσ := gσμ GT1') (GT := GPlain GT1'); simpl.
    reflexivity.
    intro n; unfold σμ; unfold gσμ; destruct n; auto. simpl.
                                         
  (* Lemma SigmaMuConnection : forall (T1 : SType) (G : GuardedType T1) (P : Plain T1),  *)
  (*     ReflectGuardedType (T1 [st| σμ T1]) *)
  (*                        (GuardedTypeSubst T1 (σμ T1) G (SigmaMuGuarded T1 G P)) *)
  (*     = (GSTypeSubst (ReflectGuardedType T1 G) (gσμ (ReflectGuardedPlainType T1 G P))). *)
  (* Proof. *)
  (*   intro T1; induction T1; intros G P; try (inversion G; inversion P; fail); auto. *)
  (*   simpl. fold ReflectGuardedType. *)
  (* Admitted. *)
                                          
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

  
