Require Import Coq.Logic.JMeq.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.

Require Export Expression.
Require Export TypedExpression.

Module MPST (E : Expression) (TE : TypedExpression E).
  Import E.
  Import TE.
  
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
  
  Inductive Chan : Set :=
    ChanVar : nat -> Chan
  | Session : nat -> Role -> Chan.
  Hint Constructors Chan : PiC.

  Lemma ChanEqDec : forall χ1 χ2 : Chan, {χ1 = χ2} + {χ1 <> χ2}.
  Proof.
    decide equality; auto with PiC; apply Nat.eq_dec.
  Qed.
  Hint Resolve ChanEqDec : PiC.
  Definition ChanRename : Chan -> (nat -> nat) -> Chan :=
    fun χ ξ => match χ with
            | ChanVar n => ChanVar (ξ n)
            | Session _ _ => χ
            end.
  Notation "χ ⟨ch| ξ ⟩" := (ChanRename χ ξ) (at level 15).

  Lemma ChanIdRenaming : forall χ : Chan, χ ⟨ch| IdRenaming⟩ = χ.
  Proof.
    induction χ; auto.
  Qed.
  Hint Resolve ChanIdRenaming : PiC.
  Hint Rewrite ChanIdRenaming : PiC.

  Lemma ChanRenameExt : forall (χ : Chan) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> χ ⟨ch| ξ1⟩ = χ ⟨ch| ξ2⟩.
  Proof.
    intros χ ξ1 ξ2 ext_eq; induction χ; simpl; auto.
  Qed.
  Hint Resolve ChanRenameExt : PiC.
  Hint Rewrite ChanRenameExt : PiC.

  Definition ChanSessionRename : Chan -> (nat -> nat) -> Chan :=
    fun χ ξ => match χ with
            | ChanVar _ => χ
            | Session n p => Session (ξ n) p
            end.
  Notation "χ ⟨chs| ξ ⟩" := (ChanSessionRename χ ξ) (at level 15).
  
  Lemma ChanIdSessionRenaming : forall χ : Chan, χ ⟨chs|IdRenaming⟩ = χ.
  Proof.
    intro χ; induction χ; auto.
  Qed.
  Hint Resolve ChanIdSessionRenaming : PiC.
  Hint Rewrite ChanIdSessionRenaming : PiC.

  Lemma ChanSessionRenameExt : forall (χ : Chan) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> χ ⟨chs| ξ1⟩ = χ ⟨chs| ξ2⟩.
  Proof.
    intros χ ξ1 ξ2 ext_eq; destruct χ; simpl; auto.
    rewrite ext_eq; reflexivity.
  Qed.
  Hint Resolve ChanSessionRenameExt : PiC.
  Hint Rewrite ChanSessionRenameExt : PiC.

  Definition ChanSubstUp : (nat -> Chan) -> nat -> Chan :=
    fun σ n => match n with
            | 0 => ChanVar 0
            | S m => σ m ⟨ch| S⟩
            end.
  Lemma ChanSubstUpExt : forall (σ1 σ2 : nat -> Chan),
      (forall n, σ1 n = σ2 n)
      -> forall n, ChanSubstUp σ1 n = ChanSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; destruct n; simpl; [|rewrite ext_eq]; reflexivity.
  Qed.
  Hint Resolve ChanSubstUpExt : PiC.
  Hint Rewrite ChanSubstUpExt : PiC.
  
  Definition ChanSubst : Chan -> (nat -> Chan) -> Chan :=
    fun χ σ => match χ with
            | ChanVar n => (σ n)
            | Session _ _ => χ
            end.
  Notation "χ [ch| σ ]" := (ChanSubst χ σ) (at level 15).

  Definition ChanIdSubst : nat -> Chan := fun n => ChanVar n.
  Lemma ChanIdSubstSpec : forall χ : Chan, χ [ch| ChanIdSubst] = χ.
  Proof.
    induction χ; auto.
  Qed.
  Hint Resolve ChanIdSubstSpec : PiC.
  Hint Rewrite ChanIdSubstSpec : PiC.

  Lemma ChanSubstIdUp : forall n, ChanSubstUp ChanIdSubst n = ChanIdSubst n.
  Proof.
    intro n; induction n; simpl; auto.
  Qed.
  Hint Resolve ChanSubstIdUp : PiC.
  Hint Rewrite ChanSubstIdUp : PiC.

  Lemma ChanSubstExt : forall (χ : Chan) (σ1 σ2 : nat -> Chan),
      (forall n, σ1 n = σ2 n)
      -> χ [ch| σ1] = χ [ch| σ2].
  Proof.
    intros χ σ1 σ2 ext_eq; induction χ; simpl; auto.
  Qed.
  Hint Resolve ChanSubstExt : PiC.
  Hint Rewrite ChanSubstExt : PiC.

  (* We only support binary choices. *)
  Inductive SessionType : Set :=
    EndType : SessionType
  | TypeVar : nat -> SessionType
  | μ : SessionType -> SessionType
  | EChoice : Role -> SessionType -> SessionType
  | IChoice : Role -> SessionType -> SessionType -> SessionType
  | SendT : Role -> SessionType -> SessionType -> SessionType
  | ReceiveT : Role -> SessionType -> SessionType -> SessionType
  | SendDT : Role -> ExprTyp -> SessionType -> SessionType
  | ReceiveDT : Role -> ExprTyp -> SessionType -> SessionType.
  Hint Constructors SessionType : PiC.
  Definition SessionTypeEqDec : forall S1 S2 : SessionType, {S1 = S2} + {S1 <> S2}.
  Proof.
    intros S1 S2; decide equality; auto with PiC.
    apply Nat.eq_dec.
    all: apply ExprTypEqDec.
  Qed.

  Fixpoint SessionTypeRename (S : SessionType) (ξ : nat -> nat) : SessionType :=
    match S with
    | EndType => EndType
    | TypeVar n => TypeVar (ξ n)
    | μ S' => μ (SessionTypeRename S' (RenamingUp ξ))
    | EChoice p S' => EChoice p (SessionTypeRename S' ξ)
    | IChoice p S1 S2 => IChoice p (SessionTypeRename S1 ξ) (SessionTypeRename S2 ξ)
    | SendT p S1 S2 => SendT p (SessionTypeRename S1 ξ) (SessionTypeRename S2 ξ)
    | ReceiveT p S1 S2 => ReceiveT p (SessionTypeRename S1 ξ) (SessionTypeRename S2 ξ)
    | SendDT p τ S' => SendDT p τ (SessionTypeRename S' ξ)
    | ReceiveDT p τ S' => ReceiveDT p τ (SessionTypeRename S' ξ)
    end.
  Notation "S ⟨s| ξ ⟩" := (SessionTypeRename S ξ) (at level 15).

  Lemma SessionTypeRenameExt : forall (S : SessionType) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> S ⟨s| ξ1⟩ = S ⟨s| ξ2⟩.
  Proof.
    intro S; induction S; intros ξ1 ξ2 ext_eq; simpl; auto.
    1: rewrite IHS with (ξ2 := RenamingUp ξ2); auto.
    apply RenamingUpExt; auto.
    1,5,6: rewrite IHS with (ξ2 := ξ2); auto.
    all: rewrite IHS1 with (ξ2 := ξ2); auto; rewrite IHS2 with (ξ2 := ξ2); auto.
  Qed.
  Hint Resolve SessionTypeRenameExt : PiC.
  Hint Rewrite SessionTypeRenameExt : PiC.

  Lemma SessionTypeIdRenamingSpec : forall S : SessionType, S ⟨s|IdRenaming⟩ = S.
  Proof.
    intro S; induction S; simpl; auto.
    rewrite SessionTypeRenameExt with (ξ2 := IdRenaming).
    rewrite IHS; reflexivity.
    apply IdRenamingUp.
    1,5,6: rewrite IHS; auto.
    all: rewrite IHS1; rewrite IHS2; auto.
  Qed.
  Hint Resolve SessionTypeIdRenamingSpec : PiC.
  Hint Rewrite SessionTypeIdRenamingSpec : PiC.

  Definition SessionTypeSubstUp : (nat -> SessionType) -> nat -> SessionType :=
    fun σ n => match n with
            | 0 => TypeVar 0
            | S n' => (σ n') ⟨s| S⟩
            end.

  Lemma SessionTypeSubstUpExt : forall (σ1 σ2 : nat -> SessionType),
      (forall n : nat, σ1 n = σ2 n)
      -> forall n : nat, SessionTypeSubstUp σ1 n = SessionTypeSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n.
    unfold SessionTypeSubstUp; destruct n; auto.
    rewrite ext_eq; reflexivity.
  Qed.
  Hint Resolve SessionTypeSubstUpExt : PiC.
  Hint Rewrite SessionTypeSubstUpExt : PiC.
  
  Fixpoint SessionTypeSubst (S : SessionType) (σ : nat -> SessionType) : SessionType :=
    match S with
    | EndType => EndType
    | TypeVar n => σ n
    | μ S' => μ (SessionTypeSubst S' (SessionTypeSubstUp σ))
    | EChoice p S' => EChoice p (SessionTypeSubst S' σ)
    | IChoice p S1 S2 => IChoice p (SessionTypeSubst S1 σ) (SessionTypeSubst S2 σ)
    | SendT p S1 S2 => SendT p (SessionTypeSubst S1 σ) (SessionTypeSubst S2 σ)
    | ReceiveT p S1 S2 => ReceiveT p (SessionTypeSubst S1 σ) (SessionTypeSubst S2 σ)
    | SendDT p τ S' => SendDT p τ (SessionTypeSubst S' σ)
    | ReceiveDT p τ S' => ReceiveDT p τ (SessionTypeSubst S' σ)
    end.
  Notation "S [s| σ ]" := (SessionTypeSubst S σ) (at level 15).

  Lemma SessionTypeSubstExt : forall (S : SessionType) (σ1 σ2 : nat -> SessionType),
      (forall n, σ1 n = σ2 n)
      -> S [s| σ1] = S [s| σ2].
  Proof.
    intro S; induction S; intros σ1 σ2 ext_eq; simpl; auto with PiC.
    rewrite IHS with (σ2 := SessionTypeSubstUp σ2); auto.
    apply SessionTypeSubstUpExt; auto.
    1,5,6:rewrite IHS with (σ2 := σ2); auto.
    all: rewrite IHS1 with (σ2 := σ2); auto; rewrite IHS2 with (σ2 := σ2); auto.
  Qed.    
  Hint Resolve SessionTypeSubstExt : PiC.
  Hint Rewrite SessionTypeSubstExt : PiC.

  Definition SessionTypeIdSubst : nat -> SessionType :=
    fun n => TypeVar n.
  Lemma SessionTypeIdSubstUp :
    forall n, SessionTypeSubstUp SessionTypeIdSubst n = SessionTypeIdSubst n.
  Proof.
    intro n; induction n; unfold SessionTypeSubstUp; unfold SessionTypeIdSubst;
      simpl; reflexivity.
  Qed.
  Hint Resolve SessionTypeIdSubstUp : PiC.
  Hint Rewrite SessionTypeIdSubstUp : PiC.

  Lemma SessionTypeIdSubstSpec : forall (S : SessionType),
      S [s| SessionTypeIdSubst] = S.
  Proof.
    intro S; induction S; simpl; auto.
    rewrite SessionTypeSubstExt with (σ2 := SessionTypeIdSubst);
      [rewrite IHS; auto | apply SessionTypeIdSubstUp].
    1,5,6:rewrite IHS; auto.
    all: rewrite IHS1; rewrite IHS2; auto.
  Qed.
  Hint Resolve SessionTypeIdSubstSpec : PiC.
  Hint Rewrite SessionTypeIdSubstSpec : PiC.

  CoInductive SessionSubtype : SessionType -> SessionType -> Prop :=
  | SubRefl: forall S : SessionType, SessionSubtype S S
  | SubTrans : forall S T U : SessionType,
      SessionSubtype S T
      -> SessionSubtype T U
      -> SessionSubtype S U
  | SubEnd : SessionSubtype (EndType) (EndType)
  | SubμL : forall S T : SessionType,
      SessionSubtype (SessionTypeSubst S (fun n =>
                                          match n with
                                          | 0 => μ S
                                          | S n' => TypeVar n'
                                          end)) T
      -> SessionSubtype (μ S) T
  | SubμR : forall S T : SessionType,
      SessionSubtype S (SessionTypeSubst T (fun n =>
                                          match n with
                                          | 0 => μ T
                                          | S n' => TypeVar n'
                                          end))
      -> SessionSubtype S (μ T)
  | SubEChoice : forall p S T,
      SessionSubtype S T
      -> SessionSubtype (EChoice p S) (EChoice p T)
  | SubIChoice : forall p S1 S2 T1 T2,
      SessionSubtype S1 T1
      -> SessionSubtype S2 T2
      -> SessionSubtype (IChoice p S1 S2) (IChoice p T1 T2)
  | SubSend : forall p S1 S2 T1 T2,
      SessionSubtype S1 T1
      -> SessionSubtype S2 T2
      -> SessionSubtype (SendT p S1 S2) (SendT p T1 T2)
  | SubReceive : forall p S1 S2 T1 T2,
      SessionSubtype T1 S1 (* Note Contravariance! *)
      -> SessionSubtype S2 T2
      -> SessionSubtype (ReceiveT p S1 S2) (ReceiveT p T1 T2)
  | SubSendDT : forall p τ S1 S2,
      SessionSubtype S1 S2
      -> SessionSubtype (SendDT p τ S1) (SendDT p τ S2)
  | SubReceiveDT : forall p τ S1 S2,
      SessionSubtype S1 S2
      -> SessionSubtype (ReceiveDT p τ S1) (ReceiveDT p τ S2).
  Infix "≤s" := SessionSubtype (at level 16).
  Hint Constructors SessionSubtype : PiC.

  Instance sessionSubtypeRefl  : Reflexive SessionSubtype  := SubRefl.
  Instance sessionSubtypeTrans : Transitive SessionSubtype := SubTrans.

  Inductive PiCtxtRed : (Chan -> SessionType) -> (Chan -> SessionType) -> Prop :=
    DataCommCtxtR : forall (Γ Δ : Chan -> SessionType) (s : nat) (p q : Role) (τ : ExprTyp)
                      (S1 S2 : SessionType),
      Γ (Session s p) = SendDT q τ S1
      -> Γ (Session s q) = ReceiveDT p τ S2
      -> Δ (Session s p) = S1
      -> Δ (Session s q) = S2
      -> (forall χ : Chan, (Session s p) <> χ -> (Session s q) <> χ -> Γ χ = Δ χ)
      -> PiCtxtRed Γ Δ                         
  | CommCtxtR : forall (Γ Δ : Chan -> SessionType) (s : nat) (p q  : Role)
                  (S1 S2 T1 T2 : SessionType),
      Γ (Session s p) = SendT q S1 S2
      -> Γ (Session s q) = ReceiveT p T1 T2
      -> S1 ≤s T1
      -> Δ (Session s p) = S2
      -> Δ (Session s q) = T2
      -> (forall χ : Chan, (Session s p) <> χ -> (Session s q) <> χ -> Γ χ = Δ χ)
      -> PiCtxtRed Γ Δ
  | ChoiceCtxtR1 : forall (Γ Δ : Chan -> SessionType) (s : nat) (p q : Role)
                     (S T1 T2 : SessionType),
      Γ (Session s p) = EChoice q S
      -> Γ (Session s q) = IChoice p T1 T2
      -> Δ (Session s p) = S
      -> Δ (Session s q) = T1
      -> (forall χ : Chan, (Session s p) <> χ -> (Session s q) <> χ -> Γ χ = Δ χ)
      -> PiCtxtRed Γ Δ
  | ChoiceCtxtR2 : forall (Γ Δ : Chan -> SessionType) (s : nat) (p q : Role)
                     (S T1 T2 : SessionType),
      Γ (Session s p) = EChoice q S
      -> Γ (Session s q) = IChoice p T1 T2
      -> Δ (Session s p) = S
      -> Δ (Session s q) = T2
      -> (forall χ : Chan, (Session s p) <> χ -> (Session s q) <> χ -> Γ χ = Δ χ)
      -> PiCtxtRed Γ Δ
  | MuCtxtR : forall (Γ1 Γ2 Δ : Chan -> SessionType) (χ : Chan) (S1 : SessionType),
      Γ1 χ = S1 [s| fun n => match n with
                          | 0 => μ S1
                          | S n' => TypeVar n'
                          end]
      -> Γ2 χ = μ S1
      -> (forall χ2 : Chan, χ <> χ2 -> Γ1 χ2 = Γ2 χ2)
      -> PiCtxtRed Γ1 Δ
      -> PiCtxtRed Γ2 Δ.
  Hint Constructors PiCtxtRed : PiC.

  Inductive PiCtxtManyRed : (Chan -> SessionType) -> (Chan -> SessionType) -> Prop :=
    PiCtxtManyZero : forall Γ : Chan -> SessionType, PiCtxtManyRed Γ Γ
  | PiCtxtManySucc : forall Γ1 Γ2 Γ3 : Chan -> SessionType,
      PiCtxtRed Γ1 Γ2 -> PiCtxtManyRed Γ2 Γ3 -> PiCtxtManyRed Γ1 Γ3.
  Hint Constructors PiCtxtManyRed : PiC.
  Lemma PiCtxtManyOne : forall Γ1 Γ2 : Chan -> SessionType,
      PiCtxtRed Γ1 Γ2 -> PiCtxtManyRed Γ1 Γ2.
  Proof.
    intros Γ1 Γ2 red; eauto with PiC.
  Qed.                                                            
  
  Definition EndCtxt : (Chan -> SessionType) -> Prop :=
    fun Γ => forall χ, Γ χ ≤s EndType.

  Definition SafetyCtxtProperty : ((Chan -> SessionType) -> Prop ) -> Prop :=
    fun φ => forall Γ : Chan -> SessionType,
        φ Γ ->
        (forall (χ1 χ2 : Chan) (p q : Role)(S1 S2 T1 T2 : SessionType),
            Γ χ1 = SendT p S1 S2
            -> Γ χ2 = ReceiveT q T1 T2
            -> S1 ≤s T1)
        /\ (forall (χ : Chan) (S : SessionType),
              Γ χ = μ S
              -> φ (fun χ2 => if ChanEqDec χ χ2
                         then S [s| fun k =>
                                      match k with
                                      | 0 => μ S
                                      | S n' => TypeVar n'
                                      end]
                         else Γ χ2))
        /\ (forall Δ, PiCtxtRed Γ Δ -> φ Δ).

  Definition DFCtxt : (Chan -> SessionType) -> Prop :=
    fun Γ : Chan -> SessionType => forall Δ : Chan -> SessionType,
        PiCtxtManyRed Γ Δ ->
        forall Δ', ~(PiCtxtRed Δ Δ') -> EndCtxt Δ'.

  Definition LiveCtxt : (Chan -> SessionType) -> Prop :=
    fun Γ => (forall (χ : Chan) (p : Role) (S1 S2 : SessionType),
              Γ χ = SendT p S1 S2
              -> exists (Γ' : Chan -> SessionType), Γ' χ = S2 /\ PiCtxtManyRed Γ Γ')
          /\ (forall (χ : Chan) (p : Role) (S1 S2 : SessionType),
                Γ χ = ReceiveT p S1 S2
                -> exists (Γ' : Chan -> SessionType), Γ' χ = S2 /\ PiCtxtManyRed Γ Γ')
          /\ (forall (χ : Chan) (p : Role) (S : SessionType),
                Γ χ = EChoice p S
                -> (exists (Γ' : Chan -> SessionType), Γ' χ = S /\ PiCtxtManyRed Γ Γ'))
          /\ (forall (χ : Chan) (p : Role) (S1 S2 : SessionType),
                Γ χ = IChoice p S1 S2
                -> (exists (Γ' : Chan -> SessionType), Γ' χ = S1 /\ PiCtxtManyRed Γ Γ')
                  /\ (exists (Γ' : Chan -> SessionType), Γ' χ = S2 /\ PiCtxtManyRed Γ Γ')).
  Axiom LiveSafety : SafetyCtxtProperty LiveCtxt. (* From Lemma 5.9 in "Less is More" *)
  Axiom LiveToDF : forall Γ : Chan -> SessionType, LiveCtxt Γ -> DFCtxt Γ. (* From Lemma 5.9 in "Less is More" *)
  
  Inductive PiCalc : Set :=
    EndPi : PiCalc
  | PiVar : nat -> PiCalc
  | Par : PiCalc -> PiCalc -> PiCalc
  | ν : PiCalc -> PiCalc
  | Sel : Chan -> Role -> Coq.Init.Datatypes.bool -> PiCalc -> PiCalc
  | Branch : Chan -> Role -> PiCalc -> PiCalc -> PiCalc
  | Send : Chan -> Role -> Chan -> PiCalc -> PiCalc
  | Receive : Chan -> Role -> PiCalc -> PiCalc
  | Def : PiCalc -> PiCalc -> PiCalc
  | SendD : Chan -> Role -> Expr -> PiCalc -> PiCalc
  | ReceiveD : Chan -> Role -> PiCalc -> PiCalc
  | IfThenElse : Expr -> PiCalc -> PiCalc -> PiCalc.
  Notation "P ∥ Q" := (Par P Q) (at level 20).

  Fixpoint PiCalcRename (P : PiCalc) (ξ : nat -> nat) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar (ξ n)
    | Par P Q => (PiCalcRename P ξ) ∥ (PiCalcRename Q ξ)
    | ν P => ν (PiCalcRename P ξ)
    | Sel χ p b P => Sel χ p b (PiCalcRename P ξ)
    | Branch χ p P Q => Branch χ p (PiCalcRename P ξ) (PiCalcRename Q ξ)
    | Send χ1 p χ2 P => Send χ1 p χ2 (PiCalcRename P ξ)
    | Receive χ p P => Receive χ p (PiCalcRename P ξ)
    | Def P Q => Def (PiCalcRename P (RenamingUp ξ)) (PiCalcRename Q (RenamingUp ξ))
    | SendD χ p e P => SendD χ p e (PiCalcRename P ξ)
    | ReceiveD χ p P => ReceiveD χ p (PiCalcRename P ξ)
    | IfThenElse e P Q => IfThenElse e (PiCalcRename P ξ) (PiCalcRename Q ξ)
    end.
  Notation "P ⟨π| ξ ⟩" := (PiCalcRename P ξ) (at level 15).
  Lemma PiCalcRenameExt : forall (P : PiCalc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n) ->
      P ⟨π| ξ1⟩ = P ⟨π| ξ2⟩.
  Proof.
    intros P; induction P; simpl; intros ξ1 ξ2 ext_eq; auto.
    1,4,10: erewrite IHP1; eauto with PiC; erewrite IHP2; eauto.
    1,2,3,4,6,7: erewrite IHP; eauto.
    rewrite IHP1 with (ξ2 := RenamingUp ξ2); auto with PiC;
      rewrite IHP2 with (ξ2 := RenamingUp ξ2); auto with PiC.
  Qed.
  
  Fixpoint PiCalcRenameChan (P : PiCalc) (ξ : nat -> nat) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar n
    | P ∥ Q => (PiCalcRenameChan P ξ) ∥ (PiCalcRenameChan Q ξ)
    | ν P => ν (PiCalcRenameChan P ξ)
    | Sel χ p b P => Sel (ChanRename χ ξ) p b (PiCalcRenameChan P ξ)
    | Branch χ p P Q => Branch (χ ⟨ch| ξ⟩) p (PiCalcRenameChan P ξ) (PiCalcRenameChan Q ξ)
    | Send χ1 p χ2 P => Send (χ1 ⟨ch| ξ⟩) p (χ2 ⟨ch| ξ⟩) (PiCalcRenameChan P ξ)
    | Receive χ p P => Receive (χ ⟨ch| ξ⟩) p (PiCalcRenameChan P (RenamingUp ξ))
    | Def P Q => Def (PiCalcRenameChan P ξ) (PiCalcRenameChan Q ξ)
    | SendD χ p e P => SendD (χ ⟨ch| ξ⟩) p e (PiCalcRenameChan P ξ)
    | ReceiveD χ p P => ReceiveD (χ ⟨ch| ξ⟩) p (PiCalcRenameChan P ξ)
    | IfThenElse e P Q => IfThenElse e (PiCalcRenameChan P ξ) (PiCalcRenameChan Q ξ)
    end.
  Notation "P ⟨πch| ξ ⟩" := (PiCalcRenameChan P ξ) (at level 15).

  Lemma PiCalcRenameChanExt : forall (P : PiCalc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨πch| ξ1⟩ = P ⟨πch| ξ2⟩.
  Proof.
    intros P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto.
    3,4,5,6,8,9: assert (c ⟨ch| ξ1⟩ = c ⟨ch| ξ2⟩) as Hc by (apply ChanRenameExt; auto);
      rewrite Hc; auto.
    2,3,5,7,8: rewrite IHP with (ξ2 := ξ2); auto.
    1,3,5,6: rewrite IHP1 with (ξ2 := ξ2); auto; rewrite IHP2 with (ξ2 := ξ2); auto.
    - assert (c0 ⟨ch| ξ1⟩ = c0 ⟨ch| ξ2⟩) as Hc0 by (apply ChanRenameExt; auto);
        rewrite Hc0; auto.
    - rewrite IHP with (ξ2 := RenamingUp ξ2); auto.
      apply RenamingUpExt; auto.
  Qed.
  Hint Resolve PiCalcRenameChanExt : PiC.
  Hint Rewrite PiCalcRenameChanExt : PiC.

  Lemma PiCalcIdRenameChan : forall P : PiCalc, P ⟨πch|IdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    all: try (rewrite IHP; auto).
    all: try (rewrite IHP1; rewrite IHP2; auto).
    all: try (repeat rewrite ChanIdRenaming; auto).
    assert (P ⟨πch| RenamingUp IdRenaming⟩ = P⟨πch| IdRenaming⟩)
      by (apply PiCalcRenameChanExt; auto with PiC).
    rewrite H; rewrite IHP; reflexivity.
  Qed.

  Fixpoint PiCalcSessionRename (P : PiCalc) (ξ : nat -> nat) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar n
    | Par P Q => (PiCalcSessionRename P ξ) ∥ (PiCalcSessionRename Q ξ)
    | ν P => ν (PiCalcSessionRename P (RenamingUp ξ))
    | Sel χ p b P => Sel (χ ⟨chs|ξ⟩) p b (PiCalcSessionRename P ξ)
    | Branch χ p P Q =>
      Branch (χ ⟨chs|ξ⟩) p (PiCalcSessionRename P ξ) (PiCalcSessionRename Q ξ)
    | Send χ1 p χ2 P =>
      Send (χ1 ⟨chs|ξ⟩) p (χ2 ⟨chs|ξ⟩) (PiCalcSessionRename P ξ)
    | Receive χ p P =>
      Receive (ChanSessionRename χ ξ) p (PiCalcSessionRename P ξ)
    | Def P Q => Def (PiCalcSessionRename P ξ) (PiCalcSessionRename Q ξ)
    | SendD χ p e P => SendD (χ ⟨chs| ξ⟩) p e (PiCalcSessionRename P ξ)
    | ReceiveD χ p P => ReceiveD (χ ⟨chs| ξ⟩) p (PiCalcSessionRename P ξ)
    | IfThenElse e P Q => IfThenElse e (PiCalcSessionRename P ξ) (PiCalcSessionRename Q ξ)
    end.
  Notation "P ⟨πs| ξ ⟩" := (PiCalcSessionRename P ξ) (at level 15).

  Lemma PiCalcSessionRenameExt : forall (P : PiCalc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨πs| ξ1⟩ = P ⟨πs| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto with PiC.
    1,4,7,10: rewrite IHP1 with (ξ2 := ξ2); auto; rewrite IHP2 with (ξ2 := ξ2);
      auto with PiC.
    1,3,4,5,6,7: assert (c ⟨chs| ξ1⟩ = c⟨chs| ξ2⟩) as Hc
        by (auto with PiC); rewrite Hc; auto.
    1,2,3,4,5: rewrite IHP with (ξ2 := ξ2); auto.
    - assert (c0 ⟨chs| ξ1⟩ = c0⟨chs| ξ2⟩) as Hc0
        by (auto with PiC); rewrite Hc0; auto.
    - rewrite IHP with (ξ2 := RenamingUp ξ2); auto with PiC.
  Qed.
  Hint Resolve PiCalcSessionRenameExt : PiC.
  Hint Rewrite PiCalcSessionRenameExt : PiC.

  Lemma PiCalcSessionIdRenaming : forall (P : PiCalc), P⟨πs| IdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto with PiC.
    1,4,7,10: rewrite IHP1; rewrite IHP2; auto.
    1,3,4,5,6,7: repeat rewrite ChanIdSessionRenaming; auto.
    1,2,3,4,5: rewrite IHP; auto.
    rewrite PiCalcSessionRenameExt with (ξ2 := IdRenaming); auto with PiC.
    rewrite IHP; reflexivity.
  Qed.
  Hint Resolve PiCalcSessionIdRenaming : PiC.
  Hint Rewrite PiCalcSessionIdRenaming : PiC.

  Fixpoint PiCalcExprRename (P : PiCalc) (ξ : nat -> nat) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar n
    | Par P Q => (PiCalcExprRename P ξ) ∥ (PiCalcExprRename Q ξ)
    | ν P => ν (PiCalcExprRename P ξ)
    | Sel χ p b P => Sel χ p b (PiCalcExprRename P ξ)
    | Branch χ p P Q => Branch χ p (PiCalcExprRename P ξ) (PiCalcExprRename Q ξ)
    | Send χ1 p χ2 P => Send χ1 p χ2 (PiCalcExprRename P ξ)
    | Receive χ p P => Receive χ p (PiCalcExprRename P ξ)
    | Def P Q => Def (PiCalcExprRename P ξ) (PiCalcExprRename Q ξ)
    | SendD χ p e P => SendD χ p (e ⟨e|ξ⟩) (PiCalcExprRename P ξ)
    | ReceiveD χ p P => ReceiveD χ p (PiCalcExprRename P (RenamingUp ξ))
    | IfThenElse e P Q => IfThenElse (e ⟨e| ξ⟩) (PiCalcExprRename P ξ) (PiCalcExprRename Q ξ)
    end.
  Notation "P ⟨πe| ξ ⟩" := (PiCalcExprRename P ξ) (at level 15).

  Lemma PiCalcExprRenameExt : forall (P : PiCalc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨πe| ξ1⟩ = P ⟨πe| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto.
    1,4,7,10: rewrite IHP1 with (ξ2 := ξ2); auto; rewrite IHP2 with (ξ2 := ξ2); auto.
    2,3,4,5,6: rewrite IHP with (ξ2 := ξ2); auto.
    1,2: rewrite ExprRenameExt with (ξ2 := ξ2); auto.
    rewrite IHP with (ξ2 := RenamingUp ξ2); auto with PiC.
  Qed.
  Hint Resolve PiCalcExprRenameExt : PiC.
  Hint Rewrite PiCalcExprRenameExt : PiC.

  Lemma PiCalcExprIdRenaming : forall (P : PiCalc),
      P ⟨πe| IdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    2,3,5,6,8: rewrite IHP; auto.
    1,3,4,6: rewrite IHP1; rewrite IHP2; auto.
    1,2: rewrite ExprIdRenamingSpec; reflexivity.
    rewrite PiCalcExprRenameExt with (ξ2 := IdRenaming); [|apply IdRenamingUp].
    rewrite IHP; auto.
  Qed.
  Hint Resolve PiCalcExprIdRenaming : PiC.
  Hint Rewrite PiCalcExprIdRenaming : PiC.  
  
  Definition PiCalcSubstUp : (nat -> PiCalc) -> nat -> PiCalc :=
    fun σ n => match n with
            | 0 => PiVar n
            | S n' => σ n' ⟨π| S⟩
            end.
  Lemma PiCalcSubstUpExt : forall (σ1 σ2 : nat -> PiCalc),
      (forall n, σ1 n = σ2 n)
      -> forall n, PiCalcSubstUp σ1 n = PiCalcSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; unfold PiCalcSubstUp; destruct n; simpl; auto.
    rewrite ext_eq; reflexivity.
  Qed.
  Hint Resolve PiCalcSubstUpExt : PiC.
  Hint Rewrite PiCalcSubstUpExt : PiC.
    
  Fixpoint PiCalcSubst (P : PiCalc) (σ : nat -> PiCalc) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => σ n
    | Par P Q => (PiCalcSubst P σ) ∥ (PiCalcSubst Q σ)
    | ν P => ν (PiCalcSubst P σ)
    | Sel χ p b P => Sel χ p b (PiCalcSubst P σ)
    | Branch χ p P Q => Branch χ p (PiCalcSubst P σ) (PiCalcSubst Q σ)
    | Send χ1 p χ2 P => Send χ1 p χ2 (PiCalcSubst P σ)
    | Receive χ p P => Receive χ p (PiCalcSubst P σ)
    | Def P Q => Def (PiCalcSubst P (PiCalcSubstUp σ)) (PiCalcSubst Q (PiCalcSubstUp σ))
    | SendD χ p e P => SendD χ p e (PiCalcSubst P σ)
    | ReceiveD χ p P => ReceiveD χ p (PiCalcSubst P σ)
    | IfThenElse e P Q => IfThenElse e (PiCalcSubst P σ) (PiCalcSubst Q σ)
    end.
  Notation "P [π| σ ]" := (PiCalcSubst P σ) (at level 15).

  Lemma PiCalcSubstExt : forall (P : PiCalc) (σ1 σ2 : nat -> PiCalc),
      (forall n, σ1 n = σ2 n)
      -> P [π|σ1] = P [π|σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto with PiC.
    1,4,10: erewrite IHP1; eauto; erewrite IHP2; eauto.
    1,2,3,4,6,7: erewrite IHP; eauto.
    rewrite IHP1 with (σ2 := PiCalcSubstUp σ2); [rewrite IHP2 with (σ2 := PiCalcSubstUp σ2)|];
      auto with PiC.
  Qed.
  Hint Resolve PiCalcSubstExt : PiC.
  Hint Rewrite PiCalcSubstExt : PiC.

  Definition PiCalcIdSubst : nat -> PiCalc := PiVar.
  Lemma PiCalcIdSubstUp : forall n, PiCalcSubstUp PiCalcIdSubst n = PiCalcIdSubst n.
  Proof.
    intros n; unfold PiCalcSubstUp; unfold PiCalcIdSubst; destruct n; simpl; reflexivity.
  Qed.
  Hint Resolve PiCalcIdSubstUp : PiC.
  Hint Rewrite PiCalcIdSubstUp : PiC.
  
  Lemma PiCalcIdSubstSpec : forall (P : PiCalc), P[π| PiCalcIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto with PiC.
    2,3,5,6,8,9: rewrite IHP; reflexivity.
    1,2,4: rewrite IHP1; rewrite IHP2; reflexivity.
    repeat rewrite PiCalcSubstExt
      with (σ1 := PiCalcSubstUp PiCalcIdSubst) (σ2 := PiCalcIdSubst);
      [rewrite IHP1; rewrite IHP2; reflexivity| |];
      exact PiCalcIdSubstUp.
  Qed.
  Hint Resolve PiCalcIdSubstSpec : PiC.
  Hint Rewrite PiCalcIdSubstSpec : PiC.

  Fixpoint PiCalcSubstChan (P : PiCalc) (σ : nat -> Chan) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar n
    | Par P Q => (PiCalcSubstChan P σ) ∥ (PiCalcSubstChan Q σ)
    | ν P => ν (PiCalcSubstChan P σ)
    | Sel χ p b P => Sel (χ [ch| σ]) p b (PiCalcSubstChan P σ)
    | Branch χ p P Q => Branch (χ [ch| σ]) p (PiCalcSubstChan P σ) (PiCalcSubstChan Q σ)
    | Send χ1 p χ2 P => Send (χ1 [ch| σ]) p (χ2 [ch| σ]) (PiCalcSubstChan P σ)
    | Receive χ p P => Receive (χ [ch| σ]) p (PiCalcSubstChan P (ChanSubstUp σ))
    | Def P Q => Def (PiCalcSubstChan P σ) (PiCalcSubstChan Q σ)
    | SendD χ p e P => SendD (χ [ch| σ]) p e (PiCalcSubstChan P σ)
    | ReceiveD χ p P => ReceiveD (χ [ch| σ]) p (PiCalcSubstChan P σ)
    | IfThenElse e P Q => IfThenElse e (PiCalcSubstChan P σ) (PiCalcSubstChan Q σ)
    end.
  Notation "P [πch| σ ]" := (PiCalcSubstChan P σ) (at level 15).

  Lemma PiCalcSubstChanExt : forall (P : PiCalc) (σ1 σ2 : nat -> Chan),
      (forall n, σ1 n = σ2 n)
      -> P [πch| σ1] = P [πch| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto with PiC.
    2,3,5,8,9: rewrite IHP with (σ2 := σ2); auto with PiC.
    1,6,8,9: rewrite IHP1 with (σ2 := σ2); auto; rewrite IHP2 with (σ2 := σ2);
      auto with PiC.
    all: assert (c[ch|σ1] = c[ch|σ2]) as Hc by (auto with PiC); rewrite Hc; auto.
    - assert (c0[ch|σ1] = c0[ch|σ2]) as Hc0 by (auto with PiC); rewrite Hc0; auto.
    - rewrite IHP with (σ2 := ChanSubstUp σ2); auto with PiC.
  Qed.
  Hint Resolve PiCalcSubstChanExt : PiC.
  Hint Rewrite PiCalcSubstChanExt : PiC.

  Lemma PiCalcSubstId : forall (P : PiCalc), P[πch| ChanIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto with PiC.
    all: autorewrite with PiC.
    2,3,5,8,9: rewrite IHP; reflexivity.
    1,2,4,5: rewrite IHP1; rewrite IHP2; reflexivity.
    assert (P [πch|ChanSubstUp ChanIdSubst] = P[πch|ChanIdSubst]) by (auto with PiC).
    rewrite H; rewrite IHP; reflexivity.
  Qed.
  Hint Resolve PiCalcSubstId : PiC.
  Hint Rewrite PiCalcSubstId : PiC.

  Fixpoint PiCalcExprSubst (P : PiCalc) (σ : nat -> Expr) : PiCalc :=
    match P with
    | EndPi => EndPi
    | PiVar n => PiVar n
    | Par P Q => (PiCalcExprSubst P σ) ∥ (PiCalcExprSubst Q σ)
    | ν P => ν (PiCalcExprSubst P σ)
    | Sel χ p b P => Sel χ p b (PiCalcExprSubst P σ)
    | Branch χ p P Q => Branch χ p (PiCalcExprSubst P σ) (PiCalcExprSubst Q σ)
    | Send χ1 p χ2 P => Send χ1 p χ2 (PiCalcExprSubst P σ)
    | Receive χ p P => Receive χ p (PiCalcExprSubst P σ)
    | Def P Q => Def (PiCalcExprSubst P σ) (PiCalcExprSubst Q σ)
    | SendD χ p e P => SendD χ p (e [e|σ]) (PiCalcExprSubst P σ)
    | ReceiveD χ p P => ReceiveD χ p (PiCalcExprSubst P (ExprUpSubst σ))
    | IfThenElse e P Q => IfThenElse (e [e|σ]) (PiCalcExprSubst P σ) (PiCalcExprSubst Q σ)
    end.
  Notation "P [πe| σ ]" := (PiCalcExprSubst P σ) (at level 15).

  Theorem PiCalcExprSubstExt : forall (P : PiCalc) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n)
      -> P [πe| σ1] = P [πe| σ2].
  Proof.
    intros P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    1,4,7,10: rewrite IHP1 with (σ2 := σ2); auto; rewrite IHP2 with (σ2 := σ2); auto.
    2,3,4,5,6: rewrite IHP with (σ2 := σ2); auto.
    1,2: rewrite ExprSubstExt with (σ2 := σ2); auto.
    rewrite IHP with (σ2 := ExprUpSubst σ2); [reflexivity|].
    intro n; unfold ExprUpSubst; destruct n; auto; rewrite ext_eq; reflexivity.
  Qed.
  Hint Resolve PiCalcExprSubstExt : PiC.
  Hint Rewrite PiCalcExprSubstExt : PiC.

  Theorem PiCaclExprSubstId : forall (P : PiCalc),
      P [πe| ExprIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    8,10: rewrite ExprIdentitySubstSpec.
    1,4,7,9: rewrite IHP1; rewrite IHP2; reflexivity.
    1,2,3,4,5: rewrite IHP; reflexivity.
    rewrite PiCalcExprSubstExt with (σ2 := ExprIdSubst).
    rewrite IHP; reflexivity.
    intro n; unfold ExprUpSubst; unfold ExprIdSubst; destruct n; simpl; auto.
    apply ExprRenameVar.
  Qed.
  Hint Resolve PiCaclExprSubstId : PiC.
  Hint Rewrite PiCaclExprSubstId : PiC.

  Inductive PiEquiv' : PiCalc -> PiCalc -> Prop :=
    SwapBranch : forall P Q, PiEquiv' (P ∥ Q) (Q ∥ P)
  | ParAssoc : forall P Q R, PiEquiv' (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R)
  | ParEnd : forall P, PiEquiv' (P ∥ EndPi) P
  | NuEnd : PiEquiv' (ν EndPi) EndPi
  | SwapNu : forall P, PiEquiv' (ν (ν P)) (ν (ν (P ⟨πs| fun n => match n with
                                                        | 0 => 1
                                                        | 1 => 0
                                                        | m => m
                                                         end⟩))).
  Hint Constructors PiEquiv' : PiC.
  Inductive PiEquiv : PiCalc -> PiCalc -> Prop :=
    PiEquivRefl : forall P, PiEquiv P P
  | LiftEquiv' : forall P Q, PiEquiv' P Q -> PiEquiv P Q
  | PiEquivSym : forall P Q, PiEquiv P Q -> PiEquiv Q P
  | PiEquivTrans : forall P Q R, PiEquiv P Q -> PiEquiv Q R -> PiEquiv P R.
  Hint Constructors PiEquiv : PiC.

  Inductive PiRedCtxt : Set :=
    EmptyRedCtxt : PiRedCtxt
  | ParCtxt : PiRedCtxt -> PiCalc -> PiRedCtxt
  | NuCtxt : PiRedCtxt -> PiRedCtxt
  | DefCtxt : PiCalc -> PiRedCtxt -> PiRedCtxt.

  Fixpoint ApplyPiCtxt (CC : PiRedCtxt) (P : PiCalc) : PiCalc :=
    match CC with
    | EmptyRedCtxt => P
    | ParCtxt CC' Q => (ApplyPiCtxt CC' P) ∥ Q
    | NuCtxt CC' => ν (ApplyPiCtxt CC' P)
    | DefCtxt Q CC' => Def Q (ApplyPiCtxt CC' P)
    end.

  Definition SendSubst (χ : Chan) : nat -> Chan := fun n => match n with
                                                     | 0 => χ
                                                     | S n' => ChanVar n'
                                                     end.
  Definition DefSubst (P : PiCalc) : nat -> PiCalc := fun n =>
                                                      match n with
                                                      | 0 => Def P (PiVar 0)
                                                      | S n' => PiVar n'
                                                      end.
  Definition SendExprSubst (e : Expr) : nat -> Expr := fun n =>
                                                     match n with
                                                     | 0 => e
                                                     | S n' => ExprVar n'
                                                     end.
    
  Inductive PiRed : PiCalc -> PiCalc -> Prop :=
  | IfThenElseE : forall e1 e2 P Q,
      ExprStep e1 e2
      -> PiRed (IfThenElse e1 P Q) (IfThenElse e2 P Q)
  | IfThenElseTrue : forall P Q,
      PiRed (IfThenElse tt P Q) P
  | IfThenElseFalse : forall P Q,
      PiRed (IfThenElse ff P Q) Q
  | RCommE : forall χ p e1 e2 P,
      ExprStep e1 e2
      -> PiRed (SendD χ p e1 P) (SendD χ p e2 P)
  | RCommD : forall s p q v P Q,
      ExprVal v ->
      PiRed ((SendD (Session s p) q v P) ∥ (ReceiveD (Session s q) p Q))
            (P ∥ (Q [πe|SendExprSubst v]))
  | RComm : forall s p q χ P Q,
      PiRed ((Send (Session s p) q χ P) ∥ (Receive (Session s q) p Q))
            (P ∥ (Q [πch|SendSubst χ]))
  | RChoice1 : forall s p q P Q1 Q2,
      PiRed ((Sel (Session s p) q true P) ∥ (Branch (Session s q) p Q1 Q2))
            (P ∥ Q1)
  | RChoice2 : forall s p q P Q1 Q2,
      PiRed ((Sel (Session s p) q false P) ∥ (Branch (Session s q) p Q1 Q2))
            (P ∥ Q2)
  | RDef : forall P Q, PiRed (Def P Q) (Q [π|DefSubst P])
  | RCtxt : forall P Q,
      PiRed P Q
      -> forall CC : PiRedCtxt, PiRed (ApplyPiCtxt CC P) (ApplyPiCtxt CC Q)
  | REq : forall P P' Q Q',
      PiEquiv P P'
      -> PiRed P' Q'
      -> PiEquiv Q' Q
      -> PiRed P Q.
  Hint Constructors PiRed : PiC.

  Inductive PiRedMany : PiCalc -> PiCalc -> Prop :=
    PiRedManyZero : forall P : PiCalc, PiRedMany P P
  | PiRedManySucc : forall P Q R : PiCalc,
      PiRed P Q
      -> PiRedMany Q R
      -> PiRedMany P R.
  Hint Constructors PiRedMany : PiC.

  Definition PiRedToMany : forall P Q, PiRed P Q -> PiRedMany P Q :=
    fun P Q step => PiRedManySucc P Q Q step (PiRedManyZero Q).
  Hint Resolve PiRedToMany : PiC.

  Definition PiCalcDF : PiCalc -> Prop :=
    fun P => forall Q, PiRedMany P Q -> (forall R, ~ PiRed Q R) -> PiEquiv Q EndPi.

  Definition PiCalcLive : PiCalc -> Prop :=
    fun P => forall (CC : PiRedCtxt) (Q : PiCalc),
        PiRedMany P (ApplyPiCtxt CC Q)
        -> (forall χ1 p χ2 Q',
              Q = Send χ1 p χ2 Q'
              -> exists CC' : PiRedCtxt, PiRedMany (ApplyPiCtxt CC Q) (ApplyPiCtxt CC' Q'))
          /\ (forall χ p b Q',
                Q = Sel χ p b Q'
                -> exists CC' : PiRedCtxt, PiRedMany (ApplyPiCtxt CC Q) (ApplyPiCtxt CC' Q'))
          /\ (forall χ p Q',
                Q = Receive χ p Q'
                -> exists CC' : PiRedCtxt, PiRedMany (ApplyPiCtxt CC Q) (ApplyPiCtxt CC' Q'))
          /\ (forall χ p Q1 Q2,
                Q = Branch χ p Q1 Q2
                -> exists (CC' : PiRedCtxt) (Q' : PiCalc),
                  (Q' = Q1 \/ Q' = Q2) 
                  /\ PiRedMany (ApplyPiCtxt CC Q) (ApplyPiCtxt CC' Q')).

  
  Definition ChannelTyping : (Chan -> SessionType) -> Chan -> SessionType -> Prop :=
    fun Γ χ T => Γ χ ≤s T.
  Notation "Γ ⊢ch χ ::: T" := (ChannelTyping Γ χ T) (at level 30).

  (* TODO: Add in stuff about sending and receiving data *)
  
  Reserved Notation "Θ ;; Γ ⋅ Δ ⊢st P" (at level 30).
  Inductive ProcessTyping : nat -> (Chan -> SessionType) -> (nat -> ExprTyp) -> PiCalc -> Prop :=
  | EndST : forall Θ Γ Δ, EndCtxt Γ -> Θ ;; Γ ⋅ Δ ⊢st EndPi
  | VarST : forall Θ Γ Δ n, n < Θ -> EndCtxt Γ -> Θ ;; Γ ⋅ Δ ⊢st PiVar n
  | DefST : forall Θ Γ Δ P Q,
      (S Θ) ;; Γ ⋅ Δ ⊢st P
      -> (S Θ) ;; Γ ⋅ Δ ⊢st Q
      -> Θ ;; Γ ⋅ Δ ⊢st Def P Q
  | SendST : forall Θ Γ Δ p χ1 χ2 P S1 S2,
      χ1 <> χ2 (* To guarantee linearity *)
      -> Γ ⊢ch χ1 ::: SendT p S1 S2
      -> Γ ⊢ch χ2 ::: S1
      -> Θ ;; (fun χ' => if ChanEqDec χ1 χ'
                    then S2
                    else if ChanEqDec χ2 χ'
                         then EndType (* Again, to guarantee linearity *)
                         else Γ χ') ⋅ Δ ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st (Send χ1 p χ2 P)
  | ReceiveST : forall Θ Γ Δ p χ P S1 S2,
      Γ ⊢ch χ ::: ReceiveT p S1 S2
      -> Θ ;; (fun χ' => match χ' with
                    | ChanVar n => match n with
                                  | 0 => S1
                                  | S n' => if ChanEqDec (ChanVar n') χ
                                           then S2
                                           else Γ (ChanVar n')
                                  end
                    | Session _ _ => if ChanEqDec χ' χ
                                    then S2
                                    else Γ χ
                    end) ⋅ Δ ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st (Receive χ p P)
  | SendDST : forall Θ Γ Δ χ p e τ P S,
      Δ ⊢e e ::: τ
      -> Γ ⊢ch χ ::: SendDT p τ S
      -> Θ ;; (fun χ' => if ChanEqDec χ χ'
                    then S
                    else Γ χ') ⋅ Δ ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st SendD χ p e P
  | ReceiveDST : forall Θ Γ Δ χ p τ P S,
      Γ ⊢ch χ ::: ReceiveDT p τ S
      -> Θ ;; (fun χ' => if ChanEqDec χ χ'
                   then S
                   else Γ χ') ⋅ (fun n => match n with
                                       | 0 => τ
                                       | S n' => Δ n'
                                       end) ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st ReceiveD χ p P 
  | BranchST : forall Θ Γ Δ χ p P1 P2 S1 S2,
      Γ ⊢ch χ ::: IChoice p S1 S2
      -> Θ ;; (fun χ' => if ChanEqDec χ χ'
                    then S1
                    else Γ χ') ⋅ Δ ⊢st P1
      -> Θ ;; (fun χ' => if ChanEqDec χ χ'
                    then S2
                    else Γ χ') ⋅ Δ ⊢st P2
      -> Θ ;; Γ ⋅ Δ ⊢st Branch χ p P1 P2
  | SelST : forall Θ Γ Δ χ p b P S,
      Γ ⊢ch χ ::: EChoice p S
      -> Θ ;; (fun χ' => if ChanEqDec χ χ'
                    then S
                    else Γ χ') ⋅ Δ ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st Sel χ p b P
  | NuST : forall Θ Γ1 Γ2 Δ P,
      (forall χ : Chan, (exists p : Role, χ = Session 0 p)
                   \/ Γ2 χ ≤s EndType)
      -> LiveCtxt Γ2
      -> Θ ;; (fun χ => match χ with
                   | ChanVar _ => Γ1 χ
                   | Session n p => match n with
                                   | 0 => Γ2 χ
                                   | S n' => Γ1 (Session n' p)
                                   end
                   end) ⋅ Δ ⊢st P
      -> Θ ;; Γ1 ⋅ Δ ⊢st ν P
  | ParST : forall Θ Γ Γ1 Γ2 Δ P Q,
      Θ ;; Γ1 ⋅ Δ ⊢st P
      -> Θ ;; Γ2 ⋅ Δ ⊢st Q
      -> (forall χ, Γ1 χ = EndType \/ Γ2 χ = EndType) (* Linearity *)
      -> (forall χ, if SessionTypeEqDec (Γ1 χ) EndType then Γ χ = Γ2 χ else Γ χ = Γ1 χ)
      -> Θ ;; Γ ⋅ Δ ⊢st P ∥ Q
  | IfST : forall Θ Γ Δ e P Q,
      Δ ⊢e e ::: bool
      -> Θ ;; Γ ⋅ Δ ⊢st P
      -> Θ ;; Γ ⋅ Δ ⊢st Q
      -> Θ ;; Γ ⋅ Δ ⊢st IfThenElse e P Q          
  where "Θ ;; Γ ⋅ Δ ⊢st P" := (ProcessTyping Θ Γ Δ P).

  (* An immediate consequence of 4.16 from "Less is More" *)
  Axiom SubjRed : forall (Θ : nat) (Γ : Chan -> SessionType) (Δ : nat -> ExprTyp) (P : PiCalc),
      Θ ;; Γ ⋅ Δ ⊢st P -> LiveCtxt Γ -> forall P' : PiCalc, PiRed P P' -> Θ ;; Γ ⋅ Δ ⊢st P'.

  (* From Theorem 5.15 of "Less is More" *)
  Axiom TypingDF : forall (Θ : nat) (Γ : Chan -> SessionType) (Δ : nat -> ExprTyp) (P : PiCalc),
      LiveCtxt Γ -> Θ ;; Γ ⋅ Δ ⊢st P -> PiCalcDF P.

End MPST.
      
