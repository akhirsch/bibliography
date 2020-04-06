Require Import Expression.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.JMeq.


Module PiCalc (E : Expression).
  Import E.

  Parameter Role : Set.
  
  Inductive Proc : Set :=
    EndProc : Proc
  | VarProc : nat -> Proc
  | DefProc : Proc -> Proc -> Proc
  | SendProc : Role -> Expr -> Proc -> Proc
  | RecvProc : Role -> Proc -> Proc
  | EChoiceL : Role -> Proc -> Proc
  | EChoiceR : Role -> Proc -> Proc
  | IChoice : Role -> Proc -> Proc -> Proc
  | IfThenElse : Expr -> Proc -> Proc -> Proc.
  Hint Constructors Proc : PiC.

  Definition ProcRenamingUp : (nat -> nat) -> nat -> nat :=
    fun ξ n => match n with
            | 0 => 0
            | S n' => S (ξ n')
            end.

  Lemma ProcRenamingUpExt : forall (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> forall n, ProcRenamingUp ξ1 n = ProcRenamingUp ξ2 n.
  Proof.
    intros ξ1 ξ2 eq_ext n; unfold ProcRenamingUp; destruct n; auto.
  Qed.
  Hint Resolve ProcRenamingUp : PiC.

  Reserved Notation "P ⟨π| ξ ⟩" (at level 15).
  Fixpoint ProcRenaming (P : Proc) (ξ : nat -> nat) : Proc :=
    match P with
    | EndProc => EndProc
    | VarProc n => VarProc (ξ n)
    | DefProc P Q => DefProc (P ⟨π| ProcRenamingUp ξ⟩) (Q ⟨π| ProcRenamingUp ξ⟩)
    | SendProc p e P => SendProc p e (P ⟨π| ξ⟩)
    | RecvProc p P => RecvProc p (P ⟨π| ξ⟩)
    | EChoiceL p P => EChoiceL p (P ⟨π| ξ⟩)
    | EChoiceR p P => EChoiceR p (P ⟨π| ξ⟩)
    | IChoice p P Q => IChoice p (P ⟨π| ξ⟩) (Q ⟨π| ξ⟩)
    | IfThenElse e P Q => IfThenElse e (P ⟨π| ξ⟩) (Q ⟨π| ξ⟩)
    end
  where "P ⟨π| ξ ⟩" := (ProcRenaming P ξ).

  Lemma ProcRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨π| ξ1⟩ = P ⟨π| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto.
    2,3,4,5: rewrite IHP with (ξ2 := ξ2); auto.
    2,3: rewrite IHP1 with (ξ2 := ξ2); [|auto]; rewrite IHP2 with (ξ2 := ξ2); auto.
    rewrite IHP1 with (ξ2 := ProcRenamingUp ξ2); [| apply ProcRenamingUpExt; auto];
      rewrite IHP2 with (ξ2 := ProcRenamingUp ξ2); [| apply ProcRenamingUpExt; auto];
        reflexivity.
  Qed.
  Hint Resolve ProcRenamingExt : PiC.
  Hint Rewrite ProcRenamingExt : PiC.

  Definition ProcRenamingId : nat -> nat := fun n => n.

  Lemma ProcRenamingIdUp : forall n, ProcRenamingUp ProcRenamingId n = ProcRenamingId n.
  Proof.
    intro n; unfold ProcRenamingUp; unfold ProcRenamingId; simpl; destruct n; reflexivity.
  Qed.
  Hint Resolve ProcRenamingIdUp : PiC.
  Hint Rewrite ProcRenamingIdUp : PiC.

  Lemma ProcRenamingIdSpec : forall (P : Proc),
      P ⟨π| ProcRenamingId⟩ = P.
  Proof.
    intro P; induction P; simpl; try reflexivity.
    2,3,4,5: rewrite IHP; auto.
    repeat (
        rewrite ProcRenamingExt
          with (ξ1 := ProcRenamingUp ProcRenamingId) (ξ2 := ProcRenamingId);
        [| exact ProcRenamingIdUp]).
    all: rewrite IHP1; rewrite IHP2; reflexivity.
  Qed.    

  Reserved Notation "P ⟨πe| ξ ⟩" (at level 15).
  Fixpoint ProcExprRenaming (P : Proc) (ξ : nat -> nat) : Proc :=
    match P with
    | EndProc => EndProc
    | VarProc n => VarProc n
    | DefProc P Q => DefProc (P ⟨πe| ξ⟩) (Q ⟨πe| ξ⟩)
    | SendProc p e P => SendProc p (e ⟨e| ξ⟩) (P ⟨πe| ξ⟩)
    | RecvProc p P => RecvProc p (P ⟨πe| ExprUpRename ξ⟩)
    | EChoiceL p P => EChoiceL p (P ⟨πe| ξ⟩)
    | EChoiceR p P => EChoiceR p (P ⟨πe| ξ⟩)
    | IChoice p P Q => IChoice p (P ⟨πe| ξ⟩) (Q ⟨πe| ξ⟩)
    | IfThenElse e P Q => IfThenElse (e ⟨e| ξ⟩) (P ⟨πe| ξ⟩) (Q ⟨πe| ξ⟩)
    end
  where "P ⟨πe| ξ ⟩" := (ProcExprRenaming P ξ).

  Lemma ProcExprRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨πe| ξ1⟩ = P ⟨πe| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; try reflexivity.
    2,4,5: rewrite IHP with (ξ2 := ξ2); auto.
    1,4,5: rewrite IHP1 with (ξ2 := ξ2); [|exact ext_eq]; rewrite IHP2 with (ξ2 := ξ2); auto.
    1,2: rewrite ExprRenameExt with (ξ2 := ξ2); auto.
    rewrite IHP with (ξ2 := ExprUpRename ξ2); auto.
    intro n; unfold ExprUpRename; destruct n; auto.
  Qed.

  Lemma ProcExprRenamingId : forall (P : Proc),
      P ⟨πe| ExprIdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,6,7: rewrite IHP1; rewrite IHP2; auto.
    3: rewrite ProcExprRenamingExt with (ξ2 := ExprIdRenaming);
      [|intro n; symmetry; apply ExprUpRenamingId].
    2,3,4,5: rewrite IHP; auto.
    all: rewrite ExprIdRenamingSpec; reflexivity.
  Qed.

  Definition ProcSubstUp : (nat -> Proc) -> nat -> Proc :=
    fun σ n => match n with
            | 0 => VarProc 0
            | S n' => σ n' ⟨π| S⟩
            end.

  Lemma ProcSubstUpExt : forall (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n = σ2 n)
      -> forall n, ProcSubstUp σ1 n = ProcSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; unfold ProcSubstUp; destruct n; [|rewrite ext_eq]; reflexivity.
  Qed.

  Reserved Notation "P [π| σ ]" (at level 15).
  Fixpoint ProcSubst (P : Proc) (σ : nat -> Proc) :=
    match P with
    | EndProc => EndProc
    | VarProc n => σ n
    | DefProc P Q => DefProc (P [π| ProcSubstUp σ]) (Q [π| ProcSubstUp σ])
    | SendProc p e P => SendProc p e (P [π| σ])
    | RecvProc p P => RecvProc p (P [π| σ])
    | EChoiceL p P => EChoiceL p (P [π| σ])
    | EChoiceR p P => EChoiceR p (P [π| σ])
    | IChoice p P Q => IChoice p (P [π| σ]) (Q [π| σ])
    | IfThenElse e P Q => IfThenElse e (P [π| σ]) (Q[π| σ])
    end
  where "P [π| σ ]" := (ProcSubst P σ).

  Lemma ProcSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n = σ2 n)
      -> P [π| σ1] = P [π| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    2,3,4,5: rewrite IHP with (σ2 := σ2); auto.
    2,3: rewrite IHP1 with (σ2 := σ2); auto;
      rewrite IHP2 with (σ2 := σ2); auto.
    rewrite IHP1 with (σ2 := ProcSubstUp σ2); auto.
    rewrite IHP2 with (σ2 := ProcSubstUp σ2); auto.
    all: apply ProcSubstUpExt; auto.
  Qed.

  Definition ProcIdSubst : nat -> Proc := VarProc.
  Lemma ProcIdSubstUp : forall n, ProcSubstUp ProcIdSubst n = ProcIdSubst n.
  Proof.
    intro n; unfold ProcSubstUp; unfold ProcIdSubst; destruct n; simpl; reflexivity.
  Qed.

  Lemma ProcSubstId : forall (P : Proc), P [π| ProcIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    2,3,4,5: rewrite IHP; reflexivity.
    repeat (rewrite ProcSubstExt with (σ1 := ProcSubstUp ProcIdSubst) (σ2 := ProcIdSubst);
            [| exact ProcIdSubstUp]).
    all: rewrite IHP1; rewrite IHP2; reflexivity.
  Qed.

  Reserved Notation "P [πe| σ ]" (at level 15).
  Fixpoint ProcExprSubst (P : Proc) (σ : nat -> Expr) : Proc :=
    match P with
    | EndProc => EndProc
    | VarProc n => VarProc n
    | DefProc P Q => DefProc (P [πe| σ]) (Q [πe| σ])
    | SendProc p e P => SendProc p (e [e| σ]) (P [πe| σ])
    | RecvProc p P => RecvProc p (P [πe| ExprUpSubst σ])
    | EChoiceL p P => EChoiceL p (P [πe| σ])
    | EChoiceR p P => EChoiceR p (P [πe| σ])
    | IChoice p P Q => IChoice p (P [πe| σ]) (Q [πe| σ])
    | IfThenElse e P Q => IfThenElse (e [e| σ]) (P[πe|σ]) (Q[πe|σ])
    end
  where "P [πe| σ ]" := (ProcExprSubst P σ).

  Lemma ProcExprSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n)
      -> P [πe| σ1] = P [πe| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    1,6,7: rewrite IHP1 with (σ2 := σ2); auto; rewrite IHP2 with (σ2 := σ2); auto.
    2,4,5: rewrite IHP with (σ2 := σ2); auto.
    1,2: rewrite ExprSubstExt with (σ2 := σ2); auto.
    rewrite IHP with (σ2 := ExprUpSubst σ2); auto.
    intro n; unfold ExprUpSubst; destruct n; auto; rewrite ext_eq; reflexivity.
  Qed.

  Lemma ProcExprSubstId : forall (P : Proc),
      P [πe| ExprIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,6,7: rewrite IHP1; rewrite IHP2; auto.
    2,4,5: rewrite IHP; auto.
    1,2: rewrite ExprIdentitySubstSpec; reflexivity.
    rewrite ProcExprSubstExt with (σ2 := ExprIdSubst); [rewrite IHP; reflexivity|].
    intro n; unfold ExprUpSubst; unfold ExprIdSubst; destruct n; auto.
    rewrite ExprRenameVar; reflexivity.
  Qed.

  Definition CommSubst : Expr -> nat -> Expr :=
    fun e n => match n with
            | 0 => e
            | S n' => ExprVar n'
            end.

  Definition PiDefSubst : Proc -> nat -> Proc :=
    fun P n => match n with
            | 0 => P [π| (fun m => match m with | 0 => DefProc P P | S m' => VarProc m' end)]
            | S n' => VarProc n'
            end.
  
  Inductive PiCalcStep : (Role -> Proc) -> (Role -> Proc) -> Prop :=
    CommEStep : forall (p q : Role) (e e' : Expr) (P : Proc) (Π Π' : Role -> Proc),
      ExprStep e e'
      -> Π p = SendProc q e P
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = SendProc q e' P
      -> PiCalcStep Π Π'
  | CommVStep : forall (p q : Role) (v : Expr) (P Q : Proc) (Π Π' : Role -> Proc),
      ExprVal v
      -> Π p = SendProc q v P
      -> Π q = RecvProc p Q
      -> (forall r, r <> p -> r <> q -> Π r = Π' r)
      -> Π' p = P
      -> Π' q = Q [πe| CommSubst v]
      -> PiCalcStep Π Π'
  | IfEStep : forall (p : Role) (e e' : Expr) (P Q : Proc) (Π Π' : Role -> Proc),
      ExprStep e e'
      -> Π p = IfThenElse e P Q
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = IfThenElse e' P Q
      -> PiCalcStep Π Π'
  | IfTrueStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc),
      Π p = IfThenElse tt P Q
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = P
      -> PiCalcStep Π Π'
  | IfFalseStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc),
      Π p = IfThenElse ff P Q
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = Q
      -> PiCalcStep Π Π'
  | DefStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc),
      Π p = DefProc P Q
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = Q [π| PiDefSubst P]
      -> PiCalcStep Π Π'
  | ChooseLStep : forall (p q : Role) (P Q1 Q2 : Proc) (Π Π' : Role -> Proc),
      Π p = EChoiceL q P
      -> Π q = IChoice p Q1 Q2
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = P
      -> Π' q = Q1
      -> PiCalcStep Π Π'
  | ChooseRStep : forall (p q : Role) (P Q1 Q2 : Proc) (Π Π' : Role -> Proc),
      Π p = EChoiceR q P
      -> Π q = IChoice p Q1 Q2
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = P
      -> Π' q = Q2
      -> PiCalcStep Π Π'.

  Inductive PiManyStep : (Role -> Proc) -> (Role -> Proc) -> Prop :=
  | PiZeroStep : forall (Π : Role -> Proc), PiManyStep Π Π
  | PiExtraStep : forall {Π1 Π2 Π3 : Role -> Proc},
      PiCalcStep Π1 Π2 -> PiManyStep Π2 Π3 -> PiManyStep Π1 Π3.

  Definition PiOneStep (Π1 Π2 : Role -> Proc) (step : PiCalcStep Π1 Π2) : PiManyStep Π1 Π2 :=
    PiExtraStep step (PiZeroStep Π2).

  Instance PiManyStepRefl : Reflexive PiManyStep := PiZeroStep.
  Instance PiManyStepTrans : Transitive PiManyStep.
  Proof.
    unfold Transitive. intros Π1 Π2 Π3 mstep1 mstep2.
    revert Π3 mstep2.
    induction mstep1.
    intros Π3 mstep; exact mstep.
    intros Π4 mstep34. apply (PiExtraStep H).
    apply IHmstep1. exact mstep34.
  Defined.

  Inductive DeadlockFree : (Role -> Proc) -> Prop :=
    mkDF : forall Π : Role -> Proc,
      ((forall p, Π p = EndProc) \/ (exists Π', PiCalcStep Π Π'))
      -> (forall Π', PiCalcStep Π Π' -> DeadlockFree Π')
      -> DeadlockFree Π.

  Definition DFProgress : forall Π, DeadlockFree Π ->
                                       (forall p, (Π p = EndProc)) \/ exists Π', PiCalcStep Π Π'
    := fun Π DF => match DF with
               | mkDF _ x _ => x
               end.

  Definition DFCont : forall Π, DeadlockFree Π -> forall Π', PiCalcStep Π Π' -> DeadlockFree Π'
    := fun Π DF => match DF  with
               | mkDF _ _ x => x
               end.

  Inductive Live : (Role -> Proc) -> Prop :=
    mkLive : forall Π : Role -> Proc,
      (forall p q e P, Π p = SendProc q e P -> exists Π', PiManyStep Π Π' /\ Π' p = P)
      -> (forall p q P, Π p = RecvProc q P -> exists Π', PiManyStep Π Π' /\ Π' p = P)
      -> (forall p q P, Π p = EChoiceL q P -> exists Π', PiManyStep Π Π' /\ Π' p = P)
      -> (forall p q P, Π p = EChoiceR q P -> exists Π', PiManyStep Π Π' /\ Π' p = P)
      -> (forall p q P1 P2, Π p = IChoice q P1 P2 -> exists Π', PiManyStep Π Π' /\ (Π' p = P1 \/ Π' p = P2))
      -> (forall Π', PiCalcStep Π Π' -> Live Π')
      -> Live Π.

  Definition LiveSend : forall Π,
      Live Π -> forall p q e P, Π p = SendProc q e P -> exists Π', PiManyStep Π Π' /\ Π' p = P :=
    fun Π L => match L with
            | mkLive _ x _ _ _ _ _ => x
            end.
  Definition LiveRecv : forall Π,
      Live Π -> forall p q P, Π p = RecvProc q P -> exists Π', PiManyStep Π Π' /\ Π' p = P :=
    fun Π L => match L with
            | mkLive _ _ x _ _ _ _ => x
            end.
  Definition LiveEChoiceL : forall Π,
      Live Π -> forall p q P, Π p = EChoiceL q P -> exists Π', PiManyStep Π Π' /\ Π' p = P :=
    fun Π L => match L with
            | mkLive _ _ _ x _ _ _ => x
            end.
  Definition LiveEChoiceR : forall Π,
      Live Π -> forall p q P, Π p = EChoiceR q P -> exists Π', PiManyStep Π Π' /\ Π' p = P :=
    fun Π L => match L with
            | mkLive _ _ _ _ x _ _ => x
            end.
  Definition LiveIChoice : forall Π,
      Live Π -> forall p q P1 P2, Π p = IChoice q P1 P2 -> exists Π', PiManyStep Π Π' /\ (Π' p = P1 \/ Π' p = P2) :=
    fun Π L => match L with
            | mkLive _ _ _ _ _ x _ => x
            end.
  Definition LiveCont : forall Π,
      Live Π -> forall Π', PiCalcStep Π Π' -> Live Π' := 
    fun Π L => match L with
            | mkLive _ _ _ _ _ _ x => x
            end.
End PiCalc.
