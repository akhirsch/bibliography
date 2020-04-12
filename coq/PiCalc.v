Require Import Expression.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.JMeq.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Module PiCalc (E : Expression).
  Import E.

  Import ListNotations.

  Parameter Role : Set.
  Parameter RoleEqDec : forall p q : Role, {p = q} + {p <> q}.

  Inductive Proc : Set :=
    EndProc : Proc
  | VarProc : nat -> Proc
  | DefProc : Proc -> Proc -> Proc
  | SendProc : Role -> Expr -> Proc -> Proc
  | RecvProc : Role -> Proc -> Proc
  | EChoiceL : Role -> Proc -> Proc
  | EChoiceR : Role -> Proc -> Proc
  | IChoice : Role -> Proc -> Proc -> Proc
  | IfThenElse : Expr -> Proc -> Proc -> Proc
  | Par : Proc -> Proc -> Proc.
  Hint Constructors Proc : PiC.

  Definition ProcEqDec : forall P Q : Proc, {P = Q} + {P <> Q}.
    decide equality.
    apply Nat.eq_dec.
    1,7: apply ExprEqDec.
    all: apply RoleEqDec.
  Qed.

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
    | Par P Q => Par (P ⟨π| ξ⟩) (Q ⟨π| ξ⟩)
    end
  where "P ⟨π| ξ ⟩" := (ProcRenaming P ξ).

    Lemma ProcRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨π| ξ1⟩ = P ⟨π| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto.
    2,3,4,5: rewrite IHP with (ξ2 := ξ2); auto.
    2,3,4: rewrite IHP1 with (ξ2 := ξ2); [|auto]; rewrite IHP2 with (ξ2 := ξ2); auto.
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
    | Par P Q => Par (P ⟨πe| ξ⟩) (Q ⟨πe| ξ⟩)
    end
  where "P ⟨πe| ξ ⟩" := (ProcExprRenaming P ξ).

  Lemma ProcExprRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨πe| ξ1⟩ = P ⟨πe| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; try reflexivity.
    2,4,5: rewrite IHP with (ξ2 := ξ2); auto.
    1,4,5,6: rewrite IHP1 with (ξ2 := ξ2); [|exact ext_eq]; rewrite IHP2 with (ξ2 := ξ2); auto.
    1,2: rewrite ExprRenameExt with (ξ2 := ξ2); auto.
    rewrite IHP with (ξ2 := ExprUpRename ξ2); auto.
    intro n; unfold ExprUpRename; destruct n; auto.
  Qed.

  Lemma ProcExprRenamingId : forall (P : Proc),
      P ⟨πe| ExprIdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,6,7,8: rewrite IHP1; rewrite IHP2; auto.
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
    | Par P Q => Par (P [π| σ]) (Q [π| σ])
    end
  where "P [π| σ ]" := (ProcSubst P σ).

  Lemma ProcSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n = σ2 n)
      -> P [π| σ1] = P [π| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    2,3,4,5: rewrite IHP with (σ2 := σ2); auto.
    2,3,4: rewrite IHP1 with (σ2 := σ2); auto;
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
    | Par P Q => Par (P [πe| σ]) (Q [πe| σ])
    end
  where "P [πe| σ ]" := (ProcExprSubst P σ).

  Lemma ProcExprSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n)
      -> P [πe| σ1] = P [πe| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    1,6,7,8: rewrite IHP1 with (σ2 := σ2); auto; rewrite IHP2 with (σ2 := σ2); auto.
    2,4,5: rewrite IHP with (σ2 := σ2); auto.
    1,2: rewrite ExprSubstExt with (σ2 := σ2); auto.
    rewrite IHP with (σ2 := ExprUpSubst σ2); auto.
    intro n; unfold ExprUpSubst; destruct n; auto; rewrite ext_eq; reflexivity.
  Qed.

  Lemma ProcExprSubstId : forall (P : Proc),
      P [πe| ExprIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,6,7,8: rewrite IHP1; rewrite IHP2; auto.
    2,4,5: rewrite IHP; auto.
    1,2: rewrite ExprIdentitySubstSpec; reflexivity.
    rewrite ProcExprSubstExt with (σ2 := ExprIdSubst); [rewrite IHP; reflexivity|].
    intro n; unfold ExprUpSubst; unfold ExprIdSubst; destruct n; auto.
    rewrite ExprRenameVar; reflexivity.
  Qed.

  Inductive PiCalcRedContext : Set :=
    Hole : PiCalcRedContext
  | ParCtxt1 : PiCalcRedContext -> Proc -> PiCalcRedContext
  | ParCtxt2 : Proc -> PiCalcRedContext -> PiCalcRedContext.

  Fixpoint ApplyRedContext (CC : PiCalcRedContext) (P : Proc) : Proc :=
    match CC with
    | Hole => P
    | ParCtxt1 CC Q => Par (ApplyRedContext CC P) Q
    | ParCtxt2 Q CC => Par Q (ApplyRedContext CC P)
    end.

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
    CommEStep : forall (p q : Role) (e e' : Expr) (P : Proc) (Π Π' : Role -> Proc) (CC : PiCalcRedContext),
      ExprStep e e'
      -> Π p = ApplyRedContext CC (SendProc q e P)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC (SendProc q e' P)
      -> PiCalcStep Π Π'
  | CommVStep : forall (p q : Role) (v : Expr) (P Q : Proc) (Π Π' : Role -> Proc) (CC CC' : PiCalcRedContext),
      p <> q
      -> ExprVal v
      -> Π p = ApplyRedContext CC (SendProc q v P)
      -> Π q = ApplyRedContext CC' (RecvProc p Q)
      -> (forall r, r <> p -> r <> q -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC P
      -> Π' q = ApplyRedContext CC' (Q [πe| CommSubst v])
      -> PiCalcStep Π Π'
  | IfEStep : forall (p : Role) (e e' : Expr) (P Q : Proc) (Π Π' : Role -> Proc) (CC : PiCalcRedContext),
      ExprStep e e'
      -> Π p = ApplyRedContext CC (IfThenElse e P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC (IfThenElse e' P Q)
      -> PiCalcStep Π Π'
  | IfTrueStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc) (CC : PiCalcRedContext),
      Π p = ApplyRedContext CC (IfThenElse tt P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC P
      -> PiCalcStep Π Π'
  | IfFalseStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc) (CC : PiCalcRedContext),
      Π p = ApplyRedContext CC (IfThenElse ff P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC Q
      -> PiCalcStep Π Π'
  | DefStep : forall (p : Role) (P Q : Proc) (Π Π' : Role -> Proc) (CC : PiCalcRedContext),
      Π p = ApplyRedContext CC (DefProc P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC (Q [π| PiDefSubst P])
      -> PiCalcStep Π Π'
  | ChooseLStep : forall (p q : Role) (P Q1 Q2 : Proc) (Π Π' : Role -> Proc) (CC CC' : PiCalcRedContext),
      p <> q
      -> Π p = ApplyRedContext CC (EChoiceL q P)
      -> Π q = ApplyRedContext CC' (IChoice p Q1 Q2)
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC P
      -> Π' q = ApplyRedContext CC' Q1
      -> PiCalcStep Π Π'
  | ChooseRStep : forall (p q : Role) (P Q1 Q2 : Proc) (Π Π' : Role -> Proc) (CC CC' : PiCalcRedContext),
      p <> q
      -> Π p = ApplyRedContext CC (EChoiceR q P)
      -> Π q = ApplyRedContext CC' (IChoice p Q1 Q2)
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = ApplyRedContext CC P
      -> Π' q = ApplyRedContext CC' Q2
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

  Reserved Infix "≡π'" (at level 15).
  Inductive PiEquiv' : Proc -> Proc -> Prop :=
    EndProcRefl' : EndProc ≡π' EndProc
  | VarProcRefl' : forall n, VarProc n ≡π' VarProc n
  | DefProcContext' : forall {P1 P2 Q1 Q2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 ->
      (DefProc P1 Q1) ≡π' (DefProc P2 Q2)
  | SendProcContext' : forall p e {P1 P2},
      P1 ≡π' P2 ->
      (SendProc p e P1) ≡π' (SendProc p e P2)
  | RecvProcContext' : forall p {P1 P2},
      P1 ≡π' P2 ->
      (RecvProc p P1) ≡π' (RecvProc p P2)
  | EChoiceLContext' : forall p {P1 P2},
      P1 ≡π' P2 ->
      (EChoiceL p P1) ≡π' (EChoiceL p P2)
  | EChoiceRContext' : forall p {P1 P2},
      P1 ≡π' P2 ->
      (EChoiceR p P1) ≡π' (EChoiceR p P2)
  | IChoiceContext' : forall p {P1 P2 Q1 Q2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 ->
      (IChoice p P1 Q1) ≡π' (IChoice p P2 Q2)
  | IfThenElseContext' : forall e {P1 P2 Q1 Q2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 ->
      (IfThenElse e P1 Q1) ≡π' (IfThenElse e P2 Q2)
  | ParContext' : forall {P1 P2 Q1 Q2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 ->
      (Par P1 Q1) ≡π' (Par P2 Q2)
  | ParSwap' : forall {P1 P2 Q1 Q2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 ->
      (Par P1 Q1) ≡π' (Par Q2 P2)
  | ParComm1' : forall {P1 P2 Q1 Q2 R1 R2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 -> R1 ≡π' R2 ->
      (Par P1 (Par Q1 R1)) ≡π' (Par (Par P2 Q2) R2)
  | ParComm2' : forall {P1 P2 Q1 Q2 R1 R2},
      P1 ≡π' P2 -> Q1 ≡π' Q2 -> R1 ≡π' R2 ->
      (Par (Par P1 Q1) R1) ≡π' (Par P2 (Par Q2 R2))
  (* | ParEnd11' : forall {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (Par P1 EndProc) ≡π' P2 *)
  (* | ParEnd12' : forall {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     P1 ≡π' (Par P2 EndProc) *)
  (* | ParEnd21' : forall {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (Par EndProc P1) ≡π' P2 *)
  (* | ParEnd22' : forall {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     P1 ≡π' (Par EndProc P2) *)
  where "P ≡π' Q" := (PiEquiv' P Q).
  Hint Constructors PiEquiv' : PiC.

  Fixpoint PiEquiv'Refl (P : Proc) : P ≡π' P :=
    match P with
    | EndProc => EndProcRefl'
    | VarProc n => VarProcRefl' n
    | DefProc P Q => DefProcContext' (PiEquiv'Refl P) (PiEquiv'Refl Q)
    | SendProc p e P => SendProcContext' p e (PiEquiv'Refl P)
    | RecvProc p P => RecvProcContext' p (PiEquiv'Refl P)
    | EChoiceL p P => EChoiceLContext' p (PiEquiv'Refl P)
    | EChoiceR p P => EChoiceRContext' p (PiEquiv'Refl P)
    | IChoice p P Q => IChoiceContext' p (PiEquiv'Refl P) (PiEquiv'Refl Q)
    | IfThenElse e P Q => IfThenElseContext' e (PiEquiv'Refl P) (PiEquiv'Refl Q)
    | Par P Q => ParContext' (PiEquiv'Refl P) (PiEquiv'Refl Q)
    end.
  Hint Resolve PiEquiv'Refl : PiC.

  Fixpoint PiEquiv'Sym {P Q : Proc} (equiv : P ≡π' Q) : Q ≡π' P :=
    match equiv with
    | EndProcRefl' => EndProcRefl'
    | VarProcRefl' n => VarProcRefl' n
    | DefProcContext' equiv'1 equiv'2 =>
      DefProcContext' (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2)
    | SendProcContext' p e equiv' =>
      SendProcContext' p e (PiEquiv'Sym equiv')
    | RecvProcContext' p equiv' =>
      RecvProcContext' p (PiEquiv'Sym equiv')
    | EChoiceLContext' p equiv' =>
      EChoiceLContext' p (PiEquiv'Sym equiv')
    | EChoiceRContext' p equiv' =>
      EChoiceRContext' p (PiEquiv'Sym equiv')
    | IChoiceContext' p equiv'1 equiv'2 =>
      IChoiceContext' p (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2)
    | IfThenElseContext' e equiv'1 equiv'2 =>
      IfThenElseContext' e (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2)
    | ParContext' equiv'1 equiv'2 =>
      ParContext' (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2)
    | ParSwap' equiv1 equiv2 => ParSwap' (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv1)
    | ParComm1' equiv1 equiv2 equiv3 =>
      ParComm2' (PiEquiv'Sym equiv1) (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv3)
    | ParComm2' equiv1 equiv2 equiv3 =>
      ParComm1' (PiEquiv'Sym equiv1) (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv3)
    (* | ParEnd11' equiv' => ParEnd12' (PiEquiv'Sym equiv') *)
    (* | ParEnd12' equiv' => ParEnd11' (PiEquiv'Sym equiv') *)
    (* | ParEnd21' equiv' => ParEnd22' (PiEquiv'Sym equiv') *)
    (* | ParEnd22' equiv' => ParEnd21' (PiEquiv'Sym equiv') *)
    end.

  Reserved Infix "≡π" (at level 15).
  Inductive PiEquiv : Proc -> Proc -> Prop :=
    PiEquiv'Lift : forall {P Q : Proc}, P ≡π' Q -> P ≡π Q
  | PiEquivStep : forall {P Q R : Proc}, P ≡π' Q -> Q ≡π R -> P ≡π R
  where "P ≡π Q" := (PiEquiv P Q).
  Hint Constructors PiEquiv : PiC.

  Instance PiEquivReflexive : Reflexive PiEquiv := fun P => PiEquiv'Lift (PiEquiv'Refl P).
  Instance PiEquivTransitive : Transitive PiEquiv.
  unfold Transitive.
  intros P Q R equiv1 equiv2.
  induction equiv1. eapply PiEquivStep; [exact H | exact equiv2].
  eapply PiEquivStep; [exact H | apply IHequiv1; exact equiv2].
  Defined.
  Instance PiEquivSymmetric : Symmetric PiEquiv.
  unfold Symmetric. intros P Q equiv. induction equiv.
  apply PiEquiv'Lift; apply PiEquiv'Sym; exact H.
  transitivity Q. exact IHequiv. apply PiEquiv'Lift. apply PiEquiv'Sym. exact H.
  Defined.

  (* Smart Constructos for PiEquiv *)
  Theorem EndProcRefl : EndProc ≡π EndProc. reflexivity. Qed.
  Theorem VarProcRefl : forall n, VarProc n ≡π VarProc n. reflexivity. Qed.
  Theorem DefProcContext : forall {P1 P2 Q1 Q2},
      P1 ≡π P2 -> Q1 ≡π Q2 ->
      (DefProc P1 Q1) ≡π (DefProc P2 Q2).
  Proof.
    intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1;
      intros Q1 Q2 equiv2; induction equiv2; eauto with PiC.
  Qed.    
  Theorem SendProcContext : forall p e {P1 P2},
      P1 ≡π P2 ->
      (SendProc p e P1) ≡π (SendProc p e P2).
  Proof.
    intros p e P1 P2 equiv1; induction equiv1; eauto with PiC.
  Qed.
  Theorem RecvProcContext : forall p {P1 P2},
      P1 ≡π P2 ->
      (RecvProc p P1) ≡π (RecvProc p P2).
  Proof.
    intros p P1 P2 equiv; induction equiv; eauto with PiC.
  Qed.
  Theorem EChoiceLContext : forall p {P1 P2},
      P1 ≡π P2 ->
      (EChoiceL p P1) ≡π (EChoiceL p P2).
  Proof.
    intros p P1 P2 equiv; induction equiv; eauto with PiC.
  Qed.
  Theorem EChoiceRContext : forall p {P1 P2},
      P1 ≡π P2 ->
      (EChoiceR p P1) ≡π (EChoiceR p P2).
  Proof.
    intros p P1 P2 equiv; induction equiv; eauto with PiC.
  Qed.
    
  Theorem IChoiceContext : forall p {P1 P2 Q1 Q2},
      P1 ≡π P2 -> Q1 ≡π Q2 ->
      (IChoice p P1 Q1) ≡π (IChoice p P2 Q2).
  Proof.
    intros p P1 P2 Q1 Q2 equiv1; revert p Q1 Q2; induction equiv1;
      intros p Q1 Q2 equiv2; induction equiv2; eauto with PiC.
  Qed.    

  Theorem IfThenElseContext : forall e {P1 P2 Q1 Q2},
      P1 ≡π P2 -> Q1 ≡π Q2 ->
      (IfThenElse e P1 Q1) ≡π (IfThenElse e P2 Q2).
  Proof.
    intros e P1 P2 Q1 Q2 equiv1; revert e Q1 Q2; induction equiv1;
      intros e Q1 Q2 equiv2; induction equiv2; eauto with PiC.
  Qed.    

  Theorem ParContext : forall {P1 P2 Q1 Q2},
      P1 ≡π P2 -> Q1 ≡π Q2 ->
      (Par P1 Q1) ≡π (Par P2 Q2).
  Proof.
    intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1;
      intros Q1 Q2 equiv2; induction equiv2; eauto with PiC.
  Qed.    

  Theorem ParSwap : forall {P1 P2 Q1 Q2},
      P1 ≡π P2 -> Q1 ≡π Q2 ->
      (Par P1 Q1) ≡π (Par Q2 P2).
  Proof.
    intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1;
      intros Q1 Q2 equiv2; induction equiv2; eauto with PiC.
  Qed.    
  Theorem ParComm1 : forall {P1 P2 Q1 Q2 R1 R2},
      P1 ≡π P2 -> Q1 ≡π Q2 -> R1 ≡π R2 ->
      (Par P1 (Par Q1 R1)) ≡π (Par (Par P2 Q2) R2).
  Proof.
    intros P1 P2 Q1 Q2 R1 R2 equiv1; revert Q1 Q2 R1 R2; induction equiv1;
      intros Q1 Q2 R1 R2 equiv2; revert R1 R2; induction equiv2; eauto with PiC;
        intros R1 R2 equiv3; induction equiv3; eauto with PiC.
  Qed.    
  Theorem ParComm2 : forall {P1 P2 Q1 Q2 R1 R2},
      P1 ≡π P2 -> Q1 ≡π Q2 -> R1 ≡π R2 ->
      (Par (Par P1 Q1) R1) ≡π (Par P2 (Par Q2 R2)).
  Proof.
    intros P1 P2 Q1 Q2 R1 R2 equiv1; revert Q1 Q2 R1 R2; induction equiv1; eauto with PiC;
      intros Q1' Q2' R1' R2' equiv2; revert R1' R2'; induction equiv2; eauto with PiC;
        intros R1 R2 equiv3; induction equiv3; eauto with PiC.
  Qed.
  Hint Resolve EndProcRefl VarProcRefl DefProcContext SendProcContext RecvProcContext
       EChoiceLContext EChoiceRContext IChoiceContext IfThenElseContext ParContext
       ParSwap ParComm1 ParComm2 : PiC.
  
  (* Theorem ParEnd11 : forall {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (Par P1 EndProc) ≡π P2. *)
  (* Proof. *)
  (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParEnd12 : forall {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     P1 ≡π (Par P2 EndProc). *)
  (* Proof. *)
  (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParEnd21 : forall {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (Par EndProc P1) ≡π P2. *)
  (* Proof. *)
  (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParEnd22 : forall {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     P1 ≡π (Par EndProc P2). *)
  (* Proof. *)
  (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  
  Inductive PiRedEquiv' : PiCalcRedContext -> PiCalcRedContext -> Prop :=
    HoleRefl' : PiRedEquiv' Hole Hole
  | ParCtxtEquiv1' : forall {CC1 CC2 P1 P2},
      P1 ≡π P2 -> PiRedEquiv' CC1 CC2 -> 
      PiRedEquiv' (ParCtxt1 CC1 P1) (ParCtxt1 CC2 P2)
  | ParCtxtEquiv2' : forall {CC1 CC2 P1 P2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv' (ParCtxt2 P1 CC1) (ParCtxt2 P2 CC2)
  | ParCtxtSwitch1' : forall {CC1 CC2 P1 P2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv' (ParCtxt1 CC1 P1) (ParCtxt2 P2 CC2)
  | ParCtxtSwitch2' : forall {CC1 CC2 P1 P2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv' (ParCtxt2 P1 CC1) (ParCtxt1 CC2 P2)
  | ParCtxtComm11' : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv' (ParCtxt1 CC1 (Par P1 Q1)) (ParCtxt1 (ParCtxt1 CC2 P2) Q2)
  | ParCtxtComm12' : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv' (ParCtxt1 (ParCtxt1 CC1 P1) Q1) (ParCtxt1 CC2 (Par P2 Q2))
  | ParCtxtComm21' : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv' (ParCtxt2  (Par P1 Q1) CC1) (ParCtxt2 P2 (ParCtxt2 Q2 CC2))
  | ParCtxtComm22' : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv' (ParCtxt2 P1 (ParCtxt2 Q1 CC1)) (ParCtxt2  (Par P2 Q2) CC2) .
  (* | ParCtxtEnd11' : forall {CC1 CC2}, *)
  (*     PiRedEquiv' CC1 CC2 -> *)
  (*     PiRedEquiv' (ParCtxt1 CC1 EndProc) CC2 *)
  (* | ParCtxtEnd12' : forall {CC1 CC2}, *)
  (*     PiRedEquiv' CC1 CC2 -> *)
  (*     PiRedEquiv' CC1 (ParCtxt1 CC2 EndProc)  *)
  (* | ParCtxtEnd21' : forall {CC1 CC2}, *)
  (*     PiRedEquiv' CC1 CC2 -> *)
  (*     PiRedEquiv' (ParCtxt2  EndProc CC1) CC2 *)
  (* | ParCtxtEnd22' : forall {CC1 CC2}, *)
  (*     PiRedEquiv' CC1 CC2 -> *)
  (*     PiRedEquiv' CC1 (ParCtxt2  EndProc CC2). *)
  Hint Constructors PiRedEquiv' : PiC.

  Fixpoint PiRedEquiv'Refl (CC : PiCalcRedContext) : PiRedEquiv' CC CC :=
    match CC with
    | Hole => HoleRefl'
    | ParCtxt1 CC P => ParCtxtEquiv1' (PiEquiv'Lift (PiEquiv'Refl P)) (PiRedEquiv'Refl CC) 
    | ParCtxt2 P CC => ParCtxtEquiv2' (PiRedEquiv'Refl CC) (PiEquiv'Lift (PiEquiv'Refl P))
    end.
  Hint Resolve PiRedEquiv'Refl : PiC.

  Lemma PiRedEquiv'Sym : forall CC1 CC2, PiRedEquiv' CC1 CC2 -> PiRedEquiv' CC2 CC1.
  Proof.
    intros CC1 CC2 equiv.
    induction equiv; auto with PiC.
    all: symmetry in H; auto with PiC.
    all: symmetry in H0; auto with PiC.
  Qed.
  Hint Resolve PiRedEquiv'Sym : PiC.

  Inductive PiRedEquiv : PiCalcRedContext -> PiCalcRedContext -> Prop :=
    PiRedEquiv'Lift : forall {CC1 CC2}, PiRedEquiv' CC1 CC2 -> PiRedEquiv CC1 CC2
  | PiRedEquivStep : forall {CC1 CC2 CC3},
      PiRedEquiv' CC1 CC2 -> PiRedEquiv CC2 CC3 -> PiRedEquiv CC1 CC3.
  Hint Constructors PiRedEquiv : PiC.

  Instance PiRedEquivReflexive : Reflexive PiRedEquiv :=
    fun CC => PiRedEquiv'Lift (PiRedEquiv'Refl CC).
  Instance PiRedEquivTransitive : Transitive PiRedEquiv.
  unfold Transitive. intros CC1 CC2 CC3 equiv1 equiv2.
  induction equiv1. eapply PiRedEquivStep; eauto with PiC.
  eapply PiRedEquivStep; [exact H| apply IHequiv1; exact equiv2].
  Defined.
  Instance PiRedEquivSymmetric : Symmetric PiRedEquiv.
  unfold Symmetric; intros CC1 CC2 equiv1; induction equiv1.
  apply PiRedEquiv'Lift; apply PiRedEquiv'Sym ;auto.
  transitivity (CC2); auto. apply PiRedEquiv'Sym in H; apply PiRedEquiv'Lift; auto.
  Defined.

  Theorem HoleRefl : PiRedEquiv Hole Hole. reflexivity. Qed.
  Theorem ParCtxtEquiv1 : forall {CC1 CC2 P1 P2},
      P1 ≡π P2 -> PiRedEquiv CC1 CC2 -> 
      PiRedEquiv (ParCtxt1 CC1 P1) (ParCtxt1 CC2 P2).
  Proof.
    intros CC1 CC2 P1 P2 equiv1 equiv2; revert P1 P2 equiv1; induction equiv2;
      intros P1 P2 equiv1; eauto with PiC.
  Qed.
  Theorem ParCtxtEquiv2 : forall {CC1 CC2 P1 P2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv (ParCtxt2 P1 CC1) (ParCtxt2 P2 CC2).
  Proof.
    intros CC1 CC2 P1 P2 equiv1; revert P1 P2;
      induction equiv1; intros P1 P2 equiv2; eauto with PiC.
  Qed.
  Theorem ParCtxtSwitch1 : forall {CC1 CC2 P1 P2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv (ParCtxt1 CC1 P1) (ParCtxt2 P2 CC2).
  Proof.
    intros CC1 CC2 P1 P2 equiv1; revert P1 P2;
      induction equiv1; intros P1 P2 equiv2; eauto with PiC.
  Qed.
  Theorem ParCtxtSwitch2 : forall {CC1 CC2 P1 P2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 ->
      PiRedEquiv (ParCtxt2 P1 CC1) (ParCtxt1 CC2 P2).
  Proof.
    intros CC1 CC2 P1 P2 equiv1; revert P1 P2;
      induction equiv1; intros P1 P2 equiv2; eauto with PiC.
  Qed.

  Theorem ParCtxtComm11 : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv (ParCtxt1 CC1 (Par P1 Q1)) (ParCtxt1 (ParCtxt1 CC2 P2) Q2).
  Proof.
    intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2;
      induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC.
  Qed.
  Theorem ParCtxtComm12 : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv (ParCtxt1 (ParCtxt1 CC1 P1) Q1) (ParCtxt1 CC2 (Par P2 Q2)).
  Proof.
    intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2;
      induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC.
    apply @PiRedEquivStep with (CC2 := ParCtxt1 (ParCtxt1 CC2 P1) Q1); eauto with PiC.
  Qed.
  Theorem ParCtxtComm21 : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv (ParCtxt2  (Par P1 Q1) CC1) (ParCtxt2 P2 (ParCtxt2 Q2 CC2)).
  Proof.
    intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2;
      induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC.
  Qed.
  Theorem ParCtxtComm22 : forall {CC1 CC2 P1 P2 Q1 Q2},
      PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 ->
      PiRedEquiv (ParCtxt2 P1 (ParCtxt2 Q1 CC1)) (ParCtxt2  (Par P2 Q2) CC2).
  Proof.
    intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2;
      induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC.
    apply @PiRedEquivStep with (CC2 := ParCtxt2 P1 (ParCtxt2 Q1 CC2)); eauto with PiC.
  Qed.
  Hint Resolve HoleRefl ParCtxtEquiv1 ParCtxtEquiv2 ParCtxtComm11 ParCtxtComm12
       ParCtxtComm21 ParCtxtComm22 ParCtxtSwitch1 ParCtxtSwitch2 : PiC.
  
  (* Theorem ParCtxtEnd11 : forall {CC1 CC2}, *)
  (*     PiRedEquiv CC1 CC2 -> *)
  (*     PiRedEquiv (ParCtxt1 CC1 EndProc) CC2. *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtEnd12 : forall {CC1 CC2}, *)
  (*     PiRedEquiv CC1 CC2 -> *)
  (*     PiRedEquiv CC1 (ParCtxt1 CC2 EndProc). *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtEnd21 : forall {CC1 CC2}, *)
  (*     PiRedEquiv CC1 CC2 -> *)
  (*     PiRedEquiv (ParCtxt2  EndProc CC1) CC2. *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtEnd22 : forall {CC1 CC2}, *)
  (*     PiRedEquiv CC1 CC2 -> *)
  (*     PiRedEquiv CC1 (ParCtxt2  EndProc CC2). *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)

  Fixpoint ContextCompose (CC1 CC2 : PiCalcRedContext) : PiCalcRedContext :=
    match CC1 with
    | Hole => CC2
    | ParCtxt1 CC1 P => ParCtxt1 (ContextCompose CC1 CC2) P
    | ParCtxt2 P CC1 => ParCtxt2 P (ContextCompose CC1 CC2)
    end.

  Lemma ApplyComposedContext: forall (CC1 CC2 : PiCalcRedContext) (P : Proc),
      ApplyRedContext (ContextCompose CC1 CC2) P = ApplyRedContext CC1 (ApplyRedContext CC2 P).
  Proof.
    intro CC1; induction CC1; simpl; auto; intros CC2 P;
      rewrite IHCC1; auto.
  Qed.

  Lemma ContextComposeEquiv' : forall (CC1 CC1' CC2 CC2' : PiCalcRedContext),
      PiRedEquiv' CC1 CC1' -> PiRedEquiv' CC2 CC2'
      -> PiRedEquiv' (ContextCompose CC1 CC2) (ContextCompose CC1' CC2').
  Proof.
    intros CC1 CC1' CC2 CC2' equiv1; revert CC2 CC2'; induction equiv1;
      simpl; auto with PiC.
  Qed.

  Lemma ContextComposeEquiv : forall (CC1 CC1' CC2 CC2' : PiCalcRedContext),
      PiRedEquiv CC1 CC1' -> PiRedEquiv CC2 CC2'
      -> PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC1' CC2').
  Proof.
    intros CC1 CC1' CC2 CC2' equiv1; revert CC2 CC2'; induction equiv1;
      simpl; auto with PiC.
    - intros CC2' CC2'' equiv2.
      induction equiv2; auto with PiC.
      constructor; apply ContextComposeEquiv'; auto.
      transitivity (ContextCompose CC1 CC3); auto.
      constructor; apply ContextComposeEquiv'; auto. apply PiRedEquiv'Refl.
    - intros CC0 CC2' equiv2. specialize (IHequiv1 CC0 CC2' equiv2).
      transitivity (ContextCompose CC2 CC0); auto.
      constructor; apply ContextComposeEquiv'; auto. apply PiRedEquiv'Refl.
  Qed.

  Lemma ContextComposeComm : forall CC1 CC2 CC3,
      ContextCompose CC1 (ContextCompose CC2 CC3) =
      ContextCompose (ContextCompose CC1 CC2) CC3.
  Proof.
    intro CC1; induction CC1; simpl; auto;
      intros CC2 CC3; rewrite IHCC1; auto.
  Qed.

  Lemma ContextComposeHole : forall CC, ContextCompose CC Hole = CC.
  Proof.
    intro CC; induction CC; simpl; auto; rewrite IHCC; auto.
  Qed.

  Lemma ContextComposeSwapEquiv : forall CC1 CC2,
      PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC2 CC1).
  Proof.
    intros CC1; induction CC1; intro CC2; simpl.
    - rewrite ContextComposeHole; reflexivity.
    - induction CC2; simpl in *; auto with PiC.
      -- rewrite ContextComposeHole; reflexivity.
      -- transitivity (ParCtxt1 (ContextCompose (ParCtxt1 CC2 p0) CC1) p); auto with PiC;
           simpl.
         transitivity (ParCtxt1 (ContextCompose CC2 CC1) (Par p0 p)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC1 CC2) p) p0); auto with PiC.
         transitivity (ParCtxt1 (ContextCompose CC1 CC2) (Par p p0)); auto with PiC.
         apply ParCtxtEquiv1; auto with PiC.
         symmetry; apply IHCC1.
      -- transitivity (ParCtxt2 p0 (ContextCompose (ParCtxt1 CC1 p) CC2)); auto with PiC;
           simpl.
         transitivity (ParCtxt1 (ContextCompose (ParCtxt2 p0 CC2) CC1) p); auto with PiC;
           simpl.
         transitivity (ParCtxt2 p (ParCtxt2 p0 (ContextCompose CC2 CC1))); auto with PiC.
         transitivity (ParCtxt2 p0 (ParCtxt2 p (ContextCompose CC1 CC2))); auto with PiC.
         transitivity (ParCtxt2 (Par p p0) (ContextCompose CC2 CC1)); auto with PiC.
         transitivity (ParCtxt2 (Par p0 p) (ContextCompose CC1 CC2)); auto with PiC.
         apply ParCtxtEquiv2; auto with PiC.
         symmetry; apply IHCC1.
    - induction CC2; simpl in *; auto with PiC.
      -- rewrite ContextComposeHole; reflexivity.
      -- transitivity (ParCtxt2 p (ContextCompose (ParCtxt1 CC2 p0) CC1)); auto with PiC;
           simpl.
         transitivity (ParCtxt1 (ContextCompose (ParCtxt2 p CC1) CC2) p0); auto with PiC;
           simpl.
         transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC2 CC1) p0) p); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC1 CC2) p) p0); auto with PiC.
         transitivity (ParCtxt1 (ContextCompose CC2 CC1) (Par p0 p)); auto with PiC.
         transitivity (ParCtxt1 (ContextCompose CC1 CC2) (Par p p0)); auto with PiC.
         apply ParCtxtEquiv1; symmetry; auto with PiC.
      -- transitivity (ParCtxt2 p (ContextCompose (ParCtxt2 p0 CC2) CC1)); auto with PiC;
           simpl.
         transitivity (ParCtxt2 p0 (ContextCompose (ParCtxt2 p CC1) CC2)); auto with PiC;
           simpl.
         transitivity (ParCtxt2 (Par p p0) (ContextCompose CC2 CC1)); auto with PiC.
         transitivity (ParCtxt2 (Par p0 p) (ContextCompose CC1 CC2)); auto with PiC.
         apply ParCtxtEquiv2; auto with PiC.
         symmetry; apply IHCC1.
  Qed.

  Lemma CCEquiv' : forall CC1 CC2,
      PiRedEquiv' CC1 CC2 ->
      forall P Q, P ≡π Q ->
             (ApplyRedContext CC1 P) ≡π (ApplyRedContext CC2 Q).
  Proof.
    intros CC1 CC2 equiv1; induction equiv1; intros Q R equiv2; simpl; auto with PiC.
  Qed.
  Lemma CCEquiv : forall CC1 CC2,
      PiRedEquiv CC1 CC2 ->
      forall P Q, P ≡π Q ->
             (ApplyRedContext CC1 P) ≡π (ApplyRedContext CC2 Q).
  Proof.
    intros CC1 CC2 equiv1; induction equiv1; intros P Q equiv.
    - apply CCEquiv'; auto.
    - transitivity (ApplyRedContext CC2 P).
      apply CCEquiv'; auto. reflexivity. apply IHequiv1; auto.
  Qed.

  Lemma Equiv'HoleInversion : forall CC, PiRedEquiv' CC Hole -> CC = Hole.
  Proof.
    intros CC equiv; destruct CC; inversion equiv; auto.
  Qed.
  Lemma EquivHoleInversion : forall CC, PiRedEquiv CC Hole -> CC = Hole.
  Proof.
    intros CC equiv; remember Hole; induction equiv; subst.
    apply Equiv'HoleInversion in H; auto.
    specialize (IHequiv eq_refl); subst. apply Equiv'HoleInversion in H; auto.
  Qed.

  Definition SingleThread : Proc -> Prop :=
    fun P => match P with
    | EndProc => True
    | VarProc x => True
    | DefProc x x0 => True
    | SendProc x x0 x1 => True
    | RecvProc x x0 => True
    | EChoiceL x x0 => True
    | EChoiceR x x0 => True
    | IChoice x x0 x1 => True
    | IfThenElse x x0 x1 => True
    | Par x x0 => False
    end.

  Lemma SingleThreadEquiv' : forall P Q, SingleThread P -> P ≡π' Q -> SingleThread Q.
  Proof.
    intros P Q ST equiv; revert ST; induction equiv; simpl; intro ST; auto.
  Qed.
  Lemma SingleThreadEquiv : forall P Q, SingleThread P -> P ≡π Q -> SingleThread Q.
  Proof.
    intros P Q ST equiv; induction equiv. apply SingleThreadEquiv' in H; auto.
    apply IHequiv. apply SingleThreadEquiv' in H; auto.
  Qed.

  Fixpoint ProcessToList (P : Proc) : list Proc :=
    match P with
    | Par P Q => ProcessToList P ++ ProcessToList Q
    | _ => [P]
    end.

  Lemma ProcessToListNonNil : forall (P : Proc), ProcessToList P <> nil.
  Proof.
    intro P; induction P; try (intro H; inversion H; fail).
    simpl. intro H; apply app_eq_nil in H; destruct H; apply IHP1; auto.
  Qed.

  Theorem AllInProcessToList' : forall (P Q : Proc),
      P ≡π' Q ->
      (forall R : Proc, In R (ProcessToList P) -> exists R', In R' (ProcessToList Q) /\ R ≡π R').
  Proof.    
    intros P Q equiv; induction equiv; simpl; intro R; intro H; auto.
    all: try (destruct H; auto; subst).
    all: try (eexists; split; auto with PiC; fail).
    - apply in_app_or in H; destruct H.
      destruct (IHequiv1 R H) as [R' IH]; destruct IH as [i equiv];
        exists R'; split; auto.
      apply in_or_app; left; auto.
      destruct (IHequiv2 R H) as [R' IH]; destruct IH as [i equiv];
        exists R'; split; auto.
      apply in_or_app; right; auto.
    - apply in_app_or in H; destruct H.
      destruct (IHequiv1 R H) as [R' IH]; destruct IH as [i equiv];
        exists R'; split; auto.
      apply in_or_app; right; auto.
      destruct (IHequiv2 R H) as [R' IH]; destruct IH as [i equiv];
        exists R'; split; auto.
      apply in_or_app; left; auto.
    - apply in_app_or in H; destruct H; [| apply in_app_or in H; destruct H].
      -- destruct (IHequiv1 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; left; apply in_or_app; left; auto.
      -- destruct (IHequiv2 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; left; apply in_or_app; right; auto.
      -- destruct (IHequiv3 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; right; auto.
    - apply in_app_or in H; destruct H; [ apply in_app_or in H; destruct H |].
      -- destruct (IHequiv1 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; left; auto.
      -- destruct (IHequiv2 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; right; apply in_or_app; left; auto.
      -- destruct (IHequiv3 R H) as [R' IH]; destruct IH;
           exists R'; split; auto.
         apply in_or_app; right; apply in_or_app; right; auto.
  Qed.
  
  Fixpoint ListToProcess (l : list Proc) : option Proc :=
    match l with
    | [] => None
    | P :: l' => match ListToProcess l' with
               | None => Some P
               | Some Q => Some (Par P Q)
               end
    end.

  Lemma ListToProcessNoneNil : forall (l : list Proc), ListToProcess l = None -> l = [].
  Proof.
    intros l H. destruct l; auto. inversion H.
    destruct (ListToProcess l); inversion H1.
  Qed.

  Inductive ListPiEquiv : list Proc -> list Proc -> Prop :=
    NilPiEquiv : ListPiEquiv [] []
  | ConsPiEquiv : forall P Q l l',
      P ≡π Q -> ListPiEquiv l l' ->
      ListPiEquiv (P :: l) (Q :: l').
  Hint Constructors ListPiEquiv : PiC.

  Theorem ListPiEquivToTerm : forall l l',
      ListPiEquiv l l' ->
      forall P Q, ListToProcess l = Some P -> ListToProcess l' = Some Q ->
             P ≡π Q.
  Proof.
    intros l l' lequiv; induction lequiv; intros R S eq1 eq2; [inversion eq1|].
    simpl in eq1; simpl in eq2.
    destruct (ListToProcess l) eqn:eql; destruct (ListToProcess l') eqn:eql'.
    - inversion eq1; inversion eq2; subst; clear eq1 eq2.
      specialize (IHlequiv p p0 eq_refl eq_refl). apply ParContext; auto.
    - inversion eq1; inversion eq2; subst; clear eq1 eq2.
      apply ListToProcessNoneNil in eql'; subst. inversion lequiv;subst. inversion eql.
    - inversion eq1; inversion eq2; subst; clear eq1 eq2.
      apply ListToProcessNoneNil in eql; subst. inversion lequiv; subst. inversion eql'.
    - inversion eq1; inversion eq2; subst; clear eq1 eq2; auto.
  Qed.

  Theorem ListPiEquivDoubleApp : forall l1 l2 l3 l4,
      ListPiEquiv l1 l3 -> ListPiEquiv l2 l4 -> ListPiEquiv (l1 ++ l2) (l3 ++ l4).
  Proof.
    intro l1; induction l1; intros l2 l3 l4 H H0.
    inversion H; simpl; auto.
    inversion H; subst; simpl; constructor; auto.
  Qed.
    
  (* How is this not in the standard library!? *)
  Theorem AppComm : forall {A : Type} (l1 l2 l3 : list A),
      l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
  Proof.
    intros A l1; induction l1; simpl; intros l2 l3; [| rewrite IHl1]; reflexivity.
  Qed.

  Theorem ProcessToListEquiv' : forall P Q,
      P ≡π' Q -> exists l l', Permutation (ProcessToList P) l /\ Permutation (ProcessToList Q) l' /\
                       ListPiEquiv l l'.
  Proof.
    intros P Q equiv; induction equiv; simpl.
    all: try (eexists; eexists; split; [|split]; eauto with PiC; fail).
    - destruct IHequiv1 as [l1 H]; destruct H as [l2 H];
        destruct H as [perm1 H]; destruct H as [perm2 lequiv1].
      destruct IHequiv2 as [l3 H]; destruct H as [l4 H];
        destruct H as [perm3 H]; destruct H as [perm4 lequiv2].
      exists (l1 ++ l3); exists (l2 ++ l4); split; [| split];
        try (apply Permutation_app; auto).
      apply ListPiEquivDoubleApp; auto.
    - destruct IHequiv1 as [l1 H]; destruct H as [l2 H];
        destruct H as [perm1 H]; destruct H as [perm2 lequiv1].
      destruct IHequiv2 as [l3 H]; destruct H as [l4 H];
        destruct H as [perm3 H]; destruct H as [perm4 lequiv2].
      exists (l1 ++ l3); exists (l2 ++ l4); split; [| split].
      apply Permutation_app; auto.
      transitivity (l4 ++ l2);
        [apply Permutation_app; auto|apply Permutation_app_comm].
      apply ListPiEquivDoubleApp; auto.
    - destruct IHequiv1 as [l1 H]; destruct H as [l2 H];
        destruct H as [perm1 H]; destruct H as [perm2 lequiv1].
      destruct IHequiv2 as [l3 H]; destruct H as [l4 H];
        destruct H as [perm3 H]; destruct H as [perm4 lequiv2].
      destruct IHequiv3 as [l5 H]; destruct H as [l6 H];
        destruct H as [perm5 H]; destruct H as [perm6 lequiv3].
      exists (l1 ++ l3 ++ l5); exists (l2 ++ l4 ++ l6); split; [|split].
      repeat (apply Permutation_app; auto). 
      rewrite AppComm.
      repeat (apply Permutation_app; auto).
      repeat (apply ListPiEquivDoubleApp; auto).
    - destruct IHequiv1 as [l1 H]; destruct H as [l2 H];
        destruct H as [perm1 H]; destruct H as [perm2 lequiv1].
      destruct IHequiv2 as [l3 H]; destruct H as [l4 H];
        destruct H as [perm3 H]; destruct H as [perm4 lequiv2].
      destruct IHequiv3 as [l5 H]; destruct H as [l6 H];
        destruct H as [perm5 H]; destruct H as [perm6 lequiv3].
      exists (l1 ++ l3 ++ l5); exists (l2 ++ l4 ++ l6); split; [|split].
      rewrite AppComm; repeat (apply Permutation_app; auto). 
      repeat (apply Permutation_app; auto).
      repeat (apply ListPiEquivDoubleApp; auto).
  Qed.

  Theorem ListEquivRefl : forall l, ListPiEquiv l l.
  Proof.
    intro l; induction l; simpl; constructor; auto with PiC.
  Qed.
  Hint Resolve ListEquivRefl : PiC.

  Theorem ListEquivTrans : forall l1 l2 l3,
      ListPiEquiv l1 l2 -> ListPiEquiv l2 l3 -> ListPiEquiv l1 l3.
  Proof.
    intros l1 l2 l3 equiv1; revert l3; induction equiv1; intros l3 equiv2;
      inversion equiv2; subst; auto with PiC.
    constructor; auto. transitivity Q; auto.
  Qed.

  Theorem ListEquivPermutation : forall l1 l2,
      ListPiEquiv l1 l2 -> forall l3, Permutation l2 l3 -> exists l4, Permutation l1 l4 /\ ListPiEquiv l4 l3.
  Proof.
    intros l1 l2 equiv l3 perm; revert l1 equiv; induction perm; intros l1 equiv.
      
    - inversion equiv; subst. exists []; split; constructor.
    - inversion equiv; subst.
      destruct (IHperm l0 H3) as [l4 Hl4]; destruct Hl4 as [perm' equiv'].
      exists (P :: l4); split; try (constructor; auto; fail).
    - inversion equiv; subst. inversion H3; subst.
      exists (P0 :: P :: l1); split; try (constructor; auto; fail).
      constructor; auto. constructor; auto.
    - specialize (IHperm1 l1 equiv).
      destruct IHperm1 as [l2 H]; destruct H as [perm12 equiv2].
      specialize (IHperm2 l2 equiv2); destruct IHperm2 as [l3 H]; destruct H as [perm23 equiv3].
      exists l3; split; auto. transitivity l2; auto.
  Qed.

  Lemma ProcessToListEquiv : forall P Q,
      P ≡π Q -> exists l l', Permutation (ProcessToList P) l /\ Permutation (ProcessToList Q) l' /\
                       ListPiEquiv l l'.
  Proof.
    intros P Q equiv; induction equiv.
    apply ProcessToListEquiv'; auto.
    apply ProcessToListEquiv' in H.
    destruct H as [lP H]; destruct H as [lQ H]; destruct H as [permP H];
      destruct H as [permQ equivPQ].
    destruct IHequiv as [lQ' H]; destruct H as [lR H]; destruct H as [permQ' H];
      destruct H as [permR equivQR].
    assert (Permutation lQ lQ') as permQ''
        by (transitivity (ProcessToList Q); [symmetry|]; auto).
    destruct (ListEquivPermutation lP lQ equivPQ lQ' permQ'') as [lP' H];
      destruct H as [perm lequiv].
    exists lP'; exists lR; split; [| split]; auto.
    transitivity lP; auto. eapply ListEquivTrans; eauto.
  Qed.
      
  Theorem ListToProcessPerm : forall l l' P Q,
      Permutation l l' ->
      ListToProcess l = Some P ->
      ListToProcess l' = Some Q ->
      P ≡π Q.
  Proof.
    intros l l' P Q perm; revert P Q; induction perm; intros p q eq1 eq2.
    - inversion eq1.
    - simpl in *. destruct l eqn:e1; destruct l' eqn:e2. simpl in *.
      inversion eq1; inversion eq2; subst; reflexivity.
      apply Permutation_nil in perm; inversion perm.
      apply Permutation_sym in perm; apply Permutation_nil in perm; inversion perm.
      simpl in *.
      destruct (ListToProcess l0); destruct (ListToProcess l1).
      all: inversion eq1; inversion eq2; subst.
      all: apply ParContext; [reflexivity|]; apply IHperm; auto.
    - simpl in eq1. simpl in eq2. destruct (ListToProcess l).
      inversion eq1; inversion eq2; subst.
      transitivity (Par (Par y x) p0).
      apply ParComm1; auto with PiC.
      transitivity (Par (Par x y) p0); auto with PiC.
      inversion eq1; inversion eq2; subst.
      auto with PiC.
    - destruct (ListToProcess l') eqn:e.
      transitivity p0. apply IHperm1; auto. apply IHperm2; auto.
      apply ListToProcessNoneNil in e; subst.
      apply Permutation_nil in perm2; subst. simpl in eq2. inversion eq2.
  Qed.

  Fixpoint ContextToLists (CC : PiCalcRedContext) : list Proc * list Proc :=
    match CC with
    | Hole => ([], [])
    | ParCtxt1 CC' P => match (ContextToLists CC') with
                       | (l1, l2) => (l1, l2 ++ ProcessToList P)
                       end
    | ParCtxt2 P CC' => match (ContextToLists CC') with
                       | (l1, l2) => (ProcessToList P ++ l1, l2)
                       end
    end.


  Theorem ApplyRedContextToLists : forall (CC : PiCalcRedContext) (P : Proc),
      ProcessToList (ApplyRedContext CC P) =
      fst (ContextToLists CC) ++ ProcessToList P ++ snd (ContextToLists CC).
  Proof.
    intro CC; induction CC; simpl; intros P.
    - apply app_nil_end.
    - destruct (ContextToLists CC); simpl in *.
      rewrite IHCC; auto.
      rewrite <- AppComm; rewrite <- AppComm; reflexivity.
    - destruct (ContextToLists CC); simpl in *.
      rewrite IHCC; auto.
      rewrite AppComm; reflexivity.
  Qed.

  Lemma SingleThreadToList : forall P, SingleThread P -> ProcessToList P = [P].
  Proof.
    intros P STP; destruct P; auto; inversion STP.
  Qed.

  Fixpoint LeftContextFromList (l : list Proc) : PiCalcRedContext :=
    match l with
    | nil => Hole
    | P :: l' => ParCtxt1 (LeftContextFromList l') P
    end.

  Lemma LeftContextAppCompose : forall (l1 l2 : list Proc),
      LeftContextFromList (l1 ++ l2) =
      ContextCompose (LeftContextFromList l1) (LeftContextFromList l2).
  Proof.
    intro l1; induction l1; simpl; auto.
    intro l2; rewrite IHl1; auto.
  Qed.

  Lemma LeftContextFromProcessList : forall (P : Proc),
      PiRedEquiv (LeftContextFromList (ProcessToList P)) (ParCtxt1 Hole P).
  Proof.
    intro P; induction P; simpl; auto with PiC.
    rewrite LeftContextAppCompose.
    transitivity (ContextCompose (ParCtxt1 Hole P1) (ParCtxt1 Hole P2)); auto.
    apply ContextComposeEquiv; auto.
    simpl. transitivity (ParCtxt1 Hole (Par P2 P1)); auto with PiC.
  Qed.

  Lemma LeftContetFromRevList : forall l,
      PiRedEquiv (LeftContextFromList l) (LeftContextFromList (rev l)).
  Proof.
    intros l; induction l; simpl; auto with PiC.
    rewrite LeftContextAppCompose; simpl.
    transitivity (ContextCompose (ParCtxt1 Hole a) (LeftContextFromList (rev l)));
      [simpl | apply ContextComposeSwapEquiv]; auto with PiC.
  Qed.

  Lemma LeftContextFromRevProcessList : forall (P : Proc),
      PiRedEquiv (LeftContextFromList (rev (ProcessToList P))) (ParCtxt1 Hole P).
  Proof.
    intro P; induction P; simpl; auto with PiC.
    rewrite rev_app_distr. rewrite LeftContextAppCompose.
    transitivity (ContextCompose (ParCtxt1 Hole P2) (ParCtxt1 Hole P1)); auto with PiC.
    apply ContextComposeEquiv; auto.
    simpl; auto with PiC.
  Qed.

  Lemma LeftContextEquivLists : forall (l1 l2 : list Proc),
      ListPiEquiv l1 l2 -> PiRedEquiv (LeftContextFromList l1) (LeftContextFromList l2).
  Proof.
    intros l1 l2 lequiv; induction lequiv; simpl.
    reflexivity.
    apply ParCtxtEquiv1; auto with PiC.
  Qed.

  Lemma LeftContextPermLists : forall l1 l2,
      Permutation l1 l2 -> PiRedEquiv (LeftContextFromList l1) (LeftContextFromList l2).
  Proof.
    intros l1 l2 perm; induction perm; simpl.
    - reflexivity.
    - apply ParCtxtEquiv1; auto with PiC.
    - transitivity (ParCtxt1 (LeftContextFromList l) (Par x y)).
      apply ParCtxtComm12; reflexivity.
      transitivity (ParCtxt1 (LeftContextFromList l) (Par y x)).
      apply ParCtxtEquiv1; auto with PiC; reflexivity.
      apply ParCtxtComm11; reflexivity.
    - transitivity (LeftContextFromList l'); auto.
  Qed.

  Fixpoint RightContextFromList (l : list Proc) : PiCalcRedContext :=
    match l with
    | [] => Hole
    | P :: l' => ParCtxt2 P (RightContextFromList l')
    end.

  Lemma RightContextAppCompose : forall (l1 l2 : list Proc),
      RightContextFromList (l1 ++ l2) =
      ContextCompose (RightContextFromList l1) (RightContextFromList l2).
  Proof.
    intro l1; induction l1; simpl; auto.
    intros l2; rewrite IHl1; reflexivity.
  Qed.

  Lemma RightContextFromProcessList : forall (P : Proc),
      PiRedEquiv (RightContextFromList (ProcessToList P))
                 (ParCtxt2 P Hole).
  Proof.
    intro P; induction P; simpl; auto with PiC.
    rewrite RightContextAppCompose.
    transitivity (ContextCompose (ParCtxt2 P1 Hole) (ParCtxt2 P2 Hole)).
    apply ContextComposeEquiv; auto.
    simpl. apply ParCtxtComm22; auto with PiC.
  Qed.
  
  Definition ContextFromLists  (l1 l2 : list Proc) : PiCalcRedContext :=
    ContextCompose (RightContextFromList l1) (LeftContextFromList (rev l2)).

  Lemma ComposeEquivBackwards : forall CC1 CC2 CC3 CC4,
      PiRedEquiv CC1 CC4 -> PiRedEquiv CC2 CC3 ->
      PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC3 CC4).
  Proof.
    intros CC1 CC2 CC3 CC4 H H0.
    transitivity (ContextCompose CC2 CC1).
    apply ContextComposeSwapEquiv.
    apply ContextComposeEquiv; auto.
  Qed.

  
  
  Lemma ContextFromListsEquiv : forall (CC : PiCalcRedContext),
      PiRedEquiv CC (ContextFromLists (fst (ContextToLists CC)) (snd (ContextToLists CC))).
  Proof.
    unfold ContextFromLists.
    induction CC; simpl; auto with PiC.
    - destruct (ContextToLists CC); simpl in *.
      rewrite rev_app_distr.
      rewrite LeftContextAppCompose. rewrite ContextComposeComm.
      transitivity (ContextCompose CC (ParCtxt1 Hole p)); simpl; auto with PiC.
      2: {transitivity (ContextCompose (ContextCompose (LeftContextFromList (rev (ProcessToList p))) (RightContextFromList l)) (LeftContextFromList (rev l0))).
          rewrite <- ContextComposeComm. apply ComposeEquivBackwards; auto.
          symmetry; apply LeftContextFromRevProcessList.
      apply ContextComposeEquiv. apply ContextComposeSwapEquiv. reflexivity. }
      clear IHCC l l0. induction CC; simpl; auto with PiC.
      -- transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC.
         transitivity (ParCtxt1 CC (Par p p0)); auto with PiC.
      -- transitivity (ParCtxt2 p0 (ParCtxt1 CC p)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC p0) p); auto with PiC.
         transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC.
         transitivity (ParCtxt1 CC (Par p p0)); auto with PiC.
    - destruct (ContextToLists CC); simpl in *.
      rewrite RightContextAppCompose; rewrite <- ContextComposeComm.
      transitivity (ContextCompose (ParCtxt2 p Hole) CC); [reflexivity|].
      apply ContextComposeEquiv; auto. symmetry; apply RightContextFromProcessList.
  Qed.

  Lemma ListPiEquivRev : forall l1 l2, ListPiEquiv l1 l2 -> ListPiEquiv (rev l1) (rev l2).
  Proof.
    intros l1 l2 lequiv; induction lequiv; simpl; auto with PiC.
    apply ListPiEquivDoubleApp; auto with PiC.
  Qed.

  Theorem FromEquivLists : forall l1 l2 l3 l4,
      ListPiEquiv (l1 ++ l2) (l3 ++ l4) ->
      PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4).
  Proof.
    unfold ContextFromLists.
    intros l1 l2 l3 l4 lequiv.
    remember (l1 ++ l2). remember (l3 ++ l4). revert l1 l2 l3 l4 Heql Heql0.
    induction lequiv.
    - intros l1 l2 l3 l4 Heql Heql0.
      symmetry in Heql; apply app_eq_nil in Heql; destruct Heql; subst.
      symmetry in Heql0; apply app_eq_nil in Heql0; destruct Heql0; subst.
      simpl. reflexivity.
    - intros l1 l2 l3 l4 Heql Heql0.
      destruct l1; destruct l3; subst; simpl in *.
      -- apply LeftContextEquivLists; auto; subst.
         apply ListPiEquivRev.
         constructor; auto.
      -- inversion Heql0; subst; simpl.
         specialize (IHlequiv [] l l3 l4 eq_refl eq_refl). simpl in IHlequiv.
         transitivity (ParCtxt2 P (LeftContextFromList (rev l))); auto with PiC.
         rewrite LeftContextAppCompose; simpl.
         transitivity (ContextCompose (ParCtxt1 Hole P) (LeftContextFromList (rev l)));
           simpl; auto with PiC.
         apply ContextComposeSwapEquiv; auto.
      -- inversion Heql; subst; simpl.
         specialize (IHlequiv l1 l2 [] l' eq_refl eq_refl); simpl in IHlequiv.
         rewrite LeftContextAppCompose; simpl.
         transitivity (ContextCompose (ParCtxt1 Hole Q) (LeftContextFromList (rev l')));
           [simpl; auto with PiC|].
         apply ContextComposeSwapEquiv.
      -- inversion Heql; inversion Heql0; subst.
         specialize (IHlequiv l1 l2 l3 l4 eq_refl eq_refl).
         apply ParCtxtEquiv2; auto.
  Qed.
      
  Theorem ToListsEquiv : forall CC1 CC2,
      ListPiEquiv (fst (ContextToLists CC1) ++ snd (ContextToLists CC1))
                  (fst (ContextToLists CC2) ++ snd (ContextToLists CC2))
      -> PiRedEquiv CC1 CC2.
  Proof.
    intros CC1 CC2 H. apply FromEquivLists in H.
    etransitivity; [| etransitivity; [exact H|]]; [| symmetry];
      apply ContextFromListsEquiv.
  Qed.

  Lemma RightEquivLeft : forall l, PiRedEquiv (RightContextFromList l) (LeftContextFromList l).
  Proof.
    intro l; induction l; simpl.
    reflexivity.
    transitivity (ParCtxt1 (RightContextFromList l) a). apply ParCtxtSwitch2; reflexivity.
    apply ParCtxtEquiv1; auto with PiC.
  Qed.

  Theorem FromNearlyEqualLists' : forall l1 l2 l3 l4,
      l1 ++ rev l2 = l3 ++ rev l4 ->
      PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4).
  Proof.
    intros l1 l2 l3 l4 H.
    unfold ContextFromLists.
    transitivity (ContextCompose (LeftContextFromList l1) (LeftContextFromList (rev l2))).
    apply ContextComposeEquiv; [|reflexivity]. apply RightEquivLeft.
    rewrite <- LeftContextAppCompose.
    transitivity (ContextCompose (LeftContextFromList l3) (LeftContextFromList (rev l4))).
    rewrite <- LeftContextAppCompose. rewrite H. reflexivity.
    apply ContextComposeEquiv; [|reflexivity]. symmetry. apply RightEquivLeft.
  Qed.

  Theorem FromNearlyEqualLists : forall l1 l2 l3 l4,
      l1 ++ l2 = l3 ++  l4 ->
      PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4).
  Proof.
    intros l1 l2 l3 l4 H.
    unfold ContextFromLists.
    transitivity (ContextCompose (LeftContextFromList l1) (LeftContextFromList l2)).
    apply ContextComposeEquiv. apply RightEquivLeft. symmetry; apply LeftContetFromRevList.
    rewrite <- LeftContextAppCompose.
    transitivity (ContextCompose (LeftContextFromList l3) (LeftContextFromList l4)).
    rewrite <- LeftContextAppCompose; rewrite H; reflexivity.
    apply ContextComposeEquiv. symmetry; apply RightEquivLeft. apply LeftContetFromRevList.
  Qed.

  Lemma TwoHoleTransfer : forall l P Q,
      PiRedEquiv (ContextCompose (ContextCompose l (ParCtxt1 Hole P)) (ParCtxt1 Hole Q))
                 (ParCtxt1 (ParCtxt1 l P) Q).
  Proof.
    intros l P Q.
    transitivity (ContextCompose (ParCtxt1 Hole Q) (ContextCompose l (ParCtxt1 Hole P)));
      [apply ContextComposeSwapEquiv | simpl].
    apply ParCtxtEquiv1; auto with PiC.
    transitivity (ContextCompose (ParCtxt1 Hole P) l); [apply ContextComposeSwapEquiv | simpl]; auto with PiC.
  Qed.
  Hint Resolve TwoHoleTransfer : PiC.
    
  Theorem FromPermutedLists : forall l1 l2 l3 l4,
      Permutation (l1 ++ l2)
                  (l3 ++ l4)
      -> PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4).
  Proof.
    intros l1 l2 l3 l4 H.
    remember (l1 ++ l2) as l. remember (l3 ++ l4) as l'.
    revert l1 l2 l3 l4 Heql Heql'. induction H; intros l1 l2 l3 l4 Heql Heql'.
    - symmetry in Heql; symmetry in Heql'. apply app_eq_nil in Heql.
      apply app_eq_nil in Heql'. destruct Heql; destruct Heql'; subst; simpl.
      unfold ContextFromLists; simpl. reflexivity.
    - destruct l1; destruct l3; simpl in *.
      -- unfold ContextFromLists; simpl; subst. simpl.
         repeat rewrite LeftContextAppCompose; simpl.
         transitivity (ContextCompose (ParCtxt1 Hole x) (LeftContextFromList (rev l))).
         apply ContextComposeSwapEquiv.
         transitivity (ContextCompose (ParCtxt1 Hole x) (LeftContextFromList (rev l')));
           [|apply ContextComposeSwapEquiv].
         simpl.
         apply ParCtxtEquiv1; auto with PiC. apply LeftContextPermLists; auto.
         transitivity l. symmetry; apply Permutation_rev. transitivity l'; auto.
         apply Permutation_rev.
      -- simpl in *; subst. inversion Heql'; subst.
         unfold ContextFromLists; simpl.
         rewrite LeftContextAppCompose. simpl.
         transitivity (ContextCompose (ParCtxt1 Hole p) (LeftContextFromList (rev l)));
           [apply ContextComposeSwapEquiv|simpl].
         transitivity (ParCtxt2 p (LeftContextFromList (rev l))).
         apply ParCtxtSwitch1; reflexivity.
         apply ParCtxtEquiv2; auto with PiC.
         specialize (IHPermutation [] l l3 l4 eq_refl eq_refl);
           unfold ContextFromLists in IHPermutation; simpl in *; auto.
      -- simpl in *; subst. unfold ContextFromLists in *; simpl in *.
         inversion Heql; subst.
         rewrite LeftContextAppCompose; simpl.
         transitivity (ContextCompose (ParCtxt1 Hole p) (LeftContextFromList (rev l')));
           [simpl|apply ContextComposeSwapEquiv].
         transitivity (ParCtxt2 p (LeftContextFromList (rev l'))); auto with PiC.
         apply ParCtxtEquiv2; auto with PiC.
         apply (IHPermutation l1 l2 [] l' eq_refl eq_refl).
      -- inversion Heql; inversion Heql'; subst.
         unfold ContextFromLists in *; simpl in *.
         apply ParCtxtEquiv2; auto with PiC.
    - destruct l1 as [| P l1]; [| destruct l1].
      all: destruct l3 as [| Q l3]; [|destruct l3].
      all: unfold ContextFromLists in *; simpl in *; subst; simpl.
      -- repeat rewrite LeftContextAppCompose; simpl.
         transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) x) y);
           auto with PiC.
         transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par x y)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) y) x);
           [| symmetry]; auto with PiC.
         transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par y x)); auto with PiC.
      -- inversion Heql'; subst; simpl.
         repeat rewrite LeftContextAppCompose; simpl.
         transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) Q)  y);
           auto with PiC.
         transitivity (ParCtxt2 Q (ContextCompose (ParCtxt1 Hole y) (LeftContextFromList (rev l)))); [simpl | apply ParCtxtEquiv2; auto with PiC; apply ContextComposeSwapEquiv].
         transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par Q y)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) y) Q); auto with PiC.
         transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par y Q)); auto with PiC.
      -- inversion Heql'; subst.
         rewrite rev_app_distr.
         repeat rewrite LeftContextAppCompose; simpl.
         etransitivity; [eapply TwoHoleTransfer; auto with PiC|].
         etransitivity; [eapply ParCtxtComm12; reflexivity|].
         etransitivity; [|eapply ParCtxtComm21; reflexivity].
         etransitivity; [|eapply ParCtxtSwitch1; reflexivity].
         apply ParCtxtEquiv1; auto with PiC. apply ComposeEquivBackwards; auto with PiC.
         symmetry. transitivity (LeftContextFromList l3). apply RightEquivLeft.
         apply LeftContetFromRevList.
      -- inversion Heql; subst. simpl.
         repeat rewrite LeftContextAppCompose; simpl.
         etransitivity;
           [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv| reflexivity]|simpl].
         etransitivity; [| eapply ContextComposeSwapEquiv]; simpl.
         etransitivity;
           [| eapply ParCtxtEquiv1; [reflexivity| apply ContextComposeSwapEquiv]].
         etransitivity; [eapply ParCtxtSwitch2; reflexivity |].
         etransitivity; [eapply ParCtxtComm12; reflexivity |].
         etransitivity; [| eapply ParCtxtComm11; reflexivity].
         apply ParCtxtEquiv1; auto with PiC; reflexivity.
      -- inversion Heql; inversion Heql'; subst; simpl.
         repeat rewrite LeftContextAppCompose; simpl.
         etransitivity;
           [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity] |]; simpl.
         etransitivity;
           [| eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]]; simpl.
         etransitivity; [eapply ParCtxtSwitch2; reflexivity|].
         etransitivity; [eapply ParCtxtComm12; reflexivity |].
         etransitivity; [|eapply ParCtxtSwitch1; reflexivity].
         etransitivity; [|eapply ParCtxtComm11; reflexivity].
         apply ParCtxtEquiv1; auto with PiC; reflexivity.
      -- inversion Heql; inversion Heql'; subst; simpl.
         rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl.
         etransitivity;
           [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]|]; simpl.
         etransitivity;
           [eapply ParCtxtEquiv2; [| reflexivity]; eapply ParCtxtSwitch1; reflexivity |].
         etransitivity; [eapply ParCtxtComm22; reflexivity |].
         etransitivity; [|eapply ParCtxtComm21; reflexivity].
         apply ParCtxtEquiv2; auto with PiC.
         apply ComposeEquivBackwards; auto with PiC.
         symmetry; etransitivity; [apply RightEquivLeft|]; apply LeftContetFromRevList.
      -- inversion Heql; subst.
         rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl.
         etransitivity; [| symmetry; eapply TwoHoleTransfer].
         etransitivity; [eapply ParCtxtSwitch2; reflexivity|].
         etransitivity;
           [eapply ParCtxtEquiv1; [ reflexivity|]; eapply ParCtxtSwitch2; reflexivity |].
         etransitivity; [eapply ParCtxtComm12; reflexivity |].
         etransitivity; [| eapply ParCtxtComm11; reflexivity].
         apply ParCtxtEquiv1; auto with PiC.
         apply ComposeEquivBackwards; auto with PiC.
         etransitivity; [apply RightEquivLeft| apply LeftContetFromRevList].
      -- inversion Heql; inversion Heql'; subst; simpl.
         rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl.
         etransitivity;
           [| eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]]; simpl.
         etransitivity;
           [| eapply ParCtxtEquiv2; [|reflexivity]; eapply ParCtxtSwitch2; reflexivity].
         etransitivity; [eapply ParCtxtComm22; reflexivity|].
         etransitivity; [|eapply ParCtxtComm21; reflexivity].
         apply ParCtxtEquiv2; auto with PiC.
         apply ComposeEquivBackwards; auto with PiC.
         etransitivity; [apply RightEquivLeft | apply LeftContetFromRevList].
      -- inversion Heql; inversion Heql'; subst; simpl.
         etransitivity; [eapply ParCtxtComm22; reflexivity|].
         etransitivity; [|eapply ParCtxtComm21; reflexivity].
         apply ParCtxtEquiv2; auto with PiC.
         fold (ContextFromLists l1 l2). fold (ContextFromLists l3 l4).
         apply FromNearlyEqualLists; auto.
    - specialize (IHPermutation1 l1 l2 [] l' Heql eq_refl).
      specialize (IHPermutation2 [] l' l3 l4 eq_refl Heql').
      transitivity (ContextFromLists [] l'); auto.
  Qed.
  
  (* Definition NormalizeContext (CC : PiCalcRedContext)  : PiCalcRedContext :=  *)
  (*   RightContextFromList (fst (ContextToLists CC) ++ snd (ContextToLists CC)). *)
  
  (* Lemma NormalizeEquiv : forall CC, *)
  (*     PiRedEquiv CC (NormalizeContext CC). *)
  (* Proof. *)
  (*   unfold NormalizeContext; intro CC; induction CC; simpl. *)
  (*   - reflexivity. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite AppComm. rewrite RightContextAppCompose. *)
  (*     transitivity (ContextCompose CC (ParCtxt2 p Hole)). *)
  (*     2: { apply ContextComposeEquiv; auto. symmetry; apply RightContextFromProcessList. } *)
  (*     clear l l0 IHCC. induction CC; simpl; try reflexivity. *)
  (*     -- apply ParCtxtSwitch1; auto with PiC. *)
  (*     -- transitivity (ParCtxt1 (ParCtxt1 CC p) p0). *)
  (*        transitivity (ParCtxt1 CC (Par p0 p)). apply ParCtxtComm12; reflexivity. *)
  (*        transitivity (ParCtxt1 CC (Par p p0)). *)
  (*        apply ParCtxtEquiv1; auto with PiC; reflexivity. *)
  (*        apply ParCtxtComm11; reflexivity. *)
  (*        apply ParCtxtEquiv1; auto with PiC. *)
  (*     -- transitivity (ParCtxt2 p0 (ParCtxt1 CC p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC p0) p); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC (Par p p0)); auto with PiC. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite RightContextAppCompose. rewrite RightContextAppCompose. *)
  (*     rewrite <- ContextComposeComm. *)
  (*     rewrite <- RightContextAppCompose. *)
  (*     transitivity (ContextCompose (ParCtxt2 p Hole) CC); [reflexivity|]. *)
  (*     apply ContextComposeEquiv; auto. symmetry. apply RightContextFromProcessList. *)
  (* Qed. *)
  
  Lemma PermutationMiddle : forall {A : Type} (l1 l2 l3 : list A) (a : A),
      Permutation (l1 ++ a :: l2) l3
      -> exists l4 l5,
        l3 = l4 ++ a :: l5.
  Proof.
    intros A l1 l2 l3 a H.
    remember (l1 ++ a :: l2). revert l1 l2 a Heql. induction H; intros l1 l2 a Heql.
    - symmetry in Heql; apply app_eq_nil in Heql; destruct Heql.
      inversion H0.
    - destruct l1; simpl in *; inversion Heql; subst.
      exists []; exists l'; simpl; reflexivity.
      destruct (IHPermutation l1 l2 a eq_refl) as [l3 H'];
        destruct H' as [l4 H']; subst.
      exists (a0 :: l3); exists l4; simpl; auto.
    - destruct l1; simpl in *; inversion Heql; subst.
      exists [x]; exists l; auto.
      destruct l1; simpl in *; inversion H1; subst.
      exists []; exists (a0 :: l2); auto.
      exists (a1 :: a0 :: l1); exists l2; auto.
    - specialize (IHPermutation1 l1 l2 a Heql).
      destruct IHPermutation1 as [l3 H']; destruct H' as [l4 eq'].
      apply (IHPermutation2 l3 l4); auto.
  Qed.

  Theorem ListPiMiddle : forall l1 l2 l3 P,
      ListPiEquiv (l1 ++ P :: l2) l3 ->
      exists l4 l5 Q,
        P ≡π Q /\ l4 ++ Q :: l5 = l3 /\ ListPiEquiv (l1 ++ l2) (l4 ++ l5).
  Proof.
    intro l1; induction l1; intros l2 l3 P equiv.
    - simpl in equiv. inversion equiv; subst.
      exists []; exists l'; exists Q; split; [|split]; auto.
    - simpl in equiv. inversion equiv; subst.
      apply IHl1 in H3. destruct H3 as [l4 H3]; destruct H3 as [l5 H3];
                          destruct H3 as [Q' H3]; destruct H3 as [equivPQ H3];
                            destruct H3 as [eq lequiv].
      exists (Q :: l4); exists l5; exists Q'; split; [| split]; subst; auto.
      simpl. constructor; auto.
  Qed.

  Lemma ContextToListsCompose : forall CC1 CC2,
      ContextToLists (ContextCompose CC1 CC2) =
      (fst (ContextToLists CC1) ++ fst (ContextToLists CC2), snd (ContextToLists CC2) ++ snd(ContextToLists CC1)).
  Proof.
    intro CC1; induction CC1; simpl.
    - intro. rewrite app_nil_r;  apply surjective_pairing.
    - intros CC2.
      rewrite IHCC1; simpl.
      destruct (ContextToLists CC1); simpl. rewrite AppComm; reflexivity.
    - intro CC2. rewrite IHCC1; simpl.
      destruct (ContextToLists CC1); simpl. rewrite AppComm. reflexivity.
  Qed.
      
  Lemma ContextToListFromLists : forall l1 l2,
      ContextToLists (ContextFromLists l1 l2) = (flat_map ProcessToList l1, flat_map ProcessToList l2).
  Proof.
    intros l1 l2. unfold ContextFromLists.
    revert l2; induction l1; simpl; intros l2.
    - induction l2; simpl; auto.
      rewrite LeftContextAppCompose; simpl.
      rewrite ContextToListsCompose; rewrite IHl2; simpl.
      reflexivity.
    - rewrite IHl1. reflexivity.
  Qed.
  Lemma ContextToListFromSingleThreadLists : forall l1 l2,
      (forall P, In P l1 -> SingleThread P) ->
      (forall P, In P l2 -> SingleThread P) -> 
      ContextToLists (ContextFromLists l1 l2) = (l1, l2).
  Proof.
    unfold ContextFromLists; intros l1; induction l1; simpl; intros l2 singles1 singles2.
    - induction l2; simpl; auto.
      rewrite LeftContextAppCompose; simpl.
      rewrite ContextToListsCompose. rewrite IHl2. simpl.
      rewrite SingleThreadToList; simpl; auto.
      apply singles2; left; auto.
      intros P H. apply singles2; right; auto.
    - rewrite IHl1; auto. rewrite SingleThreadToList; auto.
  Qed.

  Lemma ProcessToListAllSingle : forall P Q,
      In Q (ProcessToList P) -> SingleThread Q.
  Proof.
    intro P; induction P; intros Q i; simpl in *; auto with PiC.
    all: try (destruct i as [eq | f]; [| destruct f]; subst; constructor; fail).
    apply in_app_or in i; destruct i; [apply IHP1 | apply IHP2]; auto.
  Qed.

  Lemma ProcessToListInj : forall P Q, ProcessToList P = ProcessToList Q -> P = Q.
  Proof.
    intro P; induction P; intro Q; destruct Q; simpl; auto; intro H.
    all: try (inversion H; fail).
    all: try (symmetry in H; apply app_eq_unit in H;
              destruct H as [H | H]; destruct H as [H1 H2];
              [apply ProcessToListNonNil in H1; destruct H1
              | apply ProcessToListNonNil in H2; destruct H2]; fail).
    all: try (inversion H; subst; auto; fail).
    all: try (apply app_eq_unit in H;
              destruct H as [H | H]; destruct H as [H1 H2];
              [apply ProcessToListNonNil in H1; destruct H1
              | apply ProcessToListNonNil in H2; destruct H2]; fail).
  Abort.

  Lemma CCEquivInversion' : forall CC1 P Q,
      (ApplyRedContext CC1 P) ≡π' Q
      -> SingleThread P
      -> exists CC2 Q', PiRedEquiv CC1 CC2 /\ P ≡π' Q' /\ ApplyRedContext CC2 Q' = Q.
  Proof.
    intro CC1; induction CC1; intros P Q H H0.
    - simpl in H. exists Hole; exists Q; split; [| split]; auto with PiC.
    - simpl in H. inversion H; subst; try (apply IHCC1 in H3; auto).
      all: try (destruct H3 as [CC2 H3]; destruct H3 as [Q' H3];
                destruct H3 as [Cequiv H3]; destruct H3 as [equiv' app]).
      -- exists (ParCtxt1 CC2 Q2); exists Q'; split; [|split]; auto.
         apply ParCtxtEquiv1; auto with PiC. simpl. rewrite app. reflexivity.
      -- exists (ParCtxt2 Q2 CC2); exists Q'; split; [|split]; auto.
         transitivity (ParCtxt1 CC2 Q2); auto with PiC.
         simpl. rewrite app. reflexivity.
      -- exists (ParCtxt1 (ParCtxt1 CC2 Q2) R2); exists Q'; split; [|split]; auto.
         transitivity (ParCtxt1 CC2 (Par Q2 R2)); auto with PiC.
         simpl. rewrite app. reflexivity.
      -- assert (ApplyRedContext CC1 P ≡π' Par P2 Q2) as H5 by (rewrite <- H1; auto with PiC).
         apply IHCC1 in H5; auto.
         destruct H5 as [CC2 H5]; destruct H5 as [Q' H5];
           destruct H5 as [Cequiv H5]; destruct H5 as [equiv' app].
         destruct CC2; simpl in app; subst;
           [apply SingleThreadEquiv' in equiv'; auto; inversion equiv'| |].
         all: inversion app; subst; clear app.         
         exists (ParCtxt1 CC2 (Par Q2 R2)); exists Q'; split; [|split]; auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC2 Q2) R2); auto with PiC.
         exists (ParCtxt2 P2 (ParCtxt1 CC2 R2)); exists Q'; split; [|split]; auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC2 R2) P2); auto with PiC.
         transitivity (ParCtxt1 CC2 (Par R2 P2)); auto with PiC.
         transitivity (ParCtxt1 CC2 (Par P2 R2)); auto with PiC.
         transitivity (ParCtxt1 (ParCtxt1 CC2 P2) R2); auto with PiC.
         apply ParCtxtEquiv1; auto with PiC.
         transitivity (ParCtxt2 P2 CC2); auto with PiC.
    - simpl in H. inversion H; subst; try (apply IHCC1 in H5; auto).
      all: try (destruct H5 as [CC2 H5]; destruct H5 as [Q' H5];
                destruct H5 as [Cequiv H5]; destruct H5 as [equiv' app]).
      -- exists (ParCtxt2 P2 CC2); exists Q'; split; [| split]; auto with PiC.
         simpl. rewrite app. auto.
      -- exists (ParCtxt1 CC2 P2); exists Q'; split; [| split]; auto with PiC.
         simpl; rewrite app; reflexivity.
      -- assert (ApplyRedContext CC1 P ≡π' Par Q2 R2) as H1
            by (rewrite <- H2; auto with PiC).
         apply IHCC1 in H1; auto.
         destruct H1 as [CC2 H1]; destruct H1 as [Q' H1];
           destruct H1 as [Cequiv H1]; destruct H1 as [equiv' app].
         destruct CC2; simpl in app; subst;
           [apply SingleThreadEquiv' in equiv'; auto; inversion equiv'| |].
         all: inversion app; subst; clear app.
         exists (ParCtxt1 (ParCtxt2 P2 CC2) R2); exists Q'; split; [|split]; auto with PiC.
         transitivity (ParCtxt2 R2 (ParCtxt2 P2 CC2)); auto with PiC.
         transitivity (ParCtxt2 (Par R2 P2) CC2); auto with PiC.
         transitivity (ParCtxt2 (Par P2 R2) CC2); auto with PiC.
         transitivity (ParCtxt2 P2 (ParCtxt2 R2 CC2)); auto with PiC.
         apply ParCtxtEquiv2; auto with PiC.
         transitivity (ParCtxt1 CC2 R2); auto with PiC.
         exists (ParCtxt2 (Par P2 Q2) CC2); exists Q'; split; [| split]; auto with PiC.
         transitivity (ParCtxt2 P2 (ParCtxt2 Q2 CC2)); auto with PiC.
      -- apply IHCC1 in H6; auto.
         destruct H6 as [CC2 H6]; destruct H6 as [Q' H6];
           destruct H6 as [Cequiv H6]; destruct H6 as [equiv' app].
         exists (ParCtxt2 P2 (ParCtxt2 Q2 CC2)); exists Q'; split; [| split]; auto with PiC.
         simpl. rewrite app. reflexivity.
  Qed.

  Lemma CCEquivInversion : forall CC1 P Q,
      (ApplyRedContext CC1 P) ≡π Q
      -> SingleThread P
      -> exists CC2 Q', PiRedEquiv CC1 CC2 /\ P ≡π Q' /\ ApplyRedContext CC2 Q' = Q.
  Proof.
    intros CC1 P Q equiv.
    remember (ApplyRedContext CC1 P) as R.
    revert CC1 P HeqR. induction equiv.
    - intros CC1 P0 HeqR ST; subst.
      apply CCEquivInversion' in H; auto.
      destruct H as [CC2 H]; destruct H as [Q' H]; destruct H as [Cequiv H];
        destruct H as [equiv eq].
      exists CC2; exists Q'; split; [|split]; auto with PiC.
    - intros CC1 S HeqR ST; subst.
      apply CCEquivInversion' in H; auto.
      destruct H as [CC2 H]; destruct H as [Q' H]; destruct H as [Cequiv H];
        destruct H as [equiv' eq]; subst.
      specialize (IHequiv CC2 Q' eq_refl (SingleThreadEquiv' _ _ ST equiv')).
      destruct IHequiv as [CC3 H]; destruct H as [R' H]; destruct H as [Cequiv2 H];
        destruct H as [equiv'' eq]; subst.
      exists CC3; exists R'; split; [| split]; auto with PiC.
      transitivity CC2; auto.
      apply @PiEquivStep with (Q := Q'); auto.
  Qed.

  Theorem Equiv'ESubstStable : forall P Q σ, P ≡π' Q -> (P [πe| σ]) ≡π' (Q [πe| σ]).
  Proof.
    intros P Q σ equiv; revert σ; induction equiv; intros σ; simpl;
      auto with PiC.
  Qed.

  Theorem EquivESubstStable : forall P Q σ, P ≡π Q -> (P [πe| σ]) ≡π (Q [πe| σ]).
  Proof.
    intros P Q σ equiv; revert σ; induction equiv; intros σ; simpl;
      eapply Equiv'ESubstStable in H; eauto with PiC.
  Qed.

  Lemma Equiv'RenameStable : forall (P Q : Proc) (ξ : nat -> nat),
      P ≡π' Q -> (P ⟨π| ξ⟩) ≡π' (Q ⟨π| ξ⟩).
  Proof.
    intros P Q ξ equiv; revert ξ; induction equiv; intro ξ; simpl; auto with PiC.
  Qed.

  Lemma EquivRenameStable : forall (P Q : Proc) (ξ : nat -> nat),
      P ≡π Q -> (P ⟨π| ξ⟩) ≡π (Q ⟨π| ξ⟩).
  Proof.
    intros P Q ξ equiv; revert ξ; induction equiv; intro ξ; simpl; auto with PiC.
    apply Equiv'RenameStable with (ξ := ξ) in H; auto with PiC.
    transitivity (Q ⟨π|ξ⟩); auto. apply Equiv'RenameStable with (ξ := ξ) in H; auto with PiC.
  Qed.    

  Lemma ProcSubstUpEquivExt : forall (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n ≡π σ2 n) ->
      forall n, ProcSubstUp σ1 n ≡π ProcSubstUp σ2 n.
  Proof.
    intros σ1 σ2 H n.
    unfold ProcSubstUp. destruct n; auto with PiC.
    apply EquivRenameStable; auto.
  Qed.

  Theorem Equiv'SubstStable : forall P Q σ1 σ2,
      P ≡π' Q ->
      (forall n, σ1 n ≡π σ2 n) ->
      (P [π| σ1]) ≡π (Q [π| σ2]).
  Proof.
    intros P Q σ1 σ2 equiv; revert σ1 σ2; induction equiv; intros σ1 σ2 ext_equiv; simpl;
      auto with PiC.
    apply DefProcContext; [apply IHequiv1 | apply IHequiv2]; apply ProcSubstUpEquivExt; auto.
  Qed.

  Theorem EquivSubstStable : forall P Q σ1 σ2,
      P ≡π Q ->
      (forall n, σ1 n ≡π σ2 n) ->
      (P [π| σ1]) ≡π (Q [π| σ2]).
  Proof.
    intros P Q σ1 σ2 equiv; revert σ1 σ2; induction equiv; intros σ1 σ2 ext_equiv;
      simpl; eapply Equiv'SubstStable in H; eauto with PiC.
    transitivity (Q [π|σ2]); auto with PiC.
  Qed.

  Lemma EndEquivInv : forall P, EndProc ≡π P -> P = EndProc.
  Proof.
    intros P equiv; remember EndProc as Q; revert HeqQ; induction equiv; intros HeqQ;
      subst.
    - inversion H; auto.
    - inversion H; subst. apply IHequiv; reflexivity.
  Qed.

  Lemma VarEquivInv : forall n P, VarProc n ≡π P -> P = VarProc n.
  Proof.
    intros n P equiv; remember (VarProc n) as Q; revert n HeqQ; induction equiv;
      intros n HeqQ; subst.
    - inversion H; subst; reflexivity.
    - inversion H; subst. apply (IHequiv n); reflexivity.
  Qed.
  
  Lemma SendEquivInv : forall p e P Q, SendProc p e P ≡π Q -> exists Q', P ≡π Q' /\ Q = SendProc p e Q'.
  Proof.
    intros p e P Q equiv.
    remember (SendProc p e P) as R.
    revert p e P HeqR; induction equiv; intros p e P0 HeqR; subst.
    - inversion H; subst. exists P2; split; auto with PiC.
    - inversion H; subst. destruct (IHequiv p e P2 eq_refl) as [Q' HQ'];
                            destruct HQ' as [equiv' Req]; subst.
      exists Q'; split; auto. apply @PiEquivStep with (Q := P2); auto with PiC.
  Qed.

  Lemma RecvEquivInv : forall p P Q, RecvProc p P ≡π Q -> exists Q', P ≡π Q' /\ Q = RecvProc p Q'.
  Proof.
    intros p P Q equiv.
    remember (RecvProc p P) as R; revert p P HeqR; induction equiv; intros p P0 HeqR; subst.
    - inversion H; subst. exists P2; split; auto with PiC.
    - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [Q' HQ']; destruct HQ'; subst.
      exists Q'; split; eauto with PiC.
  Qed.

  Lemma IfThenElseEquivInv : forall e P Q R, IfThenElse e P Q ≡π R ->
                                        exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = IfThenElse e P' Q'.
  Proof.
    intros e P Q R equiv.
    remember (IfThenElse e P Q) as S; revert e P Q HeqS; induction equiv;
      intros e P0 Q0 HeqS; subst.
    - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC.
    - inversion H; subst; destruct (IHequiv e P2 Q2 eq_refl) as [P' IH];
        destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq];
          subst.
      exists P'; exists Q'; split; [| split]; eauto with PiC.
  Qed.

  Lemma DefEquivInv : forall P Q R,
      DefProc P Q ≡π R ->
      exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = DefProc P' Q'.
  Proof.
    intros P Q R equiv; remember (DefProc P Q) as S; revert P Q HeqS;
      induction equiv; intros P0 Q0 HeqS; subst.
    - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC.
    - inversion H; subst; destruct (IHequiv P2 Q2 eq_refl) as [P' IH];
        destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq];
          subst.
      exists P'; exists Q'; split; [| split]; eauto with PiC.
  Qed.

  Lemma EChoiceLEquivInv : forall p P Q,
      EChoiceL p P ≡π Q ->
      exists P', P ≡π P' /\ Q = EChoiceL p P'.
  Proof.
    intros p P Q equiv; remember (EChoiceL p P) as R; revert p P HeqR;
      induction equiv; intros p P0 HeqR; subst.
    - inversion H; subst. exists P2; split; auto with PiC.
    - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [P' IH]; destruct IH; subst.
      exists P'; split; eauto with PiC.
  Qed.

  Lemma EChoiceREquivInv : forall p P Q,
      EChoiceR p P ≡π Q ->
      exists P', P ≡π P' /\ Q = EChoiceR p P'.
  Proof.
    intros p P Q equiv; remember (EChoiceR p P) as R; revert p P HeqR;
      induction equiv; intros p P0 HeqR; subst.
    - inversion H; subst. exists P2; split; auto with PiC.
    - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [P' IH]; destruct IH; subst.
      exists P'; split; eauto with PiC.
  Qed.

  Lemma IChoiceEquivInv : forall p P Q R,
      IChoice p P Q ≡π R ->
      exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = IChoice p P' Q'.
  Proof.
    intros p P Q R equiv; remember (IChoice p P Q) as S; revert p P Q HeqS;
      induction equiv; intros p P0 Q0 HeqS; subst.
    - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC.
    - inversion H; subst; destruct (IHequiv p P2 Q2 eq_refl) as [P' IH];
        destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq];
          subst.
      exists P'; exists Q'; split; [| split]; eauto with PiC.
  Qed.

  (* Lemma SubstEquivInv : forall P σ Q, *)
  (*     P [π| σ] ≡π Q -> *)
  (*     exists P' σ', P ≡π P' /\ (forall n, σ n ≡π σ' n) /\ Q = P' [π|σ']. *)
  (* Proof. *)
  (*   intros P; induction P; intros σ Q equiv; simpl in *. *)
  (*   - exists EndProc; exists σ; split; [|split]; simpl; auto with PiC. *)
  (*     apply EndEquivInv; auto. *)
  (*   - exists (VarProc n); exists (fun m => if Nat.eq_dec n m *)
  (*                             then Q *)
  (*                             else σ m); split; [|split]; simpl; auto with PiC. *)
  (*     intro m; destruct (Nat.eq_dec n m); subst; auto with PiC. *)
  (*     destruct (Nat.eq_dec n n) as [_|neq]; [reflexivity|exfalso; apply neq; auto]. *)
  (*   -  *)
  
  Theorem PiCalcEquivStep : forall Π1 Π2 Π1' : Role -> Proc,
      (forall p : Role, Π1 p ≡π Π1' p) ->
      PiCalcStep Π1 Π2 ->
      exists Π2', (forall p : Role, Π2 p ≡π Π2' p) /\ PiCalcStep Π1' Π2'.
  Proof.
    intros Π1 Π2 Π1' ext_equiv step; revert Π1' ext_equiv; induction step;
      intros Π1' ext_equiv.
    - remember (ext_equiv p) as equivp; clear Heqequivp.
      rewrite H0 in equivp.
      apply CCEquivInversion in equivp; [| simpl; auto].
      destruct equivp as [CC2 Hc]; destruct Hc as [Q' Hc];
        destruct Hc as [Cequiv Hc]; destruct Hc as [equiv eq]; subst.
      destruct (SendEquivInv _ _ _ _ equiv) as [Q'' HQ''];
           destruct HQ'' as [equiv'' eqQ'']; subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 (SendProc q e' Q'')
               else Π1' r); split.
      -- intro r; destruct (RoleEqDec p r); subst.
         rewrite H2. apply CCEquiv; auto with PiC.
         transitivity (Π r). rewrite H1; auto with PiC.
         apply ext_equiv.
      -- apply CommEStep with (p := p) (q := q) (e := e) (e' := e') (P := Q'') (CC := CC2);
           auto.
         intros r H3; destruct (RoleEqDec p r); subst;
           [exfalso; apply H3; auto | reflexivity].
         destruct (RoleEqDec p p); subst; auto. exfalso; apply n; auto.
    - pose proof (ext_equiv p) as equivp.
      rewrite H1 in equivp.
      apply CCEquivInversion in equivp; [| simpl; auto].
      destruct equivp as [CC2 equivp]; destruct equivp as [Q' equivp];
        destruct equivp as [Cequiv equivp]; destruct equivp as [equivP eqp].
      pose proof (ext_equiv q) as equivq.
      rewrite H2 in equivq.
      apply CCEquivInversion in equivq; [| simpl; auto].
      destruct equivq as [CC3 equivq]; destruct equivq as [Q'' equivq];
        destruct equivq as [Cequiv' equivq]; destruct equivq as [equivQ eqq].
      destruct (SendEquivInv _ _ _ _ equivP) as [Q''' HQ'''];
        destruct HQ''' as [equiv''' eqQ''']; subst.
      destruct (RecvEquivInv _ _ _ equivQ) as [Q'''' HQ''''];
        destruct HQ'''' as [equiv'''' eqQ'''']; subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 Q'''
               else if RoleEqDec q r
                    then ApplyRedContext CC3 (Q'''' [πe|CommSubst v])
                    else Π1' r); split.
      -- intros p0. destruct (RoleEqDec p p0); subst.
         rewrite H4. apply CCEquiv; auto with PiC.
         destruct (RoleEqDec q p0); subst.
         rewrite H5. apply CCEquiv; auto with PiC.
         apply EquivESubstStable; auto.
         transitivity (Π p0); auto. rewrite H3; auto. reflexivity.
      -- apply CommVStep with (v := v) (p := p)(q := q) (P := Q''') (Q := Q'''') (CC := CC2) (CC' := CC3); auto with PiC.
         intros r H6 H7. destruct (RoleEqDec p r); subst; [exfalso; apply H6; auto|].
         destruct (RoleEqDec q r); subst; [exfalso; apply H7; auto|].
         reflexivity.
         destruct (RoleEqDec p p) as [_|n]; [reflexivity|exfalso; apply n; auto].
         destruct (RoleEqDec p q) as [eqpq|_]; subst; [exfalso; apply H; auto|].
         destruct (RoleEqDec q q) as [_|n];[reflexivity|exfalso; apply n; auto].
    - pose proof (ext_equiv p) as equivp. rewrite H0 in equivp.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 H']; destruct H' as [Q' H'];
        destruct H' as [Cequiv H']; destruct H' as [equiv' eq'].
      destruct (IfThenElseEquivInv _ _ _ _ equiv') as [P' H'];
        destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq];
          subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 (IfThenElse e' P' R')
               else Π1' r); split.
      -- intro r; destruct (RoleEqDec p r); subst.
         rewrite H2. apply CCEquiv; auto with PiC.
         rewrite <- H1; auto.
      -- apply IfEStep with (p := p) (e := e) (e' := e') (P := P') (Q := R') (CC := CC2);
           auto with PiC.
         intros r H3.
         destruct (RoleEqDec p r) as [eq|_]; [exfalso; apply H3; auto|reflexivity].
         destruct (RoleEqDec p p) as [_|n]; [reflexivity|exfalso;apply n; auto].
    - pose proof (ext_equiv p) as equivp. rewrite H in equivp.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv];
        destruct eqv as [Cequiv eqv]; destruct eqv as [IfEquiv eq].
      destruct (IfThenElseEquivInv _ _ _ _ IfEquiv) as [P' H'];
        destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq'];
          subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 P'
               else Π1' r); split.
      -- intro r; destruct (RoleEqDec p r); subst.
         rewrite H1. apply CCEquiv; auto with PiC.
         rewrite <- H0; auto with PiC.
      -- apply IfTrueStep with (p := p) (P := P') (Q := R') (CC := CC2).
         rewrite <- eq. reflexivity.
         intros r n. destruct (RoleEqDec p r) as [eqrp|_];
                       [exfalso; apply n; auto| reflexivity].
         destruct (RoleEqDec p p) as [_|n]; [reflexivity|exfalso; apply n; auto].
    - pose proof (ext_equiv p) as equivp. rewrite H in equivp.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv];
        destruct eqv as [Cequiv eqv]; destruct eqv as [IfEquiv eq].
      destruct (IfThenElseEquivInv _ _ _ _ IfEquiv) as [P' H'];
        destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq'];
          subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 R'
               else Π1' r); split.
      -- intro r; destruct (RoleEqDec p r); subst.
         rewrite H1. apply CCEquiv; auto with PiC.
         rewrite <- H0; auto with PiC.
      -- apply IfFalseStep with (p := p) (P := P') (Q := R') (CC := CC2).
         rewrite <- eq. reflexivity.
         intros r n. destruct (RoleEqDec p r) as [eqrp|_];
                       [exfalso; apply n; auto| reflexivity].
         destruct (RoleEqDec p p) as [_|n]; [reflexivity|exfalso; apply n; auto].
    - pose proof (ext_equiv p) as equivp. rewrite H in equivp.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv];
        destruct eqv as [Cequiv eqv]; destruct eqv as [DefEquiv eq].
      destruct (DefEquivInv _ _ _ DefEquiv) as [P' H'];
        destruct H' as [R' H']; destruct H' as [equivP H'];
          destruct H' as [equivR H']; subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 (R' [π|PiDefSubst P'])
               else Π1' r); split.
      -- intro r. destruct (RoleEqDec p r); subst.
         rewrite H1. apply CCEquiv; auto with PiC. apply EquivSubstStable; auto.
         unfold PiDefSubst. intro n; destruct n; auto with PiC.
         apply EquivSubstStable; auto.
         destruct n; auto with PiC.
         rewrite <- H0; auto with PiC.
      -- apply DefStep with (p := p) (P := P') (Q := R') (CC := CC2); auto with PiC.
         intros r n; destruct (RoleEqDec p r) as [ e|_];
           [exfalso; apply n; auto|reflexivity].
         destruct (RoleEqDec p p) as [_|n]; [reflexivity|exfalso; apply n; auto].
    - pose proof (ext_equiv p) as equivp; rewrite H0 in equivp.
      pose proof (ext_equiv q) as equivq; rewrite H1 in equivq.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 ep]; destruct ep as [ECQ' ep];
        destruct ep as [Cequiv ep]; destruct ep as [ECequiv eqp]; subst.
      apply CCEquivInversion in equivq; simpl; auto.
      destruct equivq as [CC3 eq]; destruct eq as [ICQ' eq];
        destruct eq as [Cequiv' eq]; destruct eq as [ICequiv eqq]; subst.
      destruct (EChoiceLEquivInv _ _ _ ECequiv) as [P' H'];
        destruct H' as [equivP eq']; subst.
      destruct (IChoiceEquivInv _ _ _ _ ICequiv) as [Q1' H'];
        destruct H' as [Q2' H']; destruct H' as [equivQ1 H'];
          destruct H' as [equivQ2 eq']; subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 P'
               else if RoleEqDec q r
                    then ApplyRedContext CC3 Q1'
                    else Π1' r); split.
      -- intro r. destruct (RoleEqDec p r); subst.
         rewrite H3. apply CCEquiv; auto with PiC.
         destruct (RoleEqDec q r); subst. rewrite H4. apply CCEquiv; auto with PiC.
         rewrite <- H2; auto.
      -- apply ChooseLStep with (p := p) (q := q) (P := P') (Q1 := Q1') (Q2 := Q2')
                                (CC := CC2) (CC' := CC3); auto.
         intros r H5 H6.
         destruct (RoleEqDec p r) as [ e|_]; [exfalso; apply H5; auto|].
         destruct (RoleEqDec q r) as [ e|_]; [exfalso; apply H6; auto|].
         reflexivity.
         destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
         destruct (RoleEqDec p q) as [ e|_]; [exfalso; apply H; auto|].
         destruct (RoleEqDec q q) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
    - pose proof (ext_equiv p) as equivp; rewrite H0 in equivp.
      pose proof (ext_equiv q) as equivq; rewrite H1 in equivq.
      apply CCEquivInversion in equivp; simpl; auto.
      destruct equivp as [CC2 ep]; destruct ep as [ECQ' ep];
        destruct ep as [Cequiv ep]; destruct ep as [ECequiv eqp]; subst.
      apply CCEquivInversion in equivq; simpl; auto.
      destruct equivq as [CC3 eq]; destruct eq as [ICQ' eq];
        destruct eq as [Cequiv' eq]; destruct eq as [ICequiv eqq]; subst.
      destruct (EChoiceREquivInv _ _ _ ECequiv) as [P' H'];
        destruct H' as [equivP eq']; subst.
      destruct (IChoiceEquivInv _ _ _ _ ICequiv) as [Q1' H'];
        destruct H' as [Q2' H']; destruct H' as [equivQ1 H'];
          destruct H' as [equivQ2 eq']; subst.
      exists (fun r => if RoleEqDec p r
               then ApplyRedContext CC2 P'
               else if RoleEqDec q r
                    then ApplyRedContext CC3 Q2'
                    else Π1' r); split.
      -- intro r. destruct (RoleEqDec p r); subst.
         rewrite H3. apply CCEquiv; auto with PiC.
         destruct (RoleEqDec q r); subst. rewrite H4. apply CCEquiv; auto with PiC.
         rewrite <- H2; auto.
      -- apply ChooseRStep with (p := p) (q := q) (P := P') (Q1 := Q1') (Q2 := Q2')
                                (CC := CC2) (CC' := CC3); auto.
         intros r H5 H6.
         destruct (RoleEqDec p r) as [ e|_]; [exfalso; apply H5; auto|].
         destruct (RoleEqDec q r) as [ e|_]; [exfalso; apply H6; auto|].
         reflexivity.
         destruct (RoleEqDec p p) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
         destruct (RoleEqDec p q) as [ e|_]; [exfalso; apply H; auto|].
         destruct (RoleEqDec q q) as [_|n]; [|exfalso; apply n; auto].
         reflexivity.
  Qed.

End PiCalc.


