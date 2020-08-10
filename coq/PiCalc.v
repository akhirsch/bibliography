Require Export Expression.
Require Export Locations.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.JMeq.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

From Equations Require Import Equations.

Module PiCalc (E : Expression) (L : Locations).
        
  Import E.
  Module LN := (LocationNotations L).
  Import LN.
  Module LF := (LocationFacts L).

  Inductive Proc : Set :=
    EndProc : Proc
  | VarProc : nat -> Proc
  | DefProc : Proc -> Proc -> Proc
  | SendProc : L.t -> Expr -> Proc -> Proc
  | RecvProc : L.t -> Proc -> Proc
  | EChoiceL : L.t -> Proc -> Proc
  | EChoiceR : L.t -> Proc -> Proc
  | IChoice : L.t -> Proc -> Proc -> Proc
  | IfThenElse : Expr -> Proc -> Proc -> Proc.
  (* | Par : Proc -> Proc -> Proc. *)
  Hint Constructors Proc : PiC.

  Definition ProcEqDec : forall P Q : Proc, {P = Q} + {P <> Q}.
    decide equality.
    apply Nat.eq_dec.
    1,7: apply ExprEqDec.
    all: apply L.eq_dec.
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
    (* | Par P Q => Par (P ⟨π| ξ⟩) (Q ⟨π| ξ⟩) *)
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
    (* | Par P Q => Par (P ⟨πe| ξ⟩) (Q ⟨πe| ξ⟩) *)
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
    (* | Par P Q => Par (P [π| σ]) (Q [π| σ]) *)
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
    (* | Par P Q => Par (P [πe| σ]) (Q [πe| σ]) *)
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

  (* Inductive PiCalcRedContext : Set := *)
  (*   Hole : PiCalcRedContext *)
  (* | ParCtxt1 : PiCalcRedContext -> Proc -> PiCalcRedContext *)
  (* | ParCtxt2 : Proc -> PiCalcRedContext -> PiCalcRedContext. *)

  (* Fixpoint ApplyRedContext (CC : PiCalcRedContext) (P : Proc) : Proc := *)
  (*   match CC with *)
  (*   | Hole => P *)
  (*   | ParCtxt1 CC Q => Par (ApplyRedContext CC P) Q *)
  (*   | ParCtxt2 Q CC => Par Q (ApplyRedContext CC P) *)
  (*   end. *)

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

  Inductive PiCalcStep : (L.t -> Proc) -> (L.t -> Proc) -> Prop :=
    CommEStep : forall (p q : L.t) (e e' : Expr) (P : Proc) (Π Π' : L.t -> Proc) (* (CC : PiCalcRedContext) *),
      ExprStep e e'
      -> Π p = (* ApplyRedContext CC *) (SendProc q e P)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) (SendProc q e' P)
      -> PiCalcStep Π Π'
  | CommVStep : forall (p q : L.t) (v : Expr) (P Q : Proc) (Π Π' : L.t -> Proc) (* (CC CC' : PiCalcRedContext) *),
      p <> q
      -> ExprVal v
      -> Π p = (* ApplyRedContext CC *) (SendProc q v P)
      -> Π q = (* ApplyRedContext CC' *) (RecvProc p Q)
      -> (forall r, r <> p -> r <> q -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) P
      -> Π' q = (* ApplyRedContext CC' *) (Q [πe| CommSubst v])
      -> PiCalcStep Π Π'
  | IfEStep : forall (p : L.t) (e e' : Expr) (P Q : Proc) (Π Π' : L.t -> Proc) (* (CC : PiCalcRedContext) *),
      ExprStep e e'
      -> Π p = (* ApplyRedContext CC *) (IfThenElse e P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) (IfThenElse e' P Q)
      -> PiCalcStep Π Π'
  | IfTrueStep : forall (p : L.t) (P Q : Proc) (Π Π' : L.t -> Proc) (* (CC : PiCalcRedContext) *),
      Π p = (* ApplyRedContext CC *) (IfThenElse tt P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC  *)P
      -> PiCalcStep Π Π'
  | IfFalseStep : forall (p : L.t) (P Q : Proc) (Π Π' : L.t -> Proc) (* (CC : PiCalcRedContext) *),
      Π p = (* ApplyRedContext CC *) (IfThenElse ff P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) Q
      -> PiCalcStep Π Π'
  | DefStep : forall (p : L.t) (P Q : Proc) (Π Π' : L.t -> Proc) (* (CC : PiCalcRedContext) *),
      Π p = (* ApplyRedContext CC *) (DefProc P Q)
      -> (forall r, r <> p -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) (Q [π| PiDefSubst P])
      -> PiCalcStep Π Π'
  | ChooseLStep : forall (p q : L.t) (P Q1 Q2 : Proc) (Π Π' : L.t -> Proc) (* (CC CC' : PiCalcRedContext) *),
      p <> q
      -> Π p = (* ApplyRedContext CC *) (EChoiceL q P)
      -> Π q = (* ApplyRedContext CC'  *)(IChoice p Q1 Q2)
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) P
      -> Π' q = (* ApplyRedContext CC' *) Q1
      -> PiCalcStep Π Π'
  | ChooseRStep : forall (p q : L.t) (P Q1 Q2 : Proc) (Π Π' : L.t -> Proc) (* (CC CC' : PiCalcRedContext) *),
      p <> q
      -> Π p = (* ApplyRedContext CC *) (EChoiceR q P)
      -> Π q = (* ApplyRedContext CC' *) (IChoice p Q1 Q2)
      -> (forall r, p <> r -> q <> r -> Π r = Π' r)
      -> Π' p = (* ApplyRedContext CC *) P
      -> Π' q = (* ApplyRedContext CC' *) Q2
      -> PiCalcStep Π Π'.

  Inductive PiManyStep : (L.t -> Proc) -> (L.t -> Proc) -> Prop :=
  | PiZeroStep : forall (Π : L.t -> Proc), PiManyStep Π Π
  | PiExtraStep : forall {Π1 Π2 Π3 : L.t -> Proc},
      PiCalcStep Π1 Π2 -> PiManyStep Π2 Π3 -> PiManyStep Π1 Π3.

  Definition PiOneStep (Π1 Π2 : L.t -> Proc) (step : PiCalcStep Π1 Π2) : PiManyStep Π1 Π2 :=
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

  Inductive DeadlockFree : (L.t -> Proc) -> Prop :=
    mkDF : forall Π : L.t -> Proc,
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

  Inductive Live : (L.t -> Proc) -> Prop :=
    mkLive : forall Π : L.t -> Proc,
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

  (* Reserved Infix "≡π'" (at level 15). *)
  (* Inductive PiEquiv' : Proc -> Proc -> Prop := *)
  (*   EndProcRefl' : EndProc ≡π' EndProc *)
  (* | VarProcRefl' : forall n, VarProc n ≡π' VarProc n *)
  (* | DefProcContext' : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> *)
  (*     (DefProc P1 Q1) ≡π' (DefProc P2 Q2) *)
  (* | SendProcContext' : forall p e {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (SendProc p e P1) ≡π' (SendProc p e P2) *)
  (* | RecvProcContext' : forall p {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (RecvProc p P1) ≡π' (RecvProc p P2) *)
  (* | EChoiceLContext' : forall p {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (EChoiceL p P1) ≡π' (EChoiceL p P2) *)
  (* | EChoiceRContext' : forall p {P1 P2}, *)
  (*     P1 ≡π' P2 -> *)
  (*     (EChoiceR p P1) ≡π' (EChoiceR p P2) *)
  (* | IChoiceContext' : forall p {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> *)
  (*     (IChoice p P1 Q1) ≡π' (IChoice p P2 Q2) *)
  (* | IfThenElseContext' : forall e {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> *)
  (*     (IfThenElse e P1 Q1) ≡π' (IfThenElse e P2 Q2) *)
  (* | ParContext' : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> *)
  (*     (Par P1 Q1) ≡π' (Par P2 Q2) *)
  (* | ParSwap' : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> *)
  (*     (Par P1 Q1) ≡π' (Par Q2 P2) *)
  (* | ParComm1' : forall {P1 P2 Q1 Q2 R1 R2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> R1 ≡π' R2 -> *)
  (*     (Par P1 (Par Q1 R1)) ≡π' (Par (Par P2 Q2) R2) *)
  (* | ParComm2' : forall {P1 P2 Q1 Q2 R1 R2}, *)
  (*     P1 ≡π' P2 -> Q1 ≡π' Q2 -> R1 ≡π' R2 -> *)
  (*     (Par (Par P1 Q1) R1) ≡π' (Par P2 (Par Q2 R2)) *)
  (* (* | ParEnd11' : forall {P1 P2}, *) *)
  (* (*     P1 ≡π' P2 -> *) *)
  (* (*     (Par P1 EndProc) ≡π' P2 *) *)
  (* (* | ParEnd12' : forall {P1 P2}, *) *)
  (* (*     P1 ≡π' P2 -> *) *)
  (* (*     P1 ≡π' (Par P2 EndProc) *) *)
  (* (* | ParEnd21' : forall {P1 P2}, *) *)
  (* (*     P1 ≡π' P2 -> *) *)
  (* (*     (Par EndProc P1) ≡π' P2 *) *)
  (* (* | ParEnd22' : forall {P1 P2}, *) *)
  (* (*     P1 ≡π' P2 -> *) *)
  (* (*     P1 ≡π' (Par EndProc P2) *) *)
  (* where "P ≡π' Q" := (PiEquiv' P Q). *)
  (* Hint Constructors PiEquiv' : PiC. *)

  (* Fixpoint PiEquiv'Refl (P : Proc) : P ≡π' P := *)
  (*   match P with *)
  (*   | EndProc => EndProcRefl' *)
  (*   | VarProc n => VarProcRefl' n *)
  (*   | DefProc P Q => DefProcContext' (PiEquiv'Refl P) (PiEquiv'Refl Q) *)
  (*   | SendProc p e P => SendProcContext' p e (PiEquiv'Refl P) *)
  (*   | RecvProc p P => RecvProcContext' p (PiEquiv'Refl P) *)
  (*   | EChoiceL p P => EChoiceLContext' p (PiEquiv'Refl P) *)
  (*   | EChoiceR p P => EChoiceRContext' p (PiEquiv'Refl P) *)
  (*   | IChoice p P Q => IChoiceContext' p (PiEquiv'Refl P) (PiEquiv'Refl Q) *)
  (*   | IfThenElse e P Q => IfThenElseContext' e (PiEquiv'Refl P) (PiEquiv'Refl Q) *)
  (*   | Par P Q => ParContext' (PiEquiv'Refl P) (PiEquiv'Refl Q) *)
  (*   end. *)
  (* Hint Resolve PiEquiv'Refl : PiC. *)

  (* Fixpoint PiEquiv'Sym {P Q : Proc} (equiv : P ≡π' Q) : Q ≡π' P := *)
  (*   match equiv with *)
  (*   | EndProcRefl' => EndProcRefl' *)
  (*   | VarProcRefl' n => VarProcRefl' n *)
  (*   | DefProcContext' equiv'1 equiv'2 => *)
  (*     DefProcContext' (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2) *)
  (*   | SendProcContext' p e equiv' => *)
  (*     SendProcContext' p e (PiEquiv'Sym equiv') *)
  (*   | RecvProcContext' p equiv' => *)
  (*     RecvProcContext' p (PiEquiv'Sym equiv') *)
  (*   | EChoiceLContext' p equiv' => *)
  (*     EChoiceLContext' p (PiEquiv'Sym equiv') *)
  (*   | EChoiceRContext' p equiv' => *)
  (*     EChoiceRContext' p (PiEquiv'Sym equiv') *)
  (*   | IChoiceContext' p equiv'1 equiv'2 => *)
  (*     IChoiceContext' p (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2) *)
  (*   | IfThenElseContext' e equiv'1 equiv'2 => *)
  (*     IfThenElseContext' e (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2) *)
  (*   | ParContext' equiv'1 equiv'2 => *)
  (*     ParContext' (PiEquiv'Sym equiv'1) (PiEquiv'Sym equiv'2) *)
  (*   | ParSwap' equiv1 equiv2 => ParSwap' (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv1) *)
  (*   | ParComm1' equiv1 equiv2 equiv3 => *)
  (*     ParComm2' (PiEquiv'Sym equiv1) (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv3) *)
  (*   | ParComm2' equiv1 equiv2 equiv3 => *)
  (*     ParComm1' (PiEquiv'Sym equiv1) (PiEquiv'Sym equiv2) (PiEquiv'Sym equiv3) *)
  (*   (* | ParEnd11' equiv' => ParEnd12' (PiEquiv'Sym equiv') *) *)
  (*   (* | ParEnd12' equiv' => ParEnd11' (PiEquiv'Sym equiv') *) *)
  (*   (* | ParEnd21' equiv' => ParEnd22' (PiEquiv'Sym equiv') *) *)
  (*   (* | ParEnd22' equiv' => ParEnd21' (PiEquiv'Sym equiv') *) *)
  (*   end. *)

  (* Reserved Infix "≡π" (at level 15). *)
  (* Inductive PiEquiv : Proc -> Proc -> Prop := *)
  (*   PiEquiv'Lift : forall {P Q : Proc}, P ≡π' Q -> P ≡π Q *)
  (* | PiEquivStep : forall {P Q R : Proc}, P ≡π' Q -> Q ≡π R -> P ≡π R *)
  (* where "P ≡π Q" := (PiEquiv P Q). *)
  (* Hint Constructors PiEquiv : PiC. *)

  (* Instance PiEquivReflexive : Reflexive PiEquiv := fun P => PiEquiv'Lift (PiEquiv'Refl P). *)
  (* Instance PiEquivTransitive : Transitive PiEquiv. *)
  (* unfold Transitive. *)
  (* intros P Q R equiv1 equiv2. *)
  (* induction equiv1. eapply PiEquivStep; [exact H | exact equiv2]. *)
  (* eapply PiEquivStep; [exact H | apply IHequiv1; exact equiv2]. *)
  (* Defined. *)
  (* Instance PiEquivSymmetric : Symmetric PiEquiv. *)
  (* unfold Symmetric. intros P Q equiv. induction equiv. *)
  (* apply PiEquiv'Lift; apply PiEquiv'Sym; exact H. *)
  (* transitivity Q. exact IHequiv. apply PiEquiv'Lift. apply PiEquiv'Sym. exact H. *)
  (* Defined. *)

  (* (* Smart Constructos for PiEquiv *) *)
  (* Theorem EndProcRefl : EndProc ≡π EndProc. reflexivity. Qed. *)
  (* Theorem VarProcRefl : forall n, VarProc n ≡π VarProc n. reflexivity. Qed. *)
  (* Theorem DefProcContext : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     (DefProc P1 Q1) ≡π (DefProc P2 Q2). *)
  (* Proof. *)
  (*   intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1; *)
  (*     intros Q1 Q2 equiv2; induction equiv2; eauto with PiC. *)
  (* Qed.     *)
  (* Theorem SendProcContext : forall p e {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (SendProc p e P1) ≡π (SendProc p e P2). *)
  (* Proof. *)
  (*   intros p e P1 P2 equiv1; induction equiv1; eauto with PiC. *)
  (* Qed. *)
  (* Theorem RecvProcContext : forall p {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (RecvProc p P1) ≡π (RecvProc p P2). *)
  (* Proof. *)
  (*   intros p P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem EChoiceLContext : forall p {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (EChoiceL p P1) ≡π (EChoiceL p P2). *)
  (* Proof. *)
  (*   intros p P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
  (* Theorem EChoiceRContext : forall p {P1 P2}, *)
  (*     P1 ≡π P2 -> *)
  (*     (EChoiceR p P1) ≡π (EChoiceR p P2). *)
  (* Proof. *)
  (*   intros p P1 P2 equiv; induction equiv; eauto with PiC. *)
  (* Qed. *)
    
  (* Theorem IChoiceContext : forall p {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     (IChoice p P1 Q1) ≡π (IChoice p P2 Q2). *)
  (* Proof. *)
  (*   intros p P1 P2 Q1 Q2 equiv1; revert p Q1 Q2; induction equiv1; *)
  (*     intros p Q1 Q2 equiv2; induction equiv2; eauto with PiC. *)
  (* Qed.     *)

  (* Theorem IfThenElseContext : forall e {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     (IfThenElse e P1 Q1) ≡π (IfThenElse e P2 Q2). *)
  (* Proof. *)
  (*   intros e P1 P2 Q1 Q2 equiv1; revert e Q1 Q2; induction equiv1; *)
  (*     intros e Q1 Q2 equiv2; induction equiv2; eauto with PiC. *)
  (* Qed.     *)

  (* Theorem ParContext : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     (Par P1 Q1) ≡π (Par P2 Q2). *)
  (* Proof. *)
  (*   intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1; *)
  (*     intros Q1 Q2 equiv2; induction equiv2; eauto with PiC. *)
  (* Qed.     *)

  (* Theorem ParSwap : forall {P1 P2 Q1 Q2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     (Par P1 Q1) ≡π (Par Q2 P2). *)
  (* Proof. *)
  (*   intros P1 P2 Q1 Q2 equiv1; revert Q1 Q2; induction equiv1; *)
  (*     intros Q1 Q2 equiv2; induction equiv2; eauto with PiC. *)
  (* Qed.     *)
  (* Theorem ParComm1 : forall {P1 P2 Q1 Q2 R1 R2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> R1 ≡π R2 -> *)
  (*     (Par P1 (Par Q1 R1)) ≡π (Par (Par P2 Q2) R2). *)
  (* Proof. *)
  (*   intros P1 P2 Q1 Q2 R1 R2 equiv1; revert Q1 Q2 R1 R2; induction equiv1; *)
  (*     intros Q1 Q2 R1 R2 equiv2; revert R1 R2; induction equiv2; eauto with PiC; *)
  (*       intros R1 R2 equiv3; induction equiv3; eauto with PiC. *)
  (* Qed.     *)
  (* Theorem ParComm2 : forall {P1 P2 Q1 Q2 R1 R2}, *)
  (*     P1 ≡π P2 -> Q1 ≡π Q2 -> R1 ≡π R2 -> *)
  (*     (Par (Par P1 Q1) R1) ≡π (Par P2 (Par Q2 R2)). *)
  (* Proof. *)
  (*   intros P1 P2 Q1 Q2 R1 R2 equiv1; revert Q1 Q2 R1 R2; induction equiv1; eauto with PiC; *)
  (*     intros Q1' Q2' R1' R2' equiv2; revert R1' R2'; induction equiv2; eauto with PiC; *)
  (*       intros R1 R2 equiv3; induction equiv3; eauto with PiC. *)
  (* Qed. *)
  (* Hint Resolve EndProcRefl VarProcRefl DefProcContext SendProcContext RecvProcContext *)
  (*      EChoiceLContext EChoiceRContext IChoiceContext IfThenElseContext ParContext *)
  (*      ParSwap ParComm1 ParComm2 : PiC. *)
  
  (* (* Theorem ParEnd11 : forall {P1 P2}, *) *)
  (* (*     P1 ≡π P2 -> *) *)
  (* (*     (Par P1 EndProc) ≡π P2. *) *)
  (* (* Proof. *) *)
  (* (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParEnd12 : forall {P1 P2}, *) *)
  (* (*     P1 ≡π P2 -> *) *)
  (* (*     P1 ≡π (Par P2 EndProc). *) *)
  (* (* Proof. *) *)
  (* (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParEnd21 : forall {P1 P2}, *) *)
  (* (*     P1 ≡π P2 -> *) *)
  (* (*     (Par EndProc P1) ≡π P2. *) *)
  (* (* Proof. *) *)
  (* (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParEnd22 : forall {P1 P2}, *) *)
  (* (*     P1 ≡π P2 -> *) *)
  (* (*     P1 ≡π (Par EndProc P2). *) *)
  (* (* Proof. *) *)
  (* (*   intros P1 P2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  
  (* Inductive PiRedEquiv' : PiCalcRedContext -> PiCalcRedContext -> Prop := *)
  (*   HoleRefl' : PiRedEquiv' Hole Hole *)
  (* | ParCtxtEquiv1' : forall {CC1 CC2 P1 P2}, *)
  (*     P1 ≡π P2 -> PiRedEquiv' CC1 CC2 ->  *)
  (*     PiRedEquiv' (ParCtxt1 CC1 P1) (ParCtxt1 CC2 P2) *)
  (* | ParCtxtEquiv2' : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv' (ParCtxt2 P1 CC1) (ParCtxt2 P2 CC2) *)
  (* | ParCtxtSwitch1' : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv' (ParCtxt1 CC1 P1) (ParCtxt2 P2 CC2) *)
  (* | ParCtxtSwitch2' : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv' (ParCtxt2 P1 CC1) (ParCtxt1 CC2 P2) *)
  (* | ParCtxtComm11' : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv' (ParCtxt1 CC1 (Par P1 Q1)) (ParCtxt1 (ParCtxt1 CC2 P2) Q2) *)
  (* | ParCtxtComm12' : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv' (ParCtxt1 (ParCtxt1 CC1 P1) Q1) (ParCtxt1 CC2 (Par P2 Q2)) *)
  (* | ParCtxtComm21' : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv' (ParCtxt2  (Par P1 Q1) CC1) (ParCtxt2 P2 (ParCtxt2 Q2 CC2)) *)
  (* | ParCtxtComm22' : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv' CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv' (ParCtxt2 P1 (ParCtxt2 Q1 CC1)) (ParCtxt2  (Par P2 Q2) CC2) . *)
  (* (* | ParCtxtEnd11' : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv' CC1 CC2 -> *) *)
  (* (*     PiRedEquiv' (ParCtxt1 CC1 EndProc) CC2 *) *)
  (* (* | ParCtxtEnd12' : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv' CC1 CC2 -> *) *)
  (* (*     PiRedEquiv' CC1 (ParCtxt1 CC2 EndProc)  *) *)
  (* (* | ParCtxtEnd21' : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv' CC1 CC2 -> *) *)
  (* (*     PiRedEquiv' (ParCtxt2  EndProc CC1) CC2 *) *)
  (* (* | ParCtxtEnd22' : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv' CC1 CC2 -> *) *)
  (* (*     PiRedEquiv' CC1 (ParCtxt2  EndProc CC2). *) *)
  (* Hint Constructors PiRedEquiv' : PiC. *)

  (* Fixpoint PiRedEquiv'Refl (CC : PiCalcRedContext) : PiRedEquiv' CC CC := *)
  (*   match CC with *)
  (*   | Hole => HoleRefl' *)
  (*   | ParCtxt1 CC P => ParCtxtEquiv1' (PiEquiv'Lift (PiEquiv'Refl P)) (PiRedEquiv'Refl CC)  *)
  (*   | ParCtxt2 P CC => ParCtxtEquiv2' (PiRedEquiv'Refl CC) (PiEquiv'Lift (PiEquiv'Refl P)) *)
  (*   end. *)
  (* Hint Resolve PiRedEquiv'Refl : PiC. *)

  (* Lemma PiRedEquiv'Sym : forall CC1 CC2, PiRedEquiv' CC1 CC2 -> PiRedEquiv' CC2 CC1. *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv. *)
  (*   induction equiv; auto with PiC. *)
  (*   all: symmetry in H; auto with PiC. *)
  (*   all: symmetry in H0; auto with PiC. *)
  (* Qed. *)
  (* Hint Resolve PiRedEquiv'Sym : PiC. *)

  (* Inductive PiRedEquiv : PiCalcRedContext -> PiCalcRedContext -> Prop := *)
  (*   PiRedEquiv'Lift : forall {CC1 CC2}, PiRedEquiv' CC1 CC2 -> PiRedEquiv CC1 CC2 *)
  (* | PiRedEquivStep : forall {CC1 CC2 CC3}, *)
  (*     PiRedEquiv' CC1 CC2 -> PiRedEquiv CC2 CC3 -> PiRedEquiv CC1 CC3. *)
  (* Hint Constructors PiRedEquiv : PiC. *)

  (* Instance PiRedEquivReflexive : Reflexive PiRedEquiv := *)
  (*   fun CC => PiRedEquiv'Lift (PiRedEquiv'Refl CC). *)
  (* Instance PiRedEquivTransitive : Transitive PiRedEquiv. *)
  (* unfold Transitive. intros CC1 CC2 CC3 equiv1 equiv2. *)
  (* induction equiv1. eapply PiRedEquivStep; eauto with PiC. *)
  (* eapply PiRedEquivStep; [exact H| apply IHequiv1; exact equiv2]. *)
  (* Defined. *)
  (* Instance PiRedEquivSymmetric : Symmetric PiRedEquiv. *)
  (* unfold Symmetric; intros CC1 CC2 equiv1; induction equiv1. *)
  (* apply PiRedEquiv'Lift; apply PiRedEquiv'Sym ;auto. *)
  (* transitivity (CC2); auto. apply PiRedEquiv'Sym in H; apply PiRedEquiv'Lift; auto. *)
  (* Defined. *)

  (* Theorem HoleRefl : PiRedEquiv Hole Hole. reflexivity. Qed. *)
  (* Theorem ParCtxtEquiv1 : forall {CC1 CC2 P1 P2}, *)
  (*     P1 ≡π P2 -> PiRedEquiv CC1 CC2 ->  *)
  (*     PiRedEquiv (ParCtxt1 CC1 P1) (ParCtxt1 CC2 P2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 equiv1 equiv2; revert P1 P2 equiv1; induction equiv2; *)
  (*     intros P1 P2 equiv1; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtEquiv2 : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv (ParCtxt2 P1 CC1) (ParCtxt2 P2 CC2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 equiv1; revert P1 P2; *)
  (*     induction equiv1; intros P1 P2 equiv2; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtSwitch1 : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv (ParCtxt1 CC1 P1) (ParCtxt2 P2 CC2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 equiv1; revert P1 P2; *)
  (*     induction equiv1; intros P1 P2 equiv2; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtSwitch2 : forall {CC1 CC2 P1 P2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> *)
  (*     PiRedEquiv (ParCtxt2 P1 CC1) (ParCtxt1 CC2 P2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 equiv1; revert P1 P2; *)
  (*     induction equiv1; intros P1 P2 equiv2; eauto with PiC. *)
  (* Qed. *)

  (* Theorem ParCtxtComm11 : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv (ParCtxt1 CC1 (Par P1 Q1)) (ParCtxt1 (ParCtxt1 CC2 P2) Q2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2; *)
  (*     induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtComm12 : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv (ParCtxt1 (ParCtxt1 CC1 P1) Q1) (ParCtxt1 CC2 (Par P2 Q2)). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2; *)
  (*     induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC. *)
  (*   apply @PiRedEquivStep with (CC2 := ParCtxt1 (ParCtxt1 CC2 P1) Q1); eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtComm21 : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv (ParCtxt2  (Par P1 Q1) CC1) (ParCtxt2 P2 (ParCtxt2 Q2 CC2)). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2; *)
  (*     induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC. *)
  (* Qed. *)
  (* Theorem ParCtxtComm22 : forall {CC1 CC2 P1 P2 Q1 Q2}, *)
  (*     PiRedEquiv CC1 CC2 -> P1 ≡π P2 -> Q1 ≡π Q2 -> *)
  (*     PiRedEquiv (ParCtxt2 P1 (ParCtxt2 Q1 CC1)) (ParCtxt2  (Par P2 Q2) CC2). *)
  (* Proof. *)
  (*   intros CC1 CC2 P1 P2 Q1 Q2 equiv1; revert P1 P2 Q1 Q2; *)
  (*     induction equiv1; intros P1 P2 Q1 Q2 equiv2 equiv3; eauto with PiC. *)
  (*   apply @PiRedEquivStep with (CC2 := ParCtxt2 P1 (ParCtxt2 Q1 CC2)); eauto with PiC. *)
  (* Qed. *)
  (* Hint Resolve HoleRefl ParCtxtEquiv1 ParCtxtEquiv2 ParCtxtComm11 ParCtxtComm12 *)
  (*      ParCtxtComm21 ParCtxtComm22 ParCtxtSwitch1 ParCtxtSwitch2 : PiC. *)
  
  (* (* Theorem ParCtxtEnd11 : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv CC1 CC2 -> *) *)
  (* (*     PiRedEquiv (ParCtxt1 CC1 EndProc) CC2. *) *)
  (* (* Proof. *) *)
  (* (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParCtxtEnd12 : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv CC1 CC2 -> *) *)
  (* (*     PiRedEquiv CC1 (ParCtxt1 CC2 EndProc). *) *)
  (* (* Proof. *) *)
  (* (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParCtxtEnd21 : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv CC1 CC2 -> *) *)
  (* (*     PiRedEquiv (ParCtxt2  EndProc CC1) CC2. *) *)
  (* (* Proof. *) *)
  (* (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)
  (* (* Theorem ParCtxtEnd22 : forall {CC1 CC2}, *) *)
  (* (*     PiRedEquiv CC1 CC2 -> *) *)
  (* (*     PiRedEquiv CC1 (ParCtxt2  EndProc CC2). *) *)
  (* (* Proof. *) *)
  (* (*   intros CC1 CC2 equiv; induction equiv; eauto with PiC. *) *)
  (* (* Qed. *) *)

  (* Fixpoint ContextCompose (CC1 CC2 : PiCalcRedContext) : PiCalcRedContext := *)
  (*   match CC1 with *)
  (*   | Hole => CC2 *)
  (*   | ParCtxt1 CC1 P => ParCtxt1 (ContextCompose CC1 CC2) P *)
  (*   | ParCtxt2 P CC1 => ParCtxt2 P (ContextCompose CC1 CC2) *)
  (*   end. *)

  (* Lemma ApplyComposedContext: forall (CC1 CC2 : PiCalcRedContext) (P : Proc), *)
  (*     ApplyRedContext (ContextCompose CC1 CC2) P = ApplyRedContext CC1 (ApplyRedContext CC2 P). *)
  (* Proof. *)
  (*   intro CC1; induction CC1; simpl; auto; intros CC2 P; *)
  (*     rewrite IHCC1; auto. *)
  (* Qed. *)

  (* Lemma ContextComposeEquiv' : forall (CC1 CC1' CC2 CC2' : PiCalcRedContext), *)
  (*     PiRedEquiv' CC1 CC1' -> PiRedEquiv' CC2 CC2' *)
  (*     -> PiRedEquiv' (ContextCompose CC1 CC2) (ContextCompose CC1' CC2'). *)
  (* Proof. *)
  (*   intros CC1 CC1' CC2 CC2' equiv1; revert CC2 CC2'; induction equiv1; *)
  (*     simpl; auto with PiC. *)
  (* Qed. *)

  (* Lemma ContextComposeEquiv : forall (CC1 CC1' CC2 CC2' : PiCalcRedContext), *)
  (*     PiRedEquiv CC1 CC1' -> PiRedEquiv CC2 CC2' *)
  (*     -> PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC1' CC2'). *)
  (* Proof. *)
  (*   intros CC1 CC1' CC2 CC2' equiv1; revert CC2 CC2'; induction equiv1; *)
  (*     simpl; auto with PiC. *)
  (*   - intros CC2' CC2'' equiv2. *)
  (*     induction equiv2; auto with PiC. *)
  (*     constructor; apply ContextComposeEquiv'; auto. *)
  (*     transitivity (ContextCompose CC1 CC3); auto. *)
  (*     constructor; apply ContextComposeEquiv'; auto. apply PiRedEquiv'Refl. *)
  (*   - intros CC0 CC2' equiv2. specialize (IHequiv1 CC0 CC2' equiv2). *)
  (*     transitivity (ContextCompose CC2 CC0); auto. *)
  (*     constructor; apply ContextComposeEquiv'; auto. apply PiRedEquiv'Refl. *)
  (* Qed. *)

  (* Lemma ContextComposeComm : forall CC1 CC2 CC3, *)
  (*     ContextCompose CC1 (ContextCompose CC2 CC3) = *)
  (*     ContextCompose (ContextCompose CC1 CC2) CC3. *)
  (* Proof. *)
  (*   intro CC1; induction CC1; simpl; auto; *)
  (*     intros CC2 CC3; rewrite IHCC1; auto. *)
  (* Qed. *)

  (* Lemma ContextComposeHole : forall CC, ContextCompose CC Hole = CC. *)
  (* Proof. *)
  (*   intro CC; induction CC; simpl; auto; rewrite IHCC; auto. *)
  (* Qed. *)

  (* Lemma ContextComposeSwapEquiv : forall CC1 CC2, *)
  (*     PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC2 CC1). *)
  (* Proof. *)
  (*   intros CC1; induction CC1; intro CC2; simpl. *)
  (*   - rewrite ContextComposeHole; reflexivity. *)
  (*   - induction CC2; simpl in *; auto with PiC. *)
  (*     -- rewrite ContextComposeHole; reflexivity. *)
  (*     -- transitivity (ParCtxt1 (ContextCompose (ParCtxt1 CC2 p0) CC1) p); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt1 (ContextCompose CC2 CC1) (Par p0 p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC1 CC2) p) p0); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ContextCompose CC1 CC2) (Par p p0)); auto with PiC. *)
  (*        apply ParCtxtEquiv1; auto with PiC. *)
  (*        symmetry; apply IHCC1. *)
  (*     -- transitivity (ParCtxt2 p0 (ContextCompose (ParCtxt1 CC1 p) CC2)); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt1 (ContextCompose (ParCtxt2 p0 CC2) CC1) p); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt2 p (ParCtxt2 p0 (ContextCompose CC2 CC1))); auto with PiC. *)
  (*        transitivity (ParCtxt2 p0 (ParCtxt2 p (ContextCompose CC1 CC2))); auto with PiC. *)
  (*        transitivity (ParCtxt2 (Par p p0) (ContextCompose CC2 CC1)); auto with PiC. *)
  (*        transitivity (ParCtxt2 (Par p0 p) (ContextCompose CC1 CC2)); auto with PiC. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        symmetry; apply IHCC1. *)
  (*   - induction CC2; simpl in *; auto with PiC. *)
  (*     -- rewrite ContextComposeHole; reflexivity. *)
  (*     -- transitivity (ParCtxt2 p (ContextCompose (ParCtxt1 CC2 p0) CC1)); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt1 (ContextCompose (ParCtxt2 p CC1) CC2) p0); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC2 CC1) p0) p); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (ContextCompose CC1 CC2) p) p0); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ContextCompose CC2 CC1) (Par p0 p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ContextCompose CC1 CC2) (Par p p0)); auto with PiC. *)
  (*        apply ParCtxtEquiv1; symmetry; auto with PiC. *)
  (*     -- transitivity (ParCtxt2 p (ContextCompose (ParCtxt2 p0 CC2) CC1)); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt2 p0 (ContextCompose (ParCtxt2 p CC1) CC2)); auto with PiC; *)
  (*          simpl. *)
  (*        transitivity (ParCtxt2 (Par p p0) (ContextCompose CC2 CC1)); auto with PiC. *)
  (*        transitivity (ParCtxt2 (Par p0 p) (ContextCompose CC1 CC2)); auto with PiC. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        symmetry; apply IHCC1. *)
  (* Qed. *)

  (* Lemma CCEquiv' : forall CC1 CC2, *)
  (*     PiRedEquiv' CC1 CC2 -> *)
  (*     forall P Q, P ≡π Q -> *)
  (*            (ApplyRedContext CC1 P) ≡π (ApplyRedContext CC2 Q). *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv1; induction equiv1; intros Q R equiv2; simpl; auto with PiC. *)
  (* Qed. *)
  (* Lemma CCEquiv : forall CC1 CC2, *)
  (*     PiRedEquiv CC1 CC2 -> *)
  (*     forall P Q, P ≡π Q -> *)
  (*            (ApplyRedContext CC1 P) ≡π (ApplyRedContext CC2 Q). *)
  (* Proof. *)
  (*   intros CC1 CC2 equiv1; induction equiv1; intros P Q equiv. *)
  (*   - apply CCEquiv'; auto. *)
  (*   - transitivity (ApplyRedContext CC2 P). *)
  (*     apply CCEquiv'; auto. reflexivity. apply IHequiv1; auto. *)
  (* Qed. *)

  (* Lemma Equiv'HoleInversion : forall CC, PiRedEquiv' CC Hole -> CC = Hole. *)
  (* Proof. *)
  (*   intros CC equiv; destruct CC; inversion equiv; auto. *)
  (* Qed. *)
  (* Lemma EquivHoleInversion : forall CC, PiRedEquiv CC Hole -> CC = Hole. *)
  (* Proof. *)
  (*   intros CC equiv; remember Hole; induction equiv; subst. *)
  (*   apply Equiv'HoleInversion in H; auto. *)
  (*   specialize (IHequiv eq_refl); subst. apply Equiv'HoleInversion in H; auto. *)
  (* Qed. *)

  (* Definition SingleThread : Proc -> Prop := *)
  (*   fun P => match P with *)
  (*   | EndProc => True *)
  (*   | VarProc x => True *)
  (*   | DefProc x x0 => True *)
  (*   | SendProc x x0 x1 => True *)
  (*   | RecvProc x x0 => True *)
  (*   | EChoiceL x x0 => True *)
  (*   | EChoiceR x x0 => True *)
  (*   | IChoice x x0 x1 => True *)
  (*   | IfThenElse x x0 x1 => True *)
  (*   | Par x x0 => False *)
  (*   end. *)

  (* Lemma SingleThreadEquiv' : forall P Q, SingleThread P -> P ≡π' Q -> SingleThread Q. *)
  (* Proof. *)
  (*   intros P Q ST equiv; revert ST; induction equiv; simpl; intro ST; auto. *)
  (* Qed. *)
  (* Lemma SingleThreadEquiv : forall P Q, SingleThread P -> P ≡π Q -> SingleThread Q. *)
  (* Proof. *)
  (*   intros P Q ST equiv; induction equiv. apply SingleThreadEquiv' in H; auto. *)
  (*   apply IHequiv. apply SingleThreadEquiv' in H; auto. *)
  (* Qed. *)

  (* Fixpoint ProcessToList (P : Proc) : list Proc := *)
  (*   match P with *)
  (*   | Par P Q => ProcessToList P ++ ProcessToList Q *)
  (*   | _ => [P] *)
  (*   end. *)

  (* Lemma ProcessToListNonNil : forall (P : Proc), ProcessToList P <> nil. *)
  (* Proof. *)
  (*   intro P; induction P; try (intro H; inversion H; fail). *)
  (*   simpl. intro H; apply app_eq_nil in H; destruct H; apply IHP1; auto. *)
  (* Qed. *)

  (* Theorem AllInProcessToList' : forall (P Q : Proc), *)
  (*     P ≡π' Q -> *)
  (*     (forall R : Proc, In R (ProcessToList P) -> exists R', In R' (ProcessToList Q) /\ R ≡π R'). *)
  (* Proof.     *)
  (*   intros P Q equiv; induction equiv; simpl; intro R; intro H; auto. *)
  (*   all: try (destruct H; auto; subst). *)
  (*   all: try (eexists; split; auto with PiC; fail). *)
  (*   - apply in_app_or in H; destruct H. *)
  (*     destruct (IHequiv1 R H) as [R' IH]; destruct IH as [i equiv]; *)
  (*       exists R'; split; auto. *)
  (*     apply in_or_app; left; auto. *)
  (*     destruct (IHequiv2 R H) as [R' IH]; destruct IH as [i equiv]; *)
  (*       exists R'; split; auto. *)
  (*     apply in_or_app; right; auto. *)
  (*   - apply in_app_or in H; destruct H. *)
  (*     destruct (IHequiv1 R H) as [R' IH]; destruct IH as [i equiv]; *)
  (*       exists R'; split; auto. *)
  (*     apply in_or_app; right; auto. *)
  (*     destruct (IHequiv2 R H) as [R' IH]; destruct IH as [i equiv]; *)
  (*       exists R'; split; auto. *)
  (*     apply in_or_app; left; auto. *)
  (*   - apply in_app_or in H; destruct H; [| apply in_app_or in H; destruct H]. *)
  (*     -- destruct (IHequiv1 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; left; apply in_or_app; left; auto. *)
  (*     -- destruct (IHequiv2 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; left; apply in_or_app; right; auto. *)
  (*     -- destruct (IHequiv3 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; right; auto. *)
  (*   - apply in_app_or in H; destruct H; [ apply in_app_or in H; destruct H |]. *)
  (*     -- destruct (IHequiv1 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; left; auto. *)
  (*     -- destruct (IHequiv2 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; right; apply in_or_app; left; auto. *)
  (*     -- destruct (IHequiv3 R H) as [R' IH]; destruct IH; *)
  (*          exists R'; split; auto. *)
  (*        apply in_or_app; right; apply in_or_app; right; auto. *)
  (* Qed. *)
  
  (* Fixpoint ListToProcess (l : list Proc) : option Proc := *)
  (*   match l with *)
  (*   | [] => None *)
  (*   | P :: l' => match ListToProcess l' with *)
  (*              | None => Some P *)
  (*              | Some Q => Some (Par P Q) *)
  (*              end *)
  (*   end. *)

  (* Lemma ListToProcessNoneNil : forall (l : list Proc), ListToProcess l = None -> l = []. *)
  (* Proof. *)
  (*   intros l H. destruct l; auto. inversion H. *)
  (*   destruct (ListToProcess l); inversion H1. *)
  (* Qed. *)

  (* Inductive ListPiEquiv : list Proc -> list Proc -> Prop := *)
  (*   NilPiEquiv : ListPiEquiv [] [] *)
  (* | ConsPiEquiv : forall P Q l l', *)
  (*     P ≡π Q -> ListPiEquiv l l' -> *)
  (*     ListPiEquiv (P :: l) (Q :: l'). *)
  (* Hint Constructors ListPiEquiv : PiC. *)

  (* Theorem ListPiEquivToTerm : forall l l', *)
  (*     ListPiEquiv l l' -> *)
  (*     forall P Q, ListToProcess l = Some P -> ListToProcess l' = Some Q -> *)
  (*            P ≡π Q. *)
  (* Proof. *)
  (*   intros l l' lequiv; induction lequiv; intros R S eq1 eq2; [inversion eq1|]. *)
  (*   simpl in eq1; simpl in eq2. *)
  (*   destruct (ListToProcess l) eqn:eql; destruct (ListToProcess l') eqn:eql'. *)
  (*   - inversion eq1; inversion eq2; subst; clear eq1 eq2. *)
  (*     specialize (IHlequiv p p0 eq_refl eq_refl). apply ParContext; auto. *)
  (*   - inversion eq1; inversion eq2; subst; clear eq1 eq2. *)
  (*     apply ListToProcessNoneNil in eql'; subst. inversion lequiv;subst. inversion eql. *)
  (*   - inversion eq1; inversion eq2; subst; clear eq1 eq2. *)
  (*     apply ListToProcessNoneNil in eql; subst. inversion lequiv; subst. inversion eql'. *)
  (*   - inversion eq1; inversion eq2; subst; clear eq1 eq2; auto. *)
  (* Qed. *)

  (* Theorem ListPiEquivDoubleApp : forall l1 l2 l3 l4, *)
  (*     ListPiEquiv l1 l3 -> ListPiEquiv l2 l4 -> ListPiEquiv (l1 ++ l2) (l3 ++ l4). *)
  (* Proof. *)
  (*   intro l1; induction l1; intros l2 l3 l4 H H0. *)
  (*   inversion H; simpl; auto. *)
  (*   inversion H; subst; simpl; constructor; auto. *)
  (* Qed. *)
    
  (* (* How is this not in the standard library!? *) *)
  (* Theorem AppComm : forall {A : Type} (l1 l2 l3 : list A), *)
  (*     l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3. *)
  (* Proof. *)
  (*   intros A l1; induction l1; simpl; intros l2 l3; [| rewrite IHl1]; reflexivity. *)
  (* Qed. *)

  (* Theorem ProcessToListEquiv' : forall P Q, *)
  (*     P ≡π' Q -> exists l l', Permutation (ProcessToList P) l /\ Permutation (ProcessToList Q) l' /\ *)
  (*                      ListPiEquiv l l'. *)
  (* Proof. *)
  (*   intros P Q equiv; induction equiv; simpl. *)
  (*   all: try (eexists; eexists; split; [|split]; eauto with PiC; fail). *)
  (*   - destruct IHequiv1 as [l1 H]; destruct H as [l2 H]; *)
  (*       destruct H as [perm1 H]; destruct H as [perm2 lequiv1]. *)
  (*     destruct IHequiv2 as [l3 H]; destruct H as [l4 H]; *)
  (*       destruct H as [perm3 H]; destruct H as [perm4 lequiv2]. *)
  (*     exists (l1 ++ l3); exists (l2 ++ l4); split; [| split]; *)
  (*       try (apply Permutation_app; auto). *)
  (*     apply ListPiEquivDoubleApp; auto. *)
  (*   - destruct IHequiv1 as [l1 H]; destruct H as [l2 H]; *)
  (*       destruct H as [perm1 H]; destruct H as [perm2 lequiv1]. *)
  (*     destruct IHequiv2 as [l3 H]; destruct H as [l4 H]; *)
  (*       destruct H as [perm3 H]; destruct H as [perm4 lequiv2]. *)
  (*     exists (l1 ++ l3); exists (l2 ++ l4); split; [| split]. *)
  (*     apply Permutation_app; auto. *)
  (*     transitivity (l4 ++ l2); *)
  (*       [apply Permutation_app; auto|apply Permutation_app_comm]. *)
  (*     apply ListPiEquivDoubleApp; auto. *)
  (*   - destruct IHequiv1 as [l1 H]; destruct H as [l2 H]; *)
  (*       destruct H as [perm1 H]; destruct H as [perm2 lequiv1]. *)
  (*     destruct IHequiv2 as [l3 H]; destruct H as [l4 H]; *)
  (*       destruct H as [perm3 H]; destruct H as [perm4 lequiv2]. *)
  (*     destruct IHequiv3 as [l5 H]; destruct H as [l6 H]; *)
  (*       destruct H as [perm5 H]; destruct H as [perm6 lequiv3]. *)
  (*     exists (l1 ++ l3 ++ l5); exists (l2 ++ l4 ++ l6); split; [|split]. *)
  (*     repeat (apply Permutation_app; auto).  *)
  (*     rewrite AppComm. *)
  (*     repeat (apply Permutation_app; auto). *)
  (*     repeat (apply ListPiEquivDoubleApp; auto). *)
  (*   - destruct IHequiv1 as [l1 H]; destruct H as [l2 H]; *)
  (*       destruct H as [perm1 H]; destruct H as [perm2 lequiv1]. *)
  (*     destruct IHequiv2 as [l3 H]; destruct H as [l4 H]; *)
  (*       destruct H as [perm3 H]; destruct H as [perm4 lequiv2]. *)
  (*     destruct IHequiv3 as [l5 H]; destruct H as [l6 H]; *)
  (*       destruct H as [perm5 H]; destruct H as [perm6 lequiv3]. *)
  (*     exists (l1 ++ l3 ++ l5); exists (l2 ++ l4 ++ l6); split; [|split]. *)
  (*     rewrite AppComm; repeat (apply Permutation_app; auto).  *)
  (*     repeat (apply Permutation_app; auto). *)
  (*     repeat (apply ListPiEquivDoubleApp; auto). *)
  (* Qed. *)

  (* Theorem ListEquivRefl : forall l, ListPiEquiv l l. *)
  (* Proof. *)
  (*   intro l; induction l; simpl; constructor; auto with PiC. *)
  (* Qed. *)
  (* Hint Resolve ListEquivRefl : PiC. *)

  (* Theorem ListEquivTrans : forall l1 l2 l3, *)
  (*     ListPiEquiv l1 l2 -> ListPiEquiv l2 l3 -> ListPiEquiv l1 l3. *)
  (* Proof. *)
  (*   intros l1 l2 l3 equiv1; revert l3; induction equiv1; intros l3 equiv2; *)
  (*     inversion equiv2; subst; auto with PiC. *)
  (*   constructor; auto. transitivity Q; auto. *)
  (* Qed. *)

  (* Theorem ListEquivPermutation : forall l1 l2, *)
  (*     ListPiEquiv l1 l2 -> forall l3, Permutation l2 l3 -> exists l4, Permutation l1 l4 /\ ListPiEquiv l4 l3. *)
  (* Proof. *)
  (*   intros l1 l2 equiv l3 perm; revert l1 equiv; induction perm; intros l1 equiv. *)
      
  (*   - inversion equiv; subst. exists []; split; constructor. *)
  (*   - inversion equiv; subst. *)
  (*     destruct (IHperm l0 H3) as [l4 Hl4]; destruct Hl4 as [perm' equiv']. *)
  (*     exists (P :: l4); split; try (constructor; auto; fail). *)
  (*   - inversion equiv; subst. inversion H3; subst. *)
  (*     exists (P0 :: P :: l1); split; try (constructor; auto; fail). *)
  (*     constructor; auto. constructor; auto. *)
  (*   - specialize (IHperm1 l1 equiv). *)
  (*     destruct IHperm1 as [l2 H]; destruct H as [perm12 equiv2]. *)
  (*     specialize (IHperm2 l2 equiv2); destruct IHperm2 as [l3 H]; destruct H as [perm23 equiv3]. *)
  (*     exists l3; split; auto. transitivity l2; auto. *)
  (* Qed. *)

  (* Lemma ProcessToListEquiv : forall P Q, *)
  (*     P ≡π Q -> exists l l', Permutation (ProcessToList P) l /\ Permutation (ProcessToList Q) l' /\ *)
  (*                      ListPiEquiv l l'. *)
  (* Proof. *)
  (*   intros P Q equiv; induction equiv. *)
  (*   apply ProcessToListEquiv'; auto. *)
  (*   apply ProcessToListEquiv' in H. *)
  (*   destruct H as [lP H]; destruct H as [lQ H]; destruct H as [permP H]; *)
  (*     destruct H as [permQ equivPQ]. *)
  (*   destruct IHequiv as [lQ' H]; destruct H as [lR H]; destruct H as [permQ' H]; *)
  (*     destruct H as [permR equivQR]. *)
  (*   assert (Permutation lQ lQ') as permQ'' *)
  (*       by (transitivity (ProcessToList Q); [symmetry|]; auto). *)
  (*   destruct (ListEquivPermutation lP lQ equivPQ lQ' permQ'') as [lP' H]; *)
  (*     destruct H as [perm lequiv]. *)
  (*   exists lP'; exists lR; split; [| split]; auto. *)
  (*   transitivity lP; auto. eapply ListEquivTrans; eauto. *)
  (* Qed. *)
      
  (* Theorem ListToProcessPerm : forall l l' P Q, *)
  (*     Permutation l l' -> *)
  (*     ListToProcess l = Some P -> *)
  (*     ListToProcess l' = Some Q -> *)
  (*     P ≡π Q. *)
  (* Proof. *)
  (*   intros l l' P Q perm; revert P Q; induction perm; intros p q eq1 eq2. *)
  (*   - inversion eq1. *)
  (*   - simpl in *. destruct l eqn:e1; destruct l' eqn:e2. simpl in *. *)
  (*     inversion eq1; inversion eq2; subst; reflexivity. *)
  (*     apply Permutation_nil in perm; inversion perm. *)
  (*     apply Permutation_sym in perm; apply Permutation_nil in perm; inversion perm. *)
  (*     simpl in *. *)
  (*     destruct (ListToProcess l0); destruct (ListToProcess l1). *)
  (*     all: inversion eq1; inversion eq2; subst. *)
  (*     all: apply ParContext; [reflexivity|]; apply IHperm; auto. *)
  (*   - simpl in eq1. simpl in eq2. destruct (ListToProcess l). *)
  (*     inversion eq1; inversion eq2; subst. *)
  (*     transitivity (Par (Par y x) p0). *)
  (*     apply ParComm1; auto with PiC. *)
  (*     transitivity (Par (Par x y) p0); auto with PiC. *)
  (*     inversion eq1; inversion eq2; subst. *)
  (*     auto with PiC. *)
  (*   - destruct (ListToProcess l') eqn:e. *)
  (*     transitivity p0. apply IHperm1; auto. apply IHperm2; auto. *)
  (*     apply ListToProcessNoneNil in e; subst. *)
  (*     apply Permutation_nil in perm2; subst. simpl in eq2. inversion eq2. *)
  (* Qed. *)

  (* Fixpoint ContextToLists (CC : PiCalcRedContext) : list Proc * list Proc := *)
  (*   match CC with *)
  (*   | Hole => ([], []) *)
  (*   | ParCtxt1 CC' P => match (ContextToLists CC') with *)
  (*                      | (l1, l2) => (l1, l2 ++ ProcessToList P) *)
  (*                      end *)
  (*   | ParCtxt2 P CC' => match (ContextToLists CC') with *)
  (*                      | (l1, l2) => (ProcessToList P ++ l1, l2) *)
  (*                      end *)
  (*   end. *)


  (* Theorem ApplyRedContextToLists : forall (CC : PiCalcRedContext) (P : Proc), *)
  (*     ProcessToList (ApplyRedContext CC P) = *)
  (*     fst (ContextToLists CC) ++ ProcessToList P ++ snd (ContextToLists CC). *)
  (* Proof. *)
  (*   intro CC; induction CC; simpl; intros P. *)
  (*   - apply app_nil_end. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite IHCC; auto. *)
  (*     rewrite <- AppComm; rewrite <- AppComm; reflexivity. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite IHCC; auto. *)
  (*     rewrite AppComm; reflexivity. *)
  (* Qed. *)

  (* Lemma SingleThreadToList : forall P, SingleThread P -> ProcessToList P = [P]. *)
  (* Proof. *)
  (*   intros P STP; destruct P; auto; inversion STP. *)
  (* Qed. *)

  (* Fixpoint LeftContextFromList (l : list Proc) : PiCalcRedContext := *)
  (*   match l with *)
  (*   | nil => Hole *)
  (*   | P :: l' => ParCtxt1 (LeftContextFromList l') P *)
  (*   end. *)

  (* Lemma LeftContextAppCompose : forall (l1 l2 : list Proc), *)
  (*     LeftContextFromList (l1 ++ l2) = *)
  (*     ContextCompose (LeftContextFromList l1) (LeftContextFromList l2). *)
  (* Proof. *)
  (*   intro l1; induction l1; simpl; auto. *)
  (*   intro l2; rewrite IHl1; auto. *)
  (* Qed. *)

  (* Lemma LeftContextFromProcessList : forall (P : Proc), *)
  (*     PiRedEquiv (LeftContextFromList (ProcessToList P)) (ParCtxt1 Hole P). *)
  (* Proof. *)
  (*   intro P; induction P; simpl; auto with PiC. *)
  (*   rewrite LeftContextAppCompose. *)
  (*   transitivity (ContextCompose (ParCtxt1 Hole P1) (ParCtxt1 Hole P2)); auto. *)
  (*   apply ContextComposeEquiv; auto. *)
  (*   simpl. transitivity (ParCtxt1 Hole (Par P2 P1)); auto with PiC. *)
  (* Qed. *)

  (* Lemma LeftContetFromRevList : forall l, *)
  (*     PiRedEquiv (LeftContextFromList l) (LeftContextFromList (rev l)). *)
  (* Proof. *)
  (*   intros l; induction l; simpl; auto with PiC. *)
  (*   rewrite LeftContextAppCompose; simpl. *)
  (*   transitivity (ContextCompose (ParCtxt1 Hole a) (LeftContextFromList (rev l))); *)
  (*     [simpl | apply ContextComposeSwapEquiv]; auto with PiC. *)
  (* Qed. *)

  (* Lemma LeftContextFromRevProcessList : forall (P : Proc), *)
  (*     PiRedEquiv (LeftContextFromList (rev (ProcessToList P))) (ParCtxt1 Hole P). *)
  (* Proof. *)
  (*   intro P; induction P; simpl; auto with PiC. *)
  (*   rewrite rev_app_distr. rewrite LeftContextAppCompose. *)
  (*   transitivity (ContextCompose (ParCtxt1 Hole P2) (ParCtxt1 Hole P1)); auto with PiC. *)
  (*   apply ContextComposeEquiv; auto. *)
  (*   simpl; auto with PiC. *)
  (* Qed. *)

  (* Lemma LeftContextEquivLists : forall (l1 l2 : list Proc), *)
  (*     ListPiEquiv l1 l2 -> PiRedEquiv (LeftContextFromList l1) (LeftContextFromList l2). *)
  (* Proof. *)
  (*   intros l1 l2 lequiv; induction lequiv; simpl. *)
  (*   reflexivity. *)
  (*   apply ParCtxtEquiv1; auto with PiC. *)
  (* Qed. *)

  (* Lemma LeftContextPermLists : forall l1 l2, *)
  (*     Permutation l1 l2 -> PiRedEquiv (LeftContextFromList l1) (LeftContextFromList l2). *)
  (* Proof. *)
  (*   intros l1 l2 perm; induction perm; simpl. *)
  (*   - reflexivity. *)
  (*   - apply ParCtxtEquiv1; auto with PiC. *)
  (*   - transitivity (ParCtxt1 (LeftContextFromList l) (Par x y)). *)
  (*     apply ParCtxtComm12; reflexivity. *)
  (*     transitivity (ParCtxt1 (LeftContextFromList l) (Par y x)). *)
  (*     apply ParCtxtEquiv1; auto with PiC; reflexivity. *)
  (*     apply ParCtxtComm11; reflexivity. *)
  (*   - transitivity (LeftContextFromList l'); auto. *)
  (* Qed. *)

  (* Fixpoint RightContextFromList (l : list Proc) : PiCalcRedContext := *)
  (*   match l with *)
  (*   | [] => Hole *)
  (*   | P :: l' => ParCtxt2 P (RightContextFromList l') *)
  (*   end. *)

  (* Lemma RightContextAppCompose : forall (l1 l2 : list Proc), *)
  (*     RightContextFromList (l1 ++ l2) = *)
  (*     ContextCompose (RightContextFromList l1) (RightContextFromList l2). *)
  (* Proof. *)
  (*   intro l1; induction l1; simpl; auto. *)
  (*   intros l2; rewrite IHl1; reflexivity. *)
  (* Qed. *)

  (* Lemma RightContextFromProcessList : forall (P : Proc), *)
  (*     PiRedEquiv (RightContextFromList (ProcessToList P)) *)
  (*                (ParCtxt2 P Hole). *)
  (* Proof. *)
  (*   intro P; induction P; simpl; auto with PiC. *)
  (*   rewrite RightContextAppCompose. *)
  (*   transitivity (ContextCompose (ParCtxt2 P1 Hole) (ParCtxt2 P2 Hole)). *)
  (*   apply ContextComposeEquiv; auto. *)
  (*   simpl. apply ParCtxtComm22; auto with PiC. *)
  (* Qed. *)
  
  (* Definition ContextFromLists  (l1 l2 : list Proc) : PiCalcRedContext := *)
  (*   ContextCompose (RightContextFromList l1) (LeftContextFromList (rev l2)). *)

  (* Lemma ComposeEquivBackwards : forall CC1 CC2 CC3 CC4, *)
  (*     PiRedEquiv CC1 CC4 -> PiRedEquiv CC2 CC3 -> *)
  (*     PiRedEquiv (ContextCompose CC1 CC2) (ContextCompose CC3 CC4). *)
  (* Proof. *)
  (*   intros CC1 CC2 CC3 CC4 H H0. *)
  (*   transitivity (ContextCompose CC2 CC1). *)
  (*   apply ContextComposeSwapEquiv. *)
  (*   apply ContextComposeEquiv; auto. *)
  (* Qed. *)

  
  
  (* Lemma ContextFromListsEquiv : forall (CC : PiCalcRedContext), *)
  (*     PiRedEquiv CC (ContextFromLists (fst (ContextToLists CC)) (snd (ContextToLists CC))). *)
  (* Proof. *)
  (*   unfold ContextFromLists. *)
  (*   induction CC; simpl; auto with PiC. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite rev_app_distr. *)
  (*     rewrite LeftContextAppCompose. rewrite ContextComposeComm. *)
  (*     transitivity (ContextCompose CC (ParCtxt1 Hole p)); simpl; auto with PiC. *)
  (*     2: {transitivity (ContextCompose (ContextCompose (LeftContextFromList (rev (ProcessToList p))) (RightContextFromList l)) (LeftContextFromList (rev l0))). *)
  (*         rewrite <- ContextComposeComm. apply ComposeEquivBackwards; auto. *)
  (*         symmetry; apply LeftContextFromRevProcessList. *)
  (*     apply ContextComposeEquiv. apply ContextComposeSwapEquiv. reflexivity. } *)
  (*     clear IHCC l l0. induction CC; simpl; auto with PiC. *)
  (*     -- transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC (Par p p0)); auto with PiC. *)
  (*     -- transitivity (ParCtxt2 p0 (ParCtxt1 CC p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC p0) p); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC (Par p p0)); auto with PiC. *)
  (*   - destruct (ContextToLists CC); simpl in *. *)
  (*     rewrite RightContextAppCompose; rewrite <- ContextComposeComm. *)
  (*     transitivity (ContextCompose (ParCtxt2 p Hole) CC); [reflexivity|]. *)
  (*     apply ContextComposeEquiv; auto. symmetry; apply RightContextFromProcessList. *)
  (* Qed. *)

  (* Lemma ListPiEquivRev : forall l1 l2, ListPiEquiv l1 l2 -> ListPiEquiv (rev l1) (rev l2). *)
  (* Proof. *)
  (*   intros l1 l2 lequiv; induction lequiv; simpl; auto with PiC. *)
  (*   apply ListPiEquivDoubleApp; auto with PiC. *)
  (* Qed. *)

  (* Theorem FromEquivLists : forall l1 l2 l3 l4, *)
  (*     ListPiEquiv (l1 ++ l2) (l3 ++ l4) -> *)
  (*     PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4). *)
  (* Proof. *)
  (*   unfold ContextFromLists. *)
  (*   intros l1 l2 l3 l4 lequiv. *)
  (*   remember (l1 ++ l2). remember (l3 ++ l4). revert l1 l2 l3 l4 Heql Heql0. *)
  (*   induction lequiv. *)
  (*   - intros l1 l2 l3 l4 Heql Heql0. *)
  (*     symmetry in Heql; apply app_eq_nil in Heql; destruct Heql; subst. *)
  (*     symmetry in Heql0; apply app_eq_nil in Heql0; destruct Heql0; subst. *)
  (*     simpl. reflexivity. *)
  (*   - intros l1 l2 l3 l4 Heql Heql0. *)
  (*     destruct l1; destruct l3; subst; simpl in *. *)
  (*     -- apply LeftContextEquivLists; auto; subst. *)
  (*        apply ListPiEquivRev. *)
  (*        constructor; auto. *)
  (*     -- inversion Heql0; subst; simpl. *)
  (*        specialize (IHlequiv [] l l3 l4 eq_refl eq_refl). simpl in IHlequiv. *)
  (*        transitivity (ParCtxt2 P (LeftContextFromList (rev l))); auto with PiC. *)
  (*        rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole P) (LeftContextFromList (rev l))); *)
  (*          simpl; auto with PiC. *)
  (*        apply ContextComposeSwapEquiv; auto. *)
  (*     -- inversion Heql; subst; simpl. *)
  (*        specialize (IHlequiv l1 l2 [] l' eq_refl eq_refl); simpl in IHlequiv. *)
  (*        rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole Q) (LeftContextFromList (rev l'))); *)
  (*          [simpl; auto with PiC|]. *)
  (*        apply ContextComposeSwapEquiv. *)
  (*     -- inversion Heql; inversion Heql0; subst. *)
  (*        specialize (IHlequiv l1 l2 l3 l4 eq_refl eq_refl). *)
  (*        apply ParCtxtEquiv2; auto. *)
  (* Qed. *)
      
  (* Theorem ToListsEquiv : forall CC1 CC2, *)
  (*     ListPiEquiv (fst (ContextToLists CC1) ++ snd (ContextToLists CC1)) *)
  (*                 (fst (ContextToLists CC2) ++ snd (ContextToLists CC2)) *)
  (*     -> PiRedEquiv CC1 CC2. *)
  (* Proof. *)
  (*   intros CC1 CC2 H. apply FromEquivLists in H. *)
  (*   etransitivity; [| etransitivity; [exact H|]]; [| symmetry]; *)
  (*     apply ContextFromListsEquiv. *)
  (* Qed. *)

  (* Lemma RightEquivLeft : forall l, PiRedEquiv (RightContextFromList l) (LeftContextFromList l). *)
  (* Proof. *)
  (*   intro l; induction l; simpl. *)
  (*   reflexivity. *)
  (*   transitivity (ParCtxt1 (RightContextFromList l) a). apply ParCtxtSwitch2; reflexivity. *)
  (*   apply ParCtxtEquiv1; auto with PiC. *)
  (* Qed. *)

  (* Theorem FromNearlyEqualLists' : forall l1 l2 l3 l4, *)
  (*     l1 ++ rev l2 = l3 ++ rev l4 -> *)
  (*     PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4). *)
  (* Proof. *)
  (*   intros l1 l2 l3 l4 H. *)
  (*   unfold ContextFromLists. *)
  (*   transitivity (ContextCompose (LeftContextFromList l1) (LeftContextFromList (rev l2))). *)
  (*   apply ContextComposeEquiv; [|reflexivity]. apply RightEquivLeft. *)
  (*   rewrite <- LeftContextAppCompose. *)
  (*   transitivity (ContextCompose (LeftContextFromList l3) (LeftContextFromList (rev l4))). *)
  (*   rewrite <- LeftContextAppCompose. rewrite H. reflexivity. *)
  (*   apply ContextComposeEquiv; [|reflexivity]. symmetry. apply RightEquivLeft. *)
  (* Qed. *)

  (* Theorem FromNearlyEqualLists : forall l1 l2 l3 l4, *)
  (*     l1 ++ l2 = l3 ++  l4 -> *)
  (*     PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4). *)
  (* Proof. *)
  (*   intros l1 l2 l3 l4 H. *)
  (*   unfold ContextFromLists. *)
  (*   transitivity (ContextCompose (LeftContextFromList l1) (LeftContextFromList l2)). *)
  (*   apply ContextComposeEquiv. apply RightEquivLeft. symmetry; apply LeftContetFromRevList. *)
  (*   rewrite <- LeftContextAppCompose. *)
  (*   transitivity (ContextCompose (LeftContextFromList l3) (LeftContextFromList l4)). *)
  (*   rewrite <- LeftContextAppCompose; rewrite H; reflexivity. *)
  (*   apply ContextComposeEquiv. symmetry; apply RightEquivLeft. apply LeftContetFromRevList. *)
  (* Qed. *)

  (* Lemma TwoHoleTransfer : forall l P Q, *)
  (*     PiRedEquiv (ContextCompose (ContextCompose l (ParCtxt1 Hole P)) (ParCtxt1 Hole Q)) *)
  (*                (ParCtxt1 (ParCtxt1 l P) Q). *)
  (* Proof. *)
  (*   intros l P Q. *)
  (*   transitivity (ContextCompose (ParCtxt1 Hole Q) (ContextCompose l (ParCtxt1 Hole P))); *)
  (*     [apply ContextComposeSwapEquiv | simpl]. *)
  (*   apply ParCtxtEquiv1; auto with PiC. *)
  (*   transitivity (ContextCompose (ParCtxt1 Hole P) l); [apply ContextComposeSwapEquiv | simpl]; auto with PiC. *)
  (* Qed. *)
  (* Hint Resolve TwoHoleTransfer : PiC. *)
    
  (* Theorem FromPermutedLists : forall l1 l2 l3 l4, *)
  (*     Permutation (l1 ++ l2) *)
  (*                 (l3 ++ l4) *)
  (*     -> PiRedEquiv (ContextFromLists l1 l2) (ContextFromLists l3 l4). *)
  (* Proof. *)
  (*   intros l1 l2 l3 l4 H. *)
  (*   remember (l1 ++ l2) as l. remember (l3 ++ l4) as l'. *)
  (*   revert l1 l2 l3 l4 Heql Heql'. induction H; intros l1 l2 l3 l4 Heql Heql'. *)
  (*   - symmetry in Heql; symmetry in Heql'. apply app_eq_nil in Heql. *)
  (*     apply app_eq_nil in Heql'. destruct Heql; destruct Heql'; subst; simpl. *)
  (*     unfold ContextFromLists; simpl. reflexivity. *)
  (*   - destruct l1; destruct l3; simpl in *. *)
  (*     -- unfold ContextFromLists; simpl; subst. simpl. *)
  (*        repeat rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole x) (LeftContextFromList (rev l))). *)
  (*        apply ContextComposeSwapEquiv. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole x) (LeftContextFromList (rev l'))); *)
  (*          [|apply ContextComposeSwapEquiv]. *)
  (*        simpl. *)
  (*        apply ParCtxtEquiv1; auto with PiC. apply LeftContextPermLists; auto. *)
  (*        transitivity l. symmetry; apply Permutation_rev. transitivity l'; auto. *)
  (*        apply Permutation_rev. *)
  (*     -- simpl in *; subst. inversion Heql'; subst. *)
  (*        unfold ContextFromLists; simpl. *)
  (*        rewrite LeftContextAppCompose. simpl. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole p) (LeftContextFromList (rev l))); *)
  (*          [apply ContextComposeSwapEquiv|simpl]. *)
  (*        transitivity (ParCtxt2 p (LeftContextFromList (rev l))). *)
  (*        apply ParCtxtSwitch1; reflexivity. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        specialize (IHPermutation [] l l3 l4 eq_refl eq_refl); *)
  (*          unfold ContextFromLists in IHPermutation; simpl in *; auto. *)
  (*     -- simpl in *; subst. unfold ContextFromLists in *; simpl in *. *)
  (*        inversion Heql; subst. *)
  (*        rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ContextCompose (ParCtxt1 Hole p) (LeftContextFromList (rev l'))); *)
  (*          [simpl|apply ContextComposeSwapEquiv]. *)
  (*        transitivity (ParCtxt2 p (LeftContextFromList (rev l'))); auto with PiC. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        apply (IHPermutation l1 l2 [] l' eq_refl eq_refl). *)
  (*     -- inversion Heql; inversion Heql'; subst. *)
  (*        unfold ContextFromLists in *; simpl in *. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*   - destruct l1 as [| P l1]; [| destruct l1]. *)
  (*     all: destruct l3 as [| Q l3]; [|destruct l3]. *)
  (*     all: unfold ContextFromLists in *; simpl in *; subst; simpl. *)
  (*     -- repeat rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) x) y); *)
  (*          auto with PiC. *)
  (*        transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par x y)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) y) x); *)
  (*          [| symmetry]; auto with PiC. *)
  (*        transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par y x)); auto with PiC. *)
  (*     -- inversion Heql'; subst; simpl. *)
  (*        repeat rewrite LeftContextAppCompose; simpl. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) Q)  y); *)
  (*          auto with PiC. *)
  (*        transitivity (ParCtxt2 Q (ContextCompose (ParCtxt1 Hole y) (LeftContextFromList (rev l)))); [simpl | apply ParCtxtEquiv2; auto with PiC; apply ContextComposeSwapEquiv]. *)
  (*        transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par Q y)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 (LeftContextFromList (rev l)) y) Q); auto with PiC. *)
  (*        transitivity (ParCtxt1 (LeftContextFromList (rev l)) (Par y Q)); auto with PiC. *)
  (*     -- inversion Heql'; subst. *)
  (*        rewrite rev_app_distr. *)
  (*        repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; [eapply TwoHoleTransfer; auto with PiC|]. *)
  (*        etransitivity; [eapply ParCtxtComm12; reflexivity|]. *)
  (*        etransitivity; [|eapply ParCtxtComm21; reflexivity]. *)
  (*        etransitivity; [|eapply ParCtxtSwitch1; reflexivity]. *)
  (*        apply ParCtxtEquiv1; auto with PiC. apply ComposeEquivBackwards; auto with PiC. *)
  (*        symmetry. transitivity (LeftContextFromList l3). apply RightEquivLeft. *)
  (*        apply LeftContetFromRevList. *)
  (*     -- inversion Heql; subst. simpl. *)
  (*        repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; *)
  (*          [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv| reflexivity]|simpl]. *)
  (*        etransitivity; [| eapply ContextComposeSwapEquiv]; simpl. *)
  (*        etransitivity; *)
  (*          [| eapply ParCtxtEquiv1; [reflexivity| apply ContextComposeSwapEquiv]]. *)
  (*        etransitivity; [eapply ParCtxtSwitch2; reflexivity |]. *)
  (*        etransitivity; [eapply ParCtxtComm12; reflexivity |]. *)
  (*        etransitivity; [| eapply ParCtxtComm11; reflexivity]. *)
  (*        apply ParCtxtEquiv1; auto with PiC; reflexivity. *)
  (*     -- inversion Heql; inversion Heql'; subst; simpl. *)
  (*        repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; *)
  (*          [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity] |]; simpl. *)
  (*        etransitivity; *)
  (*          [| eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]]; simpl. *)
  (*        etransitivity; [eapply ParCtxtSwitch2; reflexivity|]. *)
  (*        etransitivity; [eapply ParCtxtComm12; reflexivity |]. *)
  (*        etransitivity; [|eapply ParCtxtSwitch1; reflexivity]. *)
  (*        etransitivity; [|eapply ParCtxtComm11; reflexivity]. *)
  (*        apply ParCtxtEquiv1; auto with PiC; reflexivity. *)
  (*     -- inversion Heql; inversion Heql'; subst; simpl. *)
  (*        rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; *)
  (*          [eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]|]; simpl. *)
  (*        etransitivity; *)
  (*          [eapply ParCtxtEquiv2; [| reflexivity]; eapply ParCtxtSwitch1; reflexivity |]. *)
  (*        etransitivity; [eapply ParCtxtComm22; reflexivity |]. *)
  (*        etransitivity; [|eapply ParCtxtComm21; reflexivity]. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        apply ComposeEquivBackwards; auto with PiC. *)
  (*        symmetry; etransitivity; [apply RightEquivLeft|]; apply LeftContetFromRevList. *)
  (*     -- inversion Heql; subst. *)
  (*        rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; [| symmetry; eapply TwoHoleTransfer]. *)
  (*        etransitivity; [eapply ParCtxtSwitch2; reflexivity|]. *)
  (*        etransitivity; *)
  (*          [eapply ParCtxtEquiv1; [ reflexivity|]; eapply ParCtxtSwitch2; reflexivity |]. *)
  (*        etransitivity; [eapply ParCtxtComm12; reflexivity |]. *)
  (*        etransitivity; [| eapply ParCtxtComm11; reflexivity]. *)
  (*        apply ParCtxtEquiv1; auto with PiC. *)
  (*        apply ComposeEquivBackwards; auto with PiC. *)
  (*        etransitivity; [apply RightEquivLeft| apply LeftContetFromRevList]. *)
  (*     -- inversion Heql; inversion Heql'; subst; simpl. *)
  (*        rewrite rev_app_distr; repeat rewrite LeftContextAppCompose; simpl. *)
  (*        etransitivity; *)
  (*          [| eapply ParCtxtEquiv2; [apply ContextComposeSwapEquiv|reflexivity]]; simpl. *)
  (*        etransitivity; *)
  (*          [| eapply ParCtxtEquiv2; [|reflexivity]; eapply ParCtxtSwitch2; reflexivity]. *)
  (*        etransitivity; [eapply ParCtxtComm22; reflexivity|]. *)
  (*        etransitivity; [|eapply ParCtxtComm21; reflexivity]. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        apply ComposeEquivBackwards; auto with PiC. *)
  (*        etransitivity; [apply RightEquivLeft | apply LeftContetFromRevList]. *)
  (*     -- inversion Heql; inversion Heql'; subst; simpl. *)
  (*        etransitivity; [eapply ParCtxtComm22; reflexivity|]. *)
  (*        etransitivity; [|eapply ParCtxtComm21; reflexivity]. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        fold (ContextFromLists l1 l2). fold (ContextFromLists l3 l4). *)
  (*        apply FromNearlyEqualLists; auto. *)
  (*   - specialize (IHPermutation1 l1 l2 [] l' Heql eq_refl). *)
  (*     specialize (IHPermutation2 [] l' l3 l4 eq_refl Heql'). *)
  (*     transitivity (ContextFromLists [] l'); auto. *)
  (* Qed. *)
  
  (* (* Definition NormalizeContext (CC : PiCalcRedContext)  : PiCalcRedContext :=  *) *)
  (* (*   RightContextFromList (fst (ContextToLists CC) ++ snd (ContextToLists CC)). *) *)
  
  (* (* Lemma NormalizeEquiv : forall CC, *) *)
  (* (*     PiRedEquiv CC (NormalizeContext CC). *) *)
  (* (* Proof. *) *)
  (* (*   unfold NormalizeContext; intro CC; induction CC; simpl. *) *)
  (* (*   - reflexivity. *) *)
  (* (*   - destruct (ContextToLists CC); simpl in *. *) *)
  (* (*     rewrite AppComm. rewrite RightContextAppCompose. *) *)
  (* (*     transitivity (ContextCompose CC (ParCtxt2 p Hole)). *) *)
  (* (*     2: { apply ContextComposeEquiv; auto. symmetry; apply RightContextFromProcessList. } *) *)
  (* (*     clear l l0 IHCC. induction CC; simpl; try reflexivity. *) *)
  (* (*     -- apply ParCtxtSwitch1; auto with PiC. *) *)
  (* (*     -- transitivity (ParCtxt1 (ParCtxt1 CC p) p0). *) *)
  (* (*        transitivity (ParCtxt1 CC (Par p0 p)). apply ParCtxtComm12; reflexivity. *) *)
  (* (*        transitivity (ParCtxt1 CC (Par p p0)). *) *)
  (* (*        apply ParCtxtEquiv1; auto with PiC; reflexivity. *) *)
  (* (*        apply ParCtxtComm11; reflexivity. *) *)
  (* (*        apply ParCtxtEquiv1; auto with PiC. *) *)
  (* (*     -- transitivity (ParCtxt2 p0 (ParCtxt1 CC p)); auto with PiC. *) *)
  (* (*        transitivity (ParCtxt1 (ParCtxt1 CC p0) p); auto with PiC. *) *)
  (* (*        transitivity (ParCtxt1 (ParCtxt1 CC p) p0); auto with PiC. *) *)
  (* (*        transitivity (ParCtxt1 CC (Par p0 p)); auto with PiC. *) *)
  (* (*        transitivity (ParCtxt1 CC (Par p p0)); auto with PiC. *) *)
  (* (*   - destruct (ContextToLists CC); simpl in *. *) *)
  (* (*     rewrite RightContextAppCompose. rewrite RightContextAppCompose. *) *)
  (* (*     rewrite <- ContextComposeComm. *) *)
  (* (*     rewrite <- RightContextAppCompose. *) *)
  (* (*     transitivity (ContextCompose (ParCtxt2 p Hole) CC); [reflexivity|]. *) *)
  (* (*     apply ContextComposeEquiv; auto. symmetry. apply RightContextFromProcessList. *) *)
  (* (* Qed. *) *)
  
  (* Lemma PermutationMiddle : forall {A : Type} (l1 l2 l3 : list A) (a : A), *)
  (*     Permutation (l1 ++ a :: l2) l3 *)
  (*     -> exists l4 l5, *)
  (*       l3 = l4 ++ a :: l5. *)
  (* Proof. *)
  (*   intros A l1 l2 l3 a H. *)
  (*   remember (l1 ++ a :: l2). revert l1 l2 a Heql. induction H; intros l1 l2 a Heql. *)
  (*   - symmetry in Heql; apply app_eq_nil in Heql; destruct Heql. *)
  (*     inversion H0. *)
  (*   - destruct l1; simpl in *; inversion Heql; subst. *)
  (*     exists []; exists l'; simpl; reflexivity. *)
  (*     destruct (IHPermutation l1 l2 a eq_refl) as [l3 H']; *)
  (*       destruct H' as [l4 H']; subst. *)
  (*     exists (a0 :: l3); exists l4; simpl; auto. *)
  (*   - destruct l1; simpl in *; inversion Heql; subst. *)
  (*     exists [x]; exists l; auto. *)
  (*     destruct l1; simpl in *; inversion H1; subst. *)
  (*     exists []; exists (a0 :: l2); auto. *)
  (*     exists (a1 :: a0 :: l1); exists l2; auto. *)
  (*   - specialize (IHPermutation1 l1 l2 a Heql). *)
  (*     destruct IHPermutation1 as [l3 H']; destruct H' as [l4 eq']. *)
  (*     apply (IHPermutation2 l3 l4); auto. *)
  (* Qed. *)

  (* Theorem ListPiMiddle : forall l1 l2 l3 P, *)
  (*     ListPiEquiv (l1 ++ P :: l2) l3 -> *)
  (*     exists l4 l5 Q, *)
  (*       P ≡π Q /\ l4 ++ Q :: l5 = l3 /\ ListPiEquiv (l1 ++ l2) (l4 ++ l5). *)
  (* Proof. *)
  (*   intro l1; induction l1; intros l2 l3 P equiv. *)
  (*   - simpl in equiv. inversion equiv; subst. *)
  (*     exists []; exists l'; exists Q; split; [|split]; auto. *)
  (*   - simpl in equiv. inversion equiv; subst. *)
  (*     apply IHl1 in H3. destruct H3 as [l4 H3]; destruct H3 as [l5 H3]; *)
  (*                         destruct H3 as [Q' H3]; destruct H3 as [equivPQ H3]; *)
  (*                           destruct H3 as [eq lequiv]. *)
  (*     exists (Q :: l4); exists l5; exists Q'; split; [| split]; subst; auto. *)
  (*     simpl. constructor; auto. *)
  (* Qed. *)

  (* Lemma ContextToListsCompose : forall CC1 CC2, *)
  (*     ContextToLists (ContextCompose CC1 CC2) = *)
  (*     (fst (ContextToLists CC1) ++ fst (ContextToLists CC2), snd (ContextToLists CC2) ++ snd(ContextToLists CC1)). *)
  (* Proof. *)
  (*   intro CC1; induction CC1; simpl. *)
  (*   - intro. rewrite app_nil_r;  apply surjective_pairing. *)
  (*   - intros CC2. *)
  (*     rewrite IHCC1; simpl. *)
  (*     destruct (ContextToLists CC1); simpl. rewrite AppComm; reflexivity. *)
  (*   - intro CC2. rewrite IHCC1; simpl. *)
  (*     destruct (ContextToLists CC1); simpl. rewrite AppComm. reflexivity. *)
  (* Qed. *)
      
  (* Lemma ContextToListFromLists : forall l1 l2, *)
  (*     ContextToLists (ContextFromLists l1 l2) = (flat_map ProcessToList l1, flat_map ProcessToList l2). *)
  (* Proof. *)
  (*   intros l1 l2. unfold ContextFromLists. *)
  (*   revert l2; induction l1; simpl; intros l2. *)
  (*   - induction l2; simpl; auto. *)
  (*     rewrite LeftContextAppCompose; simpl. *)
  (*     rewrite ContextToListsCompose; rewrite IHl2; simpl. *)
  (*     reflexivity. *)
  (*   - rewrite IHl1. reflexivity. *)
  (* Qed. *)
  (* Lemma ContextToListFromSingleThreadLists : forall l1 l2, *)
  (*     (forall P, In P l1 -> SingleThread P) -> *)
  (*     (forall P, In P l2 -> SingleThread P) ->  *)
  (*     ContextToLists (ContextFromLists l1 l2) = (l1, l2). *)
  (* Proof. *)
  (*   unfold ContextFromLists; intros l1; induction l1; simpl; intros l2 singles1 singles2. *)
  (*   - induction l2; simpl; auto. *)
  (*     rewrite LeftContextAppCompose; simpl. *)
  (*     rewrite ContextToListsCompose. rewrite IHl2. simpl. *)
  (*     rewrite SingleThreadToList; simpl; auto. *)
  (*     apply singles2; left; auto. *)
  (*     intros P H. apply singles2; right; auto. *)
  (*   - rewrite IHl1; auto. rewrite SingleThreadToList; auto. *)
  (* Qed. *)

  (* Lemma ProcessToListAllSingle : forall P Q, *)
  (*     In Q (ProcessToList P) -> SingleThread Q. *)
  (* Proof. *)
  (*   intro P; induction P; intros Q i; simpl in *; auto with PiC. *)
  (*   all: try (destruct i as [eq | f]; [| destruct f]; subst; constructor; fail). *)
  (*   apply in_app_or in i; destruct i; [apply IHP1 | apply IHP2]; auto. *)
  (* Qed. *)

  (* Lemma ProcessToListInj : forall P Q, ProcessToList P = ProcessToList Q -> P = Q. *)
  (* Proof. *)
  (*   intro P; induction P; intro Q; destruct Q; simpl; auto; intro H. *)
  (*   all: try (inversion H; fail). *)
  (*   all: try (symmetry in H; apply app_eq_unit in H; *)
  (*             destruct H as [H | H]; destruct H as [H1 H2]; *)
  (*             [apply ProcessToListNonNil in H1; destruct H1 *)
  (*             | apply ProcessToListNonNil in H2; destruct H2]; fail). *)
  (*   all: try (inversion H; subst; auto; fail). *)
  (*   all: try (apply app_eq_unit in H; *)
  (*             destruct H as [H | H]; destruct H as [H1 H2]; *)
  (*             [apply ProcessToListNonNil in H1; destruct H1 *)
  (*             | apply ProcessToListNonNil in H2; destruct H2]; fail). *)
  (* Abort. *)

  (* Lemma CCEquivInversion' : forall CC1 P Q, *)
  (*     (ApplyRedContext CC1 P) ≡π' Q *)
  (*     -> SingleThread P *)
  (*     -> exists CC2 Q', PiRedEquiv CC1 CC2 /\ P ≡π' Q' /\ ApplyRedContext CC2 Q' = Q. *)
  (* Proof. *)
  (*   intro CC1; induction CC1; intros P Q H H0. *)
  (*   - simpl in H. exists Hole; exists Q; split; [| split]; auto with PiC. *)
  (*   - simpl in H. inversion H; subst; try (apply IHCC1 in H3; auto). *)
  (*     all: try (destruct H3 as [CC2 H3]; destruct H3 as [Q' H3]; *)
  (*               destruct H3 as [Cequiv H3]; destruct H3 as [equiv' app]). *)
  (*     -- exists (ParCtxt1 CC2 Q2); exists Q'; split; [|split]; auto. *)
  (*        apply ParCtxtEquiv1; auto with PiC. simpl. rewrite app. reflexivity. *)
  (*     -- exists (ParCtxt2 Q2 CC2); exists Q'; split; [|split]; auto. *)
  (*        transitivity (ParCtxt1 CC2 Q2); auto with PiC. *)
  (*        simpl. rewrite app. reflexivity. *)
  (*     -- exists (ParCtxt1 (ParCtxt1 CC2 Q2) R2); exists Q'; split; [|split]; auto. *)
  (*        transitivity (ParCtxt1 CC2 (Par Q2 R2)); auto with PiC. *)
  (*        simpl. rewrite app. reflexivity. *)
  (*     -- assert (ApplyRedContext CC1 P ≡π' Par P2 Q2) as H5 by (rewrite <- H1; auto with PiC). *)
  (*        apply IHCC1 in H5; auto. *)
  (*        destruct H5 as [CC2 H5]; destruct H5 as [Q' H5]; *)
  (*          destruct H5 as [Cequiv H5]; destruct H5 as [equiv' app]. *)
  (*        destruct CC2; simpl in app; subst; *)
  (*          [apply SingleThreadEquiv' in equiv'; auto; inversion equiv'| |]. *)
  (*        all: inversion app; subst; clear app.          *)
  (*        exists (ParCtxt1 CC2 (Par Q2 R2)); exists Q'; split; [|split]; auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC2 Q2) R2); auto with PiC. *)
  (*        exists (ParCtxt2 P2 (ParCtxt1 CC2 R2)); exists Q'; split; [|split]; auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC2 R2) P2); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC2 (Par R2 P2)); auto with PiC. *)
  (*        transitivity (ParCtxt1 CC2 (Par P2 R2)); auto with PiC. *)
  (*        transitivity (ParCtxt1 (ParCtxt1 CC2 P2) R2); auto with PiC. *)
  (*        apply ParCtxtEquiv1; auto with PiC. *)
  (*        transitivity (ParCtxt2 P2 CC2); auto with PiC. *)
  (*   - simpl in H. inversion H; subst; try (apply IHCC1 in H5; auto). *)
  (*     all: try (destruct H5 as [CC2 H5]; destruct H5 as [Q' H5]; *)
  (*               destruct H5 as [Cequiv H5]; destruct H5 as [equiv' app]). *)
  (*     -- exists (ParCtxt2 P2 CC2); exists Q'; split; [| split]; auto with PiC. *)
  (*        simpl. rewrite app. auto. *)
  (*     -- exists (ParCtxt1 CC2 P2); exists Q'; split; [| split]; auto with PiC. *)
  (*        simpl; rewrite app; reflexivity. *)
  (*     -- assert (ApplyRedContext CC1 P ≡π' Par Q2 R2) as H1 *)
  (*           by (rewrite <- H2; auto with PiC). *)
  (*        apply IHCC1 in H1; auto. *)
  (*        destruct H1 as [CC2 H1]; destruct H1 as [Q' H1]; *)
  (*          destruct H1 as [Cequiv H1]; destruct H1 as [equiv' app]. *)
  (*        destruct CC2; simpl in app; subst; *)
  (*          [apply SingleThreadEquiv' in equiv'; auto; inversion equiv'| |]. *)
  (*        all: inversion app; subst; clear app. *)
  (*        exists (ParCtxt1 (ParCtxt2 P2 CC2) R2); exists Q'; split; [|split]; auto with PiC. *)
  (*        transitivity (ParCtxt2 R2 (ParCtxt2 P2 CC2)); auto with PiC. *)
  (*        transitivity (ParCtxt2 (Par R2 P2) CC2); auto with PiC. *)
  (*        transitivity (ParCtxt2 (Par P2 R2) CC2); auto with PiC. *)
  (*        transitivity (ParCtxt2 P2 (ParCtxt2 R2 CC2)); auto with PiC. *)
  (*        apply ParCtxtEquiv2; auto with PiC. *)
  (*        transitivity (ParCtxt1 CC2 R2); auto with PiC. *)
  (*        exists (ParCtxt2 (Par P2 Q2) CC2); exists Q'; split; [| split]; auto with PiC. *)
  (*        transitivity (ParCtxt2 P2 (ParCtxt2 Q2 CC2)); auto with PiC. *)
  (*     -- apply IHCC1 in H6; auto. *)
  (*        destruct H6 as [CC2 H6]; destruct H6 as [Q' H6]; *)
  (*          destruct H6 as [Cequiv H6]; destruct H6 as [equiv' app]. *)
  (*        exists (ParCtxt2 P2 (ParCtxt2 Q2 CC2)); exists Q'; split; [| split]; auto with PiC. *)
  (*        simpl. rewrite app. reflexivity. *)
  (* Qed. *)

  (* Lemma CCEquivInversion : forall CC1 P Q, *)
  (*     (ApplyRedContext CC1 P) ≡π Q *)
  (*     -> SingleThread P *)
  (*     -> exists CC2 Q', PiRedEquiv CC1 CC2 /\ P ≡π Q' /\ ApplyRedContext CC2 Q' = Q. *)
  (* Proof. *)
  (*   intros CC1 P Q equiv. *)
  (*   remember (ApplyRedContext CC1 P) as R. *)
  (*   revert CC1 P HeqR. induction equiv. *)
  (*   - intros CC1 P0 HeqR ST; subst. *)
  (*     apply CCEquivInversion' in H; auto. *)
  (*     destruct H as [CC2 H]; destruct H as [Q' H]; destruct H as [Cequiv H]; *)
  (*       destruct H as [equiv eq]. *)
  (*     exists CC2; exists Q'; split; [|split]; auto with PiC. *)
  (*   - intros CC1 S HeqR ST; subst. *)
  (*     apply CCEquivInversion' in H; auto. *)
  (*     destruct H as [CC2 H]; destruct H as [Q' H]; destruct H as [Cequiv H]; *)
  (*       destruct H as [equiv' eq]; subst. *)
  (*     specialize (IHequiv CC2 Q' eq_refl (SingleThreadEquiv' _ _ ST equiv')). *)
  (*     destruct IHequiv as [CC3 H]; destruct H as [R' H]; destruct H as [Cequiv2 H]; *)
  (*       destruct H as [equiv'' eq]; subst. *)
  (*     exists CC3; exists R'; split; [| split]; auto with PiC. *)
  (*     transitivity CC2; auto. *)
  (*     apply @PiEquivStep with (Q := Q'); auto. *)
  (* Qed. *)

  (* Theorem Equiv'ESubstStable : forall P Q σ, P ≡π' Q -> (P [πe| σ]) ≡π' (Q [πe| σ]). *)
  (* Proof. *)
  (*   intros P Q σ equiv; revert σ; induction equiv; intros σ; simpl; *)
  (*     auto with PiC. *)
  (* Qed. *)

  (* Theorem EquivESubstStable : forall P Q σ, P ≡π Q -> (P [πe| σ]) ≡π (Q [πe| σ]). *)
  (* Proof. *)
  (*   intros P Q σ equiv; revert σ; induction equiv; intros σ; simpl; *)
  (*     eapply Equiv'ESubstStable in H; eauto with PiC. *)
  (* Qed. *)

  (* Lemma Equiv'RenameStable : forall (P Q : Proc) (ξ : nat -> nat), *)
  (*     P ≡π' Q -> (P ⟨π| ξ⟩) ≡π' (Q ⟨π| ξ⟩). *)
  (* Proof. *)
  (*   intros P Q ξ equiv; revert ξ; induction equiv; intro ξ; simpl; auto with PiC. *)
  (* Qed. *)

  (* Lemma EquivRenameStable : forall (P Q : Proc) (ξ : nat -> nat), *)
  (*     P ≡π Q -> (P ⟨π| ξ⟩) ≡π (Q ⟨π| ξ⟩). *)
  (* Proof. *)
  (*   intros P Q ξ equiv; revert ξ; induction equiv; intro ξ; simpl; auto with PiC. *)
  (*   apply Equiv'RenameStable with (ξ := ξ) in H; auto with PiC. *)
  (*   transitivity (Q ⟨π|ξ⟩); auto. apply Equiv'RenameStable with (ξ := ξ) in H; auto with PiC. *)
  (* Qed.     *)

  (* Lemma ProcSubstUpEquivExt : forall (σ1 σ2 : nat -> Proc), *)
  (*     (forall n, σ1 n ≡π σ2 n) -> *)
  (*     forall n, ProcSubstUp σ1 n ≡π ProcSubstUp σ2 n. *)
  (* Proof. *)
  (*   intros σ1 σ2 H n. *)
  (*   unfold ProcSubstUp. destruct n; auto with PiC. *)
  (*   apply EquivRenameStable; auto. *)
  (* Qed. *)

  (* Theorem Equiv'SubstStable : forall P Q σ1 σ2, *)
  (*     P ≡π' Q -> *)
  (*     (forall n, σ1 n ≡π σ2 n) -> *)
  (*     (P [π| σ1]) ≡π (Q [π| σ2]). *)
  (* Proof. *)
  (*   intros P Q σ1 σ2 equiv; revert σ1 σ2; induction equiv; intros σ1 σ2 ext_equiv; simpl; *)
  (*     auto with PiC. *)
  (*   apply DefProcContext; [apply IHequiv1 | apply IHequiv2]; apply ProcSubstUpEquivExt; auto. *)
  (* Qed. *)

  (* Theorem EquivSubstStable : forall P Q σ1 σ2, *)
  (*     P ≡π Q -> *)
  (*     (forall n, σ1 n ≡π σ2 n) -> *)
  (*     (P [π| σ1]) ≡π (Q [π| σ2]). *)
  (* Proof. *)
  (*   intros P Q σ1 σ2 equiv; revert σ1 σ2; induction equiv; intros σ1 σ2 ext_equiv; *)
  (*     simpl; eapply Equiv'SubstStable in H; eauto with PiC. *)
  (*   transitivity (Q [π|σ2]); auto with PiC. *)
  (* Qed. *)

  (* Lemma EndEquivInv : forall P, EndProc ≡π P -> P = EndProc. *)
  (* Proof. *)
  (*   intros P equiv; remember EndProc as Q; revert HeqQ; induction equiv; intros HeqQ; *)
  (*     subst. *)
  (*   - inversion H; auto. *)
  (*   - inversion H; subst. apply IHequiv; reflexivity. *)
  (* Qed. *)

  (* Lemma VarEquivInv : forall n P, VarProc n ≡π P -> P = VarProc n. *)
  (* Proof. *)
  (*   intros n P equiv; remember (VarProc n) as Q; revert n HeqQ; induction equiv; *)
  (*     intros n HeqQ; subst. *)
  (*   - inversion H; subst; reflexivity. *)
  (*   - inversion H; subst. apply (IHequiv n); reflexivity. *)
  (* Qed. *)
  
  (* Lemma SendEquivInv : forall p e P Q, SendProc p e P ≡π Q -> exists Q', P ≡π Q' /\ Q = SendProc p e Q'. *)
  (* Proof. *)
  (*   intros p e P Q equiv. *)
  (*   remember (SendProc p e P) as R. *)
  (*   revert p e P HeqR; induction equiv; intros p e P0 HeqR; subst. *)
  (*   - inversion H; subst. exists P2; split; auto with PiC. *)
  (*   - inversion H; subst. destruct (IHequiv p e P2 eq_refl) as [Q' HQ']; *)
  (*                           destruct HQ' as [equiv' Req]; subst. *)
  (*     exists Q'; split; auto. apply @PiEquivStep with (Q := P2); auto with PiC. *)
  (* Qed. *)

  (* Lemma RecvEquivInv : forall p P Q, RecvProc p P ≡π Q -> exists Q', P ≡π Q' /\ Q = RecvProc p Q'. *)
  (* Proof. *)
  (*   intros p P Q equiv. *)
  (*   remember (RecvProc p P) as R; revert p P HeqR; induction equiv; intros p P0 HeqR; subst. *)
  (*   - inversion H; subst. exists P2; split; auto with PiC. *)
  (*   - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [Q' HQ']; destruct HQ'; subst. *)
  (*     exists Q'; split; eauto with PiC. *)
  (* Qed. *)

  (* Lemma IfThenElseEquivInv : forall e P Q R, IfThenElse e P Q ≡π R -> *)
  (*                                       exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = IfThenElse e P' Q'. *)
  (* Proof. *)
  (*   intros e P Q R equiv. *)
  (*   remember (IfThenElse e P Q) as S; revert e P Q HeqS; induction equiv; *)
  (*     intros e P0 Q0 HeqS; subst. *)
  (*   - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC. *)
  (*   - inversion H; subst; destruct (IHequiv e P2 Q2 eq_refl) as [P' IH]; *)
  (*       destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq]; *)
  (*         subst. *)
  (*     exists P'; exists Q'; split; [| split]; eauto with PiC. *)
  (* Qed. *)

  (* Lemma DefEquivInv : forall P Q R, *)
  (*     DefProc P Q ≡π R -> *)
  (*     exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = DefProc P' Q'. *)
  (* Proof. *)
  (*   intros P Q R equiv; remember (DefProc P Q) as S; revert P Q HeqS; *)
  (*     induction equiv; intros P0 Q0 HeqS; subst. *)
  (*   - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC. *)
  (*   - inversion H; subst; destruct (IHequiv P2 Q2 eq_refl) as [P' IH]; *)
  (*       destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq]; *)
  (*         subst. *)
  (*     exists P'; exists Q'; split; [| split]; eauto with PiC. *)
  (* Qed. *)

  (* Lemma EChoiceLEquivInv : forall p P Q, *)
  (*     EChoiceL p P ≡π Q -> *)
  (*     exists P', P ≡π P' /\ Q = EChoiceL p P'. *)
  (* Proof. *)
  (*   intros p P Q equiv; remember (EChoiceL p P) as R; revert p P HeqR; *)
  (*     induction equiv; intros p P0 HeqR; subst. *)
  (*   - inversion H; subst. exists P2; split; auto with PiC. *)
  (*   - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [P' IH]; destruct IH; subst. *)
  (*     exists P'; split; eauto with PiC. *)
  (* Qed. *)

  (* Lemma EChoiceREquivInv : forall p P Q, *)
  (*     EChoiceR p P ≡π Q -> *)
  (*     exists P', P ≡π P' /\ Q = EChoiceR p P'. *)
  (* Proof. *)
  (*   intros p P Q equiv; remember (EChoiceR p P) as R; revert p P HeqR; *)
  (*     induction equiv; intros p P0 HeqR; subst. *)
  (*   - inversion H; subst. exists P2; split; auto with PiC. *)
  (*   - inversion H; subst. destruct (IHequiv p P2 eq_refl) as [P' IH]; destruct IH; subst. *)
  (*     exists P'; split; eauto with PiC. *)
  (* Qed. *)

  (* Lemma IChoiceEquivInv : forall p P Q R, *)
  (*     IChoice p P Q ≡π R -> *)
  (*     exists P' Q', P ≡π P' /\ Q ≡π Q' /\ R = IChoice p P' Q'. *)
  (* Proof. *)
  (*   intros p P Q R equiv; remember (IChoice p P Q) as S; revert p P Q HeqS; *)
  (*     induction equiv; intros p P0 Q0 HeqS; subst. *)
  (*   - inversion H; subst. exists P2; exists Q2; split; [| split]; auto with PiC. *)
  (*   - inversion H; subst; destruct (IHequiv p P2 Q2 eq_refl) as [P' IH]; *)
  (*       destruct IH as [Q' IH]; destruct IH as [equivP IH]; destruct IH as [equivQ eq]; *)
  (*         subst. *)
  (*     exists P'; exists Q'; split; [| split]; eauto with PiC. *)
  (* Qed. *)

  (* (* Lemma SubstEquivInv : forall P σ Q, *) *)
  (* (*     P [π| σ] ≡π Q -> *) *)
  (* (*     exists P' σ', P ≡π P' /\ (forall n, σ n ≡π σ' n) /\ Q = P' [π|σ']. *) *)
  (* (* Proof. *) *)
  (* (*   intros P; induction P; intros σ Q equiv; simpl in *. *) *)
  (* (*   - exists EndProc; exists σ; split; [|split]; simpl; auto with PiC. *) *)
  (* (*     apply EndEquivInv; auto. *) *)
  (* (*   - exists (VarProc n); exists (fun m => if Nat.eq_dec n m *) *)
  (* (*                             then Q *) *)
  (* (*                             else σ m); split; [|split]; simpl; auto with PiC. *) *)
  (* (*     intro m; destruct (Nat.eq_dec n m); subst; auto with PiC. *) *)
  (* (*     destruct (Nat.eq_dec n n) as [_|neq]; [reflexivity|exfalso; apply neq; auto]. *) *)
  (* (*   -  *) *)
  
  (* Theorem PiCalcEquivStep : forall Π1 Π2 Π1' : L.t -> Proc, *)
  (*     (forall p : L.t, Π1 p ≡π Π1' p) -> *)
  (*     PiCalcStep Π1 Π2 -> *)
  (*     exists Π2', (forall p : L.t, Π2 p ≡π Π2' p) /\ PiCalcStep Π1' Π2'. *)
  (* Proof. *)
  (*   intros Π1 Π2 Π1' ext_equiv step; revert Π1' ext_equiv; induction step; *)
  (*     intros Π1' ext_equiv. *)
  (*   - remember (ext_equiv p) as equivp; clear Heqequivp. *)
  (*     rewrite H0 in equivp. *)
  (*     apply CCEquivInversion in equivp; [| simpl; auto]. *)
  (*     destruct equivp as [CC2 Hc]; destruct Hc as [Q' Hc]; *)
  (*       destruct Hc as [Cequiv Hc]; destruct Hc as [equiv eq]; subst. *)
  (*     destruct (SendEquivInv _ _ _ _ equiv) as [Q'' HQ'']; *)
  (*          destruct HQ'' as [equiv'' eqQ'']; subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 (SendProc q e' Q'') *)
  (*              else Π1' r); split. *)
  (*     -- intro r; destruct (L.eq_dec p r); subst. *)
  (*        rewrite H2. apply CCEquiv; auto with PiC. *)
  (*        transitivity (Π r). rewrite H1; auto with PiC. *)
  (*        apply ext_equiv. *)
  (*     -- apply CommEStep with (p := p) (q := q) (e := e) (e' := e') (P := Q'') (CC := CC2); *)
  (*          auto. *)
  (*        intros r H3; destruct (L.eq_dec p r); subst; *)
  (*          [exfalso; apply H3; auto | reflexivity]. *)
  (*        destruct (L.eq_dec p p); subst; auto. exfalso; apply n; auto. *)
  (*   - pose proof (ext_equiv p) as equivp. *)
  (*     rewrite H1 in equivp. *)
  (*     apply CCEquivInversion in equivp; [| simpl; auto]. *)
  (*     destruct equivp as [CC2 equivp]; destruct equivp as [Q' equivp]; *)
  (*       destruct equivp as [Cequiv equivp]; destruct equivp as [equivP eqp]. *)
  (*     pose proof (ext_equiv q) as equivq. *)
  (*     rewrite H2 in equivq. *)
  (*     apply CCEquivInversion in equivq; [| simpl; auto]. *)
  (*     destruct equivq as [CC3 equivq]; destruct equivq as [Q'' equivq]; *)
  (*       destruct equivq as [Cequiv' equivq]; destruct equivq as [equivQ eqq]. *)
  (*     destruct (SendEquivInv _ _ _ _ equivP) as [Q''' HQ''']; *)
  (*       destruct HQ''' as [equiv''' eqQ''']; subst. *)
  (*     destruct (RecvEquivInv _ _ _ equivQ) as [Q'''' HQ'''']; *)
  (*       destruct HQ'''' as [equiv'''' eqQ'''']; subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 Q''' *)
  (*              else if L.eq_dec q r *)
  (*                   then ApplyRedContext CC3 (Q'''' [πe|CommSubst v]) *)
  (*                   else Π1' r); split. *)
  (*     -- intros p0. destruct (L.eq_dec p p0); subst. *)
  (*        rewrite H4. apply CCEquiv; auto with PiC. *)
  (*        destruct (L.eq_dec q p0); subst. *)
  (*        rewrite H5. apply CCEquiv; auto with PiC. *)
  (*        apply EquivESubstStable; auto. *)
  (*        transitivity (Π p0); auto. rewrite H3; auto. reflexivity. *)
  (*     -- apply CommVStep with (v := v) (p := p)(q := q) (P := Q''') (Q := Q'''') (CC := CC2) (CC' := CC3); auto with PiC. *)
  (*        intros r H6 H7. destruct (L.eq_dec p r); subst; [exfalso; apply H6; auto|]. *)
  (*        destruct (L.eq_dec q r); subst; [exfalso; apply H7; auto|]. *)
  (*        reflexivity. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [reflexivity|exfalso; apply n; auto]. *)
  (*        destruct (L.eq_dec p q) as [eqpq|_]; subst; [exfalso; apply H; auto|]. *)
  (*        destruct (L.eq_dec q q) as [_|n];[reflexivity|exfalso; apply n; auto]. *)
  (*   - pose proof (ext_equiv p) as equivp. rewrite H0 in equivp. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 H']; destruct H' as [Q' H']; *)
  (*       destruct H' as [Cequiv H']; destruct H' as [equiv' eq']. *)
  (*     destruct (IfThenElseEquivInv _ _ _ _ equiv') as [P' H']; *)
  (*       destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq]; *)
  (*         subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 (IfThenElse e' P' R') *)
  (*              else Π1' r); split. *)
  (*     -- intro r; destruct (L.eq_dec p r); subst. *)
  (*        rewrite H2. apply CCEquiv; auto with PiC. *)
  (*        rewrite <- H1; auto. *)
  (*     -- apply IfEStep with (p := p) (e := e) (e' := e') (P := P') (Q := R') (CC := CC2); *)
  (*          auto with PiC. *)
  (*        intros r H3. *)
  (*        destruct (L.eq_dec p r) as [eq|_]; [exfalso; apply H3; auto|reflexivity]. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [reflexivity|exfalso;apply n; auto]. *)
  (*   - pose proof (ext_equiv p) as equivp. rewrite H in equivp. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv]; *)
  (*       destruct eqv as [Cequiv eqv]; destruct eqv as [IfEquiv eq]. *)
  (*     destruct (IfThenElseEquivInv _ _ _ _ IfEquiv) as [P' H']; *)
  (*       destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq']; *)
  (*         subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 P' *)
  (*              else Π1' r); split. *)
  (*     -- intro r; destruct (L.eq_dec p r); subst. *)
  (*        rewrite H1. apply CCEquiv; auto with PiC. *)
  (*        rewrite <- H0; auto with PiC. *)
  (*     -- apply IfTrueStep with (p := p) (P := P') (Q := R') (CC := CC2). *)
  (*        rewrite <- eq. reflexivity. *)
  (*        intros r n. destruct (L.eq_dec p r) as [eqrp|_]; *)
  (*                      [exfalso; apply n; auto| reflexivity]. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [reflexivity|exfalso; apply n; auto]. *)
  (*   - pose proof (ext_equiv p) as equivp. rewrite H in equivp. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv]; *)
  (*       destruct eqv as [Cequiv eqv]; destruct eqv as [IfEquiv eq]. *)
  (*     destruct (IfThenElseEquivInv _ _ _ _ IfEquiv) as [P' H']; *)
  (*       destruct H' as [R' H']; destruct H' as [equivP H']; destruct H' as [equivQ eq']; *)
  (*         subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 R' *)
  (*              else Π1' r); split. *)
  (*     -- intro r; destruct (L.eq_dec p r); subst. *)
  (*        rewrite H1. apply CCEquiv; auto with PiC. *)
  (*        rewrite <- H0; auto with PiC. *)
  (*     -- apply IfFalseStep with (p := p) (P := P') (Q := R') (CC := CC2). *)
  (*        rewrite <- eq. reflexivity. *)
  (*        intros r n. destruct (L.eq_dec p r) as [eqrp|_]; *)
  (*                      [exfalso; apply n; auto| reflexivity]. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [reflexivity|exfalso; apply n; auto]. *)
  (*   - pose proof (ext_equiv p) as equivp. rewrite H in equivp. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 eqv]; destruct eqv as [Q' eqv]; *)
  (*       destruct eqv as [Cequiv eqv]; destruct eqv as [DefEquiv eq]. *)
  (*     destruct (DefEquivInv _ _ _ DefEquiv) as [P' H']; *)
  (*       destruct H' as [R' H']; destruct H' as [equivP H']; *)
  (*         destruct H' as [equivR H']; subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 (R' [π|PiDefSubst P']) *)
  (*              else Π1' r); split. *)
  (*     -- intro r. destruct (L.eq_dec p r); subst. *)
  (*        rewrite H1. apply CCEquiv; auto with PiC. apply EquivSubstStable; auto. *)
  (*        unfold PiDefSubst. intro n; destruct n; auto with PiC. *)
  (*        apply EquivSubstStable; auto. *)
  (*        destruct n; auto with PiC. *)
  (*        rewrite <- H0; auto with PiC. *)
  (*     -- apply DefStep with (p := p) (P := P') (Q := R') (CC := CC2); auto with PiC. *)
  (*        intros r n; destruct (L.eq_dec p r) as [ e|_]; *)
  (*          [exfalso; apply n; auto|reflexivity]. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [reflexivity|exfalso; apply n; auto]. *)
  (*   - pose proof (ext_equiv p) as equivp; rewrite H0 in equivp. *)
  (*     pose proof (ext_equiv q) as equivq; rewrite H1 in equivq. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 ep]; destruct ep as [ECQ' ep]; *)
  (*       destruct ep as [Cequiv ep]; destruct ep as [ECequiv eqp]; subst. *)
  (*     apply CCEquivInversion in equivq; simpl; auto. *)
  (*     destruct equivq as [CC3 eq]; destruct eq as [ICQ' eq]; *)
  (*       destruct eq as [Cequiv' eq]; destruct eq as [ICequiv eqq]; subst. *)
  (*     destruct (EChoiceLEquivInv _ _ _ ECequiv) as [P' H']; *)
  (*       destruct H' as [equivP eq']; subst. *)
  (*     destruct (IChoiceEquivInv _ _ _ _ ICequiv) as [Q1' H']; *)
  (*       destruct H' as [Q2' H']; destruct H' as [equivQ1 H']; *)
  (*         destruct H' as [equivQ2 eq']; subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 P' *)
  (*              else if L.eq_dec q r *)
  (*                   then ApplyRedContext CC3 Q1' *)
  (*                   else Π1' r); split. *)
  (*     -- intro r. destruct (L.eq_dec p r); subst. *)
  (*        rewrite H3. apply CCEquiv; auto with PiC. *)
  (*        destruct (L.eq_dec q r); subst. rewrite H4. apply CCEquiv; auto with PiC. *)
  (*        rewrite <- H2; auto. *)
  (*     -- apply ChooseLStep with (p := p) (q := q) (P := P') (Q1 := Q1') (Q2 := Q2') *)
  (*                               (CC := CC2) (CC' := CC3); auto. *)
  (*        intros r H5 H6. *)
  (*        destruct (L.eq_dec p r) as [ e|_]; [exfalso; apply H5; auto|]. *)
  (*        destruct (L.eq_dec q r) as [ e|_]; [exfalso; apply H6; auto|]. *)
  (*        reflexivity. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (*        destruct (L.eq_dec p q) as [ e|_]; [exfalso; apply H; auto|]. *)
  (*        destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (*   - pose proof (ext_equiv p) as equivp; rewrite H0 in equivp. *)
  (*     pose proof (ext_equiv q) as equivq; rewrite H1 in equivq. *)
  (*     apply CCEquivInversion in equivp; simpl; auto. *)
  (*     destruct equivp as [CC2 ep]; destruct ep as [ECQ' ep]; *)
  (*       destruct ep as [Cequiv ep]; destruct ep as [ECequiv eqp]; subst. *)
  (*     apply CCEquivInversion in equivq; simpl; auto. *)
  (*     destruct equivq as [CC3 eq]; destruct eq as [ICQ' eq]; *)
  (*       destruct eq as [Cequiv' eq]; destruct eq as [ICequiv eqq]; subst. *)
  (*     destruct (EChoiceREquivInv _ _ _ ECequiv) as [P' H']; *)
  (*       destruct H' as [equivP eq']; subst. *)
  (*     destruct (IChoiceEquivInv _ _ _ _ ICequiv) as [Q1' H']; *)
  (*       destruct H' as [Q2' H']; destruct H' as [equivQ1 H']; *)
  (*         destruct H' as [equivQ2 eq']; subst. *)
  (*     exists (fun r => if L.eq_dec p r *)
  (*              then ApplyRedContext CC2 P' *)
  (*              else if L.eq_dec q r *)
  (*                   then ApplyRedContext CC3 Q2' *)
  (*                   else Π1' r); split. *)
  (*     -- intro r. destruct (L.eq_dec p r); subst. *)
  (*        rewrite H3. apply CCEquiv; auto with PiC. *)
  (*        destruct (L.eq_dec q r); subst. rewrite H4. apply CCEquiv; auto with PiC. *)
  (*        rewrite <- H2; auto. *)
  (*     -- apply ChooseRStep with (p := p) (q := q) (P := P') (Q1 := Q1') (Q2 := Q2') *)
  (*                               (CC := CC2) (CC' := CC3); auto. *)
  (*        intros r H5 H6. *)
  (*        destruct (L.eq_dec p r) as [ e|_]; [exfalso; apply H5; auto|]. *)
  (*        destruct (L.eq_dec q r) as [ e|_]; [exfalso; apply H6; auto|]. *)
  (*        reflexivity. *)
  (*        destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (*        destruct (L.eq_dec p q) as [ e|_]; [exfalso; apply H; auto|]. *)
  (*        destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto]. *)
  (*        reflexivity. *)
  (* Qed. *)

  Definition BothIChoice {A : Type} (P Q : Proc) (default : A) (f : L.t -> Proc -> Proc -> L.t -> Proc -> Proc -> A)  : A :=
    match P with
    | IChoice p P1 P2 =>
      match Q with
      | IChoice q Q1 Q2 => f p P1 P2 q Q1 Q2
      | _ => default
      end
    | _ => default
    end.
  Arguments BothIChoice : simpl nomatch.

  Inductive Action : Set :=
    EndAct : Action
  | UnknownAct : Action
  | VarAct : nat -> Action
  | DefAct : Proc -> Action
  | SendAct : L.t -> Expr -> Action
  | RecvAct : L.t -> Action
  | EChoiceLAct : L.t -> Action
  | EChoiceRAct : L.t -> Action
  | IChoiceAct : L.t -> Action
  | IfThenElseAct : Expr -> Action.

  Definition ActionEqDec : forall A1 A2 : Action, {A1 = A2} + {A1 <> A2}.
    decide equality; try (apply L.eq_dec); try (apply ProcEqDec); try (apply ExprEqDec); apply Nat.eq_dec.
  Defined.

  (* Definiting this via Equations gives us access to the graph automatically. *)
  Equations ActionOf (P : Proc) : Action :=
    {
      ActionOf EndProc := EndAct;
      ActionOf (VarProc n) := VarAct n;
      ActionOf (DefProc P Q) := DefAct P;
      ActionOf (SendProc p e P) := SendAct p e;
      ActionOf (RecvProc p P) := RecvAct p;
      ActionOf (EChoiceL p P) := EChoiceLAct p;
      ActionOf (EChoiceR p P) := EChoiceRAct p;
      ActionOf (IChoice p P Q) := IChoiceAct p;
      ActionOf (IfThenElse e P Q) := IfThenElseAct e
    }.

  (*
    Things got really complicated when using the correct-by-construction type I had for different ICTrees before.
    So, I'm doing more idiomatic Coq and defining a "IsDifferentICTree" proposition.
    I'm then going to need functions to put an ICTree in order, etc.
   *)
  Inductive IChoiceTree : Set :=
    ICTLeaf : L.t -> Proc -> Proc -> IChoiceTree
  | ICTBranch : L.t -> IChoiceTree -> IChoiceTree -> IChoiceTree.

  Fixpoint IChoiceTreeToProc (t : IChoiceTree) : Proc :=
    match t with
    | ICTLeaf p P Q => IChoice p P Q
    | ICTBranch p l r => IChoice p (IChoiceTreeToProc l) (IChoiceTreeToProc r)
    end.
  
  Definition FirstDecider (t : IChoiceTree) : L.t :=
    match t with
    | ICTLeaf p _ _ => p
    | ICTBranch p _ _ => p
    end.

  Inductive IsOrderedICTree : IChoiceTree -> Prop :=
    IsOrderedLeaf : forall p P Q, IsOrderedICTree (ICTLeaf p P Q)
  | IsOrderedBranch : forall p t1 t2, (FirstDecider t1) <= p -> (FirstDecider t2) <= p -> IsOrderedICTree t1 -> IsOrderedICTree t2 -> IsOrderedICTree (ICTBranch p t1 t2).

  Program Fixpoint CheckOrderedICTree (t : IChoiceTree) : {IsOrderedICTree t} + {~ IsOrderedICTree t} :=
    match t with
    | ICTLeaf p P Q => left (IsOrderedLeaf p P Q)
    | ICTBranch p t1 t2 =>
      match L.compare (FirstDecider t1) p with
      | left lt1 =>
        match L.tOrderDec (FirstDecider t2) p with
        | left lt2 =>
          match CheckOrderedICTree t1 with
          | left ord1 =>
            match CheckOrderedICTree t2 with
            | left ord2 => left (IsOrderedBranch p t1 t2 lt1 lt2 ord1 ord2)
            | right n => right _
            end
          | right n => right _
          end
        | right n => right _
        end
      | right n => right _
      end
    end.
  Next Obligation.
    intro H; inversion H; auto.
  Defined.
  Next Obligation.
    intro H; inversion H; auto.
  Defined.
  Next Obligation.
    intro H; inversion H; auto.
  Defined.
  Next Obligation.
    intro H; inversion H; auto.
  Defined.
    
  Inductive IsBalancedICTreewrt : IChoiceTree -> list L.t -> Prop :=
    IsBalancedLeaf : forall p P Q, IsBalancedICTreewrt (ICTLeaf p P Q) [p]
  | IsBalancedBranch : forall p t1 t2 l, IsBalancedICTreewrt t1 l -> IsBalancedICTreewrt t2 l -> IsBalancedICTreewrt (ICTBranch p t1 t2) (p :: l).

  Program Fixpoint CheckBalancedICTreewrt (t : IChoiceTree) (l : list L.t) : {IsBalancedICTreewrt t l} + {~ IsBalancedICTreewrt t l} :=
    match t with
    | ICTLeaf p P Q =>
      match l with
      | [] => right _
      | [q] => match L.eq_dec p q with
              | left e => left (IsBalancedLeaf p P Q)
              | right n => right _
              end
      | _ => right _
      end
    | ICTBranch p t1 t2 =>
      match l with
      | [] => right _
      | q :: l' => match L.eq_dec p q with
                 | left e => match CheckBalancedICTreewrt t1 l' with
                            | left b1 =>
                              match CheckBalancedICTreewrt t2 l' with
                              | left b2 => left (IsBalancedBranch p t1 t2 l' b1 b2)
                              | right n => right _
                              end
                            | right n => right _
                            end
                 | right n => right _
                 end
      end
    end.
  Next Obligation.
    intro H; inversion H.
  Defined.
  Next Obligation.
    intro H; inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    intro H1; inversion H1; subst; apply (H p); auto.
  Defined.
  Next Obligation.
    split; [intro q |]; intro eq; discriminate eq.
  Defined.
  Next Obligation.
    intro H; inversion H.
  Defined.
  Next Obligation.
    intro H; inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    intro H; inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    intro H; inversion H; subst; apply n; auto.
  Defined.

  Fixpoint FindBalancingList (t : IChoiceTree) : option (list L.t) :=
    match t with
    | ICTLeaf p _ _ => Some [p]
    | ICTBranch p t1 t2 =>
      match FindBalancingList t1 with
      | Some l => match CheckBalancedICTreewrt t2 l with
                 | left _ => Some (p :: l)
                 | right _ => None
                 end
      | None => None
      end
    end.

  Lemma FindBalancingListSound : forall (t : IChoiceTree) (l : list L.t), FindBalancingList t = Some l -> IsBalancedICTreewrt t l.
  Proof.
    intro t; induction t; intros l eq; cbn in *.
    - inversion eq; subst; clear eq; constructor.
    - destruct (FindBalancingList t1); [| inversion eq].
      destruct (CheckBalancedICTreewrt t2 l0); [| inversion eq]. inversion eq; subst; clear eq.
      constructor; auto.
  Qed.

  Lemma FindBalancingListComplete : forall (t : IChoiceTree) (l : list L.t), IsBalancedICTreewrt t l -> FindBalancingList t = Some l.
  Proof.
    intro t; induction t; intros l b; inversion b; subst; cbn; auto.
    specialize (IHt1 l0 H3); rewrite IHt1.
    destruct (CheckBalancedICTreewrt t2 l0) as [_|n]; [|exfalso; apply n]; auto.
  Qed.    

  Definition IsBalancedICTree : IChoiceTree -> Prop := fun t => exists l, IsBalancedICTreewrt t l.

  Program Definition CheckBalancedICTree : forall t : IChoiceTree, {IsBalancedICTree t} + {~ IsBalancedICTree t} :=
    fun t => match FindBalancingList t with
          | Some l => left (ex_intro _ l _)
          | None => right _
          end.
  Next Obligation.
    apply FindBalancingListSound; symmetry; auto.
  Defined.
  Next Obligation.
    intro H; inversion H. apply FindBalancingListComplete in H0.
    assert (Some x = None) as eq by (transitivity (FindBalancingList t); auto); discriminate eq.
  Defined.

  Fixpoint NumberOfChoices (t : IChoiceTree) (p : L.t) : nat :=
    match t with
    | ICTLeaf q _ _ => if L.eq_dec p q then 1 else 0
    | ICTBranch q t1 t2 => (if L.eq_dec p q then 1 else 0) + (Nat.max (NumberOfChoices t1 p) (NumberOfChoices t2 p))
    end.

  Inductive IsDecider : L.t -> IChoiceTree -> Prop :=
  | IsLeafDecider : forall p P Q, IsDecider p (ICTLeaf p P Q)
  | IsCurrentBranchDecider : forall p t1 t2, IsDecider p (ICTBranch p t1 t2)
  | IsLeftChildDecider : forall p q t1 t2, IsDecider p t1 -> IsDecider p (ICTBranch q t1 t2)
  | IsRightChildDecider : forall p q t1 t2, IsDecider p t2 -> IsDecider p (ICTBranch q t1 t2).

  Program Fixpoint IsDeciderDec (p : L.t) (t : IChoiceTree) : {IsDecider p t} + {~ IsDecider p t} :=
    match t with
    | ICTLeaf q P Q =>
      match L.eq_dec p q with
      | left e => left (IsLeafDecider p P Q)
      | right n => right (fun id => _)
      end
    | ICTBranch q t1 t2 =>
      match L.eq_dec p q with
      | left e => left (IsCurrentBranchDecider p t1 t2)
      | right n1 =>
        match IsDeciderDec p t1 with
        | left id1 => left (IsLeftChildDecider p q t1 t2 id1)
        | right n2 =>
          match IsDeciderDec p t2 with
          | left id2 => left (IsRightChildDecider p q t1 t2 id2)
          | right n3 => right (fun id => _)
          end
        end
      end
    end.
  Next Obligation.
    inversion id; subst; apply n; reflexivity.
  Defined.
  Next Obligation.
    inversion id; subst; [apply n1 | apply n2 | apply n3]; auto.
  Defined.      

  Theorem IsDeciderOfBalancedwrt : forall (p : L.t) (t1 t2 : IChoiceTree) (l : list L.t), IsBalancedICTreewrt t1 l -> IsBalancedICTreewrt t2 l -> IsDecider p t1 -> IsDecider p t2.
  Proof.
    intros p t1 t2 l ibt1 ibt2 id1; revert t2 l ibt1 ibt2; induction id1; intros t2' l0 ibt1 ibt2; inversion ibt1; subst; inversion ibt2; subst; try (constructor; auto; fail).
    - inversion H4.
    - apply IsLeftChildDecider. apply IHid1 with (l := l); auto.
    - inversion H4.
    - apply IsRightChildDecider. apply IHid1 with (l := l); auto.
  Qed.

  Fixpoint Deciders (t : IChoiceTree) : list L.t :=
    match t with
    | ICTLeaf p _ _ => [p]
    | ICTBranch p t1 t2 => p :: Deciders t1
    end.

  Theorem BalancedDecidersBalancingList : forall (t : IChoiceTree), IsBalancedICTree t -> FindBalancingList t = Some (Deciders t).
  Proof.
    intro t; induction t; intros ibt; cbn; auto.
    inversion ibt; subst. cbn in H. destruct (FindBalancingList t1) eqn:eq; [destruct (CheckBalancedICTreewrt t2 l) |]; inversion H; subst.
    - apply FindBalancingListSound in eq. specialize (IHt1 (ex_intro _ l eq)); inversion IHt1; subst; reflexivity.
    - assert (Some l = Some l0) as eq' by (transitivity (FindBalancingList t1); apply FindBalancingListComplete in H4; auto); inversion eq'; subst; clear eq'.
      exfalso; apply n; exact H5.
    - apply FindBalancingListComplete in H4; discriminate (eq_trans (eq_sym H4) eq).
  Qed.

  Theorem DecidersSound : forall (t : IChoiceTree) (p : L.t), In p (Deciders t) -> IsDecider p t.
  Proof.
    intro t; induction t as [q P Q | q t1 IHt1 t2 IHt2]; intros p i; cbn in i; destruct i as [eq | i]; subst; [ constructor | inversion i | constructor|].
    apply IsLeftChildDecider; apply IHt1; exact i.
  Qed.

  Theorem BalancedDecidersComplete : forall (t : IChoiceTree) (p : L.t), IsBalancedICTree t -> IsDecider p t -> In p (Deciders t).
  Proof.
    intro t; induction t as [q P Q | q t1 IHt1 t2 IHt2]; intros p ibt decp; cbn in *.
    left; inversion decp; reflexivity.
    inversion decp; auto; subst; right; apply IHt1; auto.
    unfold IsBalancedICTree in ibt. destruct ibt as [l ibt]; inversion ibt; subst. exists l0; auto.
    destruct ibt as [l ibt]; inversion ibt; subst. exists l0; auto.
    destruct ibt as [l ibt]; inversion ibt; subst.
    apply IsDeciderOfBalancedwrt with (t1 := t2) (l := l0); auto.
  Qed.

  Lemma ThisIsDumb : RoleMap.key = Role.
    unfold RoleMap.key. unfold RoleOrderedType.t.

  Record DecisionType (t : IChoiceTree) : Type := {
    raw_type : RoleMap.t nat;
    all_deciders : forall p : Role, IsDecider p t -> RoleMap.mem p raw_type = true
    }.
  
  Inductive IsSameActionTreeA : IChoiceTree -> Action -> Prop :=
    IsSameActionTreeLeaf : forall p P Q A, ActionOf P = A -> ActionOf Q = A -> IsSameActionTreeA (ICTLeaf p P Q) A
  | IsSameActionTreeBranch : forall p t1 t2 A, IsSameActionTreeA t1 A -> IsSameActionTreeA t2 A -> IsSameActionTreeA (ICTBranch p t1 t2) A.

  Program Fixpoint CheckSameActionTreeA (t : IChoiceTree) (A : Action) : {IsSameActionTreeA t A} + {~ IsSameActionTreeA t A} :=
    match t with
    | ICTLeaf p P Q =>
      match ActionEqDec (ActionOf P) A with
      | left eq1 =>
        match ActionEqDec (ActionOf Q) A with
        | left eq2 => left (IsSameActionTreeLeaf p P Q A eq1 eq2)
        | right n => right _
        end  
      | right n => right _
      end
    | ICTBranch p t1 t2 =>
      match CheckSameActionTreeA t1 A with
      | left ista1 =>
        match CheckSameActionTreeA t2 A with
        | left ista2 => left (IsSameActionTreeBranch p t1 t2 A ista1 ista2)
        | right n => right _
        end
      | right n => right _
      end
    end.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.
  Next Obligation.
    inversion H; subst; apply n; auto.
  Defined.

  Fixpoint FindOnlyAction (t : IChoiceTree) : option Action :=
    match t with
    | ICTLeaf _ P Q =>
      if ActionEqDec (ActionOf P) (ActionOf Q) then Some (ActionOf P) else None
    | ICTBranch _ t1 t2 =>
      match FindOnlyAction t1 with
      | Some A => if CheckSameActionTreeA t2 A then Some A else None
      | None => None
      end
    end.

  Lemma FindOnlyActionSound : forall (t : IChoiceTree) (A : Action), FindOnlyAction t = Some A -> IsSameActionTreeA t A.
  Proof.
    intros t A eq; induction t as [p P Q | p t1 IHt1 t2 IHt2]; cbn in eq.
    destruct (ActionEqDec (ActionOf P) (ActionOf Q)); inversion eq; constructor; auto.
    destruct (FindOnlyAction t1) as [B|]; [destruct (CheckSameActionTreeA t2 B)|]; inversion eq; subst.
    clear eq; specialize (IHt1 eq_refl); constructor; auto.
  Qed.

  Lemma FindOnlyActionComplete : forall (t : IChoiceTree) (A : Action), IsSameActionTreeA t A -> FindOnlyAction t = Some A.
  Proof.
    intros t A isat; induction isat as [p P Q A eq1 eq2 | p t1 t2 A isat1 IHisat1 isat2 IHisat2]; cbn.
    destruct (ActionEqDec (ActionOf P) (ActionOf Q)); subst; auto; exfalso; apply n; auto.
    rewrite IHisat1. destruct (CheckSameActionTreeA t2 A); auto; exfalso; apply n; auto.
  Qed.
  
  Definition IsSameActionTree : IChoiceTree -> Prop := fun t : IChoiceTree => exists A : Action, IsSameActionTreeA t A.

  Definition CheckSameActionTree : forall t : IChoiceTree, {IsSameActionTree t} + {~ IsSameActionTree t}.
    intro t. destruct (FindOnlyAction t) as [A|] eqn:eq; [left; exists A; apply FindOnlyActionSound; auto|right].
    intro H; unfold IsSameActionTree in H; destruct H as [A H]; apply FindOnlyActionComplete in H.
    assert (Some A = None) as H' by (transitivity (FindOnlyAction t); auto); discriminate H'.
  Defined.

  Definition IsSameTree : IChoiceTree -> Prop := fun t : IChoiceTree => IsSameActionTree t /\ IsOrderedICTree t /\ IsBalancedICTree t.
  Definition CheckSameTree : forall t : IChoiceTree, {IsSameTree t} + {~ IsSameTree t}.
    intro t.
    destruct (CheckSameActionTree t); [ | right; intro ist; unfold IsSameTree in ist; destruct ist; apply n; auto].
    destruct (CheckOrderedICTree t); [ | right; intro ist; destruct ist as [_ H]; destruct H; apply n; auto].
    destruct (CheckBalancedICTree t); [ | right; intro ist; destruct ist as [_ H]; destruct H; apply n; auto].
    left; split; [| split]; auto.
  Defined.

  Definition IsDifferentTree : IChoiceTree -> Prop := fun t : IChoiceTree => IsOrderedICTree t /\ (~IsSameActionTree t \/ ~IsBalancedICTree t).
  Definition CheckDifferentTree : forall t : IChoiceTree, {IsDifferentTree t} + {~ IsDifferentTree t}.
    intro t.
    destruct (CheckOrderedICTree t) as [ord | n]; [ | right; intro idt; destruct idt as [ord _]; apply n; exact ord].
    destruct (CheckSameActionTree t) as [sat | n]; [|left; split; [|left]; auto].
    destruct (CheckBalancedICTree t) as [bal | n]; [|left; split; [|right]; auto].
    right; intro idt; destruct idt as [_ H]; destruct H as [n | n]; apply n; auto.
  Defined.
  
  (* SameTree l A is the type of ichoice trees such that every option has the same action.
     Here, l is the list of principals that participate in the tree.
   *)
  Inductive SameTree : list Role -> Action -> Set :=
    SameLeaf : forall (p : Role) (P Q : Proc) (A : Action), ActionOf P = A -> ActionOf Q = A -> SameTree [p] A
  | SameBranch : forall (p : Role) {l : list Role} {A : Action}, (forall q, In q l -> q ≤r p) -> SameTree l A -> SameTree l A -> SameTree (p :: l) A.

  Equations SameTreeToProc {l : list Role} {A : Action} (st : SameTree l A) : Proc :=
    {
      SameTreeToProc (SameLeaf p P Q _ _ _) := IChoice p P Q;
      SameTreeToProc (SameBranch p _ ll rr) := IChoice p (SameTreeToProc ll) (SameTreeToProc rr)
    }.

  Equations FirstDecider {l : list Role} {A : Action} (st : SameTree l A) : Role :=
    {
      FirstDecider (SameLeaf p _ _ _ _ _) := p;
      FirstDecider (SameBranch p _ ll rr) := p
    }.

  Lemma FirstDeciderHead : forall (l : list Role) {A : Action} (st : SameTree l A), exists l', l = (FirstDecider st) :: l'.
  Proof.
    intros l A st. funelim (FirstDecider st); simp FirstDecider; [exists [] | exists l0]; reflexivity.
  Qed.

  Lemma SameTreeListSorted : forall (l : list Role) {A : Action}, SameTree l A -> Sorted (fun p q => q ≤r p) l.
  Proof.
    intros l A st; induction st. constructor; constructor. constructor; auto.
    destruct l; constructor. apply r. left; reflexivity.
  Qed.

  Fixpoint SameTreeSize {l : list Role} {A : Action} (st : SameTree l A) : nat :=
    match st with
    | SameLeaf p P Q A x x0 => 1
    | SameBranch p _ ll rr => S (SameTreeSize ll + SameTreeSize rr)
    end.

  Definition SameTreeExt : Set := {l : list Role & {A : Action & SameTree l A}}.
  
  Inductive DiffTree : Role -> Set :=
    DiffLeaf : forall (p : Role) (P Q : Proc),
      ActionOf P <> ActionOf Q -> DiffTree p
  | DiffDiffTree : forall (p : Role) {q r : Role} (dt1 : DiffTree q) (dt2 : DiffTree r),
      q ≤r p -> r ≤r p -> DiffTree p
  | SameDiffTree : forall (p : Role) {q : Role} {l : list Role} {A : Action}  (st : SameTree l A) (dt : DiffTree q),
      q ≤r p -> (FirstDecider st) ≤r p -> DiffTree p
  | DiffSameTree : forall (p : Role) {q : Role} {l : list Role} {A : Action} (dt : DiffTree q) (st : SameTree l A),
      q ≤r p -> (FirstDecider st) ≤r p -> DiffTree p
  | SameSameTreeDiffAction : forall (p : Role) {l1 l2 : list Role} {A1 A2 : Action} (st1 : SameTree l1 A1) (st2 : SameTree l2 A2),
      (FirstDecider st1) ≤r p -> (FirstDecider st2) ≤r p -> A1 <> A2 -> DiffTree p
  | SameSameTreeDiffList : forall (p : Role) {l1 l2 : list Role} {A1 A2 : Action} (st1 : SameTree l1 A1) (st2 : SameTree l2 A2),
      (FirstDecider st1) ≤r p -> (FirstDecider st2) ≤r p -> l1 <> l2 -> DiffTree p.

  Definition DiffTreeExt : Set := {p : Role & DiffTree p}.

  Fixpoint DiffTreeSize {p : Role} (dt : DiffTree p) : nat :=
    match dt with
    | DiffLeaf p P Q x => 1
    | DiffDiffTree p dt1 dt2 _ _ => S (DiffTreeSize dt1 + DiffTreeSize dt2)
    | SameDiffTree p st dt _ _ => S (SameTreeSize st + DiffTreeSize dt)
    | DiffSameTree p dt st _ _ => S (DiffTreeSize dt + SameTreeSize st)
    | SameSameTreeDiffAction p st1 st2 _ _ _ => S (SameTreeSize st1 + SameTreeSize st2)
    | SameSameTreeDiffList p st1 st2 _ _ _ => S (SameTreeSize st1 + SameTreeSize st2)
    end.

  Fixpoint DiffTreeToProc {p : Role} (dt : DiffTree p) : Proc :=
    match dt with
    | DiffLeaf p P Q _ => IChoice p P Q
    | DiffDiffTree p ll rr _ _ => IChoice p (DiffTreeToProc ll) (DiffTreeToProc rr)
    | SameDiffTree p ll rr _ _ => IChoice p (SameTreeToProc ll) (DiffTreeToProc rr)
    | DiffSameTree p ll rr _ _ => IChoice p (DiffTreeToProc ll) (SameTreeToProc rr)
    | SameSameTreeDiffAction p ll rr _ _ _ => IChoice p (SameTreeToProc ll) (SameTreeToProc rr)
    | SameSameTreeDiffList p ll rr _ _ _ => IChoice p (SameTreeToProc ll) (SameTreeToProc rr)
    end.

  Definition ICTree : Set := SameTreeExt + DiffTreeExt.

  Show Match sigT.
  Program Fixpoint TreeBranch (p : Role) (t1 : ICTree) (t2 : ICTree) : ICTree :=
    match t1 with
    | inl (existT _ l1 (existT _ A1 st1)) =>
      match t2 with
      | inl (existT _ l2 (existT _ A2 st2)) =>
        match ActionEqDec A1 A2 with
        | left e => _
        | right n => _
        end
      | inr (existT _ p2 dt2) => _
      end
    | inr (existT _ p1 dt1) =>
      match t2 with
      | inl (existT _ l2 (existT _ A2 st2)) => _
      | inr (existT _ p2 dt2) => _
      end
    end.
  Next Obligation.


  Inductive Justification : Set :=
    InvolvedSend : Expr -> Justification
  | InvolvedRecv : Justification
  | InvolvedECL : Justification
  | InvolvedECR : Justification
  | InvolvedIC : Justification
  | Different : forall {p : Role}, DiffTree p -> Justification.

  Inductive Justifies : Justification -> Role -> Proc -> Proc -> Prop :=
    ISJust : forall p e P Q, Justifies (InvolvedSend e) p (SendProc p e P) (SendProc p e Q)
  | IRJust : forall p P Q, Justifies InvolvedRecv p (RecvProc p P) (RecvProc p Q)
  | IECLJust : forall p P Q, Justifies InvolvedECL p (EChoiceL p P) (EChoiceL p Q)
  | IECRJust : forall p P Q, Justifies InvolvedECR p (EChoiceR p P) (EChoiceR p Q)
  | IICJust : forall p P1 Q1 P2 Q2, Justifies InvolvedIC p (IChoice p P1 Q1) (IChoice p P2 Q2)
  | DifferentJust : forall p P Q (d : DiffTree p), (DiffTreeToProc d = IChoice p P Q) -> Justifies (Different d) p P Q.

  Inductive DiffOrSameTree : Set :=
    ItsAST : forall (l : list Role) (A : Action), SameTree l A -> DiffOrSameTree
  | ItsADT : forall {p : Role}, DiffTree p -> DiffOrSameTree.

    Fixpoint ProcSize (P : Proc) : nat :=
    match P with
    | EndProc => 1
    | VarProc n => 1
    | DefProc P Q => 1 + (ProcSize P) + (ProcSize Q)
    | SendProc p e P => 1 + (ProcSize P)
    | RecvProc p P => 1 + (ProcSize P)
    | EChoiceL p P => 1 + (ProcSize P)
    | EChoiceR p P => 1 + (ProcSize P)
    | IChoice p P Q => 1 + (ProcSize P) + (ProcSize Q)
    | IfThenElse e P Q => 1 + (ProcSize P) + (ProcSize Q)
    end.

  Equations toDiffOrSameTree (p : Role) (P Q : Proc) : DiffOrSameTree by wf (ProcSize P + ProcSize Q) lt :=
    {
      toDiffOrSameTree p EndProc EndProc := ItsAST _ EndAct (SameLeaf p EndProc EndProc EndAct eq_refl eq_refl);
      toDiffOrSameTree p EndProc _ := ItsADT (DiffLeaf p EndProc Q _);
      toDiffOrSameTree p (VarProc n) (VarProc n) := ItsAST [p] (VarAct n) (SameLeaf p (VarProc n) (VarProc n) (VarAct n) eq_refl eq_refl);
      toDiffOrSameTree p (VarProc n) _ := ItsADT (DiffLeaf p (VarProc n) Q _);
      toDiffOrSameTree p (DefProc P Q1) (DefProc P Q2) := ItsAST [p] (DefAct P) (SameLeaf p (DefProc P Q1) (DefProc P Q2) (DefAct P) eq_refl eq_refl);
      toDiffOrSameTree p (DefProc P Q1) _ := ItsADT (DiffLeaf p (DefProc P Q1) Q _);
      toDiffOrSameTree p (SendProc q e P) (SendProc q e Q) := ItsAST [p] (SendAct q e) (SameLeaf p (SendProc q e P) (SendProc q e Q) (SendAct q e) eq_refl eq_refl);
      toDiffOrSameTree p (SendProc q e P) _ := ItsADT (DiffLeaf p (SendProc q e P) Q _);
      toDiffOrSameTree p (RecvProc q P) (RecvProc q Q) := ItsAST _ (RecvAct q) (SameLeaf p (RecvProc q P) (RecvProc q Q) (RecvAct q) eq_refl eq_refl);
      toDiffOrSameTree p (RecvProc q P) _ := ItsADT (DiffLeaf p (RecvProc q P) Q _);
      toDiffOrSameTree p (EChoiceL q P) (EChoiceL q Q) := ItsAST _ (EChoiceLAct q) (SameLeaf p (EChoiceL q P) (EChoiceL q Q) (EChoiceLAct q) eq_refl eq_refl);
      toDiffOrSameTree p (EChoiceL q P) _ := ItsADT (DiffLeaf p (EChoiceL q P) Q _);
      toDiffOrSameTree p (EChoiceR q P) (EChoiceR q Q) := ItsAST _ (EChoiceRAct q) (SameLeaf p (EChoiceR q P) (EChoiceR q Q) (EChoiceRAct q) eq_refl eq_refl);
      toDiffOrSameTree p (EChoiceR q P) _ := ItsADT (DiffLeaf p (EChoiceR q P) Q _);
      toDiffOrSameTree p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) := ItsAST _ (IfThenElseAct e) (SameLeaf p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) (IfThenElseAct e) eq_refl eq_refl);
      toDiffOrSameTree p (IfThenElse e P1 Q1) _ := ItsADT (DiffLeaf p (IfThenElse e P1 Q1) Q _);
      toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) with toDiffOrSameTree q P1 Q1 :=
        {
        toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) with toDiffOrSameTree q P2 Q2 :=
          {
          toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 A2 st2) with ActionEqDec A1 A2 :=
            {
            toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 ?(A1) st2) (left eq_refl) with list_eq_dec L.eq_dec l1 l2 :=
              {
              toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST ?(l1) ?(A1) st2) (left eq_refl) (left eq_refl) := ItsAST _ _ (SameBranch _ _ st1 st2);
              toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 ?(A1) st2) (left eq_refl) (right n) := ItsADT (SameSameTreeDiffList _ st1 st2 _ _ n)
              };
            toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 A2 st2) (right n) := (ItsADT (SameSameTreeDiffAction _ st1 st2 _ _ n))
            };
          toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsADT dt2) := (ItsADT (SameDiffTree _ st1 dt2 _ _))
          };
        toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsADT dt1) := _
        };
      toDiffOrSameTree p (IChoice q P1 Q1) _ := ItsADT (DiffLeaf p (IChoice q P1 Q1) Q _)
    }.
  
  Equations justify (p : Role) (P Q : Proc) : option Justification :=
    {
      justify p (SendProc p e P) (SendProc p e Q) := Some (InvolvedSend p e);
      justify p (RecvProc p P) (RecvProc p Q) := Some (InvolvedRecv);
      justify p (EChoiceL p P) (EChoiceL p Q) := Some (InvolvedECL);
      justify _ _ _ := None
    }.
  
  Inductive ICTreeA : (list Role) -> Action -> Set :=
    LeafTreeEnd        : forall p, ICTreeA [p] EndAct
  | LeafTreeVar        : forall p n, ICTreeA [p] (VarAct n)
  | LeafTreeDef        : forall p P, Proc -> Proc ->
                              ICTreeA [p] (DefAct P)
  | LeafTreeSend       : forall p q e, Proc -> Proc ->
                                  ICTreeA [p] (SendAct q e)
  | LeafTreeRecv       : forall p q, Proc -> Proc ->
                                ICTreeA [p] (RecvAct q)
  | LeafTreeEChoiceL   : forall p q, Proc -> Proc ->
                                ICTreeA [p] (EChoiceLAct q)
  | LeafTreeEChoiceR   : forall p q, Proc -> Proc ->
                                ICTreeA [p] (EChoiceRAct q)
  | LeafTreeIChoice    : forall p q, Proc -> Proc -> Proc -> Proc ->
                              ICTreeA [p] (IChoiceAct q)
  | LeafTreeIfThenElse : forall p e, Proc -> Proc -> Proc -> Proc ->
                                ICTreeA [p] (IfThenElseAct e)
  | LeafTreeMixed      : forall p, Proc -> Proc -> ICTreeA [p] UnknownAct
  | ICTreeCons         : forall p l A, (forall q, In q l -> p ≤r q) ->
                                  ICTreeA l A -> ICTreeA l A -> ICTreeA (p :: l) A.

  Theorem ICTreeASorted : forall l A, ICTreeA l A -> Sorted (fun p q => p ≤r q) l.
  Proof.
    intros l A t; induction t; auto.
    constructor; auto.
    clear IHt1 IHt2 t1 t2 A.
    induction l; auto. constructor; auto.
    apply r; left; reflexivity.
  Qed.

  Fixpoint ForgetAction {l : list Role} {A : Action} (t : ICTreeA l A)
    : ICTreeA l UnknownAct
    := match t with
      | LeafTreeEnd p => LeafTreeMixed p (EndProc) (EndProc)
      | LeafTreeVar p n => LeafTreeMixed p (VarProc n) (VarProc n)
      | LeafTreeDef p P Q1 Q2 => LeafTreeMixed p (DefProc P Q1) (DefProc P Q2)
      | LeafTreeSend p q e P1 P2 => LeafTreeMixed p (SendProc q e P1) (SendProc q e P2)
      | LeafTreeRecv p q P1 P2 => LeafTreeMixed p (RecvProc q P1) (RecvProc q P2)
      | LeafTreeEChoiceL p q P1 P2 => LeafTreeMixed p (EChoiceL q P1) (EChoiceL q P2)
      | LeafTreeEChoiceR p q P1 P2 => LeafTreeMixed p (EChoiceR q P1) (EChoiceR q P2)
      | LeafTreeIChoice p q P1 Q1 P2 Q2 =>
        LeafTreeMixed p (IChoice q P1 Q1) (IChoice q P2 Q2)
      | LeafTreeIfThenElse p e P1 Q1 P2 Q2 =>
        LeafTreeMixed p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2)
      | LeafTreeMixed p P1 P2 => LeafTreeMixed p P1 P2
      | ICTreeCons p l A lt t1 t2 =>
        ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)
      end.

  Fixpoint InsertRole (p : Role) (l : list Role) : list Role :=
    match l with
    | [] => [p]
    | q :: l => if RoleOrderDec q p
              then q :: (InsertRole p l)
              else p :: q :: l
    end.

  Lemma InInsertRole : forall (p : Role) (l : list Role) (q : Role), In q (InsertRole p l) <-> p = q \/ In q l.
  Proof.
    intros p l; induction l; simpl; intro q; split; auto; intro H.
    all: destruct (RoleOrderDec a p); simpl; auto.
    - destruct H. right; left; auto. apply IHl in H; destruct H; [left | right; right]; auto.
    - destruct H; [right | destruct H; [left | right]]; auto; apply IHl; [left | right]; auto.
  Qed.

  Lemma SortedLeast : forall {A : Type} (R : A -> A -> Prop) (Rtrans : forall a b c : A, R a b -> R b c -> R a c) (a : A) (l : list A), Sorted R (a :: l) -> forall b : A, In b l -> R a b.
  Proof.
    intros A R Rtrans a l std b I.
    induction l; [inversion I|].
    destruct I; subst; [inversion std; subst; inversion H2; subst; auto|].
    apply IHl; auto.
    inversion std; subst; inversion H2; subst.
    constructor; auto.
    inversion H3; subst. destruct l; [inversion H|].
    inversion H5; subst. constructor. eapply Rtrans; eauto.
  Qed.
  
  Lemma InsertRoleSorted : forall (p : Role) (l : list Role),
      Sorted (fun p q => p ≤r q) l -> Sorted (fun p q => p ≤r q) (InsertRole p l).
  Proof.
    intros p l; revert p; induction l as [| q l]; intros p std; simpl; auto.
    destruct (RoleOrderDec q p); constructor; auto.
    - apply IHl; inversion std; auto.
    - assert (InsertRole p l = InsertRole p l) as H by reflexivity; revert H; generalize (InsertRole p l) at 2 3.
      intros l0 e; destruct l0; constructor.
      inversion std; subst.
      assert (In r0 (InsertRole p l)) as I by (rewrite e; left; reflexivity).
      apply InInsertRole in I; destruct I; subst; auto.
      specialize (IHl p H1).
      apply SortedLeast with (b := r0) in std; auto.
      exact RoleOrderTrans.
    - destruct (RoleOrderTotal p q); [constructor | exfalso; apply n]; auto.
  Qed.

  Fixpoint FlattenICTA {l : list Role} {A : Action} (t : ICTreeA l A) : Proc :=
    match t with
    | LeafTreeEnd p => IChoice p EndProc EndProc
    | LeafTreeVar p n => IChoice p (VarProc n) (VarProc n)
    | LeafTreeDef p P Q1 Q2 => IChoice p (DefProc P Q1) (DefProc P Q2)
    | LeafTreeSend p q e P1 P2 => IChoice p (SendProc q e P1) (SendProc q e P2)
    | LeafTreeRecv p q P1 P2 => IChoice p (RecvProc q P1) (RecvProc q P2)
    | LeafTreeEChoiceL p q P1 P2 => IChoice p (EChoiceL q P1) (EChoiceL q P2)
    | LeafTreeEChoiceR p q P1 P2 => IChoice p (EChoiceR q P1) (EChoiceR q P2)
    | LeafTreeIChoice p q P1 Q1 P2 Q2 => IChoice p (IChoice q P1 Q1) (IChoice q P2 Q2)
    | LeafTreeIfThenElse p e P1 Q1 P2 Q2 =>
      IChoice p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2)
    | LeafTreeMixed p P1 P2 => IChoice p P1 P2
    | ICTreeCons p l A lt t1 t2 =>
      IChoice p (FlattenICTA t1) (FlattenICTA t2)
    end.

  Record ICTree (l : list Role) : Set :=
    mkTree { TheAction : Action ;
             TheTree   : ICTreeA l TheAction
           }.
  Arguments TheAction [l].
  Arguments TheTree [l].

  Definition FlattenICTree {l : list Role} (t : ICTree l) : Proc :=
    FlattenICTA (TheTree t).

  Definition ICTEnd : forall p : Role, ICTree [p]  :=
    fun p => mkTree [p] EndAct (LeafTreeEnd p).

  Definition ICTVar : forall p : Role, nat -> ICTree [p] :=
    fun p n => mkTree _ _ (LeafTreeVar p n).

  Definition ICTDef : forall p : Role, Proc -> Proc -> Proc -> ICTree [p] :=
    fun p P Q1 Q2 => mkTree _ _ (LeafTreeDef p P Q1 Q2).

  Definition ICTSend : forall p : Role, Role -> Expr -> Proc -> Proc -> ICTree [p] :=
    fun p q e P1 P2 => mkTree _ _ (LeafTreeSend p q e P1 P2).

  Definition ICTRecv : forall p : Role, Role -> Proc -> Proc -> ICTree [p] :=
    fun p q P1 P2 => mkTree _ _ (LeafTreeRecv p q P1 P2).

  Definition ICTEChoiceL : forall p : Role, Role -> Proc -> Proc -> ICTree [p] :=
    fun p q P1 P2 => mkTree _ _ (LeafTreeEChoiceL p q P1 P2).

  Definition ICTEChoiceR : forall p : Role, Role -> Proc -> Proc -> ICTree [p] :=
    fun p q P1 P2 => mkTree _ _ (LeafTreeEChoiceR p q P1 P2).

  Definition ICTIChoice : forall p : Role, Role -> Proc -> Proc -> Proc -> Proc -> ICTree [p] :=
    fun p q P1 Q1 P2 Q2 => mkTree _ _ (LeafTreeIChoice p q P1 Q1 P2 Q2).

  Definition ICTITE : forall p : Role, Expr -> Proc -> Proc -> Proc -> Proc -> ICTree [p] :=
    fun p e P1 Q1 P2 Q2 => mkTree _ _ (LeafTreeIfThenElse p e P1 Q1 P2 Q2).

  Definition ICTMixed : forall p : Role, Proc -> Proc -> ICTree [p] :=
    fun p P1 P2 => mkTree _ _ (LeafTreeMixed p P1 P2).

  Equations ICTConsA : forall (p : Role) (l : list Role) (A1 A2 : Action),
      (forall q, In q l -> p ≤r q) -> ICTreeA l A1 -> ICTreeA l A2 -> ICTree (p :: l) :=
    ICTConsA p l EndAct EndAct lt t1 t2 :=
      mkTree _ _ (ICTreeCons p l EndAct lt t1 t2) ;
    ICTConsA p l (VarAct n) (VarAct m) lt t1 t2 with Nat.eq_dec n m => {
      ICTConsA p l (VarAct n) (VarAct ?(n)) lt t1 t2 (left eq_refl) :=
        mkTree _ _ (ICTreeCons p l (VarAct n) lt t1 t2) ;
      ICTConsA p l (VarAct n) (VarAct m) lt t1 t2 (right _) :=
        mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
    ICTConsA p l (DefAct P1) (DefAct P2) lt t1 t2 with ProcEqDec P1 P2 =>
    {
      ICTConsA p l (DefAct P1) (DefAct ?(P1)) lt t1 t2 (left eq_refl) := mkTree _ _ (ICTreeCons p l (DefAct P1) lt t1 t2);
      ICTConsA p l (DefAct P1) (DefAct P2) lt t1 t2 (right _) :=
        mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
    }; 
    ICTConsA p l (SendAct q e) (SendAct r e') lt t1 t2 with L.eq_dec q r => {
        ICTConsA p l (SendAct q e) (SendAct ?(q) e') lt t1 t2 (left eq_refl) with ExprEqDec e e' => {
          ICTConsA p l (SendAct q e) (SendAct ?(q) ?(e)) lt t1 t2 (left eq_refl) (left eq_refl) :=
            mkTree _ _ (ICTreeCons p l (SendAct q e) lt t1 t2);
          ICTConsA p l (SendAct q e) (SendAct ?(q) e') lt t1 t2 (left eq_refl) (right _) :=
            mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1 ) (ForgetAction t2))
        };
        ICTConsA p l (SendAct q e) (SendAct r e') lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1 ) (ForgetAction t2))
      };
    ICTConsA p l (RecvAct q) (RecvAct r) lt t1 t2 with L.eq_dec q r => {
        ICTConsA p l (RecvAct q) (RecvAct ?(q)) lt t1 t2 (left eq_refl) :=
          mkTree _ _ (ICTreeCons p l  (RecvAct q) lt t1 t2);
        ICTConsA p l _ _ lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
   ICTConsA p l (EChoiceLAct q) (EChoiceLAct r) lt t1 t2 with L.eq_dec q r => {
        ICTConsA p l (EChoiceLAct q) (EChoiceLAct ?(q)) lt t1 t2 (left eq_refl) :=
          mkTree _ _ (ICTreeCons p l ((EChoiceLAct q)) lt t1 t2);
        ICTConsA p l _ _ lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
   ICTConsA p l (EChoiceRAct q) (EChoiceRAct r) lt t1 t2 with L.eq_dec q r => {
        ICTConsA p l (EChoiceRAct q) (EChoiceRAct ?(q)) lt t1 t2 (left eq_refl) :=
          mkTree _ _ (ICTreeCons p l ((EChoiceRAct q)) lt t1 t2);
        ICTConsA p l _ _ lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
   ICTConsA p l (IChoiceAct q) (IChoiceAct r) lt t1 t2 with L.eq_dec q r => {
        ICTConsA p l (IChoiceAct q) (IChoiceAct ?(q)) lt t1 t2 (left eq_refl) :=
          mkTree _ _ (ICTreeCons p l ((IChoiceAct q)) lt t1 t2);
        ICTConsA p l _ _ lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
   ICTConsA p l (IfThenElseAct e1) (IfThenElseAct e2) lt t1 t2 with ExprEqDec e1 e2 => {
        ICTConsA p l (IfThenElseAct e1) (IfThenElseAct ?(e1)) lt t1 t2 (left eq_refl) :=
          mkTree _ _ (ICTreeCons p l ((IfThenElseAct e1)) lt t1 t2);
        ICTConsA p l _ _ lt t1 t2 (right _) :=
          mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2))
      };
   ICTConsA p l _ _  lt t1 t2 :=
     mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)).

  Definition ICTCons : forall (p : Role) (l : list Role),
      (forall q, In q l -> p ≤r q) -> ICTree l -> ICTree l -> ICTree (p :: l) :=
    fun p l lt t1 t2 => match t1 with
                     | mkTree _ A1 t1 =>
                       match t2 with
                       |mkTree _ A2 t2 => ICTConsA p l A1 A2 lt t1 t2
                       end
                     end.
        
  Equations Sapling : forall (p : Role), Proc -> Proc -> ICTree [p] :=
    {
      Sapling p EndProc EndProc := ICTEnd p;
      Sapling p (VarProc n) (VarProc m) with Nat.eq_dec n m =>
      {
        Sapling p (VarProc n) (VarProc ?(n)) (left eq_refl) := ICTVar p n;
        Sapling p (VarProc n) (VarProc m) (right _) := ICTMixed p (VarProc n) (VarProc m)
      };
      Sapling p (DefProc P1 Q1) (DefProc P2 Q2) with ProcEqDec P1 P2 =>
      {
        Sapling p (DefProc P1 Q1) (DefProc ?(P1) Q2) (left eq_refl) := ICTDef p P1 Q1 Q2;
        Sapling p (DefProc P1 Q1) (DefProc P2 Q2) (right _) := ICTMixed p (DefProc P1 Q1) (DefProc P2 Q2)
      };
      Sapling p (SendProc q e1 P1) (SendProc r e2 P2) with L.eq_dec q r =>
      {
        Sapling p (SendProc q e1 P1) (SendProc ?(q) e2 P2) (left eq_refl) with ExprEqDec e1 e2 =>
        {
          Sapling p (SendProc q e1 P1) (SendProc ?(q) ?(e1) P2) (left eq_refl) (left eq_refl) := ICTSend p q e1 P1 P2;
          Sapling p (SendProc q e1 P1) (SendProc ?(q) e2 P2) (left eq_refl) (right _) :=
            ICTMixed p (SendProc q e1 P1) (SendProc q e2 P2)
        };
        Sapling p (SendProc q e1 P1) (SendProc r e2 P2) (right _) :=
          ICTMixed p (SendProc q e1 P1) (SendProc r e2 P2)
      };
      Sapling p (RecvProc q P1) (RecvProc r P2) with L.eq_dec q r =>
      {
        Sapling p (RecvProc q P1) (RecvProc ?(q) P2) (left eq_refl) :=
          ICTRecv p q P1 P2;
        Sapling p (RecvProc q P1) (RecvProc r P2) (right _) :=
          ICTMixed p (RecvProc q P1) (RecvProc r P2)
      };
      Sapling p (EChoiceL q P1) (EChoiceL r P2) with L.eq_dec q r =>
      {
        Sapling p (EChoiceL q P1) (EChoiceL ?(q) P2) (left eq_refl) :=
          ICTEChoiceL p q P1 P2;
        Sapling p (EChoiceL q P1) (EChoiceL r P2) (right _) :=
          ICTMixed p (EChoiceL q P1) (EChoiceL r P2)
      };
      Sapling p (EChoiceR q P1) (EChoiceR r P2) with L.eq_dec q r =>
      {
        Sapling p (EChoiceR q P1) (EChoiceR ?(q) P2) (left eq_refl) :=
          ICTEChoiceR p q P1 P2;
        Sapling p (EChoiceR q P1) (EChoiceR r P2) (right _) :=
          ICTMixed p (EChoiceR q P1) (EChoiceR r P2)
      };
      Sapling p (IChoice q P1 Q1) (IChoice r P2 Q2) with L.eq_dec q r =>
      {
        Sapling p (IChoice q P1 Q1) (IChoice ?(q) P2 Q2) (left eq_refl) :=
          ICTIChoice p q P1 Q1 P2 Q2;
        Sapling p (IChoice q P1 Q1) (IChoice r P2 Q2) (right _) :=
          ICTMixed p (IChoice q P1 Q1) (IChoice r P2 Q2)
      };
      Sapling p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2) with ExprEqDec e1 e2 =>
      {
        Sapling p (IfThenElse e1 P1 Q1) (IfThenElse ?(e1) P2 Q2) (left eq_refl) :=
          ICTITE p e1 P1 Q1 P2 Q2;
        Sapling p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2) (right _) :=
          ICTMixed p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2)
      };
      Sapling p P Q := ICTMixed p P Q
    }.

  Derive NoConfusion for Action.

  Equations Lefts {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)) : ICTree l :=
    {
      Lefts (LeafTreeIChoice q p P1 Q1 P2 Q2) := Sapling q P1 P2;
      Lefts (ICTreeCons q l _ lt t1' t2') := ICTCons q l lt (Lefts t1') (Lefts t2')
    }.
  Equations Rights {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)) : ICTree l :=
    {
      Rights (LeafTreeIChoice q p P1 Q1 P2 Q2) := Sapling q Q1 Q2;
      Rights (ICTreeCons q l _ lt t1' t2') := ICTCons q l lt (Rights t1') (Rights t2')
    }.
  
  (* If every leaf is an internal choice, merges that choice into the tree. *)
  Equations MergeTree {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p))
    : ICTree (InsertRole p l) :=
    {
      MergeTree (LeafTreeIChoice q p P1 Q1 P2 Q2) with RoleOrderDec q p =>
      {
        MergeTree(LeafTreeIChoice q p P1 Q1 P2 Q2) (left o) :=
          ICTCons q [p] _ (Sapling p P1 P2) (Sapling p Q1 Q2);
        MergeTree(LeafTreeIChoice q p P1 Q1 P2 Q2) (right n) :=
          ICTCons p [q] _ (Sapling q P1 Q1) (Sapling q P2 Q2)
      };
      MergeTree (ICTreeCons q l _ lt t1' t2') with RoleOrderDec q p =>
      {
        MergeTree (ICTreeCons q l (IChoiceAct p) lt t1' t2') (left o) :=
          ICTCons q _ _ (MergeTree t1') (MergeTree t2');
        MergeTree (p := p) (ICTreeCons q l (IChoiceAct p) lt t1' t2') (right n) :=
          ICTCons p _ _ (ICTCons q  _ _ (Lefts t1') (Lefts t2')) (ICTCons q _ _ (Rights t1') (Rights t2'))
      }
    }.
  Next Obligation.
    destruct H; [| inversion H]; subst; auto.
  Defined.
  Next Obligation.
    destruct H; [| inversion H]; subst; auto.
    rename q0 into q; destruct (RoleOrderTotal p q); auto.
    exfalso; apply n; auto.
  Defined.
  Next Obligation.
    apply InInsertRole in H; destruct H; subst; auto.
  Defined.
  Next Obligation.
    assert (p ≤r q) as pleq by (destruct (RoleOrderTotal p q); [|exfalso; apply n]; auto);
      destruct H; subst; auto; apply RoleOrderTrans with (q := q); auto.
  Defined.
  (* Inductive ICTreeA : (list Role) -> Action -> Set := *)
  (*   LeafTreeEnd        : forall p, ICTreeA [p] EndAct *)
  (* | LeafTreeVar        : forall p n, ICTreeA [p] (VarAct n) *)
  (* | LeafTreeDef        : forall p, Proc -> Proc -> Proc -> Proc -> *)
  (*                             ICTreeA [p] DefAct *)
  (* | LeafTreeSend       : forall p q e, Proc -> Proc -> *)
  (*                                 ICTreeA [p] (SendAct q e) *)
  (* | LeafTreeRecv       : forall p q, Proc -> Proc -> *)
  (*                               ICTreeA [p] (RecvAct q) *)
  (* | LeafTreeEChoiceL   : forall p q, Proc -> Proc -> *)
  (*                               ICTreeA [p] (EChoiceLAct q) *)
  (* | LeafTreeEChoiceR   : forall p q, Proc -> Proc -> *)
  (*                               ICTreeA [p] (EChoiceRAct q) *)
  (* | LeafTreeIChoice    : forall p q, Proc -> Proc -> Proc -> Proc -> *)
  (*                             ICTreeA [p] (IChoiceAct q) *)
  (* | LeafTreeIfThenElse : forall p e, Proc -> Proc -> Proc -> Proc -> *)
  (*                               ICTreeA [p] (IfThenElseAct e) *)
  (* | LeafTreeMixed      : forall p, Proc -> Proc -> ICTreeA [p] UnknownAct *)
  (* | ICTreeCons         : forall p l A, (forall q, In q l -> p ≤r q) -> *)
  (*                                 ICTreeA l A -> ICTreeA l A -> ICTreeA (p :: l) A. *)

  Fixpoint ProcSize (P : Proc) : nat :=
    match P with
    | EndProc => 1
    | VarProc n => 1
    | DefProc P Q => 1 + (ProcSize P) + (ProcSize Q)
    | SendProc p e P => 1 + (ProcSize P)
    | RecvProc p P => 1 + (ProcSize P)
    | EChoiceL p P => 1 + (ProcSize P)
    | EChoiceR p P => 1 + (ProcSize P)
    | IChoice p P Q => 1 + (ProcSize P) + (ProcSize Q)
    | IfThenElse e P Q => 1 + (ProcSize P) + (ProcSize Q)
    end.
  
  Fixpoint ICTreeASize {l : list Role} {A : Action} (t : ICTreeA l A) : nat :=
    match t with
    | LeafTreeEnd p => 1
    | LeafTreeVar p n => 1
    | LeafTreeDef p P Q1 Q2 => 1 + (ProcSize P) + (ProcSize Q1) + (ProcSize Q2)
    | LeafTreeSend p q e P1 P2 => 1 + (ProcSize P1) + (ProcSize P2)
    | LeafTreeRecv p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2)
    | LeafTreeEChoiceL p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2)
    | LeafTreeEChoiceR p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2)
    | LeafTreeIChoice p q P1 Q1 P2 Q2 => 1 + (ProcSize P1) + (ProcSize Q1) + (ProcSize P2) + (ProcSize Q2)
    | LeafTreeIfThenElse p e P1 Q1 P2 Q2 => 1 + (ProcSize P1) + (ProcSize Q1) + (ProcSize P2) + (ProcSize Q2)
    | LeafTreeMixed p P1 P2 => 1 + (ProcSize P1) + (ProcSize P2)
    | ICTreeCons p l A std t1 t2 => 1 + ICTreeASize t1  + ICTreeASize t2
    end.

  Definition ICTreeSize {l : list Role} (t : ICTree l) : nat :=
    match t with
    | mkTree _ TheAction TheTree => ICTreeASize TheTree
    end.

  Lemma SaplingSize : forall p P Q, ICTreeSize (Sapling p P Q) <= 1 + (ProcSize P) + (ProcSize Q).
  Proof.
    intros p P Q.
    funelim (Sapling p P Q); simp Sapling; auto.
    all: try (rewrite Heq); try (rewrite Heq0); autorewrite with Sapling; simpl; auto.
    2,3: rewrite Heq; autorewrite with Sapling; simpl.
    3: reflexivity.
    all: try (rewrite Nat.add_succ_r; apply le_n_S; repeat apply Nat.le_le_succ_r).
    all: try reflexivity.
    - apply plus_le_compat_l. apply le_plus_r.
    - rewrite plus_assoc; reflexivity.
    - rewrite plus_assoc; reflexivity.
  Qed.

  Lemma ProcSizeBounded : forall P : Proc, 1 <= ProcSize P.
  Proof.
    intros P. destruct P; simpl; auto; apply le_n_S; apply Nat.le_0_l.
  Qed.

  Lemma ICTConsSize : forall p l lt t1 t2, ICTreeSize (ICTCons p l lt t1 t2) <= S(ICTreeSize t1 + ICTreeSize t2).
  Proof.
    intros p l lt t1 t2. unfold ICTCons; destruct t1 as [A1 t1]; destruct t2 as [A2 t2].
    funelim (ICTConsA p l A1 A2 lt t1 t2); autorewrite with ICTConsA; simpl.
    all: auto.
    

  Lemma LeftsSize : forall {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)), ICTreeSize (Lefts t) < ICTreeASize t.
  Proof.
    intros l p t.
    funelim (Lefts t); autorewrite with Lefts; simpl.
    - apply Nat.lt_le_trans with (m := 2 + (ProcSize p18) + (ProcSize p20)); [apply le_n_S; apply SaplingSize |].
      simpl. apply le_n_S. transitivity (ProcSize p18 + 1 + ProcSize p20 + ProcSize p21).
      -- rewrite Nat.add_succ_r. simpl. rewrite Nat.add_0_r. apply le_n_S. apply le_plus_l.
      -- repeat rewrite <- plus_assoc. apply plus_le_compat_l. apply plus_le_compat_r. apply ProcSizeBounded.
    - 
      

  Lemma MergeTreeSize : 
  
  Equations ICTreeMinProc {l : list Role} (t : ICTree l) : Proc by wf (ICTreeSize t) lt :=
    {
      ICTreeMinProc (mkTree _ (LeafTreeEnd p)) := EndProc;
      ICTreeMinProc (mkTree _ (LeafTreeVar p n)) := VarProc n;
      ICTreeMinProc (mkTree _ (LeafTreeDef p P Q1 Q2)) := DefProc P (ICTreeMinProc (Sapling p Q1 Q2));
      ICTreeMinProc (mkTree _ (LeafTreeSend p q e P1 P2)) := Send q e (ICTreeMinProc (Sapling p P1 P2));
      ICTreeMinProc (mkTree _ (LeafTreeRecv p q P1 P2)) := Recv q (ICTreeMinProc (Sapling p P1 P2));
      ICTreeMinProc (mkTree _ (LeafTreeEChoiceL p q P1 P2)) := EChoiceL q (ICTreeMinProc (Sapling p P1 P2));
      ICTreeMinProc (mkTree _ (LeafTreeEChoiceR p q P1 P2)) := EChoiceR q (ICTreeMinProc (Sapling p P1 P2));
    }.
  
  
  Fixpoint InsertIChoice (p : Role) (P Q : Proc) : Proc :=
    let default := IChoice p P Q 
    in BothIChoice
         P Q default
         (fun q P1 P2 r Q1 Q2 =>
            if L.eq_dec q r
            then if RoleOrderDec q p
                 then if L.eq_dec p q
                      then default
                      else IChoice q (InsertIChoice p P1 Q1) (InsertIChoice p P2 Q2)
                 else default
            else default).

  Ltac LICF := repeat match goal with
                      | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
                      | [ H1 : ?P, H2 : ~ ?P |- _] => exfalso; apply H2; exact H1
                      | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] =>
                        exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto
                      | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] =>
                        match goal with
                        | [_ : p = q |- _ ] => fail 1
                        | [_ : q = p |- _ ] => fail 1
                        | _ =>
                          let e := fresh "eq" in
                          assert (p = q) as e by (apply RoleOrderAntisym; auto);
                          rewrite e in *
                        end
                      (* | [ |-context[InsertIChoice ?a ?b] ] => destruct a; simpl; auto *)
                      | [ |- context[L.eq_dec ?a ?a]] =>
                        let n := fresh "n" in
                        destruct (L.eq_dec a a) as [_|n];
                        [|exfalso; apply n; reflexivity]; simpl; auto
                      | [ |- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); subst; simpl; auto
                      | [ |- context[RoleOrderDec ?a ?b]] => destruct (RoleOrderDec a b); simpl; auto
                      end.
  (* Lemma InsertIChoiceFlip : forall p q P1_1 P1_2 P2_1 P2_2, *)
  (*     p <> q -> *)
  (*     InsertIChoice q (InsertIChoice p P1_1 P2_1) (InsertIChoice p P1_2 P2_2) = *)
  (*     InsertIChoice p (InsertIChoice q P1_1 P1_2) (InsertIChoice q P2_1 P2_2). *)
  (* Proof. *)
  (*   intros p q P1_1; revert p q; induction P1_1; intros p q P1_2 P2_1 P2_2 neq; simpl. *)
  (*   - destruct P1_2; destruct P2_1; destruct P2_2; simpl. *)
  (*     all: repeat unfold BothIChoice; try reflexivity. *)
  (*     all: try (timeout 1 LICF; try reflexivity). *)
  (*     all: unfold BothIChoice; LICF; try reflexivity. *)
      


  (*     all: let n := fresh "n" in *)
  (*          destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; reflexivity]. *)
  (*     all: let n := fresh "n" in *)
  (*          destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; reflexivity]. *)
  (*     all: destruct ( *)
    
  (*   all: destruct P1_2; destruct P2_1; simpl; auto. *)
  (*   (* all: destruct P2_2; optimize_heap. *) *)
  (*   all: try (let n := fresh "n" in *)
  (*             destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; reflexivity]). *)
  (*   all: try (let n := fresh "n" in *)
  (*             destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; reflexivity]). *)
  (*   Optimize Proof. Optimize Heap. *)

  (*   all: try (let l1 := fresh "l" in *)
  (*             let n1 := fresh "n" in *)
  (*             let l2 := fresh "l" in *)
  (*             let n2 := fresh "n" in *)
  (*             destruct (RoleOrderDec p q) as [l1 | n1]; *)
  (*             destruct (RoleOrderDec q p) as [l2 | n2]; *)
  (*             (* [let e := fresh "eq" in *) *)
  (*             (*  assert (p = q) as e by (apply RoleOrderAntisym; auto); *) *)
  (*             (*  try (exfalso; apply neq; rewrite e; reflexivity; fail) | | *) *)
  (*             (*  exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto] *) *)
  (*             match goal with *)
  (*             | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] => *)
  (*               exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto *)
  (*             | _ => try (reflexivity) *)
  (*             end). *)
  (*   all: match goal with *)
  (*          | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] => *)
  (*            match goal with *)
  (*            | [_ : p = q |- _ ] => fail 1 *)
  (*            | [_ : q = p |- _ ] => fail 1 *)
  (*            | _ => *)
  (*              let e := fresh "eq" in *)
  (*              assert (p = q) as e by (apply RoleOrderAntisym; auto); *)
  (*                try (exfalso; apply neq; rewrite e; reflexivity; fail) *)
  (*            end *)
  (*          | _ => idtac *)
  (*        end. *)
  (*   Optimize Proof. Optimize Heap. *)
  (*   all: try (let e := fresh "e" in *)
  (*             destruct (L.eq_dec q p) as [e |_]; *)
  (*             [exfalso; apply neq; auto| try reflexivity]). *)
  (*   all: try (let e := fresh "e" in *)
  (*             destruct (L.eq_dec p q) as [e |_]; *)
  (*             [exfalso; apply neq; auto| try reflexivity]). *)
  (*   Optimize Proof. Optimize Heap. *)
  (*   Show. *)
  (*   all: destruct P2_2; simpl; auto. *)
  (*   all: try (let n := fresh "n" in destruct (L.eq_dec q q) as [_|n]; *)
  (*                                   [| exfalso; apply n; reflexivity]; *)
  (*                                   try reflexivity). *)
  (*   Optimize Proof. Optimize Heap. *)
  (*   Show. *)
  (*   all: try (destruct (L.eq_dec r r0); simpl; auto). *)
  (*   all: try (destruct (RoleOrderDec r q); simpl; auto). *)
  (*   Optimize Proof. Optimize Heap. *)
  (*   all: try (destruct (L.eq_dec q r); simpl; auto; subst). *)
  (*   Optimize Proof. Optimize Heap. *)
  (*   Show. *)
  (*   destruct (L.eq_dec r0 r0) as [_|n]; [|exfalso; apply n; reflexivity]. *)
  (*   reflexivity. *)
  (*   Optimize Proof. Optimize Heap. *)
    
  (*   all: try (let n := fresh "n" in destruct (L.eq_dec r0 r0) as [_|n]; *)
  (*                                   [|exfalso; apply n; reflexivity]; try reflexivity). *)


  Fixpoint MergeProcs (p : Role) (P1 P2 : Proc) : Proc :=
    match P1 with
    | EndProc =>
      match P2 with
      | EndProc => IChoice p EndProc EndProc
      | _ => IChoice p EndProc P2
      end
    | VarProc n => IChoice p P1 P2
    | DefProc _ _ => 
      IChoice p P1 P2
    | SendProc q e P1' =>
      match P2 with
      | SendProc r e' P2' =>
        if L.eq_dec q r
        then if ExprEqDec e e'
             then if L.eq_dec p q
                  then IChoice p P1 P2
                  else SendProc q e (MergeProcs p P1' P2')
             else IChoice p P1 P2
        else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    | RecvProc q P1' =>
      match P2 with
      |RecvProc r P2' =>
       if L.eq_dec q r
       then if L.eq_dec p q
            then IChoice p P1 P2
            else RecvProc q (MergeProcs p P1' P2')
       else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    | EChoiceL q P1' =>
      match P2 with
      | EChoiceL r P2' =>
        if L.eq_dec q r
        then (* if L.eq_dec p q *)
             (* then IChoice p P1 P2 *)
             (* else *) EChoiceL q (MergeProcs p P1' P2')
        else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    | EChoiceR q P1' => 
      match P2 with
      | EChoiceR r P2' =>
        if L.eq_dec q r
        then (* if L.eq_dec p q *)
             (* then IChoice p P1 P2 *)
             (* else *) EChoiceR q (MergeProcs p P1' P2')
        else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    | IChoice q P11 P12 =>
      match P2 with
      | IChoice r P21 P22 =>
        if L.eq_dec q r
        then if L.eq_dec p q
             then IChoice p P1 P2
             else if RoleOrderDec p q
                  then IChoice p P1 P2
                  else IChoice q (MergeProcs p P11 P21) (MergeProcs p P12 P22)
        else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    | IfThenElse e P11 P12 =>
      match P2 with
      | IfThenElse e' P21 P22 =>
        if ExprEqDec e e'
        then IfThenElse e (MergeProcs p P11 P21) (MergeProcs p P12 P22)
        else IChoice p P1 P2
      | _ => IChoice p P1 P2
      end
    (* | Par P11 P12 => *)
    (*   match P2 with *)
    (*   | Par P21 P22 => Par (MergeProcs p P11 P21) (MergeProcs p P12 P22) *)
    (*   |_ => IChoice p P1 P2 *)
    (*   end *)
      (* IChoice p P1 P2 *)
    end.

  Lemma SwapMergeProcs: forall p q P1 P2 P3 P4,
      p <> q ->
      MergeProcs p (MergeProcs q P1 P2) (MergeProcs q P3 P4) =
      MergeProcs q (MergeProcs p P1 P3) (MergeProcs p P2 P4).
  Proof.
    intros p q P1; revert p q; induction P1; simpl; intros p q P2 P3 P4 neq; auto.
    all: try (destruct P2; destruct P3; simpl; auto; fail).
    - destruct P2; destruct P3; destruct P4; simpl; auto.
      all:
        let n := fresh "n" in
        destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; auto];
        destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto].
      all: destruct (L.eq_dec p q); subst.
      all: try (let n := fresh "n" in destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto]); auto.
      Optimize Proof. Optimize Heap.
      Show.
      all: repeat match goal with
             | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
             | [ H1 : ?P, H2 : ~ ?P |- _] => exfalso; apply H2; exact H1
             | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] =>
               exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto
             | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] =>
               match goal with
               | [_ : p = q |- _ ] => fail 1
               | [_ : q = p |- _ ] => fail 1
               | _ =>
                 let e := fresh "eq" in
                 assert (p = q) as e by (apply RoleOrderAntisym; auto);
                   rewrite e in *
               end
             (* | [ |-context[InsertIChoice ?a ?b] ] => destruct a; simpl; auto *)
             | [ |- context[L.eq_dec ?a ?a]] =>
               let n := fresh "n" in
               destruct (L.eq_dec a a) as [_|n];
                 [|exfalso; apply n; reflexivity]; simpl; auto
             | [ |- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); subst; simpl; auto
             | [ |- context[ExprEqDec ?a ?a]] =>
               let n := fresh "n" in
               destruct (ExprEqDec a a) as [_|n];
                 [|exfalso; apply n; reflexivity]; simpl; auto
             | [ |- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); subst; simpl; auto
             | [ |- context[RoleOrderDec ?a ?b]] => destruct (RoleOrderDec a b); simpl; auto
             end.

      
      match goal with
      | [ |- context[L.eq_dec ?a ?a]] =>
        let n := fresh "n" in
        destruct (L.eq_dec a a) as [_|n]; [|exfalso; apply n; reflexivity]
      | [ |- context[RoleEq
      
  Fixpoint Normalize (P : Proc) : Proc :=
    match P with
    | EndProc => EndProc
    | VarProc n => VarProc n
    | DefProc P Q => DefProc (Normalize P) (Normalize Q)
    | SendProc p e P => SendProc p e (Normalize P)
    | RecvProc p P => RecvProc p (Normalize P)
    | EChoiceL p P => EChoiceL p (Normalize P)
    | EChoiceR p P => EChoiceR p (Normalize P)
    | IChoice p P Q => MergeProcs p (Normalize P) (Normalize Q)
    | IfThenElse e P Q => IfThenElse e (Normalize P) (Normalize Q)
    (* | Par P Q => Par (Normalize P) (Normalize Q) *)
    end.

  
End PiCalc.


