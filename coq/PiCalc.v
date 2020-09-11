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
  Import LF.

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


                  
  
  (* (* SameTree l A is the type of ichoice trees such that every option has the same action. *)
  (*    Here, l is the list of principals that participate in the tree. *)
  (*  *) *)
  (* Inductive SameTree : list Role -> Action -> Set := *)
  (*   SameLeaf : forall (p : Role) (P Q : Proc) (A : Action), ActionOf P = A -> ActionOf Q = A -> SameTree [p] A *)
  (* | SameBranch : forall (p : Role) {l : list Role} {A : Action}, (forall q, In q l -> q ≤r p) -> SameTree l A -> SameTree l A -> SameTree (p :: l) A. *)

  (* Equations SameTreeToProc {l : list Role} {A : Action} (st : SameTree l A) : Proc := *)
  (*   { *)
  (*     SameTreeToProc (SameLeaf p P Q _ _ _) := IChoice p P Q; *)
  (*     SameTreeToProc (SameBranch p _ ll rr) := IChoice p (SameTreeToProc ll) (SameTreeToProc rr) *)
  (*   }. *)

  (* Equations FirstDecider {l : list Role} {A : Action} (st : SameTree l A) : Role := *)
  (*   { *)
  (*     FirstDecider (SameLeaf p _ _ _ _ _) := p; *)
  (*     FirstDecider (SameBranch p _ ll rr) := p *)
  (*   }. *)

  (* Lemma FirstDeciderHead : forall (l : list Role) {A : Action} (st : SameTree l A), exists l', l = (FirstDecider st) :: l'. *)
  (* Proof. *)
  (*   intros l A st. funelim (FirstDecider st); simp FirstDecider; [exists [] | exists l0]; reflexivity. *)
  (* Qed. *)

  (* Lemma SameTreeListSorted : forall (l : list Role) {A : Action}, SameTree l A -> Sorted (fun p q => q ≤r p) l. *)
  (* Proof. *)
  (*   intros l A st; induction st. constructor; constructor. constructor; auto. *)
  (*   destruct l; constructor. apply r. left; reflexivity. *)
  (* Qed. *)

  (* Fixpoint SameTreeSize {l : list Role} {A : Action} (st : SameTree l A) : nat := *)
  (*   match st with *)
  (*   | SameLeaf p P Q A x x0 => 1 *)
  (*   | SameBranch p _ ll rr => S (SameTreeSize ll + SameTreeSize rr) *)
  (*   end. *)

  (* Definition SameTreeExt : Set := {l : list Role & {A : Action & SameTree l A}}. *)
  
  (* Inductive DiffTree : Role -> Set := *)
  (*   DiffLeaf : forall (p : Role) (P Q : Proc), *)
  (*     ActionOf P <> ActionOf Q -> DiffTree p *)
  (* | DiffDiffTree : forall (p : Role) {q r : Role} (dt1 : DiffTree q) (dt2 : DiffTree r), *)
  (*     q ≤r p -> r ≤r p -> DiffTree p *)
  (* | SameDiffTree : forall (p : Role) {q : Role} {l : list Role} {A : Action}  (st : SameTree l A) (dt : DiffTree q), *)
  (*     q ≤r p -> (FirstDecider st) ≤r p -> DiffTree p *)
  (* | DiffSameTree : forall (p : Role) {q : Role} {l : list Role} {A : Action} (dt : DiffTree q) (st : SameTree l A), *)
  (*     q ≤r p -> (FirstDecider st) ≤r p -> DiffTree p *)
  (* | SameSameTreeDiffAction : forall (p : Role) {l1 l2 : list Role} {A1 A2 : Action} (st1 : SameTree l1 A1) (st2 : SameTree l2 A2), *)
  (*     (FirstDecider st1) ≤r p -> (FirstDecider st2) ≤r p -> A1 <> A2 -> DiffTree p *)
  (* | SameSameTreeDiffList : forall (p : Role) {l1 l2 : list Role} {A1 A2 : Action} (st1 : SameTree l1 A1) (st2 : SameTree l2 A2), *)
  (*     (FirstDecider st1) ≤r p -> (FirstDecider st2) ≤r p -> l1 <> l2 -> DiffTree p. *)

  (* Definition DiffTreeExt : Set := {p : Role & DiffTree p}. *)

  (* Fixpoint DiffTreeSize {p : Role} (dt : DiffTree p) : nat := *)
  (*   match dt with *)
  (*   | DiffLeaf p P Q x => 1 *)
  (*   | DiffDiffTree p dt1 dt2 _ _ => S (DiffTreeSize dt1 + DiffTreeSize dt2) *)
  (*   | SameDiffTree p st dt _ _ => S (SameTreeSize st + DiffTreeSize dt) *)
  (*   | DiffSameTree p dt st _ _ => S (DiffTreeSize dt + SameTreeSize st) *)
  (*   | SameSameTreeDiffAction p st1 st2 _ _ _ => S (SameTreeSize st1 + SameTreeSize st2) *)
  (*   | SameSameTreeDiffList p st1 st2 _ _ _ => S (SameTreeSize st1 + SameTreeSize st2) *)
  (*   end. *)

  (* Fixpoint DiffTreeToProc {p : Role} (dt : DiffTree p) : Proc := *)
  (*   match dt with *)
  (*   | DiffLeaf p P Q _ => IChoice p P Q *)
  (*   | DiffDiffTree p ll rr _ _ => IChoice p (DiffTreeToProc ll) (DiffTreeToProc rr) *)
  (*   | SameDiffTree p ll rr _ _ => IChoice p (SameTreeToProc ll) (DiffTreeToProc rr) *)
  (*   | DiffSameTree p ll rr _ _ => IChoice p (DiffTreeToProc ll) (SameTreeToProc rr) *)
  (*   | SameSameTreeDiffAction p ll rr _ _ _ => IChoice p (SameTreeToProc ll) (SameTreeToProc rr) *)
  (*   | SameSameTreeDiffList p ll rr _ _ _ => IChoice p (SameTreeToProc ll) (SameTreeToProc rr) *)
  (*   end. *)

  (* Definition ICTree : Set := SameTreeExt + DiffTreeExt. *)

  (* Show Match sigT. *)
  (* Program Fixpoint TreeBranch (p : Role) (t1 : ICTree) (t2 : ICTree) : ICTree := *)
  (*   match t1 with *)
  (*   | inl (existT _ l1 (existT _ A1 st1)) => *)
  (*     match t2 with *)
  (*     | inl (existT _ l2 (existT _ A2 st2)) => *)
  (*       match ActionEqDec A1 A2 with *)
  (*       | left e => _ *)
  (*       | right n => _ *)
  (*       end *)
  (*     | inr (existT _ p2 dt2) => _ *)
  (*     end *)
  (*   | inr (existT _ p1 dt1) => *)
  (*     match t2 with *)
  (*     | inl (existT _ l2 (existT _ A2 st2)) => _ *)
  (*     | inr (existT _ p2 dt2) => _ *)
  (*     end *)
  (*   end. *)
  (* Next Obligation. *)


  (* Inductive Justification : Set := *)
  (*   InvolvedSend : Expr -> Justification *)
  (* | InvolvedRecv : Justification *)
  (* | InvolvedECL : Justification *)
  (* | InvolvedECR : Justification *)
  (* | InvolvedIC : Justification *)
  (* | Different : forall {p : Role}, DiffTree p -> Justification. *)

  (* Inductive Justifies : Justification -> Role -> Proc -> Proc -> Prop := *)
  (*   ISJust : forall p e P Q, Justifies (InvolvedSend e) p (SendProc p e P) (SendProc p e Q) *)
  (* | IRJust : forall p P Q, Justifies InvolvedRecv p (RecvProc p P) (RecvProc p Q) *)
  (* | IECLJust : forall p P Q, Justifies InvolvedECL p (EChoiceL p P) (EChoiceL p Q) *)
  (* | IECRJust : forall p P Q, Justifies InvolvedECR p (EChoiceR p P) (EChoiceR p Q) *)
  (* | IICJust : forall p P1 Q1 P2 Q2, Justifies InvolvedIC p (IChoice p P1 Q1) (IChoice p P2 Q2) *)
  (* | DifferentJust : forall p P Q (d : DiffTree p), (DiffTreeToProc d = IChoice p P Q) -> Justifies (Different d) p P Q. *)

  (* Inductive DiffOrSameTree : Set := *)
  (*   ItsAST : forall (l : list Role) (A : Action), SameTree l A -> DiffOrSameTree *)
  (* | ItsADT : forall {p : Role}, DiffTree p -> DiffOrSameTree. *)

  (*   Fixpoint ProcSize (P : Proc) : nat := *)
  (*   match P with *)
  (*   | EndProc => 1 *)
  (*   | VarProc n => 1 *)
  (*   | DefProc P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   | SendProc p e P => 1 + (ProcSize P) *)
  (*   | RecvProc p P => 1 + (ProcSize P) *)
  (*   | EChoiceL p P => 1 + (ProcSize P) *)
  (*   | EChoiceR p P => 1 + (ProcSize P) *)
  (*   | IChoice p P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   | IfThenElse e P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   end. *)

  (* Equations toDiffOrSameTree (p : Role) (P Q : Proc) : DiffOrSameTree by wf (ProcSize P + ProcSize Q) lt := *)
  (*   { *)
  (*     toDiffOrSameTree p EndProc EndProc := ItsAST _ EndAct (SameLeaf p EndProc EndProc EndAct eq_refl eq_refl); *)
  (*     toDiffOrSameTree p EndProc _ := ItsADT (DiffLeaf p EndProc Q _); *)
  (*     toDiffOrSameTree p (VarProc n) (VarProc n) := ItsAST [p] (VarAct n) (SameLeaf p (VarProc n) (VarProc n) (VarAct n) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (VarProc n) _ := ItsADT (DiffLeaf p (VarProc n) Q _); *)
  (*     toDiffOrSameTree p (DefProc P Q1) (DefProc P Q2) := ItsAST [p] (DefAct P) (SameLeaf p (DefProc P Q1) (DefProc P Q2) (DefAct P) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (DefProc P Q1) _ := ItsADT (DiffLeaf p (DefProc P Q1) Q _); *)
  (*     toDiffOrSameTree p (SendProc q e P) (SendProc q e Q) := ItsAST [p] (SendAct q e) (SameLeaf p (SendProc q e P) (SendProc q e Q) (SendAct q e) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (SendProc q e P) _ := ItsADT (DiffLeaf p (SendProc q e P) Q _); *)
  (*     toDiffOrSameTree p (RecvProc q P) (RecvProc q Q) := ItsAST _ (RecvAct q) (SameLeaf p (RecvProc q P) (RecvProc q Q) (RecvAct q) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (RecvProc q P) _ := ItsADT (DiffLeaf p (RecvProc q P) Q _); *)
  (*     toDiffOrSameTree p (EChoiceL q P) (EChoiceL q Q) := ItsAST _ (EChoiceLAct q) (SameLeaf p (EChoiceL q P) (EChoiceL q Q) (EChoiceLAct q) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (EChoiceL q P) _ := ItsADT (DiffLeaf p (EChoiceL q P) Q _); *)
  (*     toDiffOrSameTree p (EChoiceR q P) (EChoiceR q Q) := ItsAST _ (EChoiceRAct q) (SameLeaf p (EChoiceR q P) (EChoiceR q Q) (EChoiceRAct q) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (EChoiceR q P) _ := ItsADT (DiffLeaf p (EChoiceR q P) Q _); *)
  (*     toDiffOrSameTree p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) := ItsAST _ (IfThenElseAct e) (SameLeaf p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) (IfThenElseAct e) eq_refl eq_refl); *)
  (*     toDiffOrSameTree p (IfThenElse e P1 Q1) _ := ItsADT (DiffLeaf p (IfThenElse e P1 Q1) Q _); *)
  (*     toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) with toDiffOrSameTree q P1 Q1 := *)
  (*       { *)
  (*       toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) with toDiffOrSameTree q P2 Q2 := *)
  (*         { *)
  (*         toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 A2 st2) with ActionEqDec A1 A2 := *)
  (*           { *)
  (*           toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 ?(A1) st2) (left eq_refl) with list_eq_dec L.eq_dec l1 l2 := *)
  (*             { *)
  (*             toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST ?(l1) ?(A1) st2) (left eq_refl) (left eq_refl) := ItsAST _ _ (SameBranch _ _ st1 st2); *)
  (*             toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 ?(A1) st2) (left eq_refl) (right n) := ItsADT (SameSameTreeDiffList _ st1 st2 _ _ n) *)
  (*             }; *)
  (*           toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsAST l2 A2 st2) (right n) := (ItsADT (SameSameTreeDiffAction _ st1 st2 _ _ n)) *)
  (*           }; *)
  (*         toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsAST l1 A1 st1) (ItsADT dt2) := (ItsADT (SameDiffTree _ st1 dt2 _ _)) *)
  (*         }; *)
  (*       toDiffOrSameTree p (IChoice q P1 Q1) (IChoice q P2 Q2) (ItsADT dt1) := _ *)
  (*       }; *)
  (*     toDiffOrSameTree p (IChoice q P1 Q1) _ := ItsADT (DiffLeaf p (IChoice q P1 Q1) Q _) *)
  (*   }. *)
  
  (* Equations justify (p : Role) (P Q : Proc) : option Justification := *)
  (*   { *)
  (*     justify p (SendProc p e P) (SendProc p e Q) := Some (InvolvedSend p e); *)
  (*     justify p (RecvProc p P) (RecvProc p Q) := Some (InvolvedRecv); *)
  (*     justify p (EChoiceL p P) (EChoiceL p Q) := Some (InvolvedECL); *)
  (*     justify _ _ _ := None *)
  (*   }. *)
  
  (* Inductive ICTreeA : (list Role) -> Action -> Set := *)
  (*   LeafTreeEnd        : forall p, ICTreeA [p] EndAct *)
  (* | LeafTreeVar        : forall p n, ICTreeA [p] (VarAct n) *)
  (* | LeafTreeDef        : forall p P, Proc -> Proc -> *)
  (*                             ICTreeA [p] (DefAct P) *)
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

  (* Theorem ICTreeASorted : forall l A, ICTreeA l A -> Sorted (fun p q => p ≤r q) l. *)
  (* Proof. *)
  (*   intros l A t; induction t; auto. *)
  (*   constructor; auto. *)
  (*   clear IHt1 IHt2 t1 t2 A. *)
  (*   induction l; auto. constructor; auto. *)
  (*   apply r; left; reflexivity. *)
  (* Qed. *)

  (* Fixpoint ForgetAction {l : list Role} {A : Action} (t : ICTreeA l A) *)
  (*   : ICTreeA l UnknownAct *)
  (*   := match t with *)
  (*     | LeafTreeEnd p => LeafTreeMixed p (EndProc) (EndProc) *)
  (*     | LeafTreeVar p n => LeafTreeMixed p (VarProc n) (VarProc n) *)
  (*     | LeafTreeDef p P Q1 Q2 => LeafTreeMixed p (DefProc P Q1) (DefProc P Q2) *)
  (*     | LeafTreeSend p q e P1 P2 => LeafTreeMixed p (SendProc q e P1) (SendProc q e P2) *)
  (*     | LeafTreeRecv p q P1 P2 => LeafTreeMixed p (RecvProc q P1) (RecvProc q P2) *)
  (*     | LeafTreeEChoiceL p q P1 P2 => LeafTreeMixed p (EChoiceL q P1) (EChoiceL q P2) *)
  (*     | LeafTreeEChoiceR p q P1 P2 => LeafTreeMixed p (EChoiceR q P1) (EChoiceR q P2) *)
  (*     | LeafTreeIChoice p q P1 Q1 P2 Q2 => *)
  (*       LeafTreeMixed p (IChoice q P1 Q1) (IChoice q P2 Q2) *)
  (*     | LeafTreeIfThenElse p e P1 Q1 P2 Q2 => *)
  (*       LeafTreeMixed p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) *)
  (*     | LeafTreeMixed p P1 P2 => LeafTreeMixed p P1 P2 *)
  (*     | ICTreeCons p l A lt t1 t2 => *)
  (*       ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2) *)
  (*     end. *)

  (* Fixpoint InsertRole (p : Role) (l : list Role) : list Role := *)
  (*   match l with *)
  (*   | [] => [p] *)
  (*   | q :: l => if RoleOrderDec q p *)
  (*             then q :: (InsertRole p l) *)
  (*             else p :: q :: l *)
  (*   end. *)

  (* Lemma InInsertRole : forall (p : Role) (l : list Role) (q : Role), In q (InsertRole p l) <-> p = q \/ In q l. *)
  (* Proof. *)
  (*   intros p l; induction l; simpl; intro q; split; auto; intro H. *)
  (*   all: destruct (RoleOrderDec a p); simpl; auto. *)
  (*   - destruct H. right; left; auto. apply IHl in H; destruct H; [left | right; right]; auto. *)
  (*   - destruct H; [right | destruct H; [left | right]]; auto; apply IHl; [left | right]; auto. *)
  (* Qed. *)

  (* Lemma SortedLeast : forall {A : Type} (R : A -> A -> Prop) (Rtrans : forall a b c : A, R a b -> R b c -> R a c) (a : A) (l : list A), Sorted R (a :: l) -> forall b : A, In b l -> R a b. *)
  (* Proof. *)
  (*   intros A R Rtrans a l std b I. *)
  (*   induction l; [inversion I|]. *)
  (*   destruct I; subst; [inversion std; subst; inversion H2; subst; auto|]. *)
  (*   apply IHl; auto. *)
  (*   inversion std; subst; inversion H2; subst. *)
  (*   constructor; auto. *)
  (*   inversion H3; subst. destruct l; [inversion H|]. *)
  (*   inversion H5; subst. constructor. eapply Rtrans; eauto. *)
  (* Qed. *)
  
  (* Lemma InsertRoleSorted : forall (p : Role) (l : list Role), *)
  (*     Sorted (fun p q => p ≤r q) l -> Sorted (fun p q => p ≤r q) (InsertRole p l). *)
  (* Proof. *)
  (*   intros p l; revert p; induction l as [| q l]; intros p std; simpl; auto. *)
  (*   destruct (RoleOrderDec q p); constructor; auto. *)
  (*   - apply IHl; inversion std; auto. *)
  (*   - assert (InsertRole p l = InsertRole p l) as H by reflexivity; revert H; generalize (InsertRole p l) at 2 3. *)
  (*     intros l0 e; destruct l0; constructor. *)
  (*     inversion std; subst. *)
  (*     assert (In r0 (InsertRole p l)) as I by (rewrite e; left; reflexivity). *)
  (*     apply InInsertRole in I; destruct I; subst; auto. *)
  (*     specialize (IHl p H1). *)
  (*     apply SortedLeast with (b := r0) in std; auto. *)
  (*     exact RoleOrderTrans. *)
  (*   - destruct (RoleOrderTotal p q); [constructor | exfalso; apply n]; auto. *)
  (* Qed. *)

  (* Fixpoint FlattenICTA {l : list Role} {A : Action} (t : ICTreeA l A) : Proc := *)
  (*   match t with *)
  (*   | LeafTreeEnd p => IChoice p EndProc EndProc *)
  (*   | LeafTreeVar p n => IChoice p (VarProc n) (VarProc n) *)
  (*   | LeafTreeDef p P Q1 Q2 => IChoice p (DefProc P Q1) (DefProc P Q2) *)
  (*   | LeafTreeSend p q e P1 P2 => IChoice p (SendProc q e P1) (SendProc q e P2) *)
  (*   | LeafTreeRecv p q P1 P2 => IChoice p (RecvProc q P1) (RecvProc q P2) *)
  (*   | LeafTreeEChoiceL p q P1 P2 => IChoice p (EChoiceL q P1) (EChoiceL q P2) *)
  (*   | LeafTreeEChoiceR p q P1 P2 => IChoice p (EChoiceR q P1) (EChoiceR q P2) *)
  (*   | LeafTreeIChoice p q P1 Q1 P2 Q2 => IChoice p (IChoice q P1 Q1) (IChoice q P2 Q2) *)
  (*   | LeafTreeIfThenElse p e P1 Q1 P2 Q2 => *)
  (*     IChoice p (IfThenElse e P1 Q1) (IfThenElse e P2 Q2) *)
  (*   | LeafTreeMixed p P1 P2 => IChoice p P1 P2 *)
  (*   | ICTreeCons p l A lt t1 t2 => *)
  (*     IChoice p (FlattenICTA t1) (FlattenICTA t2) *)
  (*   end. *)

  (* Record ICTree (l : list Role) : Set := *)
  (*   mkTree { TheAction : Action ; *)
  (*            TheTree   : ICTreeA l TheAction *)
  (*          }. *)
  (* Arguments TheAction [l]. *)
  (* Arguments TheTree [l]. *)

  (* Definition FlattenICTree {l : list Role} (t : ICTree l) : Proc := *)
  (*   FlattenICTA (TheTree t). *)

  (* Definition ICTEnd : forall p : Role, ICTree [p]  := *)
  (*   fun p => mkTree [p] EndAct (LeafTreeEnd p). *)

  (* Definition ICTVar : forall p : Role, nat -> ICTree [p] := *)
  (*   fun p n => mkTree _ _ (LeafTreeVar p n). *)

  (* Definition ICTDef : forall p : Role, Proc -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p P Q1 Q2 => mkTree _ _ (LeafTreeDef p P Q1 Q2). *)

  (* Definition ICTSend : forall p : Role, Role -> Expr -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p q e P1 P2 => mkTree _ _ (LeafTreeSend p q e P1 P2). *)

  (* Definition ICTRecv : forall p : Role, Role -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p q P1 P2 => mkTree _ _ (LeafTreeRecv p q P1 P2). *)

  (* Definition ICTEChoiceL : forall p : Role, Role -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p q P1 P2 => mkTree _ _ (LeafTreeEChoiceL p q P1 P2). *)

  (* Definition ICTEChoiceR : forall p : Role, Role -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p q P1 P2 => mkTree _ _ (LeafTreeEChoiceR p q P1 P2). *)

  (* Definition ICTIChoice : forall p : Role, Role -> Proc -> Proc -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p q P1 Q1 P2 Q2 => mkTree _ _ (LeafTreeIChoice p q P1 Q1 P2 Q2). *)

  (* Definition ICTITE : forall p : Role, Expr -> Proc -> Proc -> Proc -> Proc -> ICTree [p] := *)
  (*   fun p e P1 Q1 P2 Q2 => mkTree _ _ (LeafTreeIfThenElse p e P1 Q1 P2 Q2). *)

  (* Definition ICTMixed : forall p : Role, Proc -> Proc -> ICTree [p] := *)
  (*   fun p P1 P2 => mkTree _ _ (LeafTreeMixed p P1 P2). *)

  (* Equations ICTConsA : forall (p : Role) (l : list Role) (A1 A2 : Action), *)
  (*     (forall q, In q l -> p ≤r q) -> ICTreeA l A1 -> ICTreeA l A2 -> ICTree (p :: l) := *)
  (*   ICTConsA p l EndAct EndAct lt t1 t2 := *)
  (*     mkTree _ _ (ICTreeCons p l EndAct lt t1 t2) ; *)
  (*   ICTConsA p l (VarAct n) (VarAct m) lt t1 t2 with Nat.eq_dec n m => { *)
  (*     ICTConsA p l (VarAct n) (VarAct ?(n)) lt t1 t2 (left eq_refl) := *)
  (*       mkTree _ _ (ICTreeCons p l (VarAct n) lt t1 t2) ; *)
  (*     ICTConsA p l (VarAct n) (VarAct m) lt t1 t2 (right _) := *)
  (*       mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*   ICTConsA p l (DefAct P1) (DefAct P2) lt t1 t2 with ProcEqDec P1 P2 => *)
  (*   { *)
  (*     ICTConsA p l (DefAct P1) (DefAct ?(P1)) lt t1 t2 (left eq_refl) := mkTree _ _ (ICTreeCons p l (DefAct P1) lt t1 t2); *)
  (*     ICTConsA p l (DefAct P1) (DefAct P2) lt t1 t2 (right _) := *)
  (*       mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*   };  *)
  (*   ICTConsA p l (SendAct q e) (SendAct r e') lt t1 t2 with L.eq_dec q r => { *)
  (*       ICTConsA p l (SendAct q e) (SendAct ?(q) e') lt t1 t2 (left eq_refl) with ExprEqDec e e' => { *)
  (*         ICTConsA p l (SendAct q e) (SendAct ?(q) ?(e)) lt t1 t2 (left eq_refl) (left eq_refl) := *)
  (*           mkTree _ _ (ICTreeCons p l (SendAct q e) lt t1 t2); *)
  (*         ICTConsA p l (SendAct q e) (SendAct ?(q) e') lt t1 t2 (left eq_refl) (right _) := *)
  (*           mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1 ) (ForgetAction t2)) *)
  (*       }; *)
  (*       ICTConsA p l (SendAct q e) (SendAct r e') lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1 ) (ForgetAction t2)) *)
  (*     }; *)
  (*   ICTConsA p l (RecvAct q) (RecvAct r) lt t1 t2 with L.eq_dec q r => { *)
  (*       ICTConsA p l (RecvAct q) (RecvAct ?(q)) lt t1 t2 (left eq_refl) := *)
  (*         mkTree _ _ (ICTreeCons p l  (RecvAct q) lt t1 t2); *)
  (*       ICTConsA p l _ _ lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*  ICTConsA p l (EChoiceLAct q) (EChoiceLAct r) lt t1 t2 with L.eq_dec q r => { *)
  (*       ICTConsA p l (EChoiceLAct q) (EChoiceLAct ?(q)) lt t1 t2 (left eq_refl) := *)
  (*         mkTree _ _ (ICTreeCons p l ((EChoiceLAct q)) lt t1 t2); *)
  (*       ICTConsA p l _ _ lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*  ICTConsA p l (EChoiceRAct q) (EChoiceRAct r) lt t1 t2 with L.eq_dec q r => { *)
  (*       ICTConsA p l (EChoiceRAct q) (EChoiceRAct ?(q)) lt t1 t2 (left eq_refl) := *)
  (*         mkTree _ _ (ICTreeCons p l ((EChoiceRAct q)) lt t1 t2); *)
  (*       ICTConsA p l _ _ lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*  ICTConsA p l (IChoiceAct q) (IChoiceAct r) lt t1 t2 with L.eq_dec q r => { *)
  (*       ICTConsA p l (IChoiceAct q) (IChoiceAct ?(q)) lt t1 t2 (left eq_refl) := *)
  (*         mkTree _ _ (ICTreeCons p l ((IChoiceAct q)) lt t1 t2); *)
  (*       ICTConsA p l _ _ lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*  ICTConsA p l (IfThenElseAct e1) (IfThenElseAct e2) lt t1 t2 with ExprEqDec e1 e2 => { *)
  (*       ICTConsA p l (IfThenElseAct e1) (IfThenElseAct ?(e1)) lt t1 t2 (left eq_refl) := *)
  (*         mkTree _ _ (ICTreeCons p l ((IfThenElseAct e1)) lt t1 t2); *)
  (*       ICTConsA p l _ _ lt t1 t2 (right _) := *)
  (*         mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)) *)
  (*     }; *)
  (*  ICTConsA p l _ _  lt t1 t2 := *)
  (*    mkTree _ _ (ICTreeCons p l UnknownAct lt (ForgetAction t1) (ForgetAction t2)). *)

  (* Definition ICTCons : forall (p : Role) (l : list Role), *)
  (*     (forall q, In q l -> p ≤r q) -> ICTree l -> ICTree l -> ICTree (p :: l) := *)
  (*   fun p l lt t1 t2 => match t1 with *)
  (*                    | mkTree _ A1 t1 => *)
  (*                      match t2 with *)
  (*                      |mkTree _ A2 t2 => ICTConsA p l A1 A2 lt t1 t2 *)
  (*                      end *)
  (*                    end. *)
        
  (* Equations Sapling : forall (p : Role), Proc -> Proc -> ICTree [p] := *)
  (*   { *)
  (*     Sapling p EndProc EndProc := ICTEnd p; *)
  (*     Sapling p (VarProc n) (VarProc m) with Nat.eq_dec n m => *)
  (*     { *)
  (*       Sapling p (VarProc n) (VarProc ?(n)) (left eq_refl) := ICTVar p n; *)
  (*       Sapling p (VarProc n) (VarProc m) (right _) := ICTMixed p (VarProc n) (VarProc m) *)
  (*     }; *)
  (*     Sapling p (DefProc P1 Q1) (DefProc P2 Q2) with ProcEqDec P1 P2 => *)
  (*     { *)
  (*       Sapling p (DefProc P1 Q1) (DefProc ?(P1) Q2) (left eq_refl) := ICTDef p P1 Q1 Q2; *)
  (*       Sapling p (DefProc P1 Q1) (DefProc P2 Q2) (right _) := ICTMixed p (DefProc P1 Q1) (DefProc P2 Q2) *)
  (*     }; *)
  (*     Sapling p (SendProc q e1 P1) (SendProc r e2 P2) with L.eq_dec q r => *)
  (*     { *)
  (*       Sapling p (SendProc q e1 P1) (SendProc ?(q) e2 P2) (left eq_refl) with ExprEqDec e1 e2 => *)
  (*       { *)
  (*         Sapling p (SendProc q e1 P1) (SendProc ?(q) ?(e1) P2) (left eq_refl) (left eq_refl) := ICTSend p q e1 P1 P2; *)
  (*         Sapling p (SendProc q e1 P1) (SendProc ?(q) e2 P2) (left eq_refl) (right _) := *)
  (*           ICTMixed p (SendProc q e1 P1) (SendProc q e2 P2) *)
  (*       }; *)
  (*       Sapling p (SendProc q e1 P1) (SendProc r e2 P2) (right _) := *)
  (*         ICTMixed p (SendProc q e1 P1) (SendProc r e2 P2) *)
  (*     }; *)
  (*     Sapling p (RecvProc q P1) (RecvProc r P2) with L.eq_dec q r => *)
  (*     { *)
  (*       Sapling p (RecvProc q P1) (RecvProc ?(q) P2) (left eq_refl) := *)
  (*         ICTRecv p q P1 P2; *)
  (*       Sapling p (RecvProc q P1) (RecvProc r P2) (right _) := *)
  (*         ICTMixed p (RecvProc q P1) (RecvProc r P2) *)
  (*     }; *)
  (*     Sapling p (EChoiceL q P1) (EChoiceL r P2) with L.eq_dec q r => *)
  (*     { *)
  (*       Sapling p (EChoiceL q P1) (EChoiceL ?(q) P2) (left eq_refl) := *)
  (*         ICTEChoiceL p q P1 P2; *)
  (*       Sapling p (EChoiceL q P1) (EChoiceL r P2) (right _) := *)
  (*         ICTMixed p (EChoiceL q P1) (EChoiceL r P2) *)
  (*     }; *)
  (*     Sapling p (EChoiceR q P1) (EChoiceR r P2) with L.eq_dec q r => *)
  (*     { *)
  (*       Sapling p (EChoiceR q P1) (EChoiceR ?(q) P2) (left eq_refl) := *)
  (*         ICTEChoiceR p q P1 P2; *)
  (*       Sapling p (EChoiceR q P1) (EChoiceR r P2) (right _) := *)
  (*         ICTMixed p (EChoiceR q P1) (EChoiceR r P2) *)
  (*     }; *)
  (*     Sapling p (IChoice q P1 Q1) (IChoice r P2 Q2) with L.eq_dec q r => *)
  (*     { *)
  (*       Sapling p (IChoice q P1 Q1) (IChoice ?(q) P2 Q2) (left eq_refl) := *)
  (*         ICTIChoice p q P1 Q1 P2 Q2; *)
  (*       Sapling p (IChoice q P1 Q1) (IChoice r P2 Q2) (right _) := *)
  (*         ICTMixed p (IChoice q P1 Q1) (IChoice r P2 Q2) *)
  (*     }; *)
  (*     Sapling p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2) with ExprEqDec e1 e2 => *)
  (*     { *)
  (*       Sapling p (IfThenElse e1 P1 Q1) (IfThenElse ?(e1) P2 Q2) (left eq_refl) := *)
  (*         ICTITE p e1 P1 Q1 P2 Q2; *)
  (*       Sapling p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2) (right _) := *)
  (*         ICTMixed p (IfThenElse e1 P1 Q1) (IfThenElse e2 P2 Q2) *)
  (*     }; *)
  (*     Sapling p P Q := ICTMixed p P Q *)
  (*   }. *)

  (* Derive NoConfusion for Action. *)

  (* Equations Lefts {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)) : ICTree l := *)
  (*   { *)
  (*     Lefts (LeafTreeIChoice q p P1 Q1 P2 Q2) := Sapling q P1 P2; *)
  (*     Lefts (ICTreeCons q l _ lt t1' t2') := ICTCons q l lt (Lefts t1') (Lefts t2') *)
  (*   }. *)
  (* Equations Rights {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)) : ICTree l := *)
  (*   { *)
  (*     Rights (LeafTreeIChoice q p P1 Q1 P2 Q2) := Sapling q Q1 Q2; *)
  (*     Rights (ICTreeCons q l _ lt t1' t2') := ICTCons q l lt (Rights t1') (Rights t2') *)
  (*   }. *)
  
  (* (* If every leaf is an internal choice, merges that choice into the tree. *) *)
  (* Equations MergeTree {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)) *)
  (*   : ICTree (InsertRole p l) := *)
  (*   { *)
  (*     MergeTree (LeafTreeIChoice q p P1 Q1 P2 Q2) with RoleOrderDec q p => *)
  (*     { *)
  (*       MergeTree(LeafTreeIChoice q p P1 Q1 P2 Q2) (left o) := *)
  (*         ICTCons q [p] _ (Sapling p P1 P2) (Sapling p Q1 Q2); *)
  (*       MergeTree(LeafTreeIChoice q p P1 Q1 P2 Q2) (right n) := *)
  (*         ICTCons p [q] _ (Sapling q P1 Q1) (Sapling q P2 Q2) *)
  (*     }; *)
  (*     MergeTree (ICTreeCons q l _ lt t1' t2') with RoleOrderDec q p => *)
  (*     { *)
  (*       MergeTree (ICTreeCons q l (IChoiceAct p) lt t1' t2') (left o) := *)
  (*         ICTCons q _ _ (MergeTree t1') (MergeTree t2'); *)
  (*       MergeTree (p := p) (ICTreeCons q l (IChoiceAct p) lt t1' t2') (right n) := *)
  (*         ICTCons p _ _ (ICTCons q  _ _ (Lefts t1') (Lefts t2')) (ICTCons q _ _ (Rights t1') (Rights t2')) *)
  (*     } *)
  (*   }. *)
  (* Next Obligation. *)
  (*   destruct H; [| inversion H]; subst; auto. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   destruct H; [| inversion H]; subst; auto. *)
  (*   rename q0 into q; destruct (RoleOrderTotal p q); auto. *)
  (*   exfalso; apply n; auto. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   apply InInsertRole in H; destruct H; subst; auto. *)
  (* Defined. *)
  (* Next Obligation. *)
  (*   assert (p ≤r q) as pleq by (destruct (RoleOrderTotal p q); [|exfalso; apply n]; auto); *)
  (*     destruct H; subst; auto; apply RoleOrderTrans with (q := q); auto. *)
  (* Defined. *)
  (* (* Inductive ICTreeA : (list Role) -> Action -> Set := *) *)
  (* (*   LeafTreeEnd        : forall p, ICTreeA [p] EndAct *) *)
  (* (* | LeafTreeVar        : forall p n, ICTreeA [p] (VarAct n) *) *)
  (* (* | LeafTreeDef        : forall p, Proc -> Proc -> Proc -> Proc -> *) *)
  (* (*                             ICTreeA [p] DefAct *) *)
  (* (* | LeafTreeSend       : forall p q e, Proc -> Proc -> *) *)
  (* (*                                 ICTreeA [p] (SendAct q e) *) *)
  (* (* | LeafTreeRecv       : forall p q, Proc -> Proc -> *) *)
  (* (*                               ICTreeA [p] (RecvAct q) *) *)
  (* (* | LeafTreeEChoiceL   : forall p q, Proc -> Proc -> *) *)
  (* (*                               ICTreeA [p] (EChoiceLAct q) *) *)
  (* (* | LeafTreeEChoiceR   : forall p q, Proc -> Proc -> *) *)
  (* (*                               ICTreeA [p] (EChoiceRAct q) *) *)
  (* (* | LeafTreeIChoice    : forall p q, Proc -> Proc -> Proc -> Proc -> *) *)
  (* (*                             ICTreeA [p] (IChoiceAct q) *) *)
  (* (* | LeafTreeIfThenElse : forall p e, Proc -> Proc -> Proc -> Proc -> *) *)
  (* (*                               ICTreeA [p] (IfThenElseAct e) *) *)
  (* (* | LeafTreeMixed      : forall p, Proc -> Proc -> ICTreeA [p] UnknownAct *) *)
  (* (* | ICTreeCons         : forall p l A, (forall q, In q l -> p ≤r q) -> *) *)
  (* (*                                 ICTreeA l A -> ICTreeA l A -> ICTreeA (p :: l) A. *) *)

  (* Fixpoint ProcSize (P : Proc) : nat := *)
  (*   match P with *)
  (*   | EndProc => 1 *)
  (*   | VarProc n => 1 *)
  (*   | DefProc P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   | SendProc p e P => 1 + (ProcSize P) *)
  (*   | RecvProc p P => 1 + (ProcSize P) *)
  (*   | EChoiceL p P => 1 + (ProcSize P) *)
  (*   | EChoiceR p P => 1 + (ProcSize P) *)
  (*   | IChoice p P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   | IfThenElse e P Q => 1 + (ProcSize P) + (ProcSize Q) *)
  (*   end. *)
  
  (* Fixpoint ICTreeASize {l : list Role} {A : Action} (t : ICTreeA l A) : nat := *)
  (*   match t with *)
  (*   | LeafTreeEnd p => 1 *)
  (*   | LeafTreeVar p n => 1 *)
  (*   | LeafTreeDef p P Q1 Q2 => 1 + (ProcSize P) + (ProcSize Q1) + (ProcSize Q2) *)
  (*   | LeafTreeSend p q e P1 P2 => 1 + (ProcSize P1) + (ProcSize P2) *)
  (*   | LeafTreeRecv p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2) *)
  (*   | LeafTreeEChoiceL p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2) *)
  (*   | LeafTreeEChoiceR p q P1 P2 => 1 + (ProcSize P1) + (ProcSize P2) *)
  (*   | LeafTreeIChoice p q P1 Q1 P2 Q2 => 1 + (ProcSize P1) + (ProcSize Q1) + (ProcSize P2) + (ProcSize Q2) *)
  (*   | LeafTreeIfThenElse p e P1 Q1 P2 Q2 => 1 + (ProcSize P1) + (ProcSize Q1) + (ProcSize P2) + (ProcSize Q2) *)
  (*   | LeafTreeMixed p P1 P2 => 1 + (ProcSize P1) + (ProcSize P2) *)
  (*   | ICTreeCons p l A std t1 t2 => 1 + ICTreeASize t1  + ICTreeASize t2 *)
  (*   end. *)

  (* Definition ICTreeSize {l : list Role} (t : ICTree l) : nat := *)
  (*   match t with *)
  (*   | mkTree _ TheAction TheTree => ICTreeASize TheTree *)
  (*   end. *)

  (* Lemma SaplingSize : forall p P Q, ICTreeSize (Sapling p P Q) <= 1 + (ProcSize P) + (ProcSize Q). *)
  (* Proof. *)
  (*   intros p P Q. *)
  (*   funelim (Sapling p P Q); simp Sapling; auto. *)
  (*   all: try (rewrite Heq); try (rewrite Heq0); autorewrite with Sapling; simpl; auto. *)
  (*   2,3: rewrite Heq; autorewrite with Sapling; simpl. *)
  (*   3: reflexivity. *)
  (*   all: try (rewrite Nat.add_succ_r; apply le_n_S; repeat apply Nat.le_le_succ_r). *)
  (*   all: try reflexivity. *)
  (*   - apply plus_le_compat_l. apply le_plus_r. *)
  (*   - rewrite plus_assoc; reflexivity. *)
  (*   - rewrite plus_assoc; reflexivity. *)
  (* Qed. *)

  (* Lemma ProcSizeBounded : forall P : Proc, 1 <= ProcSize P. *)
  (* Proof. *)
  (*   intros P. destruct P; simpl; auto; apply le_n_S; apply Nat.le_0_l. *)
  (* Qed. *)

  (* Lemma ICTConsSize : forall p l lt t1 t2, ICTreeSize (ICTCons p l lt t1 t2) <= S(ICTreeSize t1 + ICTreeSize t2). *)
  (* Proof. *)
  (*   intros p l lt t1 t2. unfold ICTCons; destruct t1 as [A1 t1]; destruct t2 as [A2 t2]. *)
  (*   funelim (ICTConsA p l A1 A2 lt t1 t2); autorewrite with ICTConsA; simpl. *)
  (*   all: auto. *)
    

  (* Lemma LeftsSize : forall {l : list Role} {p : Role} (t : ICTreeA l (IChoiceAct p)), ICTreeSize (Lefts t) < ICTreeASize t. *)
  (* Proof. *)
  (*   intros l p t. *)
  (*   funelim (Lefts t); autorewrite with Lefts; simpl. *)
  (*   - apply Nat.lt_le_trans with (m := 2 + (ProcSize p18) + (ProcSize p20)); [apply le_n_S; apply SaplingSize |]. *)
  (*     simpl. apply le_n_S. transitivity (ProcSize p18 + 1 + ProcSize p20 + ProcSize p21). *)
  (*     -- rewrite Nat.add_succ_r. simpl. rewrite Nat.add_0_r. apply le_n_S. apply le_plus_l. *)
  (*     -- repeat rewrite <- plus_assoc. apply plus_le_compat_l. apply plus_le_compat_r. apply ProcSizeBounded. *)
  (*   -  *)
      

  (* Lemma MergeTreeSize :  *)
  
  (* Equations ICTreeMinProc {l : list Role} (t : ICTree l) : Proc by wf (ICTreeSize t) lt := *)
  (*   { *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeEnd p)) := EndProc; *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeVar p n)) := VarProc n; *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeDef p P Q1 Q2)) := DefProc P (ICTreeMinProc (Sapling p Q1 Q2)); *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeSend p q e P1 P2)) := Send q e (ICTreeMinProc (Sapling p P1 P2)); *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeRecv p q P1 P2)) := Recv q (ICTreeMinProc (Sapling p P1 P2)); *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeEChoiceL p q P1 P2)) := EChoiceL q (ICTreeMinProc (Sapling p P1 P2)); *)
  (*     ICTreeMinProc (mkTree _ (LeafTreeEChoiceR p q P1 P2)) := EChoiceR q (ICTreeMinProc (Sapling p P1 P2)); *)
  (*   }. *)
  
  
  (* Fixpoint InsertIChoice (p : Role) (P Q : Proc) : Proc := *)
  (*   let default := IChoice p P Q  *)
  (*   in BothIChoice *)
  (*        P Q default *)
  (*        (fun q P1 P2 r Q1 Q2 => *)
  (*           if L.eq_dec q r *)
  (*           then if RoleOrderDec q p *)
  (*                then if L.eq_dec p q *)
  (*                     then default *)
  (*                     else IChoice q (InsertIChoice p P1 Q1) (InsertIChoice p P2 Q2) *)
  (*                else default *)
  (*           else default). *)

  (* Ltac LICF := repeat match goal with *)
  (*                     | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity *)
  (*                     | [ H1 : ?P, H2 : ~ ?P |- _] => exfalso; apply H2; exact H1 *)
  (*                     | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] => *)
  (*                       exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto *)
  (*                     | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] => *)
  (*                       match goal with *)
  (*                       | [_ : p = q |- _ ] => fail 1 *)
  (*                       | [_ : q = p |- _ ] => fail 1 *)
  (*                       | _ => *)
  (*                         let e := fresh "eq" in *)
  (*                         assert (p = q) as e by (apply RoleOrderAntisym; auto); *)
  (*                         rewrite e in * *)
  (*                       end *)
  (*                     (* | [ |-context[InsertIChoice ?a ?b] ] => destruct a; simpl; auto *) *)
  (*                     | [ |- context[L.eq_dec ?a ?a]] => *)
  (*                       let n := fresh "n" in *)
  (*                       destruct (L.eq_dec a a) as [_|n]; *)
  (*                       [|exfalso; apply n; reflexivity]; simpl; auto *)
  (*                     | [ |- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); subst; simpl; auto *)
  (*                     | [ |- context[RoleOrderDec ?a ?b]] => destruct (RoleOrderDec a b); simpl; auto *)
  (*                     end. *)
  (* (* Lemma InsertIChoiceFlip : forall p q P1_1 P1_2 P2_1 P2_2, *) *)
  (* (*     p <> q -> *) *)
  (* (*     InsertIChoice q (InsertIChoice p P1_1 P2_1) (InsertIChoice p P1_2 P2_2) = *) *)
  (* (*     InsertIChoice p (InsertIChoice q P1_1 P1_2) (InsertIChoice q P2_1 P2_2). *) *)
  (* (* Proof. *) *)
  (* (*   intros p q P1_1; revert p q; induction P1_1; intros p q P1_2 P2_1 P2_2 neq; simpl. *) *)
  (* (*   - destruct P1_2; destruct P2_1; destruct P2_2; simpl. *) *)
  (* (*     all: repeat unfold BothIChoice; try reflexivity. *) *)
  (* (*     all: try (timeout 1 LICF; try reflexivity). *) *)
  (* (*     all: unfold BothIChoice; LICF; try reflexivity. *) *)
      


  (* (*     all: let n := fresh "n" in *) *)
  (* (*          destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; reflexivity]. *) *)
  (* (*     all: let n := fresh "n" in *) *)
  (* (*          destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; reflexivity]. *) *)
  (* (*     all: destruct ( *) *)
    
  (* (*   all: destruct P1_2; destruct P2_1; simpl; auto. *) *)
  (* (*   (* all: destruct P2_2; optimize_heap. *) *) *)
  (* (*   all: try (let n := fresh "n" in *) *)
  (* (*             destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; reflexivity]). *) *)
  (* (*   all: try (let n := fresh "n" in *) *)
  (* (*             destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; reflexivity]). *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)

  (* (*   all: try (let l1 := fresh "l" in *) *)
  (* (*             let n1 := fresh "n" in *) *)
  (* (*             let l2 := fresh "l" in *) *)
  (* (*             let n2 := fresh "n" in *) *)
  (* (*             destruct (RoleOrderDec p q) as [l1 | n1]; *) *)
  (* (*             destruct (RoleOrderDec q p) as [l2 | n2]; *) *)
  (* (*             (* [let e := fresh "eq" in *) *) *)
  (* (*             (*  assert (p = q) as e by (apply RoleOrderAntisym; auto); *) *) *)
  (* (*             (*  try (exfalso; apply neq; rewrite e; reflexivity; fail) | | *) *) *)
  (* (*             (*  exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto] *) *) *)
  (* (*             match goal with *) *)
  (* (*             | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] => *) *)
  (* (*               exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto *) *)
  (* (*             | _ => try (reflexivity) *) *)
  (* (*             end). *) *)
  (* (*   all: match goal with *) *)
  (* (*          | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] => *) *)
  (* (*            match goal with *) *)
  (* (*            | [_ : p = q |- _ ] => fail 1 *) *)
  (* (*            | [_ : q = p |- _ ] => fail 1 *) *)
  (* (*            | _ => *) *)
  (* (*              let e := fresh "eq" in *) *)
  (* (*              assert (p = q) as e by (apply RoleOrderAntisym; auto); *) *)
  (* (*                try (exfalso; apply neq; rewrite e; reflexivity; fail) *) *)
  (* (*            end *) *)
  (* (*          | _ => idtac *) *)
  (* (*        end. *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
  (* (*   all: try (let e := fresh "e" in *) *)
  (* (*             destruct (L.eq_dec q p) as [e |_]; *) *)
  (* (*             [exfalso; apply neq; auto| try reflexivity]). *) *)
  (* (*   all: try (let e := fresh "e" in *) *)
  (* (*             destruct (L.eq_dec p q) as [e |_]; *) *)
  (* (*             [exfalso; apply neq; auto| try reflexivity]). *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
  (* (*   Show. *) *)
  (* (*   all: destruct P2_2; simpl; auto. *) *)
  (* (*   all: try (let n := fresh "n" in destruct (L.eq_dec q q) as [_|n]; *) *)
  (* (*                                   [| exfalso; apply n; reflexivity]; *) *)
  (* (*                                   try reflexivity). *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
  (* (*   Show. *) *)
  (* (*   all: try (destruct (L.eq_dec r r0); simpl; auto). *) *)
  (* (*   all: try (destruct (RoleOrderDec r q); simpl; auto). *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
  (* (*   all: try (destruct (L.eq_dec q r); simpl; auto; subst). *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
  (* (*   Show. *) *)
  (* (*   destruct (L.eq_dec r0 r0) as [_|n]; [|exfalso; apply n; reflexivity]. *) *)
  (* (*   reflexivity. *) *)
  (* (*   Optimize Proof. Optimize Heap. *) *)
    
  (* (*   all: try (let n := fresh "n" in destruct (L.eq_dec r0 r0) as [_|n]; *) *)
  (* (*                                   [|exfalso; apply n; reflexivity]; try reflexivity). *) *)


  (* Fixpoint MergeProcs (p : Role) (P1 P2 : Proc) : Proc := *)
  (*   match P1 with *)
  (*   | EndProc => *)
  (*     match P2 with *)
  (*     | EndProc => IChoice p EndProc EndProc *)
  (*     | _ => IChoice p EndProc P2 *)
  (*     end *)
  (*   | VarProc n => IChoice p P1 P2 *)
  (*   | DefProc _ _ =>  *)
  (*     IChoice p P1 P2 *)
  (*   | SendProc q e P1' => *)
  (*     match P2 with *)
  (*     | SendProc r e' P2' => *)
  (*       if L.eq_dec q r *)
  (*       then if ExprEqDec e e' *)
  (*            then if L.eq_dec p q *)
  (*                 then IChoice p P1 P2 *)
  (*                 else SendProc q e (MergeProcs p P1' P2') *)
  (*            else IChoice p P1 P2 *)
  (*       else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   | RecvProc q P1' => *)
  (*     match P2 with *)
  (*     |RecvProc r P2' => *)
  (*      if L.eq_dec q r *)
  (*      then if L.eq_dec p q *)
  (*           then IChoice p P1 P2 *)
  (*           else RecvProc q (MergeProcs p P1' P2') *)
  (*      else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   | EChoiceL q P1' => *)
  (*     match P2 with *)
  (*     | EChoiceL r P2' => *)
  (*       if L.eq_dec q r *)
  (*       then (* if L.eq_dec p q *) *)
  (*            (* then IChoice p P1 P2 *) *)
  (*            (* else *) EChoiceL q (MergeProcs p P1' P2') *)
  (*       else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   | EChoiceR q P1' =>  *)
  (*     match P2 with *)
  (*     | EChoiceR r P2' => *)
  (*       if L.eq_dec q r *)
  (*       then (* if L.eq_dec p q *) *)
  (*            (* then IChoice p P1 P2 *) *)
  (*            (* else *) EChoiceR q (MergeProcs p P1' P2') *)
  (*       else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   | IChoice q P11 P12 => *)
  (*     match P2 with *)
  (*     | IChoice r P21 P22 => *)
  (*       if L.eq_dec q r *)
  (*       then if L.eq_dec p q *)
  (*            then IChoice p P1 P2 *)
  (*            else if RoleOrderDec p q *)
  (*                 then IChoice p P1 P2 *)
  (*                 else IChoice q (MergeProcs p P11 P21) (MergeProcs p P12 P22) *)
  (*       else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   | IfThenElse e P11 P12 => *)
  (*     match P2 with *)
  (*     | IfThenElse e' P21 P22 => *)
  (*       if ExprEqDec e e' *)
  (*       then IfThenElse e (MergeProcs p P11 P21) (MergeProcs p P12 P22) *)
  (*       else IChoice p P1 P2 *)
  (*     | _ => IChoice p P1 P2 *)
  (*     end *)
  (*   (* | Par P11 P12 => *) *)
  (*   (*   match P2 with *) *)
  (*   (*   | Par P21 P22 => Par (MergeProcs p P11 P21) (MergeProcs p P12 P22) *) *)
  (*   (*   |_ => IChoice p P1 P2 *) *)
  (*   (*   end *) *)
  (*     (* IChoice p P1 P2 *) *)
  (*   end. *)

  (* Lemma SwapMergeProcs: forall p q P1 P2 P3 P4, *)
  (*     p <> q -> *)
  (*     MergeProcs p (MergeProcs q P1 P2) (MergeProcs q P3 P4) = *)
  (*     MergeProcs q (MergeProcs p P1 P3) (MergeProcs p P2 P4). *)
  (* Proof. *)
  (*   intros p q P1; revert p q; induction P1; simpl; intros p q P2 P3 P4 neq; auto. *)
  (*   all: try (destruct P2; destruct P3; simpl; auto; fail). *)
  (*   - destruct P2; destruct P3; destruct P4; simpl; auto. *)
  (*     all: *)
  (*       let n := fresh "n" in *)
  (*       destruct (L.eq_dec p p) as [_|n]; [|exfalso; apply n; auto]; *)
  (*       destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto]. *)
  (*     all: destruct (L.eq_dec p q); subst. *)
  (*     all: try (let n := fresh "n" in destruct (L.eq_dec q q) as [_|n]; [|exfalso; apply n; auto]); auto. *)
  (*     Optimize Proof. Optimize Heap. *)
  (*     Show. *)
  (*     all: repeat match goal with *)
  (*            | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity *)
  (*            | [ H1 : ?P, H2 : ~ ?P |- _] => exfalso; apply H2; exact H1 *)
  (*            | [ n1 : ?p ≰r ?q, n2 : ?q ≰r ?p |- _ ] => *)
  (*              exfalso; destruct (RoleOrderTotal p q); [apply n1 | apply n2]; auto *)
  (*            | [ l1 : ?p ≤r ?q, l2 : ?q ≤r ?p |- _ ] => *)
  (*              match goal with *)
  (*              | [_ : p = q |- _ ] => fail 1 *)
  (*              | [_ : q = p |- _ ] => fail 1 *)
  (*              | _ => *)
  (*                let e := fresh "eq" in *)
  (*                assert (p = q) as e by (apply RoleOrderAntisym; auto); *)
  (*                  rewrite e in * *)
  (*              end *)
  (*            (* | [ |-context[InsertIChoice ?a ?b] ] => destruct a; simpl; auto *) *)
  (*            | [ |- context[L.eq_dec ?a ?a]] => *)
  (*              let n := fresh "n" in *)
  (*              destruct (L.eq_dec a a) as [_|n]; *)
  (*                [|exfalso; apply n; reflexivity]; simpl; auto *)
  (*            | [ |- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); subst; simpl; auto *)
  (*            | [ |- context[ExprEqDec ?a ?a]] => *)
  (*              let n := fresh "n" in *)
  (*              destruct (ExprEqDec a a) as [_|n]; *)
  (*                [|exfalso; apply n; reflexivity]; simpl; auto *)
  (*            | [ |- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); subst; simpl; auto *)
  (*            | [ |- context[RoleOrderDec ?a ?b]] => destruct (RoleOrderDec a b); simpl; auto *)
  (*            end. *)

      
  (*     match goal with *)
  (*     | [ |- context[L.eq_dec ?a ?a]] => *)
  (*       let n := fresh "n" in *)
  (*       destruct (L.eq_dec a a) as [_|n]; [|exfalso; apply n; reflexivity] *)
  (*     | [ |- context[RoleEq *)
      
  (* Fixpoint Normalize (P : Proc) : Proc := *)
  (*   match P with *)
  (*   | EndProc => EndProc *)
  (*   | VarProc n => VarProc n *)
  (*   | DefProc P Q => DefProc (Normalize P) (Normalize Q) *)
  (*   | SendProc p e P => SendProc p e (Normalize P) *)
  (*   | RecvProc p P => RecvProc p (Normalize P) *)
  (*   | EChoiceL p P => EChoiceL p (Normalize P) *)
  (*   | EChoiceR p P => EChoiceR p (Normalize P) *)
  (*   | IChoice p P Q => MergeProcs p (Normalize P) (Normalize Q) *)
  (*   | IfThenElse e P Q => IfThenElse e (Normalize P) (Normalize Q) *)
  (*   (* | Par P Q => Par (Normalize P) (Normalize Q) *) *)
  (*   end. *)

  
End PiCalc.


