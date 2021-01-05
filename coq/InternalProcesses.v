Require Export Expression.
Require Export Locations.
Require Export Choreography.
Require Export ProcessCalculus.
Require Import LocationMap.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Sorted Orders Coq.Sorting.Mergesort Permutation.
Require Import Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Psatz.

From Equations Require Import Equations.

Module InternalProcesses (Import E : Expression) (L : Locations) (LM : LocationMap L).
  Include (LocationNotations L).
  Include ListNotations.

  Module LF := (LocationFacts L).
  Module C := (Choreography E L).
  Module P := (ProcessCalculus E L LM).
  Module LMF := (LocationMapFacts L LM).

  Import C.
  (* Intermediate language for process calculus. Can contain partial IChoices *)
  (* Skip just exists so that <Proc, MergeProcs> forms a monoid. This allows me to develop the unbiased version, which is easier to reason about for twist. *)
  Inductive Proc : Set := 
    Skip : Proc 
  | EndProc : Proc
  | VarProc : nat -> Proc
  | DefProc : Proc -> Proc -> Proc
  | SendProc : Loc -> Expr -> Proc -> Proc
  | RecvProc : Loc -> Proc -> Proc
  | EChoiceL : Loc -> Proc -> Proc
  | EChoiceR : Loc -> Proc -> Proc
  | IChoiceL : Loc -> Proc -> Proc
  | IChoiceR : Loc -> Proc -> Proc
  | IChoiceLR : Loc -> Proc -> Proc -> Proc
  | IfThenElse : Expr -> Proc -> Proc -> Proc.
  Hint Constructors Proc : acc.
  Instance : EqDec Loc := L.eq_dec.
  Instance : EqDec Expr := ExprEqDec.
  Definition ProcEqDec : forall P Q : Proc, {P = Q} + {P <> Q}.
    decide equality.
    all: try (apply L.eq_dec).
    apply Nat.eq_dec.
    all: apply ExprEqDec.
  Defined.
  Instance : EqDec Proc := ProcEqDec.

  Ltac ProcInduction x :=
    let P := fresh "P" in
    let Q := fresh "Q" in
    let p := fresh "p" in
    let e := fresh "e" in
    let IHP := fresh "IH" P in
    let IHQ := fresh "IH" Q in
    let n := fresh "n" in
    induction x as [| | n | P IHP Q IHQ | p e P IHP | p P IHP | p P IHP | p P IHP | p P IHP | p P IHP | p P IHP Q IHQ | e P IHP Q IHQ].
  Ltac ProcDestruct x :=
    let P := fresh "P" in
    let Q := fresh "Q" in
    let p := fresh "p" in
    let e := fresh "e" in
    let n := fresh "n" in
    induction x as [| | n | P Q | p e P | p P | p P | p P | p P | p P | p P Q | e P Q].
  
  Fixpoint NoPartialIChoices (P : Proc) : Prop :=
    match P with
    | Skip => False
    | EndProc => True
    | VarProc x => True
    | DefProc P Q => NoPartialIChoices P /\ NoPartialIChoices Q
    | SendProc p e P => NoPartialIChoices P
    | RecvProc p P => NoPartialIChoices P
    | EChoiceL p P => NoPartialIChoices P
    | EChoiceR p P => NoPartialIChoices P
    | IChoiceL p P => False
    | IChoiceR p P => False
    | IChoiceLR p P Q => NoPartialIChoices P /\ NoPartialIChoices Q
    | IfThenElse e P Q => NoPartialIChoices P /\ NoPartialIChoices Q
    end.

  Fixpoint ProcToProc (P : Proc) : option P.Proc :=
    match P with
    | Skip => None
    | EndProc => Some P.EndProc
    | VarProc X => Some (P.VarProc X)
    | DefProc P Q =>
      match (ProcToProc P) with
      | Some P' =>
        match (ProcToProc Q) with
        | Some Q' => Some (P.DefProc P' Q')
        | None => None
        end
      | None => None
      end
    | SendProc p e P =>
      match ProcToProc P with
      | Some P' => Some (P.SendProc p e P')
      | None => None
      end
    | RecvProc p P =>
      match ProcToProc P with
      | Some P' => Some (P.RecvProc p P')
      | None => None
      end
    | EChoiceL p P =>
      match ProcToProc P with
      | Some P' => Some (P.EChoiceL p P')
      | None => None
      end
    | EChoiceR p P =>
      match ProcToProc P with
      | Some P' => Some (P.EChoiceR p P')
      | None => None
      end
    | IChoiceL p P => None
    | IChoiceR p P => None
    | IChoiceLR p P Q =>
      match ProcToProc P with
      | Some P' => match ProcToProc Q with
                  | Some Q' => Some (P.IChoice p P' Q')
                  | None => None
                  end
      | None => None
      end
    | IfThenElse e P Q =>
      match ProcToProc P with
      | Some P' => match ProcToProc Q with
                  | Some Q' => Some (P.IfThenElse e P' Q')
                  | None => None
                  end
      | None => None
      end
    end.

  Theorem TotalProcToProc : forall (P : Proc), NoPartialIChoices P -> ProcToProc P <> None.
  Proof using.
    intro x; ProcInduction x; intro npic; cbn in *; try discriminate.
    all: repeat match goal with
                | [H : False |- _] => destruct H
                | [H : ?P, H' : ?P -> ?a <> ?a |- _ ] => exfalso; apply (H' H); auto
                | [H : ?a <> ?a |- _] => exfalso; apply H; auto
                | [|- Some _ <> None] => discriminate
                | [H : ?P /\ ?Q |- _ ] => destruct H
                | [|- context[ProcToProc ?P]] =>
                  let iptp := fresh "iptp_" P in
                  destruct (ProcToProc P) eqn:iptp
                end.
  Qed.
  Corollary TotalProcToProc_Exists : forall (P : Proc), NoPartialIChoices P -> exists Q : P.Proc, ProcToProc P = Some Q.
  Proof using.
    intros P npic; destruct (ProcToProc P) as [Q|] eqn:iptp_P; [exists Q; reflexivity | apply TotalProcToProc in iptp_P; auto; destruct iptp_P].
  Qed.

  Fixpoint MergeProcs (P Q : Proc) : option Proc :=
    match P with
    | Skip => Some Q
    | EndProc =>
      match Q with
      | EndProc => Some EndProc
      | Skip => Some P
      | _ => None
      end
    | VarProc x =>
      match Q with
      | VarProc y => if Nat.eq_dec x y then Some (VarProc x) else None
      | Skip => Some P
      | _ => None
      end 
    | DefProc P1 Q1 =>
      match Q with
      | Skip => Some P
      | DefProc P2 Q2 =>
        match MergeProcs P1 P2 with
        | Some P => match MergeProcs Q1 Q2 with
                   | Some Q => Some (DefProc P Q)
                   | None => None
                   end
        | None => None
        end
      | _ => None
      end
    | SendProc p e P' =>
      match Q with
      | Skip => Some P
      | SendProc q e' Q' =>
        if L.eq_dec p q
        then if ExprEqDec e e'
             then match MergeProcs P' Q' with
                  | Some R => Some (SendProc p e R)
                  | None => None
                  end
             else None
        else None
      | _ => None
      end
    | RecvProc p P' =>
      match Q with
      | Skip => Some P
      | RecvProc q Q' =>
        if L.eq_dec p q
        then match MergeProcs P' Q' with
             | Some R => Some (RecvProc p R)
             | _ => None
             end
        else None
      | _ => None
      end
    | EChoiceL p P' =>
      match Q with
      | Skip => Some P
      | EChoiceL q Q' =>
        if L.eq_dec p q
        then match MergeProcs P' Q' with
             | Some R => Some (EChoiceL p R)
             | None => None
             end
        else None
      | _ => None
      end
    | EChoiceR p P' =>
      match Q with
      | Skip => Some P
      | EChoiceR q Q' =>
        if L.eq_dec p q
        then match MergeProcs P' Q' with
             | Some R => Some (EChoiceR p R)
             | None => None
             end
        else None
      | _ => None
      end
    | IChoiceL p P1 =>
      match Q with
      | Skip => Some P
      | IChoiceL q P2 =>
        if L.eq_dec p q
        then match MergeProcs P1 P2 with
             | Some R => Some (IChoiceL p R)
             | None => None
             end
        else None
      | IChoiceR q Q1 =>
        if L.eq_dec p q
        then Some (IChoiceLR p P1 Q1)
        else None
      | IChoiceLR q P2 Q1 =>
        if L.eq_dec p q
        then match MergeProcs P1 P2 with
             | Some R => Some (IChoiceLR p R Q1)
             | None => None
             end
        else None
      | _ => None
      end
    | IChoiceR p Q1 =>
      match Q with
      | Skip => Some P
      | IChoiceL q P1 =>
        if L.eq_dec p q
        then Some (IChoiceLR p P1 Q1)
        else None
      | IChoiceR q Q2 =>
        if L.eq_dec p q
        then match MergeProcs Q1 Q2 with
             | Some R => Some (IChoiceR p R)
             | None => None
             end
        else None
      | IChoiceLR q P1 Q2 =>
        if L.eq_dec p q
        then match MergeProcs Q1 Q2 with
             | Some R => Some (IChoiceLR p P1 R)
             | None => None
             end
        else None
      | _ => None
      end      
    | IChoiceLR p P1 Q1 => 
      match Q with
      | Skip => Some P
      | IChoiceL q P2 =>
        if L.eq_dec p q
        then match MergeProcs P1 P2 with
             | Some R => Some (IChoiceLR p R Q1)
             | None => None
             end
        else None
      | IChoiceR q Q2 =>
        if L.eq_dec p q
        then match MergeProcs Q1 Q2 with
             | Some R => Some (IChoiceLR p P1 R)
             | None => None
             end
        else None
      | IChoiceLR q P2 Q2 =>
        if L.eq_dec p q
        then match MergeProcs P1 P2 with
             | Some P => match MergeProcs Q1 Q2 with
                        | Some Q => Some (IChoiceLR p P Q)
                        | None => None
                        end
             | None => None
             end
        else None
      | _ => None
      end
    | IfThenElse e P1 Q1 =>
      match Q with
      | Skip => Some P
      | IfThenElse e' P2 Q2 =>
        if ExprEqDec e e'
        then match MergeProcs P1 P2 with
             | Some P => match MergeProcs Q1 Q2 with
                        | Some Q => Some (IfThenElse e P Q)
                        | None => None
                        end
             | None => None
             end
        else None
      | _ => None
      end
    end.

  Lemma MergeProcsComm : forall P Q, MergeProcs P Q = MergeProcs Q P.
  Proof using.
    intros P; induction P; destruct Q; cbn; auto.
    all: repeat match goal with
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; auto
                | [ |- ?a = ?a ] => reflexivity
                | [|- context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; auto
                | [|- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); LF.LocationOrder; subst; auto
                | [|- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); LF.LocationOrder; subst; auto
                | [|- context[MergeProcs ?a ?b]] => try (let eq := fresh "merge_" a "_" b in destruct (MergeProcs a b) eqn:eq); simp MergeProc; cbn; auto
                | [ IH : forall Q, MergeProcs ?P Q = MergeProcs Q ?P, H1 : MergeProcs ?P ?Q = ?a, H2 : MergeProcs ?Q ?P = ?b |- _ ] =>
                  rewrite IH in H1; rewrite H2 in H1; inversion H1; subst; clear H1
                end.
  Qed.

  Lemma MergeProcsInvolutive : forall P, MergeProcs P P = Some P.
  Proof using.
    intro P; induction P; cbn; auto.
    all: repeat match goal with
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; auto
                | [ |- ?a = ?a ] => reflexivity
                | [|- context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; auto
                | [|- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); LF.LocationOrder; subst; auto
                | [|- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); LF.LocationOrder; subst; auto
                | [ H : MergeProcs ?a ?a = Some ?a |- context[MergeProcs ?a ?a]] => rewrite H; auto
                end.
  Qed.
  Lemma MergeProcsIdentityL : forall P, MergeProcs Skip P = Some P.
  Proof using.
    intro P; cbn; auto.
  Qed.
  Lemma MergeProcsIdentityR : forall P, MergeProcs P Skip = Some P.
  Proof using.
    destruct P; cbn; auto.
  Qed.
    
  Definition OptionSequence : forall {A B : Type}, (A -> option B) -> option A -> option B :=
    fun A B f oa => match oa with
                 | Some a => f a
                 | None => None
                 end.
  Definition OptionSequence2 : forall {A B C : Type}, (A -> B -> option C) -> option A -> option B -> option C :=
    fun A B C f oa ob => match oa with
                      | Some a => match ob with
                                 | Some b => f a b
                                 | None => None
                                 end
                      | None => None
                      end.

  Inductive MarkedSequence : Proc -> Proc -> Proc -> Proc -> Prop := Mark : forall P Q R S, MarkedSequence P Q R S.
  Lemma MergeProcsAssoc : forall P Q R, OptionSequence (MergeProcs P) (MergeProcs Q R) = OptionSequence (fun P => MergeProcs P R) (MergeProcs P Q).
  Proof using.
    intro P; induction P; intros Q R; destruct Q; destruct R; cbn;
      repeat match goal with
             | [ |- ?a = ?a ] => reflexivity
             | [ H : Some _ = None |- _ ] => inversion H
             | [ H : None = Some _ |- _ ] => inversion H
             | [ H : Some ?a = Some ?b |- _ ] => inversion H; subst; clear H
             | [ H1 : ?a = Some _, H2 : ?a = None |- _ ] => rewrite H1 in H2; inversion H2
             | [ H1 : ?a = Some _, H2 : None = ?a |- _ ] => rewrite H1 in H2; inversion H2
             | [ H1 : Some _ = ?a, H2 : None = ?a |- _ ] => rewrite <- H1 in H2; inversion H2
             | [ H1 : Some _ = ?a, H2 : ?a = None |- _ ] => rewrite <- H1 in H2; inversion H2
             | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl)
             | [ |- None = Some _ -> _ ] => let H := fresh in intro H; inversion H
             | [ |- Some ?a = Some ?b -> _ ] => let H := fresh in intro H; inversion H; subst; clear H; cbn
             | [ |- _ -> Some _ = None -> _ ] => let H := fresh in let H' := fresh in intros H  H'; inversion H'
             | [ |- _ -> Some ?a = Some ?b -> _ ] => let H := fresh in let H' := fresh in intros H H'; revert H; inversion H'; subst; clear H'
             | [ |- context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; cbn
             | [ |- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); subst; cbn
             | [ |- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); subst; cbn
             | [ |- context[MergeProcs ?a ?b]] => let eq := fresh "eq" in destruct (MergeProcs a b) eqn:eq; cbn
             (* | [ IH : forall Q R, OptionSequence (MergeProcs ?P) (MergeProcs Q R) = OptionSequence (fun S => MergeProcs S R) (MergeProcs ?P Q), H : MergeProcs ?P ?Q = Some ?S, H' : MergeProcs ?Q ?R = Some ?T, eq1 : MergeProcs ?S ?R = _, eq2 : MergeProcs ?P ?T = _ |- _ ] => *)
             (*   lazymatch goal with *)
             (*   | [_ : MarkedSequence P Q R S |- _ ] => fail *)
             (*   | _ => pose proof (Mark P Q R S); let eq := fresh "eq" in pose proof (IH Q R) as eq; rewrite H' in eq; rewrite H in eq; cbn in eq; rewrite eq1 in eq; rewrite eq2 in eq; cbn in eq *)
             (*   end *)
             | [ IH : forall Q R, OptionSequence (MergeProcs ?P) (MergeProcs Q R) = OptionSequence (fun S => MergeProcs S R) (MergeProcs ?P Q), H : MergeProcs ?P ?Q = _, H' : MergeProcs ?Q ?R = _ |- _ ] =>
               lazymatch goal with
               | [_ : MarkedSequence P Q P Q |- _ ] => fail
               | _ => pose proof (Mark P Q P Q); let eq := fresh "eq" in pose proof (IH Q R) as eq; rewrite H' in eq; rewrite H in eq; cbn in eq
               end
             | [ H : MergeProcs ?a ?b = MergeProcs ?c ?d, H' : MergeProcs ?a ?b = Some _, H'' : MergeProcs ?c ?d = _ |- _ ] =>
               rewrite H' in H; rewrite H'' in H; inversion H; subst; clear H
             | [ H : MergeProcs ?a ?b = MergeProcs ?c ?d, H' : MergeProcs ?a ?b = None, H'' : MergeProcs ?c ?d = _ |- _ ] =>
               rewrite H' in H; rewrite H'' in H; inversion H; subst; clear H
             end.
  Qed.
  Corollary MergeProcsAssoc' : forall P Q R S T, MergeProcs P Q = Some S -> MergeProcs Q R = Some T -> MergeProcs S R = MergeProcs P T.
  Proof using.
    intros P Q R S T H H0; pose proof (MergeProcsAssoc P Q R) as eq; rewrite H in eq; rewrite H0 in eq; cbn in eq; auto.
  Qed.

  Fixpoint MergeProcsList (l : list Proc) : option Proc :=
    match l with
    | [] => Some Skip
    | [P] => Some P
    | P :: l => OptionSequence (MergeProcs P) (MergeProcsList l)
    end.

  Lemma MergeProcsList2 : forall P Q, MergeProcs P Q = MergeProcsList [P; Q].
  Proof using.
    intros P Q; cbn; auto.
  Qed.

  Fixpoint Deduplicate_ProcList (l : list Proc) : list Proc :=
    match l with
    | [] => []
    | P :: l => if in_dec ProcEqDec P l then Deduplicate_ProcList l else P :: (Deduplicate_ProcList l)
    end.

  Lemma Deduplicate_In : forall P l, In P l -> In P (Deduplicate_ProcList l).
  Proof using.
    intros P l; induction l; cbn; auto; intro i.
    destruct i as [eq | i]; subst; auto. destruct (in_dec ProcEqDec P l); auto; left; auto.
    destruct (in_dec ProcEqDec a l); auto; right; auto.
  Qed.
    
  Lemma Deduplicate_In2In : forall P l, In P (Deduplicate_ProcList l) -> In P l.
  Proof using.
    intros P l; induction l; cbn; auto; intro i.
    destruct (in_dec ProcEqDec a l). right; auto. destruct i; auto.
  Qed.
  Lemma NoDup_Deduplicate : forall l, NoDup (Deduplicate_ProcList l).
  Proof using.
    intro l; induction l; cbn; try (constructor; auto; fail).
    destruct (in_dec ProcEqDec a l); auto. constructor; auto. intro i; apply n; apply Deduplicate_In2In; auto.
  Qed.

  Lemma EquivToPerm : forall l l', (forall P, In P l <-> In P l') -> Permutation (Deduplicate_ProcList l) (Deduplicate_ProcList l').
  Proof using.
    intros l l' eqv; apply NoDup_Permutation; try (apply NoDup_Deduplicate).
    intro P; split; intro i; apply Deduplicate_In2In in i; apply eqv in i; apply Deduplicate_In in i; auto.
  Qed.

  Lemma MergeProcsListPerm : forall l l', Permutation l l' -> MergeProcsList l = MergeProcsList l'.
  Proof using.
    intros l l' perm; induction perm; auto; cbn.
    - destruct l. apply Permutation_nil in perm; subst; auto. destruct l'. apply Permutation_sym in perm; apply Permutation_nil_cons in perm; destruct perm.
      rewrite IHperm; auto.
    - destruct l; cbn. apply MergeProcsComm.
      destruct (match l with
                | [] => Some p
                | _ :: _ => OptionSequence (MergeProcs p) (MergeProcsList l)
                end); cbn; auto.
      pose proof (MergeProcsAssoc x y p0).
      pose proof (MergeProcsAssoc y x p0).
      rewrite MergeProcsComm with (P := y) (Q := x) in H0. rewrite <- H0 in H. rewrite H. reflexivity.
    - transitivity (MergeProcsList l'); auto.
  Qed.

  Lemma MergeProcsIn : forall P l, In P l -> MergeProcsList (P :: l) = MergeProcsList l.
  Proof using.
    intros P l; revert P; induction l as [| Q l]; intros P i; cbn; [inversion i|].
    destruct l; [cbn; destruct i as [eq|i]; [|inversion i]; subst; apply MergeProcsInvolutive|].
    destruct i as [eq|i]; subst; cbn; destruct (match l with
                                                | [] => Some p
                                                | _ :: _ => OptionSequence (MergeProcs p) (MergeProcsList l)
                                                end) eqn:eq; cbn; auto.
    rewrite (MergeProcsAssoc P P p0); rewrite MergeProcsInvolutive; cbn; auto.
    pose proof (IHl P i) as H; cbn in H. rewrite eq in H.
    rewrite MergeProcsComm with (P := Q) (Q := p0).
    rewrite (MergeProcsAssoc P p0 Q). cbn in H. rewrite H. cbn. reflexivity.
  Qed.
    

  Lemma MergeProcsDeduplicate : forall l, MergeProcsList l = MergeProcsList (Deduplicate_ProcList l).
  Proof using.
    intro l; induction l; cbn; auto.
    destruct (in_dec ProcEqDec a l); cbn.
    destruct l; [inversion i |rewrite <- IHl; apply MergeProcsIn in i; rewrite <- i at 2; auto].
    rewrite <- IHl.
    destruct l. cbn; auto.
    destruct (Deduplicate_ProcList (p :: l)) eqn:eq. assert (In p []) as H by (rewrite <- eq; apply Deduplicate_In; left; auto); inversion H.
    reflexivity.
  Qed.

  Corollary MergeProcsEquiv : forall l l', (forall P, In P l <-> In P l') -> MergeProcsList l = MergeProcsList l'.
  Proof using.
    intros l l' H; rewrite MergeProcsDeduplicate; rewrite (MergeProcsDeduplicate l'); apply MergeProcsListPerm; apply EquivToPerm; auto.
  Qed.

  Lemma MergeProcsApp : forall l l', (OptionSequence2 MergeProcs) (MergeProcsList l) (MergeProcsList l') = MergeProcsList (l ++ l').
  Proof using.
    intro l; induction l as [|P l]; cbn; intro l'.
    destruct (MergeProcsList l'); auto.
    rewrite <- IHl.
    destruct (l ++ l') eqn:eq. apply app_eq_nil in eq; destruct eq; subst; cbn; rewrite MergeProcsIdentityR; reflexivity.
    destruct l; cbn in eq; subst. rewrite IHl. rewrite app_nil_l. destruct (MergeProcsList (p :: l0)); cbn; auto.
    inversion eq; subst; clear eq. cbn. destruct (match l with | [] => Some p | _ :: _ => OptionSequence (MergeProcs p) (MergeProcsList l) end); cbn; auto.
    destruct (MergeProcsList l'); cbn.
    rewrite (MergeProcsAssoc P p0 p1). destruct (MergeProcs P p0); cbn; reflexivity.
    destruct (MergeProcs P p0); cbn; reflexivity.
  Qed.
       
  Lemma MergeProcsTwist : forall P1 P2 Q1 Q2, (OptionSequence2 MergeProcs) (MergeProcs P1 Q1) (MergeProcs P2 Q2) = (OptionSequence2 MergeProcs) (MergeProcs P1 P2) (MergeProcs Q1 Q2).
  Proof using.
    intros P1 P2 Q1 Q2. repeat rewrite MergeProcsList2. repeat rewrite MergeProcsApp. apply MergeProcsListPerm.
    cbn; repeat constructor; auto; fail.
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

  Reserved Notation "P ⟨iπ| ξ ⟩" (at level 15).
  Fixpoint ProcRenaming (P : Proc) (ξ : nat -> nat) : Proc :=
    match P with
    | EndProc => EndProc
    | Skip => Skip
    | VarProc n => VarProc (ξ n)
    | DefProc P Q => DefProc (P ⟨iπ| ProcRenamingUp ξ⟩) (Q ⟨iπ| ProcRenamingUp ξ⟩)
    | SendProc p e P => SendProc p e (P ⟨iπ| ξ⟩)
    | RecvProc p P => RecvProc p (P ⟨iπ| ξ⟩)
    | EChoiceL p P => EChoiceL p (P ⟨iπ| ξ⟩)
    | EChoiceR p P => EChoiceR p (P ⟨iπ| ξ⟩)
    | IChoiceL p P => IChoiceL p (P ⟨iπ| ξ⟩)
    | IChoiceR p Q => IChoiceR p (Q ⟨iπ| ξ⟩)
    | IChoiceLR p P Q => IChoiceLR p (P ⟨iπ| ξ⟩) (Q ⟨iπ| ξ⟩)
    | IfThenElse e P Q => IfThenElse e (P ⟨iπ| ξ⟩) (Q ⟨iπ| ξ⟩)
    end
  where "P ⟨iπ| ξ ⟩" := (ProcRenaming P ξ).

    Lemma ProcRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨iπ| ξ1⟩ = P ⟨iπ| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; auto.
    2-7: rewrite IHP with (ξ2 := ξ2); auto.
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
      P ⟨iπ| ProcRenamingId⟩ = P.
  Proof.
    intro P; induction P; simpl; try reflexivity.
    2-7: rewrite IHP; auto.
    repeat (
        rewrite ProcRenamingExt
          with (ξ1 := ProcRenamingUp ProcRenamingId) (ξ2 := ProcRenamingId);
        [| exact ProcRenamingIdUp]).
    all: rewrite IHP1; rewrite IHP2; reflexivity.
  Qed.    

  Reserved Notation "P ⟨iπe| ξ ⟩" (at level 15).
  Fixpoint ProcExprRenaming (P : Proc) (ξ : nat -> nat) : Proc :=
    match P with
    | EndProc => EndProc
    | Skip => Skip
    | VarProc n => VarProc n
    | DefProc P Q => DefProc (P ⟨iπe| ξ⟩) (Q ⟨iπe| ξ⟩)
    | SendProc p e P => SendProc p (e ⟨e| ξ⟩) (P ⟨iπe| ξ⟩)
    | RecvProc p P => RecvProc p (P ⟨iπe| ExprUpRename ξ⟩)
    | EChoiceL p P => EChoiceL p (P ⟨iπe| ξ⟩)
    | EChoiceR p P => EChoiceR p (P ⟨iπe| ξ⟩)
    | IChoiceL p P => IChoiceL p (P ⟨iπe| ξ⟩)
    | IChoiceR p Q => IChoiceR p (Q ⟨iπe| ξ⟩)
    | IChoiceLR p P Q => IChoiceLR p (P ⟨iπe| ξ⟩) (Q ⟨iπe| ξ⟩)
    | IfThenElse e P Q => IfThenElse (e ⟨e| ξ⟩) (P ⟨iπe| ξ⟩) (Q ⟨iπe| ξ⟩)
    end
  where "P ⟨iπe| ξ ⟩" := (ProcExprRenaming P ξ).

  Lemma ProcExprRenamingExt : forall (P : Proc) (ξ1 ξ2 : nat -> nat),
      (forall n, ξ1 n = ξ2 n)
      -> P ⟨iπe| ξ1⟩ = P ⟨iπe| ξ2⟩.
  Proof.
    intro P; induction P; intros ξ1 ξ2 ext_eq; simpl; try reflexivity.
    2,4,5,6,7: rewrite IHP with (ξ2 := ξ2); auto.
    1,4,5: rewrite IHP1 with (ξ2 := ξ2); [|exact ext_eq]; rewrite IHP2 with (ξ2 := ξ2); auto.
    1,2: rewrite ExprRenameExt with (ξ2 := ξ2); auto.
    rewrite IHP with (ξ2 := ExprUpRename ξ2); auto.
    intro n; unfold ExprUpRename; destruct n; auto.
  Qed.

  Lemma ProcExprRenamingId : forall (P : Proc),
      P ⟨iπe| ExprIdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,8,9: rewrite IHP1; rewrite IHP2; auto.
    3: rewrite ProcExprRenamingExt with (ξ2 := ExprIdRenaming);
      [|intro n; symmetry; apply ExprUpRenamingId].
    2-7: rewrite IHP; auto.
    all: rewrite ExprIdRenamingSpec; reflexivity.
  Qed.

    Definition ProcSubstUp : (nat -> Proc) -> nat -> Proc :=
    fun σ n => match n with
            | 0 => VarProc 0
            | S n' => σ n' ⟨iπ| S⟩
            end.

  Lemma ProcSubstUpExt : forall (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n = σ2 n)
      -> forall n, ProcSubstUp σ1 n = ProcSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; unfold ProcSubstUp; destruct n; [|rewrite ext_eq]; reflexivity.
  Qed.

  Reserved Notation "P [iπ| σ ]" (at level 15).
  Fixpoint ProcSubst (P : Proc) (σ : nat -> Proc) :=
    match P with
    | EndProc => EndProc
    | Skip => Skip
    | VarProc n => σ n
    | DefProc P Q => DefProc (P [iπ| ProcSubstUp σ]) (Q [iπ| ProcSubstUp σ])
    | SendProc p e P => SendProc p e (P [iπ| σ])
    | RecvProc p P => RecvProc p (P [iπ| σ])
    | EChoiceL p P => EChoiceL p (P [iπ| σ])
    | EChoiceR p P => EChoiceR p (P [iπ| σ])
    | IChoiceL p P => IChoiceL p (P [iπ| σ])
    | IChoiceR p Q => IChoiceR p (Q [iπ| σ])
    | IChoiceLR p P Q => IChoiceLR p (P [iπ| σ]) (Q [iπ| σ])
    | IfThenElse e P Q => IfThenElse e (P [iπ| σ]) (Q[iπ| σ])
    end
  where "P [iπ| σ ]" := (ProcSubst P σ).

  Lemma ProcSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Proc),
      (forall n, σ1 n = σ2 n)
      -> P [iπ| σ1] = P [iπ| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    2-7: rewrite IHP with (σ2 := σ2); auto.
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

  Lemma ProcSubstId : forall (P : Proc), P [iπ| ProcIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    2-7: rewrite IHP; reflexivity.
    repeat (rewrite ProcSubstExt with (σ1 := ProcSubstUp ProcIdSubst) (σ2 := ProcIdSubst);
            [| exact ProcIdSubstUp]).
    all: rewrite IHP1; rewrite IHP2; reflexivity.
  Qed.

  Reserved Notation "P [iπe| σ ]" (at level 15).
  Fixpoint ProcExprSubst (P : Proc) (σ : nat -> Expr) : Proc :=
    match P with
    | EndProc => EndProc
    | Skip => Skip
    | VarProc n => VarProc n
    | DefProc P Q => DefProc (P [iπe| σ]) (Q [iπe| σ])
    | SendProc p e P => SendProc p (e [e| σ]) (P [iπe| σ])
    | RecvProc p P => RecvProc p (P [iπe| ExprUpSubst σ])
    | EChoiceL p P => EChoiceL p (P [iπe| σ])
    | EChoiceR p P => EChoiceR p (P [iπe| σ])
    | IChoiceL p P => IChoiceL p (P [iπe| σ])
    | IChoiceR p Q => IChoiceR p (Q [iπe| σ])
    | IChoiceLR p P Q => IChoiceLR p (P [iπe| σ]) (Q [iπe| σ])
    | IfThenElse e P Q => IfThenElse (e [e| σ]) (P[iπe|σ]) (Q[iπe|σ])
    end
  where "P [iπe| σ ]" := (ProcExprSubst P σ).

  Lemma ProcExprSubstExt : forall (P : Proc) (σ1 σ2 : nat -> Expr),
      (forall n, σ1 n = σ2 n)
      -> P [iπe| σ1] = P [iπe| σ2].
  Proof.
    intro P; induction P; intros σ1 σ2 ext_eq; simpl; auto.
    1,8,9: rewrite IHP1 with (σ2 := σ2); auto; rewrite IHP2 with (σ2 := σ2); auto.
    2,4-7: rewrite IHP with (σ2 := σ2); auto.
    1,2: rewrite ExprSubstExt with (σ2 := σ2); auto.
    rewrite IHP with (σ2 := ExprUpSubst σ2); auto.
    intro n; unfold ExprUpSubst; destruct n; auto; rewrite ext_eq; reflexivity.
  Qed.

  Lemma ProcExprSubstId : forall (P : Proc),
      P [iπe| ExprIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,8,9: rewrite IHP1; rewrite IHP2; auto.
    2,4-7: rewrite IHP; auto.
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
            | 0 => P [iπ| (fun m => match m with | 0 => DefProc P P | S m' => VarProc m' end)]
            | S n' => VarProc n'
            end.

  Inductive PiCalcStep : LM.t Proc -> LM.t Proc -> Prop :=
    CommEStep : forall (p q : Loc) (e e' : Expr) (P : Proc) (Π Π' : LM.t Proc),
      ExprStep e e'
      -> LM.MapsTo p (SendProc q e P) Π
      -> (forall r, r <> p -> forall Q, LM.MapsTo r Q Π <-> LM.MapsTo r Q Π') (* Perhaps we could get away with only one direction? *)
      -> LM.MapsTo p (SendProc q e' P) Π'
      -> PiCalcStep Π Π'
  | CommVStep : forall (p q : Loc) (v : Expr) (P Q : Proc) (Π Π' : LM.t Proc),
      ExprVal v
      -> LM.MapsTo p (SendProc q v P) Π
      -> LM.MapsTo q (RecvProc p Q) Π
      -> (forall r, r <> p -> r <> q -> forall Q, LM.MapsTo r Q Π <-> LM.MapsTo r Q Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q (Q [iπe| CommSubst v]) Π'
      -> PiCalcStep Π Π'
  | IfEStep : forall (p : Loc) (e e' : Expr) (P Q : Proc) (Π Π' : LM.t Proc),
      ExprStep e e'
      -> LM.MapsTo p (IfThenElse e P Q) Π
      -> (forall r, r <> p -> forall R : Proc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p (IfThenElse e' P Q) Π'
      -> PiCalcStep Π Π'
  | IfTrueStep : forall (p : Loc) (P Q : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (IfThenElse tt P Q) Π
      -> (forall r, r <> p -> forall R : Proc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> PiCalcStep Π Π'
  | IfFalseStep : forall (p : Loc) (P Q : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (IfThenElse ff P Q) Π
      -> (forall r, r <> p -> forall R : Proc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p Q Π'
      -> PiCalcStep Π Π'
  | DefStep : forall (p : Loc) (P Q : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (DefProc P Q) Π
      -> (forall r, r <> p -> forall R : Proc, LM.MapsTo p R Π <-> LM.MapsTo p R Π')
      -> LM.MapsTo p (Q [iπ| PiDefSubst P]) Π'
      -> PiCalcStep Π Π'
  | ChooseLLStep : forall (p q : Loc) (P Q : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (EChoiceL q P) Π
      -> LM.MapsTo q (IChoiceL p Q) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q Q Π'
      -> PiCalcStep Π Π'
  | ChooseLLRStep : forall (p q : Loc) (P Q1 Q2 : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (EChoiceL q P) Π
      -> LM.MapsTo q (IChoiceLR p Q1 Q2) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q Q1 Π'
      -> PiCalcStep Π Π'
  | ChooseRRStep : forall (p q : Loc) (P Q : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (EChoiceR q P) Π
      -> LM.MapsTo q (IChoiceR p Q) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo p Q Π'
      -> PiCalcStep Π Π'
  | ChooseRLRStep : forall (p q : Loc) (P Q1 Q2 : Proc) (Π Π' : LM.t Proc),
      LM.MapsTo p (EChoiceR q P) Π
      -> LM.MapsTo q (IChoiceLR p Q1 Q2) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo p Q2 Π'
      -> PiCalcStep Π Π'.

End InternalProcesses.
