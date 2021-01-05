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
  (* Skip just exists so that <IProc, MergeIProcs> forms a monoid. This allows me to develop the unbiased version, which is easier to reason about for twist. *)
  Inductive IProc : Set := 
    Skip : IProc 
  | EndProc : IProc
  | VarProc : nat -> IProc
  | DefProc : IProc -> IProc -> IProc
  | SendProc : Loc -> Expr -> IProc -> IProc
  | RecvProc : Loc -> IProc -> IProc
  | EChoiceL : Loc -> IProc -> IProc
  | EChoiceR : Loc -> IProc -> IProc
  | IChoiceL : Loc -> IProc -> IProc
  | IChoiceR : Loc -> IProc -> IProc
  | IChoiceLR : Loc -> IProc -> IProc -> IProc
  | IfThenElse : Expr -> IProc -> IProc -> IProc.
  Hint Constructors IProc : acc.
  Instance : EqDec Loc := L.eq_dec.
  Instance : EqDec Expr := ExprEqDec.
  Definition IProcEqDec : forall P Q : IProc, {P = Q} + {P <> Q}.
    decide equality.
    all: try (apply L.eq_dec).
    apply Nat.eq_dec.
    all: apply ExprEqDec.
  Defined.
  Instance : EqDec IProc := IProcEqDec.

  Ltac IProcInduction x :=
    let P := fresh "P" in
    let Q := fresh "Q" in
    let p := fresh "p" in
    let e := fresh "e" in
    let IHP := fresh "IH" P in
    let IHQ := fresh "IH" Q in
    let n := fresh "n" in
    induction x as [| | n | P IHP Q IHQ | p e P IHP | p P IHP | p P IHP | p P IHP | p P IHP | p P IHP | p P IHP Q IHQ | e P IHP Q IHQ].
  Ltac IProcDestruct x :=
    let P := fresh "P" in
    let Q := fresh "Q" in
    let p := fresh "p" in
    let e := fresh "e" in
    let n := fresh "n" in
    induction x as [| | n | P Q | p e P | p P | p P | p P | p P | p P | p P Q | e P Q].
  
  Fixpoint NoPartialIChoices (P : IProc) : Prop :=
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

  Fixpoint IProcToProc (P : IProc) : option P.Proc :=
    match P with
    | Skip => None
    | EndProc => Some P.EndProc
    | VarProc X => Some (P.VarProc X)
    | DefProc P Q =>
      match (IProcToProc P) with
      | Some P' =>
        match (IProcToProc Q) with
        | Some Q' => Some (P.DefProc P' Q')
        | None => None
        end
      | None => None
      end
    | SendProc p e P =>
      match IProcToProc P with
      | Some P' => Some (P.SendProc p e P')
      | None => None
      end
    | RecvProc p P =>
      match IProcToProc P with
      | Some P' => Some (P.RecvProc p P')
      | None => None
      end
    | EChoiceL p P =>
      match IProcToProc P with
      | Some P' => Some (P.EChoiceL p P')
      | None => None
      end
    | EChoiceR p P =>
      match IProcToProc P with
      | Some P' => Some (P.EChoiceR p P')
      | None => None
      end
    | IChoiceL p P => None
    | IChoiceR p P => None
    | IChoiceLR p P Q =>
      match IProcToProc P with
      | Some P' => match IProcToProc Q with
                  | Some Q' => Some (P.IChoice p P' Q')
                  | None => None
                  end
      | None => None
      end
    | IfThenElse e P Q =>
      match IProcToProc P with
      | Some P' => match IProcToProc Q with
                  | Some Q' => Some (P.IfThenElse e P' Q')
                  | None => None
                  end
      | None => None
      end
    end.

  Theorem TotalIProcToProc : forall (P : IProc), NoPartialIChoices P -> IProcToProc P <> None.
  Proof using.
    intro x; IProcInduction x; intro npic; cbn in *; try discriminate.
    all: repeat match goal with
                | [H : False |- _] => destruct H
                | [H : ?P, H' : ?P -> ?a <> ?a |- _ ] => exfalso; apply (H' H); auto
                | [H : ?a <> ?a |- _] => exfalso; apply H; auto
                | [|- Some _ <> None] => discriminate
                | [H : ?P /\ ?Q |- _ ] => destruct H
                | [|- context[IProcToProc ?P]] =>
                  let iptp := fresh "iptp_" P in
                  destruct (IProcToProc P) eqn:iptp
                end.
  Qed.
  Corollary TotalIProcToProc_Exists : forall (P : IProc), NoPartialIChoices P -> exists Q : P.Proc, IProcToProc P = Some Q.
  Proof using.
    intros P npic; destruct (IProcToProc P) as [Q|] eqn:iptp_P; [exists Q; reflexivity | apply TotalIProcToProc in iptp_P; auto; destruct iptp_P].
  Qed.

  Fixpoint MergeIProcs (P Q : IProc) : option IProc :=
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
        match MergeIProcs P1 P2 with
        | Some P => match MergeIProcs Q1 Q2 with
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
             then match MergeIProcs P' Q' with
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
        then match MergeIProcs P' Q' with
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
        then match MergeIProcs P' Q' with
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
        then match MergeIProcs P' Q' with
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
        then match MergeIProcs P1 P2 with
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
        then match MergeIProcs P1 P2 with
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
        then match MergeIProcs Q1 Q2 with
             | Some R => Some (IChoiceR p R)
             | None => None
             end
        else None
      | IChoiceLR q P1 Q2 =>
        if L.eq_dec p q
        then match MergeIProcs Q1 Q2 with
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
        then match MergeIProcs P1 P2 with
             | Some R => Some (IChoiceLR p R Q1)
             | None => None
             end
        else None
      | IChoiceR q Q2 =>
        if L.eq_dec p q
        then match MergeIProcs Q1 Q2 with
             | Some R => Some (IChoiceLR p P1 R)
             | None => None
             end
        else None
      | IChoiceLR q P2 Q2 =>
        if L.eq_dec p q
        then match MergeIProcs P1 P2 with
             | Some P => match MergeIProcs Q1 Q2 with
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
        then match MergeIProcs P1 P2 with
             | Some P => match MergeIProcs Q1 Q2 with
                        | Some Q => Some (IfThenElse e P Q)
                        | None => None
                        end
             | None => None
             end
        else None
      | _ => None
      end
    end.

  Lemma MergeIProcsComm : forall P Q, MergeIProcs P Q = MergeIProcs Q P.
  Proof using.
    intros P; induction P; destruct Q; cbn; auto.
    all: repeat match goal with
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; auto
                | [ |- ?a = ?a ] => reflexivity
                | [|- context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; auto
                | [|- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); LF.LocationOrder; subst; auto
                | [|- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); LF.LocationOrder; subst; auto
                | [|- context[MergeIProcs ?a ?b]] => try (let eq := fresh "merge_" a "_" b in destruct (MergeIProcs a b) eqn:eq); simp MergeIProc; cbn; auto
                | [ IH : forall Q, MergeIProcs ?P Q = MergeIProcs Q ?P, H1 : MergeIProcs ?P ?Q = ?a, H2 : MergeIProcs ?Q ?P = ?b |- _ ] =>
                  rewrite IH in H1; rewrite H2 in H1; inversion H1; subst; clear H1
                end.
  Qed.

  Lemma MergeIProcsInvolutive : forall P, MergeIProcs P P = Some P.
  Proof using.
    intro P; induction P; cbn; auto.
    all: repeat match goal with
                | [ H : ?a <> ?a |- _ ] => exfalso; apply H; auto
                | [ |- ?a = ?a ] => reflexivity
                | [|- context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; auto
                | [|- context[L.eq_dec ?a ?b]] => destruct (L.eq_dec a b); LF.LocationOrder; subst; auto
                | [|- context[ExprEqDec ?a ?b]] => destruct (ExprEqDec a b); LF.LocationOrder; subst; auto
                | [ H : MergeIProcs ?a ?a = Some ?a |- context[MergeIProcs ?a ?a]] => rewrite H; auto
                end.
  Qed.
  Lemma MergeIProcsIdentityL : forall P, MergeIProcs Skip P = Some P.
  Proof using.
    intro P; cbn; auto.
  Qed.
  Lemma MergeIProcsIdentityR : forall P, MergeIProcs P Skip = Some P.
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

  Inductive MarkedSequence : IProc -> IProc -> IProc -> IProc -> Prop := Mark : forall P Q R S, MarkedSequence P Q R S.
  Lemma MergeIProcsAssoc : forall P Q R, OptionSequence (MergeIProcs P) (MergeIProcs Q R) = OptionSequence (fun P => MergeIProcs P R) (MergeIProcs P Q).
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
             | [ |- context[MergeIProcs ?a ?b]] => let eq := fresh "eq" in destruct (MergeIProcs a b) eqn:eq; cbn
             (* | [ IH : forall Q R, OptionSequence (MergeIProcs ?P) (MergeIProcs Q R) = OptionSequence (fun S => MergeIProcs S R) (MergeIProcs ?P Q), H : MergeIProcs ?P ?Q = Some ?S, H' : MergeIProcs ?Q ?R = Some ?T, eq1 : MergeIProcs ?S ?R = _, eq2 : MergeIProcs ?P ?T = _ |- _ ] => *)
             (*   lazymatch goal with *)
             (*   | [_ : MarkedSequence P Q R S |- _ ] => fail *)
             (*   | _ => pose proof (Mark P Q R S); let eq := fresh "eq" in pose proof (IH Q R) as eq; rewrite H' in eq; rewrite H in eq; cbn in eq; rewrite eq1 in eq; rewrite eq2 in eq; cbn in eq *)
             (*   end *)
             | [ IH : forall Q R, OptionSequence (MergeIProcs ?P) (MergeIProcs Q R) = OptionSequence (fun S => MergeIProcs S R) (MergeIProcs ?P Q), H : MergeIProcs ?P ?Q = _, H' : MergeIProcs ?Q ?R = _ |- _ ] =>
               lazymatch goal with
               | [_ : MarkedSequence P Q P Q |- _ ] => fail
               | _ => pose proof (Mark P Q P Q); let eq := fresh "eq" in pose proof (IH Q R) as eq; rewrite H' in eq; rewrite H in eq; cbn in eq
               end
             | [ H : MergeIProcs ?a ?b = MergeIProcs ?c ?d, H' : MergeIProcs ?a ?b = Some _, H'' : MergeIProcs ?c ?d = _ |- _ ] =>
               rewrite H' in H; rewrite H'' in H; inversion H; subst; clear H
             | [ H : MergeIProcs ?a ?b = MergeIProcs ?c ?d, H' : MergeIProcs ?a ?b = None, H'' : MergeIProcs ?c ?d = _ |- _ ] =>
               rewrite H' in H; rewrite H'' in H; inversion H; subst; clear H
             end.
  Qed.
  Corollary MergeIProcsAssoc' : forall P Q R S T, MergeIProcs P Q = Some S -> MergeIProcs Q R = Some T -> MergeIProcs S R = MergeIProcs P T.
  Proof using.
    intros P Q R S T H H0; pose proof (MergeIProcsAssoc P Q R) as eq; rewrite H in eq; rewrite H0 in eq; cbn in eq; auto.
  Qed.

  Fixpoint MergeIProcsList (l : list IProc) : option IProc :=
    match l with
    | [] => Some Skip
    | [P] => Some P
    | P :: l => OptionSequence (MergeIProcs P) (MergeIProcsList l)
    end.

  Lemma MergeIProcsList2 : forall P Q, MergeIProcs P Q = MergeIProcsList [P; Q].
  Proof using.
    intros P Q; cbn; auto.
  Qed.

  Fixpoint Deduplicate_ProcList (l : list IProc) : list IProc :=
    match l with
    | [] => []
    | P :: l => if in_dec IProcEqDec P l then Deduplicate_ProcList l else P :: (Deduplicate_ProcList l)
    end.

  Lemma Deduplicate_In : forall P l, In P l -> In P (Deduplicate_ProcList l).
  Proof using.
    intros P l; induction l; cbn; auto; intro i.
    destruct i as [eq | i]; subst; auto. destruct (in_dec IProcEqDec P l); auto; left; auto.
    destruct (in_dec IProcEqDec a l); auto; right; auto.
  Qed.
    
  Lemma Deduplicate_In2In : forall P l, In P (Deduplicate_ProcList l) -> In P l.
  Proof using.
    intros P l; induction l; cbn; auto; intro i.
    destruct (in_dec IProcEqDec a l). right; auto. destruct i; auto.
  Qed.
  Lemma NoDup_Deduplicate : forall l, NoDup (Deduplicate_ProcList l).
  Proof using.
    intro l; induction l; cbn; try (constructor; auto; fail).
    destruct (in_dec IProcEqDec a l); auto. constructor; auto. intro i; apply n; apply Deduplicate_In2In; auto.
  Qed.

  Lemma EquivToPerm : forall l l', (forall P, In P l <-> In P l') -> Permutation (Deduplicate_ProcList l) (Deduplicate_ProcList l').
  Proof using.
    intros l l' eqv; apply NoDup_Permutation; try (apply NoDup_Deduplicate).
    intro P; split; intro i; apply Deduplicate_In2In in i; apply eqv in i; apply Deduplicate_In in i; auto.
  Qed.

  Lemma MergeIProcsListPerm : forall l l', Permutation l l' -> MergeIProcsList l = MergeIProcsList l'.
  Proof using.
    intros l l' perm; induction perm; auto; cbn.
    - destruct l. apply Permutation_nil in perm; subst; auto. destruct l'. apply Permutation_sym in perm; apply Permutation_nil_cons in perm; destruct perm.
      rewrite IHperm; auto.
    - destruct l; cbn. apply MergeIProcsComm.
      destruct (match l with
                | [] => Some i
                | _ :: _ => OptionSequence (MergeIProcs i) (MergeIProcsList l)
                end); cbn; auto.
      pose proof (MergeIProcsAssoc x y i0).
      pose proof (MergeIProcsAssoc y x i0).
      rewrite MergeIProcsComm with (P := y) (Q := x) in H0. rewrite <- H0 in H. rewrite H. reflexivity.
    - transitivity (MergeIProcsList l'); auto.
  Qed.

  Lemma MergeIProcsIn : forall P l, In P l -> MergeIProcsList (P :: l) = MergeIProcsList l.
  Proof using.
    intros P l; revert P; induction l as [| Q l]; intros P i; cbn; [inversion i|].
    destruct l; [cbn; destruct i as [eq|i]; [|inversion i]; subst; apply MergeIProcsInvolutive|].
    destruct i as [eq|i]; subst; cbn; destruct (match l with
                                                | [] => Some i0
                                                | _ :: _ => OptionSequence (MergeIProcs i0) (MergeIProcsList l)
                                                end) eqn:eq; cbn; auto.
    rewrite (MergeIProcsAssoc P P i); rewrite MergeIProcsInvolutive; cbn; auto.
    pose proof (IHl P i) as H; cbn in H. rewrite eq in H.
    rewrite MergeIProcsComm with (P := Q) (Q := i1).
    rewrite (MergeIProcsAssoc P i1 Q). cbn in H. rewrite H. cbn. reflexivity.
  Qed.
    

  Lemma MergeIProcsDeduplicate : forall l, MergeIProcsList l = MergeIProcsList (Deduplicate_ProcList l).
  Proof using.
    intro l; induction l; cbn; auto.
    destruct (in_dec IProcEqDec a l); cbn.
    destruct l; [inversion i |rewrite <- IHl; apply MergeIProcsIn in i; rewrite <- i at 2; auto].
    rewrite <- IHl.
    destruct l. cbn; auto.
    destruct (Deduplicate_ProcList (i :: l)) eqn:eq. assert (In i []) as H by (rewrite <- eq; apply Deduplicate_In; left; auto); inversion H.
    reflexivity.
  Qed.

  Corollary MergeIProcsEquiv : forall l l', (forall P, In P l <-> In P l') -> MergeIProcsList l = MergeIProcsList l'.
  Proof using.
    intros l l' H; rewrite MergeIProcsDeduplicate; rewrite (MergeIProcsDeduplicate l'); apply MergeIProcsListPerm; apply EquivToPerm; auto.
  Qed.

  Lemma MergeIProcsApp : forall l l', (OptionSequence2 MergeIProcs) (MergeIProcsList l) (MergeIProcsList l') = MergeIProcsList (l ++ l').
  Proof using.
    intro l; induction l as [|P l]; cbn; intro l'.
    destruct (MergeIProcsList l'); auto.
    rewrite <- IHl.
    destruct (l ++ l') eqn:eq. apply app_eq_nil in eq; destruct eq; subst; cbn; rewrite MergeIProcsIdentityR; reflexivity.
    destruct l; cbn in eq; subst. rewrite IHl. rewrite app_nil_l. destruct (MergeIProcsList (i :: l0)); cbn; auto.
    inversion eq; subst; clear eq. cbn. destruct (match l with | [] => Some i | _ :: _ => OptionSequence (MergeIProcs i) (MergeIProcsList l) end); cbn; auto.
    destruct (MergeIProcsList l'); cbn.
    rewrite (MergeIProcsAssoc P i0 i1). destruct (MergeIProcs P i0); cbn; reflexivity.
    destruct (MergeIProcs P i0); cbn; reflexivity.
  Qed.
       
  Lemma MergeIProcsTwist : forall P1 P2 Q1 Q2, (OptionSequence2 MergeIProcs) (MergeIProcs P1 Q1) (MergeIProcs P2 Q2) = (OptionSequence2 MergeIProcs) (MergeIProcs P1 P2) (MergeIProcs Q1 Q2).
  Proof using.
    intros P1 P2 Q1 Q2. repeat rewrite MergeIProcsList2. repeat rewrite MergeIProcsApp. apply MergeIProcsListPerm.
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
  Fixpoint ProcRenaming (P : IProc) (ξ : nat -> nat) : IProc :=
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

    Lemma ProcRenamingExt : forall (P : IProc) (ξ1 ξ2 : nat -> nat),
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

  Lemma ProcRenamingIdSpec : forall (P : IProc),
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
  Fixpoint ProcExprRenaming (P : IProc) (ξ : nat -> nat) : IProc :=
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

  Lemma ProcExprRenamingExt : forall (P : IProc) (ξ1 ξ2 : nat -> nat),
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

  Lemma ProcExprRenamingId : forall (P : IProc),
      P ⟨iπe| ExprIdRenaming⟩ = P.
  Proof.
    intro P; induction P; simpl; auto.
    1,8,9: rewrite IHP1; rewrite IHP2; auto.
    3: rewrite ProcExprRenamingExt with (ξ2 := ExprIdRenaming);
      [|intro n; symmetry; apply ExprUpRenamingId].
    2-7: rewrite IHP; auto.
    all: rewrite ExprIdRenamingSpec; reflexivity.
  Qed.

    Definition ProcSubstUp : (nat -> IProc) -> nat -> IProc :=
    fun σ n => match n with
            | 0 => VarProc 0
            | S n' => σ n' ⟨iπ| S⟩
            end.

  Lemma ProcSubstUpExt : forall (σ1 σ2 : nat -> IProc),
      (forall n, σ1 n = σ2 n)
      -> forall n, ProcSubstUp σ1 n = ProcSubstUp σ2 n.
  Proof.
    intros σ1 σ2 ext_eq n; unfold ProcSubstUp; destruct n; [|rewrite ext_eq]; reflexivity.
  Qed.

  Reserved Notation "P [iπ| σ ]" (at level 15).
  Fixpoint ProcSubst (P : IProc) (σ : nat -> IProc) :=
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

  Lemma ProcSubstExt : forall (P : IProc) (σ1 σ2 : nat -> IProc),
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

  Definition ProcIdSubst : nat -> IProc := VarProc.
  Lemma ProcIdSubstUp : forall n, ProcSubstUp ProcIdSubst n = ProcIdSubst n.
  Proof.
    intro n; unfold ProcSubstUp; unfold ProcIdSubst; destruct n; simpl; reflexivity.
  Qed.

  Lemma ProcSubstId : forall (P : IProc), P [iπ| ProcIdSubst] = P.
  Proof.
    intro P; induction P; simpl; auto.
    2-7: rewrite IHP; reflexivity.
    repeat (rewrite ProcSubstExt with (σ1 := ProcSubstUp ProcIdSubst) (σ2 := ProcIdSubst);
            [| exact ProcIdSubstUp]).
    all: rewrite IHP1; rewrite IHP2; reflexivity.
  Qed.

  Reserved Notation "P [iπe| σ ]" (at level 15).
  Fixpoint ProcExprSubst (P : IProc) (σ : nat -> Expr) : IProc :=
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

  Lemma ProcExprSubstExt : forall (P : IProc) (σ1 σ2 : nat -> Expr),
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

  Lemma ProcExprSubstId : forall (P : IProc),
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

  Definition PiDefSubst : IProc -> nat -> IProc :=
    fun P n => match n with
            | 0 => P [iπ| (fun m => match m with | 0 => DefProc P P | S m' => VarProc m' end)]
            | S n' => VarProc n'
            end.

  Inductive PiCalcStep : LM.t IProc -> LM.t IProc -> Prop :=
    CommEStep : forall (p q : Loc) (e e' : Expr) (P : IProc) (Π Π' : LM.t IProc),
      ExprStep e e'
      -> LM.MapsTo p (SendProc q e P) Π
      -> (forall r, r <> p -> forall Q, LM.MapsTo r Q Π <-> LM.MapsTo r Q Π') (* Perhaps we could get away with only one direction? *)
      -> LM.MapsTo p (SendProc q e' P) Π'
      -> PiCalcStep Π Π'
  | CommVStep : forall (p q : Loc) (v : Expr) (P Q : IProc) (Π Π' : LM.t IProc),
      ExprVal v
      -> LM.MapsTo p (SendProc q v P) Π
      -> LM.MapsTo q (RecvProc p Q) Π
      -> (forall r, r <> p -> r <> q -> forall Q, LM.MapsTo r Q Π <-> LM.MapsTo r Q Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q (Q [iπe| CommSubst v]) Π'
      -> PiCalcStep Π Π'
  | IfEStep : forall (p : Loc) (e e' : Expr) (P Q : IProc) (Π Π' : LM.t IProc),
      ExprStep e e'
      -> LM.MapsTo p (IfThenElse e P Q) Π
      -> (forall r, r <> p -> forall R : IProc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p (IfThenElse e' P Q) Π'
      -> PiCalcStep Π Π'
  | IfTrueStep : forall (p : Loc) (P Q : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (IfThenElse tt P Q) Π
      -> (forall r, r <> p -> forall R : IProc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> PiCalcStep Π Π'
  | IfFalseStep : forall (p : Loc) (P Q : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (IfThenElse ff P Q) Π
      -> (forall r, r <> p -> forall R : IProc, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p Q Π'
      -> PiCalcStep Π Π'
  | DefStep : forall (p : Loc) (P Q : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (DefProc P Q) Π
      -> (forall r, r <> p -> forall R : IProc, LM.MapsTo p R Π <-> LM.MapsTo p R Π')
      -> LM.MapsTo p (Q [iπ| PiDefSubst P]) Π'
      -> PiCalcStep Π Π'
  | ChooseLLStep : forall (p q : Loc) (P Q : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (EChoiceL q P) Π
      -> LM.MapsTo q (IChoiceL p Q) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q Q Π'
      -> PiCalcStep Π Π'
  | ChooseLLRStep : forall (p q : Loc) (P Q1 Q2 : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (EChoiceL q P) Π
      -> LM.MapsTo q (IChoiceLR p Q1 Q2) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo q Q1 Π'
      -> PiCalcStep Π Π'
  | ChooseRRStep : forall (p q : Loc) (P Q : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (EChoiceR q P) Π
      -> LM.MapsTo q (IChoiceR p Q) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo p Q Π'
      -> PiCalcStep Π Π'
  | ChooseRLRStep : forall (p q : Loc) (P Q1 Q2 : IProc) (Π Π' : LM.t IProc),
      LM.MapsTo p (EChoiceR q P) Π
      -> LM.MapsTo q (IChoiceLR p Q1 Q2) Π
      -> (forall r, p <> r -> q <> r -> forall R, LM.MapsTo r R Π <-> LM.MapsTo r R Π')
      -> LM.MapsTo p P Π'
      -> LM.MapsTo p Q2 Π'
      -> PiCalcStep Π Π'.

  
End InternalProcesses.
