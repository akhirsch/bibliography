Require Export Expression.
Require Export Locations.
Require Export Choreography.
Require Export PiCalc.
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

Module ChoreographyCompiler (Import E : Expression) (L : Locations) (LM : LocationMap L).
  Include (LocationNotations L).
  Include ListNotations.

  Module LF := (LocationFacts L).
  Module C := (Choreography E L).
  Module P := (PiCalc E L).
  Module LMF := (LocationMapFacts L LM).

  Import C.


  Inductive IProc : Set := (* Intermediate language for process calculus. Can contain partial IChoices *)
    Skip : IProc (* Skip just exists so that <IProc, MergeIProcs> forms a monoid. This allows me to develop the unbiased version, which is easier to reason about for twist. *)
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

  Inductive Cont : Set :=
  | SecondaryC : IProc -> Cont
  | PrimaryC : (Expr -> option IProc) -> Cont.

  Equations ProjectChor (C : Chor) (l : Loc) (K : Cont)  : option IProc by wf (ChorSize C) lt :=
    {
      ProjectChor (Done l' e) l K with (L.eq_dec l l') :=
        {
        ProjectChor (Done ?(l) e) l (PrimaryC f) (left eq_refl) := f e;
        ProjectChor (Done ?(l) e) l (SecondaryC _) (left eq_refl) := None;
        ProjectChor (Done l' e) l (PrimaryC _) (right neq) := None;
        ProjectChor (Done l' e) l (SecondaryC C) (right neq) := Some C
        };
      ProjectChor (Var x) l K := Some (VarProc x);
      ProjectChor (Send p e q C) l K with L.eq_dec l p, L.eq_dec l q :=
        {
        ProjectChor (Send ?(l) e ?(l) C) l K (left eq_refl) (left eq_refl) :=
          ProjectChor (ChorExprSubst
                         C
                         (fun p n =>
                            if L.eq_dec p l
                            then match n with
                                 | 0 => e
                                 | S n => ExprVar n
                                 end
                            else ExprVar n)) l K;
        ProjectChor (Send ?(l) e q C) l K (left eq_refl) (right neq) with ProjectChor C l K :=
          {
          ProjectChor (Send ?(l) e q C) l K (left eq_refl) (right neq) (Some C') :=
            Some (SendProc q e C');
          ProjectChor (Send ?(l) e q C) l K (left eq_refl) (right neq) None := None
          };
        ProjectChor (Send p e ?(l) C) l K (right neq) (left eq_refl) with ProjectChor C l K :=
          {
          ProjectChor (Send p e ?(l) C) l K (right neq) (left eq_refl) (Some C') :=
            Some (RecvProc p C');
          ProjectChor (Send p e ?(l) C) l K (right neq) (left eq_refl) None := None
          };
        ProjectChor (Send p e q C) l K (right neq1) (right neq2) := ProjectChor C l K
        };
      ProjectChor (If p e C1 C2) l K with L.eq_dec l p, ProjectChor C1 l K, ProjectChor C2 l K :=
        {
        ProjectChor (If ?(l) e C1 C2) l K (left eq_refl) (Some C1') (Some C2') :=
          Some (IfThenElse e C1' C2');
        ProjectChor (If ?(l) e C1 C2) l K (left eq_refl) _ _ :=
          None;
        ProjectChor (If p e C1 C2) l K (right neq) (Some C1') (Some C2') :=
          MergeIProcs C1' C2';
        ProjectChor (If p e C1 C2) l K (right neq) _ _ := None
        };
      ProjectChor (Sync p d q C) l K with L.eq_dec l p, L.eq_dec l q, ProjectChor C l K :=
        {
        ProjectChor (Sync ?(l) d ?(l) C) l K (left eq_refl) (left eq_refl) (Some C') :=
          Some C';
        ProjectChor (Sync ?(l) d ?(l) C) l K (left eq_refl) (left eq_refl) None := None;
        ProjectChor (Sync ?(l) d q C) l K (left eq_refl) (right neq) (Some C') :=
          match d with
          | LChoice => Some (EChoiceL q C')
          | RChoice => Some (EChoiceR q C')
          end;
        ProjectChor (Sync ?(l) d q C) l K (left eq_refl) (right neq) None := None;
        ProjectChor (Sync p d ?(l) C) l K (right neq) (left eq_refl) (Some C') :=
          match d with
          | LChoice => Some (IChoiceL p C')
          | RChoice => Some (IChoiceR p C')
          end;
        ProjectChor (Sync p d ?(l) C) l K (right neq) (left eq_refl) None := None;
        ProjectChor (Sync p d q C) l K (right neq1) (right neq2) (Some C') :=
          Some C';
        ProjectChor (Sync p d q C) l K (right neq1) (right neq2) None := None
        };
      ProjectChor (DefLocal p C1 C2) l K with L.eq_dec l p :=
        {
        ProjectChor (DefLocal ?(l) C1 C2) l K (left eq_refl) :=
          ProjectChor C1 l (PrimaryC (fun e => ProjectChor
                                              (ChorExprSubst
                                                 C2 (fun p n =>
                                                       if L.eq_dec p l
                                                       then match n with
                                                            | 0 => e
                                                            | S n => ExprVar n
                                                            end
                                                       else ExprVar n)) l K));
        ProjectChor (DefLocal p C1 C2) l K (right neq) :=
          match ProjectChor C2 l K with
          | Some C2' => ProjectChor C1 l (SecondaryC C2')
          | None => None
          end
        };
      ProjectChor (DefGlobal C1 C2) l K with ProjectChor C1 l K, ProjectChor C2 l K :=
        {
        ProjectChor (DefGlobal C1 C2) l K (Some C1') (Some C2') := Some (DefProc C1' C2');
        ProjectChor (DefGlobal C1 C2) l K _ _ := None
        }
    }.
  Next Obligation.
    rewrite ChorExprSubstSize; lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    rewrite ChorExprSubstSize; lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    lia.
  Defined.
  Next Obligation.
    lia.
  Defined.


  Reserved Infix "≡K" (at level 30).
  Inductive ContEquiv : Cont -> Cont -> Prop :=
  | PrimaryEquiv : forall (f g : Expr -> option IProc),
      (forall e : Expr, f e = g e) -> PrimaryC f ≡K PrimaryC g
  | SecondaryEquiv : forall P : IProc, SecondaryC P ≡K SecondaryC P
  where "K1 ≡K K2" := (ContEquiv K1 K2).
  Hint Constructors ContEquiv : Chor.

  Instance : Reflexive ContEquiv.
  unfold Reflexive; intro K; induction K; auto with Chor.
  Qed.
  Instance : Symmetric ContEquiv.
  unfold Symmetric; intros K1 K2 eqv; induction eqv; auto with Chor.
  Qed.
  

  Lemma KEquivProjectToEqual : forall (C : Chor) (l : Loc) (K1 K2 : Cont),
      K1 ≡K K2 -> ProjectChor C l K1 = ProjectChor C l K2.
  Proof using.
    intros C l K1; funelim (ProjectChor C l K1);
      intros K2 eqv; simp ProjectChor; auto with Chor.
    all: repeat match goal with
                | [ |- ?a = ?a ] => reflexivity
                | [H : ?a <> ?a |- _ ] => destruct (H eq_refl)
                | [ H : Some _ = None |- _ ] => inversion H
                | [ H : None = Some _ |- _ ] => inversion H
                | [ H : Some ?a = Some ?b |- _ ] =>
                  inversion H; subst; clear H
                | [ |- context[L.eq_dec ?a ?b]]=>
                  lazymatch goal with
                  | [ H : L.eq_dec a b = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                  | _ =>
                    let eq := fresh "eq" in
                    let neq := fresh "neq" in
                    destruct (L.eq_dec a b) as [eq|neq]; [subst|]; cbn; simp ProjectChor
                  end
                | [ |- context[ExprEqDec ?a ?b]] =>
                  lazymatch goal with
                  | [ H : ExprEqDec a b = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                  | _ => let eq := fresh "eq" in
                        let neq := fresh "neq" in
                        destruct (ExprEqDec a b) as [eq|neq];[subst|]; cbn; simp ProjectChor
                  end
                | [ H : forall K2, ?K1 ≡K K2 -> ProjectChor ?C ?l ?K1 = ProjectChor ?C ?l K2,
                      H' : ?K1 ≡K ?K2 |- _ ] =>
                  lazymatch goal with
                  | [ _ : ProjectChor C l K1 = ProjectChor C l K2 |- _ ] => fail
                  | _ => pose proof (H K2 H')
                  end
                | [ |- context[ProjectChor ?C ?l ?K]] =>
                  lazymatch goal with
                  | [ H : ProjectChor C l K = _ |-  _ ] => rewrite H
                  | _ =>
                    let eq := fresh "eq_" C in destruct (ProjectChor C l K) eqn:eq; cbn
                  end
                | [ |- context[MergeIProcs ?a ?b]] =>
                  lazymatch goal with
                  | [ H : MergeIProcs a b = _ |- _ ] => rewrite H
                  | _ => let eq := fresh "eq_merge" in destruct (MergeIProcs a b) eqn:eq; cbn
                  end
                | [ d : LRChoice |- _ ] =>
                  lazymatch goal with
                  | [|- context[d]] =>
                    lazymatch goal with
                    | [H : d = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                    | _ => let eq := fresh "eq" in destruct d eqn:eq; cbn; simp ProjectChor
                    end
                  end
                end.
    1-4: inversion eqv; cbn; auto.
    simp ProjectChor. rewrite Heq; cbn. erewrite H0; [apply eq_c3|].
    constructor. intro e. apply H; auto.
    simp ProjectChor. rewrite Heq; cbn. erewrite H0; [apply eq_c3|].
    constructor. intro e. apply H; auto.
  Qed.
  
  Lemma NTEquivProjectToEqual : forall (C1 C2 : Chor) (l : Loc) (K (* K2 *) : Cont),
      C1 ≡NT C2 (* -> K1 ≡K K2 *) -> ProjectChor C1 l K = ProjectChor C2 l K.
  Proof using.
    intros C1 C2 l K; revert C2; funelim(ProjectChor C1 l K);
      intros C2 eqv; inversion eqv; subst; simp ProjectChor; auto with Chor.
    all: repeat match goal with
                | [ |- ?a = ?a ] => reflexivity
                | [H : ?a <> ?a |- _ ] => destruct (H eq_refl)
                | [ H : Some _ = None |- _ ] => inversion H
                | [ H : None = Some _ |- _ ] => inversion H
                | [ H : Some ?a = Some ?b |- _ ] =>
                  inversion H; subst; clear H
                | [ |- context[L.eq_dec ?a ?b]]=>
                  lazymatch goal with
                  | [ H : L.eq_dec a b = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                  | _ =>
                    let eq := fresh "eq" in
                    let neq := fresh "neq" in
                    destruct (L.eq_dec a b) as [eq|neq]; [subst|]; cbn; simp ProjectChor
                  end
                | [ |- context[ExprEqDec ?a ?b]] =>
                  lazymatch goal with
                  | [ H : ExprEqDec a b = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                  | _ => let eq := fresh "eq" in
                        let neq := fresh "neq" in
                        destruct (ExprEqDec a b) as [eq|neq];[subst|]; cbn; simp ProjectChor
                  end
                | [ H : ?C1 ≡NT ?C2, H' : context[?C1 [ce| ?σ]] |- _ ] =>
                  lazymatch goal with
                  | [ _ : C1 [ce| σ] ≡NT C2 [ce| σ] |- _ ] => fail
                  | _ => pose proof (NTEquivExprSubst C1 C2 σ H)
                  end
                | [ H : forall C2 : Chor, ?C1 ≡NT C2 -> ProjectChor ?C1 ?l ?K = ProjectChor C2 ?l ?K,
                      H2 : ?C1 ≡NT ?C2 |- _ ] =>
                  lazymatch goal with
                  | [ _ : ProjectChor C1 l K = ProjectChor C2 l K |- _] => fail
                  | _ => pose proof (H C2 H2)
                  end
                | [ |- context[ProjectChor ?C ?l ?K]] =>
                  lazymatch goal with
                  | [ H : ProjectChor C l K = _ |-  _ ] => rewrite H
                  | _ =>
                    let eq := fresh "eq_" C in destruct (ProjectChor C l K) eqn:eq; cbn
                  end
                | [ |- context[MergeIProcs ?a ?b]] =>
                  lazymatch goal with
                  | [ H : MergeIProcs a b = _ |- _ ] => rewrite H
                  | _ => let eq := fresh "eq_merge" in destruct (MergeIProcs a b) eqn:eq; cbn
                  end
                | [ d : LRChoice |- _ ] =>
                  lazymatch goal with
                  | [|- context[d]] =>
                    lazymatch goal with
                    | [H : d = _ |- _ ] => rewrite H; cbn; simp ProjectChor
                    | _ => let eq := fresh "eq" in destruct d eqn:eq; cbn; simp ProjectChor
                    end
                  end
                | [ H1 : MergeIProcs ?i1 ?i2 = _, H2 : MergeIProcs ?i3 ?i4 = _,
                    H3 : MergeIProcs ?i1 ?i3 = _, H4 : MergeIProcs ?i2 ?i4 = _ |- _] =>
                  lazymatch goal with
                  | [ _ : MarkedSequence i1 i2 i3 i4 |- _ ] => fail
                  | _ =>
                    pose proof (Mark i1 i2 i3 i4); 
                      let H := fresh in
                      pose proof (MergeIProcsTwist i1 i2 i3 i4);
                        rewrite H1 in H; rewrite H2 in H; rewrite H3 in H; rewrite H4 in H; cbn in H;
                          match type of H with
                          | Some _ = None => inversion H
                          | None = Some _ => inversion H
                          | None = None => idtac
                          | MergeIProcs ?i5 ?i6 = MergeIProcs ?i7 ?i8 =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i5 i6 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i5 i6 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          | MergeIProcs ?i5 ?i6 = None =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i5 i6 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i5 i6 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          | None = MergeIProcs ?i7 ?i8 =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i7 i8 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          end
                  end
                | [ H1 : MergeIProcs ?i1 ?i2 = _, H2 : MergeIProcs ?i3 ?i4 = _,
                    H3 : MergeIProcs ?i1 ?i3 = None |- _] =>
                  lazymatch goal with
                  | [ _ : MarkedSequence i1 i2 i3 i4 |- _ ] => fail
                  | _ =>
                    pose proof (Mark i1 i2 i3 i4); 
                      let H := fresh in
                      pose proof (MergeIProcsTwist i1 i2 i3 i4);
                        rewrite H1 in H; rewrite H2 in H; rewrite H3 in H; cbn in H;
                          match type of H with
                          | Some _ = None => inversion H
                          | None = Some _ => inversion H
                          | None = None => idtac
                          | MergeIProcs ?i5 ?i6 = MergeIProcs ?i7 ?i8 =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i5 i6 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i5 i6 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          | MergeIProcs ?i5 ?i6 = None =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i5 i6 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i5 i6 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          | None = MergeIProcs ?i7 ?i8 =>
                            repeat match goal with
                                   | [ H' : MergeIProcs i7 i8 = Some _ |- _ ] =>
                                     rewrite H' in H; clear H'
                                   | [ H' : MergeIProcs i7 i8 = None |- _ ] =>
                                     rewrite H' in H; clear H'
                                   end;
                              match type of H with
                              | Some _ = None => inversion H
                              | None = Some _ => inversion H
                              | Some _ = Some _ => inversion H; subst; clear H
                              | _ => idtac
                              end
                          end
                  end

                end.

    3-5: erewrite KEquivProjectToEqual in eq_C0; [rewrite eq_C0 in H2|];
      rewrite H1 in H2; auto;
        constructor; intro e; symmetry; apply H; apply NTEquivExprSubst; auto.
    3-5:  pose proof (H0 i c3 l (SecondaryC i) eq_refl eq_refl);
      rewrite (H3 C21 H5) in eq_c3; rewrite eq_C21 in eq_c3; auto.
    - erewrite ChorExprSubstExt; [reflexivity|]; intros p n; unfold ChorUpExprSubst;
        destruct (L.eq_dec l4 p); destruct (L.eq_dec p l); subst;
          try match goal with | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl) end;
          auto; destruct n; cbn; auto; apply ExprRenameVar.
    - erewrite ChorExprSubstExt; [reflexivity|]; intros p m; unfold ChorUpExprSubst;
        destruct (L.eq_dec p l4); destruct (L.eq_dec l2 p); subst;
          try match goal with | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl) end;
          auto; destruct m; cbn; auto; symmetry; apply ExprRenameVar.
  Qed.      

  Lemma AEquivProjectToEqual : forall (C1 C2 : Chor) (l : Loc) (K : Cont),
      C1 ≡A C2 -> ProjectChor C1 l K = ProjectChor C2 l K.
  Proof using.
    intros C1 C2 l K eqv; revert l K; induction eqv; intros l K.
    apply NTEquivProjectToEqual; auto.
    transitivity (ProjectChor C2 l K); auto.
  Qed.

  Theorem EquivProjectToEqual : forall (C1 C2 : Chor) (l : Loc) (K : Cont),
      C1 ≡ C2 -> ProjectChor C1 l K = ProjectChor C2 l K.
  Proof using.
    intros C1 C2 l K eqv; apply EquivToAltEquiv in eqv; apply AEquivProjectToEqual; auto.
  Qed.
  
End ChoreographyCompiler.
