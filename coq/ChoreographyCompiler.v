Require Export Expression.
Require Export Locations.
Require Export AnnotatedChoreography.
Require Export PiCalc.
Require Import LocationMap.
Require Import LocationSets.


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


Module AChoreographyCompiler (Import E : Expression) (L : Locations) (LM : LocationMap L) (LSorter : LocationSorter L).
  Include (LocationNotations L).
  Include ListNotations.

  Module LS := LocationSets L LSorter.
  Module LF := (LocationFacts L).
  Module P := (PiCalc E L).
  Module A := (AnnotatedChoreography E L).
  Module LMF := (LocationMapFacts L LM).
    
  Definition Loc := L.t.


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
  (* Equations MergeIProcs (P Q : IProc) : option IProc := *)
  (*   { *)
  (*     MergeIProcs EndProc EndProc := Some EndProc; *)
  (*     MergeIProcs (VarProc x) (VarProc y) with Nat.eq_dec x y := *)
  (*       { *)
  (*       MergeIProcs (VarProc x) (VarProc y) (left eq1) := Some (VarProc x); *)
  (*       MergeIProcs (VarProc x) (VarProc y) (right neq1) := None *)
  (*       }; *)
  (*     MergeIProcs (SendProc p e P) (SendProc q e' Q) with L.eq_dec p q, ExprEqDec e e', MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (SendProc p e P) (SendProc q e' Q) (left eq1) (left eq2) (Some P') := Some (SendProc p e P'); *)
  (*       MergeIProcs (SendProc p e P) (SendProc q e' Q) (left eq1) (left eq2) None := None; *)
  (*       MergeIProcs (SendProc p e P) (SendProc q e' Q) (left eq1) (right neq2) _ := None; *)
  (*       MergeIProcs (SendProc p e P) (SendProc q e' Q) (right neq1) (left neq2) _ := None; *)
  (*       MergeIProcs (SendProc p e P) (SendProc q e' Q) (right neq1) (right neq2) _ := None *)
  (*       }; *)
  (*     MergeIProcs (RecvProc p P) (RecvProc q Q) with L.eq_dec p q, MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (RecvProc p P) (RecvProc q Q) (left eq1) (Some P') := Some (RecvProc p P'); *)
  (*       MergeIProcs (RecvProc p P) (RecvProc q Q) (left eq1) None := None; *)
  (*       MergeIProcs (RecvProc p P) (RecvProc q Q) (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (EChoiceL p P) (EChoiceL q Q) with L.eq_dec p q, MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (EChoiceL p P) (EChoiceL q Q) (left eq1) (Some P') := Some (EChoiceL p P'); *)
  (*       MergeIProcs (EChoiceL p P) (EChoiceL q Q) (left eq1) None := None; *)
  (*       MergeIProcs (EChoiceL p P) (EChoiceL q Q) (right neq2) _ := None *)
  (*       }; *)
  (*     MergeIProcs (EChoiceR p P) (EChoiceR q Q) with L.eq_dec p q, MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (EChoiceR p P) (EChoiceR q Q) (left eq1) (Some P') := Some (EChoiceR p P'); *)
  (*       MergeIProcs (EChoiceR p P) (EChoiceR q Q) (left eq1) None := None; *)
  (*       MergeIProcs (EChoiceR p P) (EChoiceR q Q) (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceL p P) (IChoiceL q Q) with L.eq_dec p q, MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceL q Q) (left eq1) (Some P') := Some (IChoiceL p P'); *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceL q Q) (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceL q Q) (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceR p P) (IChoiceR q Q) with L.eq_dec p q, MergeIProcs P Q := *)
  (*       { *)
  (*       MergeIProcs (IChoiceR p P) (IChoiceR q Q) (left eq1) (Some P') := Some (IChoiceR p P'); *)
  (*       MergeIProcs (IChoiceR p P) (IChoiceR q Q) (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceR p P) (IChoiceR q Q) (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceL p P) (IChoiceR q Q) with L.eq_dec p q := *)
  (*       { *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceR q Q) (left eq1) := Some (IChoiceLR p P Q); *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceR q Q) (right neq1) := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceR p P) (IChoiceL q Q) with L.eq_dec p q := *)
  (*       { *)
  (*       MergeIProcs (IChoiceR p P) (IChoiceL q Q) (left eq1) := Some (IChoiceLR p Q P); *)
  (*       MergeIProcs (IChoiceR p P) (IChoiceL q Q) (right neq1) := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceL p P) (IChoiceLR q P' Q') with L.eq_dec p q, MergeIProcs P P' := *)
  (*       { *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceLR q P' Q') (left eq1) (Some P'') := Some (IChoiceLR p P'' Q'); *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceLR q P' Q') (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceL p P) (IChoiceLR q P' Q') (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceLR p P Q) (IChoiceL q P') with L.eq_dec p q, MergeIProcs P P' := *)
  (*       { *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceL q P') (left eq1) (Some P'') := Some (IChoiceLR p P'' Q); *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceL q P') (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceL q P') (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceR p Q) (IChoiceLR q P' Q') with L.eq_dec p q, MergeIProcs Q Q' := *)
  (*       { *)
  (*       MergeIProcs (IChoiceR p Q) (IChoiceLR q P' Q') (left eq1) (Some Q'') := Some (IChoiceLR p P' Q''); *)
  (*       MergeIProcs (IChoiceR p Q) (IChoiceLR q P' Q') (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceR p Q) (IChoiceLR q P' Q') (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceLR p P Q) (IChoiceR q Q') with L.eq_dec p q, MergeIProcs Q Q' := *)
  (*       { *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceR q Q') (left eq1) (Some Q'') := Some (IChoiceLR p P Q''); *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceR q Q') (left eq1) None := None; *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceR q Q') (right neq1) _ := None *)
  (*       }; *)
  (*     MergeIProcs (IChoiceLR p P Q) (IChoiceLR q P' Q') with L.eq_dec p q, MergeIProcs P P', MergeIProcs Q Q' := *)
  (*       { *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceLR q P' Q') (left eq1) (Some P'') (Some Q'') := Some (IChoiceLR p P'' Q''); *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceLR q P' Q') (left eq1) _ _ := None; *)
  (*       MergeIProcs (IChoiceLR p P Q) (IChoiceLR q P' Q') (right neq1) _ _ := None *)
  (*       }; *)
  (*     MergeIProcs (IfThenElse e P Q) (IfThenElse e' P' Q') with ExprEqDec e e', MergeIProcs P P', MergeIProcs Q Q' := *)
  (*       { *)
  (*       MergeIProcs (IfThenElse e P Q) (IfThenElse e' P' Q') (left eq1) (Some P'') (Some Q'') := Some (IfThenElse e P'' Q''); *)
  (*       MergeIProcs (IfThenElse e P Q) (IfThenElse e' P' Q') (left eq1) _ _ := None; *)
  (*       MergeIProcs (IfThenElse e P Q) (IfThenElse e' P' Q') (right neq1) _ _ := None *)
  (*       }; *)
  (*     MergeIProcs (DefProc P1 Q1) (DefProc P2 Q2) with MergeIProcs P1 P2, MergeIProcs Q1 Q2 := *)
  (*       { *)
  (*       MergeIProcs (DefProc P1 Q1) (DefProc P2 Q2) (Some P) (Some Q) := Some (DefProc P Q); *)
  (*       MergeIProcs (DefProc P1 Q1) (DefProc P2 Q2) _ _ := None *)
  (*       }; *)
  (*     MergeIProcs _ _ := None *)
  (*   }. *)

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

  Equations ProjectAChor (C: A.Chor) (l : Loc) (Env : Loc) : option IProc :=
    {
      ProjectAChor (A.Done p e) l Env with L.eq_dec p l :=
        {
        ProjectAChor (A.Done p e) l Env (left eq1) := Some (SendProc Env e EndProc);
        ProjectAChor (A.Done p e) l Env (right neq) := Some EndProc
        };
      ProjectAChor (A.Var x) _ _ := Some (VarProc x);
      ProjectAChor (A.Send p e q C) l Env with L.eq_dec p l, L.eq_dec q l, ProjectAChor C l Env :=
        {
        ProjectAChor (A.Send p e q C) l Env (left eq1) (right neq) (Some P) := Some (SendProc q e P);
        ProjectAChor (A.Send p e q C) l Env (right neq) (left eq1) (Some P) := Some (RecvProc p P);
        ProjectAChor (A.Send p e q C) l Env _ _ _ := None
        };
      ProjectAChor (A.If n p e C1 C2) l Env with L.eq_dec p l, ProjectAChor C1 l Env, ProjectAChor C2 l Env :=
        {
        ProjectAChor (A.If n p e C1 C2) l Env (left eq1) (Some P) (Some Q) := Some (IfThenElse e P Q);
        ProjectAChor (A.If n p e C1 C2) l Env (right neq) (Some P) (Some Q) := MergeIProcs P Q;
        ProjectAChor (A.If n p e C1 C2) l Env _ _ _ := None
        };
      ProjectAChor (A.Sync p d q C) l Env with L.eq_dec p l, L.eq_dec q l, ProjectAChor C l Env :=
        {
        ProjectAChor (A.Sync p d q C) l Env (left eq1) (right neq) (Some P) := 
          match d with
          | A.LChoice => Some (EChoiceL q P)
          | A.RChoice => Some (EChoiceR q P)
          end;
        ProjectAChor (A.Sync p d q C) l Env (right neq) (left eq2) (Some P) :=
          match d with
          | A.LChoice => Some (IChoiceL q P)
          | A.RChoice => Some (IChoiceR q P)
          end;
        ProjectAChor (A.Sync p d q C) l Env (right neq) (right neq) (Some P) := Some P;
        ProjectAChor (A.Sync p d q C) l Env _ _ _ := None
        };
      ProjectAChor (A.Def C1 C2) l Env with ProjectAChor C1 l Env, ProjectAChor C2 l Env :=
        {
        ProjectAChor (A.Def C1 C2) l Env (Some P) (Some Q) := Some (DefProc P Q);
        ProjectAChor (A.Def C1 C2) l Env _ _ := None
        }
    }.
  Inductive MarkedProjection : A.Chor -> Loc -> Loc -> Prop := MarkProj : forall C l Env, MarkedProjection C l Env.
  Theorem ProjectAChorEquiv' : forall (C C' : A.Chor) (l : Loc) (Env : Loc), A.chorEquiv' C C' -> ProjectAChor C l Env = ProjectAChor C' l Env.
  Proof using.
    intros C C' l Env equiv; revert l Env; induction equiv; intros l' Env; simp ProjectAChor;
      repeat (match goal with
              | [ H : ?a <> ?a |- _ ] => destruct (H eq_refl)
              | [ |- ?a = ?a ] => reflexivity
              | [ H : ?a = Some _, H2 : ?a = None |- _ ] => rewrite H in H2; inversion H2
              | [ H1 : ?a = Some ?b, H2 : ?a = Some ?c |- _ ] =>
                (unify b c) + (rewrite H1 in H2; inversion H2; subst; clear H2)
              | [ |-context[ExprEqDec ?a ?b]]=> destruct (ExprEqDec a b); subst; cbn; auto
              | [ |-context[L.eq_dec ?a ?b]]=> destruct (L.eq_dec a b); LF.LocationOrder; subst; cbn; auto
              | [ |-context[Nat.eq_dec ?a ?b]] => destruct (Nat.eq_dec a b); subst; cbn; auto
              | [ |-context[MergeIProcs ?a ?b]] =>
                lazymatch goal with
                | [ H : MergeIProcs a b = _ |- _ ] => rewrite H
                | _ => let eq := fresh "merge_" a "_" b in destruct (MergeIProcs a b) eqn:eq; auto; cbn
                end
              | [ |-context[ProjectAChor ?a ?b]] => let eq := fresh "eq_project_" a "_" b in destruct (ProjectAChor a b) eqn:eq; auto; cbn
              | [ d : A.LRChoice |- _] =>
                match goal with
                | [ |- context[d]] => destruct d; cbn
                end
              | [ IH : forall l E, ProjectAChor ?C1 l E = ProjectAChor ?C2 l E, H : ProjectAChor ?C1 ?l ?E = _ , H2 : ProjectAChor ?C2 ?l ?E = _ |- _ ] =>
                lazymatch goal with
                | [ _ : MarkedProjection C1 l E |- _ ] => fail
                | _ => pose proof (MarkProj C1 l E); let eq := fresh "eq_" IH in pose proof (IH l E) as eq; rewrite H in eq; rewrite H2 in eq; inversion eq; subst
                end
              end; simp ProjectAChor).
    all: repeat match goal with
           | [ H : ?a = ?a |- _ ] => clear H
           | [ H : MarkedProjection _ _ _ |- _ ] => clear H
           end.
    - pose proof (MergeIProcsTwist i10 i7 i9 i6). rewrite merge_i10_i9 in H0. rewrite merge_i3_i2 in H0. rewrite merge_i7_i6 in H0. rewrite merge_i0_i in H0. cbn in H0.
      rewrite merge_i11_i8 in H0; rewrite merge_i4_i1 in H0; auto.
    - pose proof (MergeIProcsTwist i10 i7 i9 i6). rewrite merge_i10_i9 in H0. rewrite merge_i3_i2 in H0. rewrite merge_i7_i6 in H0. rewrite merge_i0_i in H0. cbn in H0.
      rewrite merge_i11_i8 in H0; rewrite merge_i4_i1 in H0; auto.
    - pose proof (MergeIProcsTwist i10 i7 i9 i6). rewrite merge_i10_i9 in H0. rewrite merge_i3_i2 in H0. rewrite merge_i7_i6 in H0. rewrite merge_i0_i in H0. cbn in H0.
      rewrite merge_i4_i1 in H0; auto.
    - pose proof (MergeIProcsTwist i0 i6 i3 i7). rewrite merge_i0_i in H0. rewrite merge_i3_i2 in H0. rewrite MergeIProcsComm with (P := i6) (Q := i7) in H0. rewrite merge_i7_i6 in H0.
      cbn in H0. rewrite MergeIProcsComm with (P := i1) (Q := i4) in H0. rewrite merge_i4_i1 in H0. destruct (MergeIProcs i0 i3); cbn in H0; inversion H0.
    - pose proof (MergeIProcsTwist i8 i5 i9 i6). rewrite merge_i0_i in H0. rewrite merge_i3_i2 in H0. rewrite (MergeIProcsComm i8 i9) in H0. rewrite merge_i9_i8 in H0.
      rewrite (MergeIProcsComm i5 i6) in H0; rewrite merge_i6_i5 in H0. cbn in H0. rewrite merge_i10_i7 in H0. rewrite (MergeIProcsComm i1 i4) in H0; rewrite merge_i4_i1 in H0.
      inversion H0.
    - pose proof (MergeIProcsTwist i4 i7 i5 i8). rewrite (MergeIProcsComm i4 i7) in H0; rewrite merge_i0_i in H0. rewrite (MergeIProcsComm i5 i8) in H0; rewrite merge_i3_i2 in H0.
      rewrite (MergeIProcsComm i4 i5) in H0; rewrite merge_i5_i4 in H0. rewrite (MergeIProcsComm i7 i8) in H0; rewrite merge_i8_i7 in H0. cbn in H0.
      rewrite (MergeIProcsComm i6 i9) in H0; rewrite merge_i9_i6 in H0. inversion H0.
    - pose proof (MergeIProcsTwist i2 i1 i5 i4). rewrite (MergeIProcsComm i1 i4) in H0; rewrite merge_i0_i in H0. rewrite merge_i2_i1 in H0; rewrite merge_i5_i4 in H0. cbn in H0.
      rewrite (MergeIProcsComm i3 i6) in H0; rewrite merge_i6_i3 in H0. destruct (MergeIProcs i2 i5); cbn in H0; inversion H0.
  Qed.
End AChoreographyCompiler.
