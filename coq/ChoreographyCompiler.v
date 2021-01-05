Require Export Expression.
Require Export Locations.
Require Export Choreography.
Require Export ProcessCalculus.
Require Import LocationMap.
Require Import InternalProcesses.

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
  Module P := (ProcessCalculus E L LM).
  Module LMF := (LocationMapFacts L LM).
  Module IP := (InternalProcesses E L LM).

  Import C. Import IP.

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

  Definition ProjectChorToProc C l K := OptionSequence IProcToProc (ProjectChor C l K).

End ChoreographyCompiler.
