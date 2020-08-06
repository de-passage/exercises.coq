(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(** This short chapter constructs such a function and proves it
    correct. *)

Set Warnings "-notation-overridden,-parsing,-implicit-core-hint-db".
From Coq Require Import Bool.Bool.
From LF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | Bool, Bool =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1=Arrow T1_1 T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [Arrow T11 T12]
    for some [T11] and [T12]). *)

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      Gamma x
  | abs x T11 t12 =>
      match type_check (update Gamma x T11) t12 with
      | Some T12 => Some (Arrow T11 T12)
      | _ => None
      end
  | app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some (Arrow T11 T12),Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | tru =>
      Some Bool
  | fls =>
      Some Bool
  | test guard t f =>
      match type_check Gamma guard with
      | Some Bool =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.

(* ################################################################# *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).
         
Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 ;;
      return (Arrow T11 T12)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tru =>
      return Bool
  | fls =>
      return Bool
  | test guard t1 t2 =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | Bool =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert; 
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T11)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** **** Exercise: 5 stars, standard (typechecker_extensions)  

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | Nat, Nat =>
      true
  | Unit, Unit =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Prod T11 T12, Prod T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Sum T11 T12, Sum T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | List T11, List T21 =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1.
  induction T1; simpl;
    try reflexivity;
    try (rewrite IHT1_1; rewrite IHT1_2; reflexivity);
    try (rewrite IHT1; reflexivity).  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x1 T1 t2 =>
      T2 <- type_check (update Gamma x1 T1) t2 ;;
      return (Arrow T1 T2)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | const _ =>
      return Nat
  | scc t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | prd t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | mlt t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | Nat, Nat => return Nat
      | _,_        => fail
      end
  | test0 guard t f =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | Nat => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | tinl T2 t => 
      T1 <- type_check Gamma t;;
      return (Sum T1 T2)
  | tinr T1 t => 
      T2 <- type_check Gamma t;;
      return (Sum T1 T2)
  | tcase t0 y1 t1 y2 t2 =>
      match type_check Gamma t0 with
      | Some (Sum T1 T2) =>
          T1' <- type_check (update Gamma y1 T1) t1;;
          T2' <- type_check (update Gamma y2 T2) t2;;
          if eqb_ty T1' T2' then return T1' else fail
      | _ => fail
      end
  (* lists (the [tlcase] is given for free) *)
  | tnil T => return (List T)
  | tcons t1 t2 =>
      T1 <- type_check Gamma t1;;
      match type_check Gamma t2 with
      | Some (List T2) =>
        if eqb_ty T1 T2 then Some (List T1) else None
      | _ => None
      end
  | tlcase t0 t1 x21 x22 t2 =>
      match type_check Gamma t0 with
      | Some (List T) =>
          match type_check Gamma t1,
                type_check (update (update Gamma x22 (List T)) x21 T) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then Some T1' else None
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  | unit => return Unit
  (* pairs *)
  | pair t1 t2 =>
      T1 <- type_check Gamma t1;;
      T2 <- type_check Gamma t2;;
      return (Prod T1 T2)
  | fst t => 
      match type_check Gamma t with
      | Some (Prod T1 T2) => return T1
      | _ => fail
      end
  | snd t =>
      match type_check Gamma t with
      | Some (Prod T1 T2) => return T2
      | _ => fail
      end
  (* let *)
  | tlet x t1 t2 => 
      T1 <- type_check Gamma t1;;
      type_check (update Gamma x T1) t2
  (* fix *)
  | tfix t =>
      match type_check Gamma t with
      | Some (Arrow T1 T2) => 
          if eqb_ty T1 T2 then return T1
          else fail
      | _ => fail
      end
  end.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|]; 
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* tinl *)
    fully_invert_typecheck Gamma t0 T T11 T12.
  - (* tinr *)
    fully_invert_typecheck Gamma t0 T T11 T12.
  - (* tcase *)
    fully_invert_typecheck Gamma t1 T T11 T12.
    invert_typecheck (update Gamma s T11) t2 T1'.
    invert_typecheck (update Gamma s0 T12) t3 T2'.
    case_equality T1' T2'.
  - (* tnil *)
    auto. 
  - (* tcons *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    destruct T2; try solve_by_invert.
    case_equality T1 T2.
  - (* tlcase *)
    rename s into x31. rename s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (update (update Gamma x32 (List T11)) x31 T11) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *)
    auto.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    invert_typecheck Gamma t T'.
    destruct T'; try solve_by_invert.
    inversion H0; subst...
  - (* snd *)
    invert_typecheck Gamma t T'.
    destruct T'; try solve_by_invert.
    inversion H0; subst...
  - (* tlet *)
    fully_invert_typecheck Gamma t1 T T11 T12.
  - (* fix *)
    fully_invert_typecheck Gamma t T T11 T12.
    case_equality T11 T12.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T)); 
    try (rewrite (eqb_ty_refl T1)); 
    try (rewrite (eqb_ty_refl T2)); 
    eauto.
  - destruct (Gamma x); try solve_by_invert. eauto.
Qed.
(* 
Qed. (* ... and uncomment this one *)
*)
End TypecheckerExtensions.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_step_function)  

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a function [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

Fixpoint is_value (t : tm) : bool :=
  match t with
  | const _ => true
  | abs _ _ _ => true
  | tinl _ v => is_value v
  | tinr _ v => is_value v
  | tnil _ => true
  | tcons h t => is_value h && is_value t
  | unit => true
  | pair v1 v2 => is_value v1 && is_value v2
  | _ => false
  end.

Definition as_const (t : tm) : option nat :=
  match t with
  | const n => Some n
  | _ => None
  end.

Inductive sum_cat : Type := 
| cinl (T : ty) (t : tm)
| cinr (T : ty) (t : tm)
| cneither
.

Definition as_sum_cat (t : tm) : sum_cat :=
  match t with
  | tinl T t' => 
      if is_value t' then cinl T t' else cneither
  | tinr T t' => 
      if is_value t' then cinr T t' else cneither
  | _ => cneither
  end.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | var y => None
  | abs y T t1 => None
  | app t1 t2 =>
    match stepf t1, stepf t2, t1 with
    | None, None, abs x T t' => 
        if is_value t2 then return [x:= t2]t' else fail
    | None, Some t, _  => 
        if is_value t1 then return (app t1 t) else fail
    | Some t, _, _ => return (app t t2)
    | _, _, _ => fail
    end
    
  | const n => fail
  | scc t1 => 
      match stepf t1 with
      | None => n <- as_const t1;; return (const (S n))
      | Some t => return (scc t)
      end
  | prd t1 => 
      match stepf t1 with
      | None => n <- as_const t1;; return (const (pred n))
      | Some t2 => return (prd t2)
      end
  | mlt t1 t2 => 
      match stepf t1, stepf t2 with
      | None, None => 
          v1 <- as_const t1;;
          v2 <- as_const t2;;
          return (const (mult v1 v2))
      | None, Some t => 
          if is_value t1 then return (mlt t1 t) else fail
      | Some t, _ => return (mlt t t2)
      end
  | test0 t1 t2 t3 =>
    match stepf t1 with
    | None => 
        n <- as_const t1;;
        match n with
        | 0 => return t2 
        | S _ => return t3
        end
    | Some t => return (test0 t t2 t3)
    end
  | tinl T t1 => 
      t' <- stepf t1;;
      return (tinl T t')
  | tinr T t1 => 
      t' <- stepf t1;;
      return (tinr T t')
  | tcase t0 y1 t1 y2 t2 =>
      match stepf t0 with
      | Some t => 
          return (tcase t y1 t1 y2 t2)
      | None => 
          match as_sum_cat t0 with
          | cinl _ t => return [y1:=t]t1
          | cinr _ t => return [y2:=t]t2
          | cneither => fail
          end
      end
  | tnil T => fail
  | tcons t1 t2 =>
      match stepf t1, stepf t2 with
      | None, Some t => 
          if is_value t1 then return (tcons t1 t) else fail
      | Some t, _ => return (tcons t t2)
      | _, _ => fail
      end
  | tlcase t1 t2 y1 y2 t3 =>
      match stepf t1, t1 with
      | None, tnil T => return t2
      | None, tcons h t => 
          if is_value h && is_value t then 
              return [y2:=t]([y1:=h]t3)
          else
              fail
      | Some t, _ => return (tlcase t t2 y1 y2 t3)
      | _, _ => fail
      end
  | unit => fail
  | pair t1 t2 => 
      match stepf t1, stepf t2 with
      | None, Some t => 
          if is_value t1 then return (pair t1 t) else fail
      | Some t, _ => return (pair t t2)
      | _, _ => fail
      end
  | fst t => 
      match stepf t with
      | Some t' => return (fst t')
      | None => 
          match t with
          | pair t1 t2 => 
              if is_value t1 && is_value t2 
              then return t1 else fail
          | _ => fail
          end
      end
  | snd t =>
      match stepf t with
      | Some t' => return (snd t')
      | None => 
          match t with
          | pair t1 t2 => 
              if is_value t1 && is_value t2 
              then return t2 else fail
          | _ => fail
          end
      end
  | tlet y t1 t2 => 
      match stepf t1 with
      | None => if is_value t1 then return [y:=t1]t2 else fail
      | Some t => return (tlet y t t2)
      end
  | tfix t =>
      match stepf t, t with
      | None, abs x T t' => return [x:=(tfix (abs x T t'))]t'
      | Some t, _ => return (tfix t)
      | _, _ => fail
      end
  end.
  
Lemma is_value_true_iff: forall v,
  is_value v = true <-> value v.
Proof.
  Hint Constructors value.
  intros v; induction v; split; intros; 
  try solve_by_invert; auto; simpl in H;
  try (apply IHv in H; auto);
  try (inversion H; subst; simpl; apply IHv in H1; auto);
  try (apply andb_true_iff in H as [H1 H2];
    apply IHv1 in H1; apply IHv2 in H2; auto);
  try (inversion H; simpl; subst; apply andb_true_intro;
    apply IHv1 in H2; apply IHv2 in H3; auto).
Qed.

Lemma as_const_n: forall t n,
  as_const t = return n <-> t = (const n).
Proof.
  induction t; split; intros; try solve_by_invert;
  inversion H; auto.
Qed.

Lemma as_sum_cat_inl: forall t0 T t,
    as_sum_cat t0 = cinl T t <-> 
    t0 = tinl T t /\ value t.
Proof with auto. 
  induction t0; split; intros;
  try inversion H; try solve_by_invert; simpl in H...
  - destruct (is_value t0) eqn: D; inversion H; subst.
    apply is_value_true_iff in D... 
  - inversion H0; subst... simpl. 
    apply is_value_true_iff in H1. 
    destruct (is_value t1)... discriminate.
  - destruct (is_value t0); inversion H...
Qed.

Lemma as_sum_cat_inr: forall t0 T t,
    as_sum_cat t0 = cinr T t <->
    t0 = tinr T t /\ value t.
Proof with auto.
  induction t0; split; intros;
  try inversion H; try solve_by_invert; simpl in H...
  - destruct (is_value t0) eqn: D; inversion H; subst.
  - destruct (is_value t0) eqn: D; inversion H; subst. 
    apply is_value_true_iff in D...
  - simpl. inversion H0; subst. 
    destruct (is_value t1) eqn: D... 
    apply is_value_true_iff in H1.
    rewrite H1 in D. discriminate.
Qed.

Lemma as_sum_cat_value: forall t t' T,
  as_sum_cat t = cinl T t' \/ as_sum_cat t = cinr T t'
  -> value t.
Proof with auto.
  induction t; intros; try solve_by_invert; inversion H; subst; simpl; (try inversion H0; subst);
      try (destruct (is_value t0) eqn:D); 
      try apply is_value_true_iff in D; 
      try constructor;
      try inversion H2; subst...
Qed.

(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof with eauto. 
  intros t. induction t; intros; try inversion H.
  - destruct (stepf t1) eqn:Dt1.
    inversion H1; subst.
    apply ST_App1. apply IHt1...
    destruct (stepf t2) eqn:Dt2.
    destruct (is_value t1) eqn:Dv1.
    inversion H1; subst. apply ST_App2.
    apply is_value_true_iff in Dv1. auto. 
    apply IHt2; auto. inversion H1.
    destruct t1; try solve_by_invert.
    destruct (is_value t2) eqn:Dv2; try solve_by_invert.
    inversion H1; subst. apply ST_AppAbs.
    apply is_value_true_iff in Dv2...
  - destruct (stepf t) eqn:Dt. 
    inversion H1; subst. apply ST_Succ1. apply IHt...
    destruct (as_const t) eqn: D; inversion H1; subst.
    apply as_const_n in D. subst. apply ST_SuccNat.
  - destruct (stepf t). inversion H1; subst. apply ST_Pred...
    destruct (as_const t) eqn: D; inversion H1; subst.
    apply as_const_n in D. subst. apply ST_PredNat.
  - destruct (stepf t1).
    inversion H1; subst. apply ST_Mult1...
    destruct (stepf t2). inversion H1; subst.
    destruct (is_value t1) eqn:Dt1. apply is_value_true_iff in Dt1.
    inversion H1; subst. apply ST_Mult2... inversion H1.
    destruct (as_const t1) eqn:Dt1. apply as_const_n in Dt1; subst.
    destruct (as_const t2) eqn:Dt2. apply as_const_n in Dt2; subst.
    inversion H1; subst... inversion H1. inversion H1.
  - destruct (stepf t1). inversion H1; subst... 
    destruct (as_const t1) eqn:Dt1; try solve_by_invert.
    destruct n eqn:Dn; apply as_const_n in Dt1; 
    inversion H1; subst... 
  - destruct (stepf t0); inversion H1; subst...
  - destruct (stepf t0); inversion H1; subst...
  - destruct (stepf t1); inversion H1; subst...
    destruct (as_sum_cat t1) eqn:Dt3; inversion H1; 
    subst; assert (value t1); 
    try (apply as_sum_cat_inl in Dt3 as [H' Hv]; subst);
    try (apply as_sum_cat_inr in Dt3 as [Ht Hv]; subst)...
  - destruct (stepf t1); inversion H1...
    destruct (stepf t2); inversion H1; subst.
    destruct (is_value t1) eqn:D; inversion H1; subst.
    apply is_value_true_iff in D...
  - destruct (stepf t1); inversion H1...
    destruct t1 eqn:D; try solve_by_invert; inversion H1; 
    subst... 
    destruct (is_value t4) eqn:Dt4, (is_value t5) eqn:Dt5;
    simpl in *; clear H; inversion H1.
    apply is_value_true_iff in Dt4. 
    apply is_value_true_iff in Dt5...
  - destruct (stepf t1) eqn: Dt1; inversion H1...
    destruct (stepf t2); inversion H1; subst...
    destruct (is_value t1) eqn: D. apply is_value_true_iff in D.
    inversion H1... inversion H1. 
  - destruct (stepf t); inversion H1...
    destruct t; try solve_by_invert.
    destruct (is_value t1) eqn:D1; try (solve [inversion H1]).
    destruct (is_value t2) eqn:D2; inversion H1; subst. 
    apply is_value_true_iff in D1.
    apply is_value_true_iff in D2...
  - destruct (stepf t); inversion H1...
    destruct t; try solve_by_invert.
    destruct (is_value t1) eqn:D1; try (solve [inversion H1]).
    destruct (is_value t2) eqn:D2; inversion H1; subst.
    apply is_value_true_iff in D1.
    apply is_value_true_iff in D2...
  - destruct (stepf t1); inversion H1... 
    destruct (is_value t1) eqn:D; inversion H1; 
    apply is_value_true_iff in D...
  - destruct (stepf t); inversion H1; subst...
    destruct t; try solve_by_invert. inversion H1; subst...
Qed.

Lemma stepf_value_fail: forall t, 
  value t -> stepf t = fail.
Proof with auto.
  induction t; intros; try solve_by_invert; simpl; 
  inversion H; subst...
  - apply IHt in H1. rewrite H1...
  - apply IHt in H1. rewrite H1...
  - apply IHt1 in H2. apply IHt2 in H3. rewrite H2, H3...
  - apply IHt1 in H2. apply IHt2 in H3. rewrite H2, H3...
Qed.

(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof with eauto. 
  induction t; intros; try solve_by_invert; simpl.
  + inversion H; subst.
    - pose proof (stepf_value_fail _ H3). rewrite H0. 
      apply is_value_true_iff in H3. rewrite H3...
    - apply IHt1 in H3. rewrite H3...
    - pose proof (stepf_value_fail _ H2). rewrite H0. 
      apply IHt2 in H4. rewrite H4. 
      apply is_value_true_iff in H2. rewrite H2...
  + inversion H; subst... apply IHt in H1. rewrite H1...
  + inversion H; subst... apply IHt in H1. rewrite H1...
  + inversion H; subst... 
    - apply IHt1 in H3. rewrite H3...
    - pose proof (stepf_value_fail _ H2). rewrite H0.
      apply IHt2 in H4. rewrite H4. 
      apply is_value_true_iff in H2. rewrite H2...
  + inversion H; subst... apply IHt1 in H4. rewrite H4...
  + inversion H; subst. apply IHt in H3. rewrite H3...
  + inversion H; subst. apply IHt in H3. rewrite H3...
  + inversion H; subst; simpl. 
    - apply IHt1 in H6. rewrite H6...
    - pose proof (stepf_value_fail _ H6). rewrite H0.
      apply is_value_true_iff in H6. rewrite H6...
    - pose proof (stepf_value_fail _ H6). rewrite H0.
      apply is_value_true_iff in H6. rewrite H6...
  + inversion H; subst. 
    - apply IHt1 in H3. rewrite H3...
    - pose proof (stepf_value_fail _ H2). rewrite H0.
      apply IHt2 in H4. rewrite H4. 
      apply is_value_true_iff in H2. rewrite H2...
  + inversion H; subst...
    - apply IHt1 in H6. rewrite H6...
    - assert (value (tcons v1 vl)) by auto. 
      apply stepf_value_fail in H0. rewrite H0...
      apply is_value_true_iff in H6. 
      apply is_value_true_iff in H7. rewrite H6, H7...
  + inversion H; subst...
    - apply IHt1 in H3. rewrite H3...
    - pose proof (stepf_value_fail _ H2). rewrite H0.
      apply IHt2 in H4. rewrite H4. 
      apply is_value_true_iff in H2. rewrite H2...
  + inversion H; subst...
    - apply IHt in H1. rewrite H1...
    - simpl. pose proof (stepf_value_fail _ H1). 
      rewrite H0. pose proof (stepf_value_fail _ H2).
      rewrite H3. apply is_value_true_iff in H1. 
      rewrite H1. apply is_value_true_iff in H2. rewrite H2...
  + inversion H; subst...
    - apply IHt in H1. rewrite H1...
    - simpl. pose proof (stepf_value_fail _ H1). rewrite H0.
      pose proof (stepf_value_fail _ H2). rewrite H3.
      apply is_value_true_iff in H1. apply is_value_true_iff in H2.
      rewrite H1, H2...
  + inversion H; subst... 
    - apply IHt1 in H4. rewrite H4...
    - pose proof (stepf_value_fail _ H4). rewrite H0.
      apply is_value_true_iff in H4. rewrite H4...
  + inversion H; subst...
    apply IHt in H1. rewrite H1...
Qed.
End StepFunction.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_impl)  

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* FILL IN HERE *)
End StlcImpl.
(** [] *)

(* Thu Feb 7 20:09:25 EST 2019 *)
