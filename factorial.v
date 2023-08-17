Set Implicit Arguments.

Require Import ZArith.
Require Import hoarelogic.
Require Import Wellfounded.
Require Import Lia.
Require Import Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import NArith.BinNat.


(** * Implementation of the expression language *)
Module Example2 <: ExprLang.

(** Here, I use only two global variables [VX] and [VY] of type [Z]
(binary integers). *)
Inductive ExVar: Type -> Type :=
  VN: (ExVar nat) |
  VI: (ExVar nat) |
  VR: (ExVar nat).

Definition Var:=ExVar.

(** An environment is just a triple of natural numbers. First component
represents [VX] and second component represents [VY].  This is
expressed in [upd] and [get] below. *)
Definition Env:= (nat*nat*nat)%type.

(*fst e snd definidas no coq estavam a dar erro, foi preciso dar override das definições*)
Definition fst {A B C:Type} (e : A * B * C) : A :=
  match e with
  | (c, _, _) => c
  end.

Definition snd {A B C:Type} (e : A * B * C) : B :=
  match e with
  | (_, c, _) => c
  end.

Definition trd {A B C:Type} (e : A * B * C) : C :=
  match e with
  | (_, _, c) => c
  end.


Definition upd (A:Type): (ExVar A) -> A -> Env -> Env :=
 fun x =>
   match x in (ExVar A) return A -> Env -> Env with
   | VN => fun vn e => (vn, snd e, trd e)
   | VI => fun vi e => (fst e, vi, trd e)
   | VR => fun vr e => (fst e, snd e, vr)
   end.

Definition get (A:Type): (ExVar A) -> Env -> A :=
 fun x =>
   match x in (ExVar A) return Env -> A with
   | VN => fun e => fst e
   | VI => fun e => snd e
   | VR => fun e => trd e
   end.

(** I consider only three binary operators [PLUS], [MINUS] and [MULT]. Their
meaning is given by [eval_binOP] below *)
Inductive binOP: Type := PLUS | MINUS | MULT.

Definition eval_binOP: binOP -> nat -> nat -> nat :=
 fun op => match op with
  | PLUS => add
  | MINUS => sub
  | MULT => mul
 end.

(** I consider only three comparison operators [EQ] and
[LT]. Their meaning is given by [eval_relOP] below *)
Inductive relOP: Type := EQ | LT.

Definition eval_relOP: relOP -> nat -> nat -> bool :=
 fun op => match op with
  | EQ => eqb
  | LT => ltb
 end.

(** Here is the abstract syntax of expressions. The semantics is given
by [eval] below *)
Inductive ExExpr: Type -> Type :=
 | const: nat-> (ExExpr nat)
 | binop: binOP -> (ExExpr nat) -> (ExExpr nat) -> (ExExpr nat)
 | relop: relOP -> (ExExpr nat) -> (ExExpr nat) -> (ExExpr bool)
 | getvar: forall (A:Type), (ExVar A) -> (ExExpr A).

Definition Expr:= ExExpr.

Fixpoint eval (A:Type) (expr:Expr A) (e:Env) { struct expr } : A :=
 match expr in ExExpr A return A with
 | const v => v
 | binop op e1 e2 => eval_binOP op (eval e1 e) (eval e2 e)
 | relop op e1 e2 => eval_relOP op (eval e1 e) (eval e2 e)
 | getvar A x => (get x e)
end.

(** These coercions makes the abstract syntax more user-friendly *)
Coercion getvar: ExVar >-> ExExpr.
Coercion binop: binOP >-> Funclass.
Coercion relop: relOP >-> Funclass.

(** A last coercion useful for assertions *)
Coercion get: ExVar >-> Funclass.

End Example2.



(** * Instantiation of the Hoare logic on this language. *)
(*Module HL :=  HoareLogic(Example).*)
Module HL2 :=  HoareLogic(Example2).
Import HL2.
Import Example2.


Definition Ifactorial :=
  (Iseq (Iset VI (const 0%nat))
  (Iseq (Iset VR (const 1%nat))
  (Iwhile (LT VI VN) 
    (Iseq (Iset VI (PLUS VI (const 1))) 
    (Iset VR (MULT VR VI)))))).

Definition isfact (n res : nat): Prop := (fact n) = res.


Lemma leb_false_implies_geq : forall a b : nat, (leb a b) = false -> ge a b.
Proof.
  intros a b H.
  apply leb_complete_conv in H.
  auto with zarith.
Qed.



(*Partial correctness of Ifactorial: *)
Lemma Ifactorial_partial_proof:
forall n:nat, (fun e => (VN e)=n)
   |= Ifactorial  {= fun e => (isfact n (VR e)) =}.
Proof.
intros n.
apply PHL.soundness.
simpl.
intros e; intuition subst.
(*Invariant*)
constructor 1 with (x := fun e' =>
  (isfact (VI e') (VR e')) /\ (eq (VN e') (VN e)) /\ (
    (ge (VI e') (VN e')) ->  ( isfact (VN e) (VR e'))));simpl.
intuition auto with zarith.
unfold isfact; auto.

replace (fst e) with 0%nat.
unfold isfact; auto with zarith.
apply le_n_0_eq.
auto with zarith.

apply H3.
apply Nat.ltb_ge; assumption.

unfold isfact in *.
replace (fact (snd e'+1)) with (((snd e')+1)*fact(snd e'))%nat.
replace (fact (snd e')) with (trd e') by H1.
auto with zarith.
replace (snd e' + 1)%nat with (S (snd e')) by auto with zarith.
unfold fact.
auto with zarith.

unfold isfact in *.

assert ((snd e' + 1)%nat = fst e').
apply Nat.ltb_lt in H0.
assert (snd e' + 1 <= fst e')%nat.
assert ((snd e' + 1 < fst e' + 1)%nat).
apply Nat.add_lt_mono_r.
assumption.
auto with zarith.
auto with zarith.

replace (snd e' + 1)%nat with (fst e').
replace (fst e) with (fst e').
replace (fst e') with (snd e' + 1)%nat.
replace (trd e') with (fact (snd e')).
replace (snd e' + 1)%nat with (S (snd e')) by auto with zarith.
unfold fact.
auto with zarith.
Qed.


(*Total correctness of Ifactorial: *)
Lemma Ifactorial_total_proof:
forall n:nat, (fun e => (VN e)=n)
   |= Ifactorial  [= fun e => (isfact n (VR e)) =].
Proof.
intros n.
apply THL.soundness.
simpl.
intros e; intuition subst.
(*Invariant*)
constructor 1 with (x := fun e' =>
  (isfact (VI e') (VR e')) /\ (eq (VN e') (VN e)) /\ (
    (ge (VI e') (VN e')) ->  ( isfact (VN e) (VR e'))));simpl.
(*Variant*)
constructor 1 with (x:= fun e1 e0 => (lt ((VN e1)-(VI e1)) ((VN e0)-(VI e0)))).
constructor 1.
(*Proof that the variant is a well-founded relation*)
apply wf_inverse_image with (f:=fun e=> ((VN e) - (VI e))%nat).
apply lt_wf.
unfold lt; simpl; (intuition auto with zarith).

unfold isfact; auto with zarith.
assert (0 <= fst e)%nat.
apply Nat.le_0_l.
replace (fst e) with 0%nat.
unfold isfact; auto with zarith.
auto with zarith.

apply H3.
apply Nat.ltb_ge; assumption.

unfold isfact in *.
replace (fact (snd e'+1)) with (((snd e')+1)*fact(snd e'))%nat.
replace (fact (snd e')) with (trd e') by H1.
auto with zarith.
replace (snd e' + 1)%nat with (S (snd e')) by auto with zarith.
unfold fact.
auto with zarith.

unfold isfact in *.

assert ((snd e' + 1)%nat = fst e').
apply Nat.ltb_lt in H0.
assert (snd e' + 1 <= fst e')%nat.
assert ((snd e' + 1 < fst e' + 1)%nat).
apply Nat.add_lt_mono_r.
assumption.
auto with zarith.
auto with zarith.

replace (snd e' + 1)%nat with (fst e').
replace (fst e) with (fst e').
replace (fst e') with (snd e' + 1)%nat.
replace (trd e') with (fact (snd e')).
replace (snd e' + 1)%nat with (S (snd e')) by auto with zarith.
unfold fact.
auto with zarith.
replace (snd e0 + 1)%nat with (S (snd e0)).
replace (fst e0 - S (snd e0))%nat with (pred (fst e0 - snd e0))%nat.
apply Nat.lt_pred_l.
apply Nat.ltb_lt in H0.
assert (((fst e0) - (snd e0)) > 0)%nat.
auto with zarith.
auto with zarith.
symmetry.
apply Nat.sub_succ_r with (n:=(fst e0)) (m:=(snd e0)).
auto with zarith.
Qed.