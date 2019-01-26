Require Import QArith.
Require Import QArith.Qcanon.
Require Import Lists.List.
Require Import Coq.Program.Basics.

Open Scope Qc_scope.
Open Scope list_scope.

Notation "( x , y )" := (pair x y).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* An apparent encoding issue causes trouble when compiling code using the \u2218 character.
   To avoid potential brittleness, we introduce @, reminiscent of "after", for composition.
*)
Notation " g @ f " := (compose g f) (at level 40, left associativity) : program_scope.

Fixpoint allCuts' {X : Type} (l l' : list X) : list (prod X (list X)) :=
  match l' with
  | [] => []
  | x::t => (x, t++l) :: allCuts' (l++[x]) t
  end.

Definition allCuts {X:Type} := (@allCuts' X []).

Definition zipToPairs {X : Type} (l : list X) : list (prod X X) := combine l (tail l).

Definition closeList {X : Type} (l : list X) : list X :=
  match l with
  | [] => []
  | x::t => l ++ [x]
  end.

Definition Qc_lt_bool (x y : Qc) := if Qclt_le_dec x y then true else false.

Definition signum (x : Qc) : Qc := if Qc_lt_bool x 0 then -(1%Qc) else (if Qc_eq_dec x 0 then 0 else 1).

Lemma signum_zero : signum 0 = 0.
Proof. unfold signum. reflexivity. Defined.

Lemma signum_zero_is_zero : forall x : Qc, 0 = signum x -> x = 0.
Proof.
  unfold signum. unfold Qc_lt_bool. intros x H.
  destruct (Qclt_le_dec x 0).
  - inversion H.
  - destruct (Qc_eq_dec x 0).
    + assumption.
    + inversion H.
Defined.

Lemma signum_minus : forall x : Qc,
  signum (-x) = - signum x.
Proof. (* The below is HORRENDOUS. Sort it out. *)
  intros x. unfold signum. unfold Qc_lt_bool.
  destruct (Qclt_le_dec (-x) 0).
  - rewrite Qclt_minus_iff in q. rewrite Qcopp_involutive in q. rewrite Qcplus_0_l in q.
    destruct (Qclt_le_dec x 0).
    + pose (H:= ( Qclt_trans 0 x 0 q q0)). inversion H.
    + destruct (Qc_eq_dec x 0).
      * rewrite -> e in q. inversion q.
      * reflexivity.
  - apply Qcopp_le_compat in q. rewrite Qcopp_involutive in q.
    assert (neg0 : -0 = 0). { trivial. } rewrite neg0 in q.
    destruct (Qc_eq_dec (-x) 0).
    + assert (Hx : x = 0). { rewrite <- neg0. rewrite <- e. rewrite Qcopp_involutive. reflexivity. }
      rewrite -> Hx. reflexivity.
    + assert (Hx : x <> 0). { unfold not. unfold not in n. intros H. apply n. rewrite -> H. reflexivity. }
      destruct (Qclt_le_dec x 0).
      * reflexivity.
      * assert (Hx' : x = 0). { apply Qcle_antisym; assumption. }
        contradiction.
Defined.

Lemma signum_minus' : forall x y : Qc,
  signum x = signum y <-> signum (-x) = signum (-y).
Proof.
  intros x y. repeat (rewrite signum_minus). split; intros H.
  - rewrite <- H. reflexivity.
  - assert (H' : - (- signum x) = - (- signum y)). { rewrite <- H. reflexivity. }
    repeat (rewrite Qcopp_involutive in H'). assumption.
Defined.

Lemma Qc_eq_zero_dec : forall x:Qc, x = 0 \/ x <> 0.
Proof. intros. destruct (Qc_eq_dec x 0); [left|right]; assumption. Defined.

Lemma Qc_eq_bool_refl : forall x : Qc, Qc_eq_bool x x = true.
Proof.
  intros x. unfold Qc_eq_bool. destruct (Qc_eq_dec x x) as [H|H]; [reflexivity | contradiction].
Defined.

Lemma Qc_quot_non_zero : forall x y : Qc,
  y <> 0 -> x <> 0 -> x / y <> 0.
Proof.
  intros x y Hy Hx. unfold not. intros Hq.
  assert (Hq' : x / y * y = 0). { rewrite -> Hq. apply Qcmult_0_l. }
  rewrite -> (test_field x y Hy) in Hq'. contradiction.
Defined.

(* TODO Use reflection properly to eliminate the insanity of these various Qc_eq_bool_correct lemmata *)
Lemma Qc_eq_bool_correct' : forall x y : Qc,
  Qc_eq_bool x y = false -> x <> y.
Proof.
  unfold not. intros x y Hbneq Heq.
  destruct (Qc_eq_bool x y) eqn:Hbeq.
  - inversion Hbneq.
  - rewrite Heq in Hbeq. rewrite -> Qc_eq_bool_refl in Hbeq. inversion Hbeq.
Defined.

Lemma Qc_eq_bool_correct'' : forall z : Qc,
  z <> 0 -> Qc_eq_bool z 0 = false.
Proof.
  intros. destruct (Qc_eq_bool z 0) eqn:Hbeq.
  - exfalso. apply H. apply Qc_eq_bool_correct. assumption.
  - reflexivity.
Defined.

Lemma Qc_eq_bool_correct''' : forall x y : Qc,
  Qc_eq_bool x y = true <-> x = y.
Proof.
  intros. split.
  - apply Qc_eq_bool_correct.
  - intros Heq. rewrite -> Heq. apply Qc_eq_bool_refl.
Defined.

Lemma Qc_1_not_0 : (1<>0)%Qc.
Proof. unfold not. intros contra. inversion contra. Defined.

Lemma Qc_zero_diff : forall x y : Qc, x - y = 0 -> x = y.
Proof.
  intros. assert (H' : x = x - y + y). { ring. }
  rewrite -> H in H'. rewrite -> H'. ring.
Defined.

Definition Qc_from_Z (z : Z) := Q2Qc (z#1).

Lemma Qc_opp_x_zero : forall x : Qc,
  -x = 0 <-> x = 0.
Proof.
  intros x.
  split; intros H.
  - assert (H' : -(-x) = -0). { rewrite -> H. reflexivity. }
    rewrite Qcopp_involutive in H'. rewrite -> H'. reflexivity.
  - rewrite -> H. reflexivity.
Defined.

Lemma Qc_non_vanishing_sign : forall x : Qc,
  x <> 0 <-> -x <> 0.
Proof.
  unfold not. intros x; split; intros H H'; apply H; apply Qc_opp_x_zero; assumption.
Defined.

Definition det2 (a b
                 c d : Qc) := a*d - b*c.

Lemma det2_vanish_bool : forall a b c d : Qc,
  Qc_eq_bool (det2 a b c d) 0 = true <-> a*d = b*c.
Proof.
  intros a b c d. rewrite -> Qc_eq_bool_correct'''. unfold det2. split; intros H.
  - apply Qc_zero_diff. assumption.
  - rewrite -> H. apply Qcplus_opp_r.
Defined.

Lemma det2_vanishing_symmetry : forall a b c d,
  Qc_eq_bool (det2 a b c d) 0 = Qc_eq_bool (det2 c d a b) 0.
Proof.
  assert (H : forall a b c d, det2 a b c d = 0 <-> det2 c d a b = 0). {
    intros a b c d. unfold det2. assert (H' : a*d - b*c = -(c*b - d*a) ). { ring. }
    rewrite -> H'. split; apply Qc_opp_x_zero.
  }
  intros a b c d.
  destruct (Qc_eq_bool (det2 a b c d)) eqn:H1; destruct (Qc_eq_bool (det2 c d a b)) eqn:H2; try reflexivity.
  - apply Qc_eq_bool_correct in H1. apply Qc_eq_bool_correct' in H2. exfalso. unfold not in H2. apply H2.
    apply H. assumption.
  - apply Qc_eq_bool_correct' in H1. apply Qc_eq_bool_correct in H2. exfalso. unfold not in H1. apply H1.
    apply H. assumption.
Defined.

Lemma solve_det2 : forall a b c d : Qc,
  d <> 0 -> d*a = c*b -> a = b / d * c.
Proof.
  intros a b c d Hd Heq.
  assert (H : d * a / d = a). { field. apply Hd. }
  rewrite <- H. rewrite -> Heq. field. apply Hd.
Defined.

Definition det3 (a b c
                 d e f
                 g h i : Qc) := a * (det2 e f h i) +
                                b * (det2 f d i g) +
                                c * (det2 d e g h).
