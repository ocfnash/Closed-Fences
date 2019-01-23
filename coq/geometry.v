Require Import QArith.
Require Import QArith.Qcanon.

Open Scope Qc_scope.

From F4 Require Export misc.

Inductive Triple :=
  | triple : forall (x y z : Qc), Triple.

Definition isNotZero t :=
  match t with
  | triple x y z => x <> 0 \/ y <> 0 \/ z <> 0
  end.

Definition isOrthogonal_b (t t' : Triple) :=
  match t, t' with
  | triple x y z, triple x' y' z' => Qc_eq_bool (x*x' + y*y' + z*z') 0
  end.

Lemma isOrthogonal_b_symmetric : forall (t t' : Triple),
  isOrthogonal_b t t' = isOrthogonal_b t' t.
Proof.
  intros [x y z] [x' y' z']. unfold isOrthogonal_b.
  rewrite -> (Qcmult_comm x x').
  rewrite -> (Qcmult_comm y y').
  rewrite -> (Qcmult_comm z z').
  reflexivity.
Defined.

Definition polar (t1 t2 : Triple) : Triple :=
  match t1, t2 with
  | triple x1 y1 z1, triple x2 y2 z2 => triple (det2 y1 z1 y2 z2) (det2 z1 x1 z2 x2) (det2 x1 y1 x2 y2)
  end.

Lemma polar_is_orthogonal : forall t t' : Triple,
  isOrthogonal_b t (polar t t') = true /\ isOrthogonal_b t' (polar t t') = true.
Proof.
  intros [x y z] [x' y' z'].
  unfold polar. unfold isOrthogonal_b. unfold det2.
  (* It's a bit gross / brittle being so explicit with H1, H2 below. Maybe should factor through general det3 results. *)
  assert (H1 : x * (y * z' - z * y') + y * (z * x' - x * z') + z * (x * y' - y * x') = 0). { ring. } rewrite -> H1.
  assert (H2 : x' * (y * z' - z * y') + y' * (z * x' - x * z') + z' * (x * y' - y * x') = 0). { ring. } rewrite -> H2.
  split; reflexivity.
Defined.

Definition eqt_b (t1 t2 : Triple) : bool :=
  match polar t1 t2 with
  | triple x y z => (Qc_eq_bool x 0) && (Qc_eq_bool y 0) && (Qc_eq_bool z 0)
  end.

Definition eqt (t1 t2 : Triple) := eqt_b t1 t2 = true.

Lemma eqt_refl : forall t1 t2 : Triple,
  eqt_b t1 t2 = true <-> eqt t1 t2.
Proof. intros. unfold eqt. apply iff_refl. Defined.

Lemma isNotZero_equiv : forall (x y z : Qc),
  isNotZero (triple x y z) <-> ~(x = 0 /\ y = 0 /\ z = 0).
Proof.
  unfold isNotZero. intros x y z. split.
  - intros [Hx | [Hy | Hz]]; unfold not; intros [Hx' [Hy' Hz']]; contradiction.
  - intros H.
    assert (Hx : x = 0 \/ x <> 0). { apply Qc_eq_zero_dec. }
    assert (Hy : y = 0 \/ y <> 0). { apply Qc_eq_zero_dec. }
    assert (Hz : z = 0 \/ z <> 0). { apply Qc_eq_zero_dec. }
    destruct Hx.
    + destruct Hy.
      * destruct Hz.
        -- subst. exfalso. apply H. split; [reflexivity | split; reflexivity].
        -- right. right. assumption.
      * right. left. assumption.
    + left. assumption.
Defined.

Lemma polar_not_zero : forall t1 t2 : Triple,
  isNotZero t1 -> isNotZero t2 -> ~eqt t1 t2 -> isNotZero (polar t1 t2).
Proof.
  intros [x1 y1 z1] [x2 y2 z2] ev1 ev2 Hne.
  unfold polar. rewrite -> isNotZero_equiv. unfold not. intros [Hx [Hy Hz]].
  unfold not in Hne. apply Hne. unfold eqt. unfold eqt_b. unfold polar.
  rewrite -> Hx. rewrite -> Hy. rewrite -> Hz.
  reflexivity.
Defined.

Lemma solve_det2 : forall a b c d : Qc,
  d <> 0 -> d*a = c*b -> a = b / d * c.
Proof.
  intros a b c d Hd Heq.
  assert (H : d * a / d = a). { field. apply Hd. }
  rewrite <- H. rewrite -> Heq. field. apply Hd.
Defined.

Lemma eqt_spec: forall (x y z x' y' z' : Qc) (ev : isNotZero (triple x y z)) (ev' : isNotZero (triple x' y' z')),
  eqt (triple x y z) (triple x' y' z') <-> exists t, t<>0 /\ x' = t*x /\ y' = t*y /\ z' = t*z.
Proof.
  intros. subst. unfold eqt. unfold eqt_b. unfold polar. split.
  - intros Heq. repeat (rewrite -> andb_true_iff in Heq). destruct Heq as [[Hyz Hzx] Hxy].
    rewrite -> det2_vanish_bool in Hyz.
    rewrite -> det2_vanish_bool in Hzx.
    rewrite -> det2_vanish_bool in Hxy.
    (* Alternative proof (relies on Qc having a norm via its ordering) uses:
    exists (x*x' + y*y' + z*z' / (x*x + y*y + z*z)). *)
    destruct (Qc_eq_bool z 0) eqn:Hz0.
    + apply Qc_eq_bool_correct in Hz0. subst.
      rewrite -> Qcmult_0_l in Hzx. apply symmetry in Hzx. apply Qcmult_integral in Hzx.
      rewrite -> Qcmult_0_l in Hyz. apply Qcmult_integral in Hyz.
      destruct (Qc_eq_bool y 0) eqn:Hy0.
      * apply Qc_eq_bool_correct in Hy0. subst.
        rewrite -> Qcmult_0_l in Hxy. apply Qcmult_integral in Hxy.
        assert (Hx : x <> 0). {
          unfold isNotZero in ev.
          destruct ev as [H | [H | H]]; [assumption | contradiction | contradiction].
        }
        exists (x'/x). rewrite -> Qcmult_0_r. split.
        -- assert (Hy' : y' = 0). { destruct Hxy; [contradiction | assumption]. }
           assert (Hz' : z' = 0). { destruct Hzx; [contradiction | assumption]. }
           assert (Hx' : x' <> 0). { destruct ev' as [H | [H | H]]; [assumption | contradiction | contradiction]. }
           apply Qc_quot_non_zero; assumption.
        -- split.
           ++ rewrite -> (test_field x' x Hx). reflexivity.
           ++ split.
              ** destruct Hxy; [contradiction | assumption].
              ** destruct Hzx; [contradiction | assumption].
      * exists (y'/y).
        assert (Hyn0: y <>0). { apply Qc_eq_bool_correct'. assumption. } split.
        -- apply (Qc_quot_non_zero y' y Hyn0). destruct (Qc_eq_zero_dec y') as [Hy'|Hy']; try assumption.
           exfalso. subst. rewrite -> Qcmult_0_r in Hxy. apply symmetry in Hxy. apply Qcmult_integral in Hxy.
           assert (Hx' : x' = 0). { destruct Hxy; [contradiction | assumption]. }
           assert (Hz' : z' = 0). { destruct Hyz; [contradiction | assumption]. }
           subst. destruct ev' as [H | [H | H]]; contradiction.
        -- split.
           ++ apply symmetry in Hxy. apply solve_det2; assumption.
           ++ split.
              ** rewrite -> (test_field y' y Hyn0). reflexivity.
              ** rewrite -> Qcmult_0_r. destruct Hyz; [contradiction | assumption].
    + exists (z'/z).
      assert (Hzn0: z<>0). { apply Qc_eq_bool_correct'. assumption. } split.
      * apply (Qc_quot_non_zero z' z Hzn0). destruct (Qc_eq_zero_dec z') as [Hz'|Hz']; try assumption.
        exfalso. subst.
        rewrite -> Qcmult_0_r in Hzx. apply Qcmult_integral in Hzx.
        assert (Hx' : x' = 0). { destruct Hzx; [contradiction | assumption]. }
        rewrite -> Qcmult_0_r in Hyz. apply symmetry in Hyz. apply Qcmult_integral in Hyz.
        assert (Hy' : y' = 0). { destruct Hyz; [contradiction | assumption]. }
        subst. destruct ev' as [H | [H | H]]; contradiction.
      * split.
        -- apply solve_det2; assumption.
        -- split.
           ** apply symmetry in Hyz. apply solve_det2; assumption.
           ** rewrite -> (test_field z' z Hzn0). reflexivity.
  - intros [t [Ht0 [Htx [Hty Htz]]]]. subst. unfold det2.
    repeat (apply andb_true_intro; (try split)); rewrite -> Qc_eq_bool_correct'''; ring.
Defined.

Inductive Point :=
  | point : forall t : Triple, isNotZero t -> Point.

Inductive Line :=
  | line : forall t : Triple, isNotZero t -> Line.

Definition eqp_b (p1 p2 : Point) :=
  match p1, p2 with
  | point t1 _, point t2 _ => eqt_b t1 t2
  end.

Definition eqp (p1 p2 : Point) := eqp_b p1 p2 = true.

Lemma eqp_refl : forall p1 p2 : Point,
  eqp_b p1 p2 = true <-> eqp p1 p2.
Proof. intros. unfold eqp. apply iff_refl. Defined.

Definition eql_b (l1 l2 : Line) :=
  match l1, l2 with
  | line t1 _, line t2 _ => eqt_b t1 t2
  end.

Definition eql (l1 l2 : Line) := eql_b l1 l2 = true.

Lemma eql_refl : forall l1 l2 : Line,
  eql_b l1 l2 = true <-> eql l1 l2.
Proof. intros. unfold eql. apply iff_refl. Defined.

Lemma eqt_b_symmetric : forall t t' : Triple,
  eqt_b t t' = eqt_b t' t.
Proof.
  intros [x y z] [x' y' z']. unfold eqt_b. simpl.
  rewrite -> (det2_vanishing_symmetry y z y' z').
  rewrite -> (det2_vanishing_symmetry z x z' x').
  rewrite -> (det2_vanishing_symmetry x y x' y').
  reflexivity.
Defined.

Corollary eqp_symmetric : forall p p' : Point,
  eqp p p' <-> eqp p' p.
Proof.
  intros [t ev] [t' ev']. unfold eqp. unfold eqp_b. rewrite -> eqt_b_symmetric. reflexivity.
Defined.

Corollary eql_symmetric : forall l l' : Line,
  eql l l' <-> eql l' l.
Proof.
  intros [t ev] [t' ev']. unfold eql. unfold eql_b. rewrite -> eqt_b_symmetric. reflexivity.
Defined.

Lemma eqt_transitive : forall (t t' t'' : Triple) (ev : isNotZero t) (ev' : isNotZero t') (ev'' : isNotZero t''),
  eqt t t' -> eqt t' t'' -> eqt t t''.
Proof.
  intros [x y z] [x' y' z'] [x'' y'' z''] ev ev' ev'' Heq Heq'.
  rewrite -> (eqt_spec _ _ _ _ _ _ ev ev') in Heq.
  rewrite -> (eqt_spec _ _ _ _ _ _ ev' ev'') in Heq'.
  rewrite -> (eqt_spec _ _ _ _ _ _ ev ev'').
  destruct Heq as [t [Ht [Hx [Hy Hz]]]].
  destruct Heq' as [t' [Ht' [Hx' [Hy' Hz']]]].
  exists (t' * t).
  repeat split.
  - unfold not. intros contra. apply Qcmult_integral in contra. destruct contra; contradiction.
  - rewrite <- Qcmult_assoc. rewrite <- Hx. assumption.
  - rewrite <- Qcmult_assoc. rewrite <- Hy. assumption.
  - rewrite <- Qcmult_assoc. rewrite <- Hz. assumption.
Defined.

Corollary eql_transitive : forall l l' l'' : Line,
  eql l l' -> eql l' l'' -> eql l l''.
Proof.
  intros [t ev] [t' ev'] [t'' ev'']. unfold eql. unfold eql_b. repeat (rewrite -> eqt_refl). apply eqt_transitive; assumption.
Defined.

Definition isPointOnLine_b (p : Point) (l : Line) : bool :=
  match p, l with
  | point t _, line t' _ => isOrthogonal_b t t'
  end.

Definition isPointOnLine (p : Point) (l : Line) := isPointOnLine_b p l = true.

Lemma isPointOnLine_refl : forall (p : Point) (l : Line),
  isPointOnLine_b p l = true <-> isPointOnLine p l.
Proof. intros. unfold isPointOnLine. apply iff_refl. Defined.

Lemma incidence_equality_compatible : forall t1 t1' t2 : Triple,
  isNotZero t1 -> isNotZero t1' -> eqt t1 t1' -> isOrthogonal_b t1 t2 = true -> isOrthogonal_b t1' t2 = true.
Proof.
  intros [x y z] [x' y' z'] [u v w] Hn0 Hn0' Heq Hinc.
  rewrite -> (eqt_spec x y z x' y' z' Hn0 Hn0') in Heq.
  destruct Heq as [t [Ht [Hx [Hy Hz]]]]. subst.
  simpl in Hinc. apply Qc_eq_bool_correct in Hinc.
  simpl. assert (H : t * x * u + t * y * v + t * z * w = t * (x * u + y * v + z * w)). { ring. }
  rewrite -> H. rewrite -> Hinc. rewrite Qcmult_0_r. reflexivity.
Defined.

Corollary equal_points_on_line : forall (p p' : Point) (l : Line),
  eqp p p' -> isPointOnLine p l -> isPointOnLine p' l.
Proof.
  intros [t1 evT1] [t1' evT1'] [t2 evT2] Heq Hinc.
  unfold eqp in Heq. unfold isPointOnLine in Hinc. unfold isPointOnLine_b in Hinc.
  unfold isPointOnLine. unfold isPointOnLine_b.
  apply (incidence_equality_compatible t1 t1' t2 evT1 evT1' Heq Hinc).
Defined.

Corollary equal_lines_contain_same_points : forall (l l' : Line) (p : Point),
  eql l l' -> isPointOnLine p l -> isPointOnLine p l'.
Proof.
  intros [t1 evT1] [t1' evT1'] [t2 evT2] Heq Hinc.
  unfold eql in Heq. unfold isPointOnLine in Hinc. unfold isPointOnLine_b in Hinc.
  unfold isPointOnLine. unfold isPointOnLine_b.
  rewrite isOrthogonal_b_symmetric in Hinc.  rewrite isOrthogonal_b_symmetric.
  apply (incidence_equality_compatible t1 t1' t2 evT1 evT1' Heq Hinc).
Defined.

Corollary line_pair_distinct_point : forall (p : Point) (l l' : Line),
  isPointOnLine p l -> ~isPointOnLine p l' -> ~eql l l'.
Proof.
  unfold not. intros p l l' H H' Heq. apply H'. apply (equal_lines_contain_same_points l l' p Heq H).
Defined.

Inductive LinePair :=
  | linePair : forall (l l' : Line), ~eql l l' -> LinePair.

Inductive PointPair :=
  | pointPair : forall (p p' : Point), ~eqp p p' -> PointPair.

Definition linePairIntersection (lp : LinePair) : Point :=
  match lp with
  | linePair (line t evT) (line t' evT') evLp => point (polar t t') (polar_not_zero t t' evT evT' evLp)
  end.

Definition pointPairLine (pp : PointPair) : Line :=
  match pp with
  | pointPair (point t evT) (point t' evT') evPp => line (polar t t') (polar_not_zero t t' evT evT' evPp)
  end.

Lemma intersection_on_lines : forall (l l' : Line) (ev : ~eql l l'),
  isPointOnLine (linePairIntersection (linePair l l' ev)) l /\
  isPointOnLine (linePairIntersection (linePair l l' ev)) l'.
Proof.
  intros [t evT] [t' evT'] Hne.
  unfold linePairIntersection. unfold isPointOnLine. unfold isPointOnLine_b.
  rewrite (isOrthogonal_b_symmetric _ t). rewrite (isOrthogonal_b_symmetric _ t').
  apply polar_is_orthogonal.
Defined.

Lemma end_points_on_line : forall (p p' : Point) (ev : ~eqp p p'),
  isPointOnLine p (pointPairLine (pointPair p p' ev)) /\
  isPointOnLine p' (pointPairLine (pointPair p p' ev)).
Proof.
  intros [t evT] [t' evT'] Hne.
  unfold pointPairLine. unfold isPointOnLine. unfold isPointOnLine_b. apply polar_is_orthogonal.
Defined.

Lemma two_points_characterise_line' : forall (l : Line) (p q : Point) (evDistinct : ~eqp p q),
  isPointOnLine p l -> isPointOnLine q l -> eql l (pointPairLine (pointPair p q evDistinct)).
Proof.
  intros [[x y z] evl] [[u v w] ev] [[u' v' w'] ev'] evDistinct evInc evInc'.
  unfold isPointOnLine in evInc. simpl in evInc. apply Qc_eq_bool_correct in evInc.
  unfold isPointOnLine in evInc'. simpl in evInc'. apply Qc_eq_bool_correct in evInc'.
  unfold pointPairLine. unfold polar. unfold eql. unfold eql_b. unfold eqt_b. unfold polar. unfold det2.
  assert (Hx : y * (u*v' - v*u') - z * (w*u' - u*w') = u * (u'*x + v'*y + w'*z) - u' * (u*x + v*y + w*z)). { ring. }
  assert (Hy : z * (v*w' - w*v') - x * (u*v' - v*u') = v * (u'*x + v'*y + w'*z) - v' * (u*x + v*y + w*z)). { ring. }
  assert (Hz : x * (w*u' - u*w') - y * (v*w' - w*v') = w * (u'*x + v'*y + w'*z) - w' * (u*x + v*y + w*z)). { ring. }
  rewrite -> Hx. rewrite -> Hy. rewrite -> Hz. rewrite -> evInc. rewrite -> evInc'.
  repeat (rewrite -> Qcmult_0_r). repeat (rewrite -> Qcmult_0_l). reflexivity.
Defined.

Corollary two_points_characterise_line : forall (l l' : Line) (p q : Point) (evDistinct : ~eqp p q),
  isPointOnLine p l -> isPointOnLine q l -> isPointOnLine p l' -> isPointOnLine q l' -> eql l l'.
Proof.
  intros l l' p q Hpq Hp Hq Hp' Hq'.
  assert (Hl := two_points_characterise_line' l p q Hpq Hp Hq).
  assert (Hl' := two_points_characterise_line' l' p q Hpq Hp' Hq'). rewrite -> eql_symmetric in Hl'.
  apply (eql_transitive l _ l' Hl Hl').
Defined.

Definition isAffine_b p :=
  match p with
  | point (triple x y z) _ => negb (Qc_eq_bool z 0)
  end.

Definition isAffine p := isAffine_b p = true.

Lemma isAffine_refl : forall (p : Point),
  isAffine_b p = true <-> isAffine p.
Proof. intros p. unfold isAffine. apply iff_refl. Defined.

Inductive LineSeg :=
  | lineSeg : forall (p q : Point), ~eqp p q -> isAffine p -> isAffine q -> LineSeg.

Definition lineFromLineSeg (ls : LineSeg) :=
  match ls with
  | lineSeg p p' evDistinct evAff evAff' => pointPairLine (pointPair p p' evDistinct)
  end.

Definition dotProd2 (x1 y1 x2 y2 : Qc) := x1*x2 + y1*y2.

Definition isPointOnLineSeg_b (p : Point) (l : LineSeg) : bool :=
  match (isAffine_b p && isPointOnLine_b p (lineFromLineSeg l)) with
  | false => false
  | true => match p, l with
    | point (triple x y z) _, lineSeg (point (triple x1 y1 z1) _) (point (triple x2 y2 z2) _) _ _ _ =>
      let u := x/z - x1/z1 in
      let v := y/z - y1/z1 in
      let u' := x2/z2 - x1/z1 in
      let v' := y2/z2 - y1/z1 in
      let t := dotProd2 u v u' v' / (dotProd2 u' v' u' v') in
        (Qc_lt_bool 0 t) && (Qc_lt_bool t 1)
    end
  end.

Definition isPointOnLineSeg (p : Point) (l : LineSeg) := isPointOnLineSeg_b p l = true.

Lemma isPointOnLineSeg_refl : forall (p : Point) (l : LineSeg),
  isPointOnLineSeg_b p l = true <-> isPointOnLineSeg p l.
Proof. intros. unfold isPointOnLineSeg. apply iff_refl. Defined.

Definition det3pt p q r :=
  match p, q, r with
  | point (triple a b c) _,
    point (triple d e f) _,
    point (triple g h i) _ =>
      det3 a b c
           d e f
           g h i
  end.

Lemma det3pt_permute : forall p q r : Point,
  det3pt p q r = det3pt r p q.
Proof.
  intros [[x1 y1 z1] ev1] [[x2 y2 z2] ev2] [[x3 y3 z3] ev3].
  simpl. unfold det3. unfold det2. ring.
Defined.

Lemma det3pt_permute_sign : forall p q r : Point,
  det3pt p q r = -det3pt p r q.
Proof.
  intros [[x1 y1 z1] ev1] [[x2 y2 z2] ev2] [[x3 y3 z3] ev3].
  unfold det3pt. unfold det3. unfold det2. ring.
Defined.

Lemma point_on_line_seg_det : forall (p1 p2 p3 : Point) (evL : ~eqp p2 p3),
  det3pt p1 p2 p3 = 0 <-> isPointOnLine p1 (pointPairLine (pointPair p2 p3 evL)).
Proof.
  intros [[x1 y1 z1] ev1] [[x2 y2 z2] ev2] [[x3 y3 z3] ev3] evL.
  unfold isPointOnLine. unfold isPointOnLine_b. unfold pointPairLine. unfold isOrthogonal_b. unfold polar. unfold det3pt.
  rewrite -> Qc_eq_bool_correct'''. unfold det3. apply iff_refl.
Defined.

Definition lineSegMeetsLine_b ls l (evLp : ~eql (lineFromLineSeg ls) l) :=
  let lp := linePair (lineFromLineSeg ls) l evLp in
    isPointOnLineSeg_b (linePairIntersection lp) ls.

Definition lineSegMeetsLineSeg_b (l m : LineSeg) : bool.
refine (
  let sameLine := eql_b (lineFromLineSeg l) (lineFromLineSeg m) in
    match sameLine as sameLine' return (sameLine = sameLine' -> _) with
    | true => fun _ => false
    | false => fun evDistinct => (lineSegMeetsLine_b l (lineFromLineSeg m) _) && (lineSegMeetsLine_b m (lineFromLineSeg l) _)
    end (eq_refl sameLine)
);
  [| rewrite eql_symmetric];
  unfold not; intros contra; rewrite <- eql_refl in contra;
  unfold sameLine in evDistinct; rewrite -> evDistinct in contra;
  inversion contra.
Defined.

Definition lineSegMeetsLineSeg (l m : LineSeg) := lineSegMeetsLineSeg_b l m = true.

Lemma lineSegMeetsLineSeg_refl : forall (l m : LineSeg),
  lineSegMeetsLineSeg_b l m = true <-> lineSegMeetsLineSeg l m.
Proof. intros. unfold lineSegMeetsLineSeg. apply iff_refl. Defined.

Definition lineSegMeetsLineSegClosed_b (l m : LineSeg) :=
  match l, m with
  | lineSeg p q _ _ _, lineSeg p' q' _ _ _ =>
    lineSegMeetsLineSeg_b l m ||
    isPointOnLineSeg_b p m || isPointOnLineSeg_b q m ||
    isPointOnLineSeg_b p' l || isPointOnLineSeg_b q' l ||
    eqp_b p p' || eqp_b p q' || eqp_b q p' || eqp_b q q'
  end.

Definition flipLineSeg (l : LineSeg) : LineSeg.
refine (
  match l with
  | lineSeg p p' evNe evAff evAff' => lineSeg p' p _ evAff' evAff
  end
).
  rewrite eqp_symmetric. assumption.
Defined.

Lemma flipped_line_seg_same_line : forall l : LineSeg,
  eql (lineFromLineSeg (flipLineSeg l)) (lineFromLineSeg l).
Proof.
  intros [[[x y z] evT] [[x' y' z'] evT'] evNe evAff evAff'].
  unfold flipLineSeg. unfold lineFromLineSeg. unfold pointPairLine.
  unfold eql. unfold eql_b. unfold eqt_b. unfold polar.
  repeat (rewrite andb_true_iff; split); apply Qc_eq_bool_correct'''; unfold det2; ring.
Defined.
