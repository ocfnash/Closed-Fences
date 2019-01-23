Require Import QArith.
Require Import QArith.Qcanon.

From F4 Require Export geometry.

Open Scope Qc_scope.
Open Scope program_scope.

Inductive ViewPort :=
  | viewPort : forall (e : Point) (ls : LineSeg), isAffine e -> ~isPointOnLine e (lineFromLineSeg ls) -> ViewPort.

Definition flipViewPort (v : ViewPort) : ViewPort.
refine (
  match v with
  | viewPort e l evAffE evV => viewPort e (flipLineSeg l) evAffE _
  end
).
  unfold not. intros contra. unfold not in evV. apply evV.
  apply (equal_lines_contain_same_points _ _ e (flipped_line_seg_same_line l) contra).
Defined.

Definition vpEye (v : ViewPort) :=
  match v with
  | viewPort e _ _ _ => e
  end.

Definition vpVertexA (v : ViewPort) :=
  match v with
  | viewPort _ (lineSeg a b _ _ _) _ _ => a
  end.

Definition vpVertexB := vpVertexA @ flipViewPort.

Definition vpBackLine (v : ViewPort) : Line :=
  match v with
  | viewPort _ lv _ _ => lineFromLineSeg lv
  end.

Definition viewPortEdgeA (v : ViewPort) : LineSeg.
refine (
  lineSeg (vpEye v) (vpVertexA v) _ _ _
); destruct v as [e [a b evNe evAffA evAffB] evAffE evV]; unfold vpEye; unfold vpVertexA.
  - unfold not. intros H. unfold lineFromLineSeg in evV. unfold not in evV. apply evV.
    apply equal_points_on_line with (p:=a).
    + rewrite -> eqp_symmetric. assumption.
    + destruct (end_points_on_line a b evNe) as [Ha Hb]. assumption.
  - assumption.
  - assumption.
Defined.

Definition viewPortEdgeB := viewPortEdgeA @ flipViewPort.

Definition negT (t : Triple) :=
  match t with
  | triple x y z => triple (-x) (-y) (-z)
  end.

Definition zPosify (p : Point) : Point.
refine (
  match p as p' return (p = p' -> _) with
  | point t ev =>
    let q := point (negT t) _ in
    match t with
    | triple _ _ z =>
      fun H => if Qc_lt_bool z 0 then q else p
    end
  end (eq_refl p)).
  destruct t as [x y z]. simpl in ev. simpl. repeat (rewrite <- Qc_non_vanishing_sign). assumption.
Defined.

(* TODO (maybe) kill zPosify and negT and just implement the below
  by exclusive or with boolean signs as needed *)
Definition isPointInsideViewPort_b (p : Point) (v : ViewPort) : bool :=
  match v with
  | viewPort e (lineSeg a b _ _ _) _ _ =>
    let p' := zPosify p in
    let e' := zPosify e in
    let a' := zPosify a in
    let b' := zPosify b in
    let sv   := signum (det3pt e' a' b') in
    let spab := signum (det3pt p' a' b') in
    let sepb := signum (det3pt e' p' b') in
    let seap := signum (det3pt e' a' p') in
    let sameSide_ab := Qc_eq_bool sv spab in
    let sameSide_be := Qc_eq_bool sv sepb in
    let sameSide_ea := Qc_eq_bool sv seap in
      sameSide_ab && sameSide_be && sameSide_ea
  end.

Definition isPointInsideViewPort (p : Point) (v : ViewPort) :=
  isPointInsideViewPort_b p v = true.

Lemma isPointInsideViewPort_refl : forall (p : Point) (v : ViewPort),
  isPointInsideViewPort_b p v = true <-> isPointInsideViewPort p v.
Proof. intros. unfold isPointInsideViewPort. apply iff_refl. Defined.

Lemma flipped_viewport_same_inside : forall (p : Point) (v : ViewPort),
  isPointInsideViewPort p v -> isPointInsideViewPort p (flipViewPort v).
Proof.
  intros p [e [a b evAB evAffA evAffB] evAffE evV].
  unfold flipViewPort. unfold flipLineSeg. unfold isPointInsideViewPort. unfold isPointInsideViewPort_b.
  repeat (rewrite andb_true_iff). repeat (rewrite Qc_eq_bool_correct'''). intros [[He Ha] Hb]. repeat split; [
    repeat (rewrite (det3pt_permute_sign _ (zPosify b) (zPosify a))) |
    repeat (rewrite (det3pt_permute_sign (zPosify e) _ (zPosify a))) |
    repeat (rewrite (det3pt_permute_sign (zPosify e) (zPosify b) _)) ];
  rewrite <- signum_minus'; assumption.
Defined.

Lemma zPosify_det3pt' : forall p q r : Point,
  det3pt (zPosify p) q r = 0 <-> det3pt p q r = 0.
Proof.
  intros [[x1 y1 z1] ev1] [[x2 y2 z2] ev2] [[x3 y3 z3] ev3].
  unfold zPosify. destruct (Qc_lt_bool z1 0).
  - unfold negT. unfold det3pt. unfold det3.
    assert (H : forall a b c u v w : Qc, (-a)*u + (-b)*v + (-c)*w = -(a*u + b*v + c*w)). { intros. ring. }
    rewrite -> H. apply Qc_opp_x_zero.
  - apply iff_refl.
Defined.

Lemma zPosify_det3pt : forall p q r : Point,
  det3pt (zPosify p) (zPosify q) (zPosify r) = 0 <-> det3pt p q r = 0.
Proof.
  intros p q r.
  rewrite -> zPosify_det3pt'.
  rewrite det3pt_permute. rewrite -> zPosify_det3pt'.
  rewrite det3pt_permute. rewrite -> zPosify_det3pt'.
  rewrite det3pt_permute.
  apply iff_refl.
Defined.

Lemma inside_viewport_not_on_edge_a : forall (p : Point) (v : ViewPort),
  isPointInsideViewPort p v -> ~isPointOnLine p (lineFromLineSeg (viewPortEdgeA v)).
Proof.
  unfold not. intros p [e [a b evL evAffA evAffB] evAffE evV] evInside evOnEdge.
  unfold not in evV. apply evV.
  unfold lineFromLineSeg.
  apply point_on_line_seg_det.
  assert (H : det3pt e a p = 0). {
    unfold viewPortEdgeA in evOnEdge. unfold vpEye in evOnEdge. unfold vpVertexA in evOnEdge.
    unfold lineFromLineSeg in evOnEdge.
    rewrite <- point_on_line_seg_det in evOnEdge. rewrite <- det3pt_permute in evOnEdge.
    assumption.
  }
  unfold isPointInsideViewPort in evInside. unfold isPointInsideViewPort_b in evInside.
  apply andb_prop in evInside. destruct evInside as [_ evInside'].
  rewrite <- zPosify_det3pt. rewrite <- zPosify_det3pt in H.
  rewrite -> H in evInside'. rewrite signum_zero in evInside'.
  rewrite -> Qc_eq_bool_correct''' in evInside'.
  apply signum_zero_is_zero. apply symmetry in evInside'.
  assumption.
Defined.

Lemma inside_viewport_not_eye : forall (p : Point) (v : ViewPort),
  isPointInsideViewPort p v -> ~eqp (vpEye v) p.
Proof.
  unfold not. intros p v evInside evEq.
  apply (inside_viewport_not_on_edge_a _ _ evInside).
  apply (equal_points_on_line _ _ _ evEq).
  apply end_points_on_line.
Defined.

Definition viewPortClippingLine (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v) : Line :=
  pointPairLine (pointPair (vpEye v) p (inside_viewport_not_eye p v evInside)).

Lemma viewport_clipping_line_contains_eye : forall (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v),
  isPointOnLine (vpEye v) (viewPortClippingLine p v evInside).
Proof.
  intros p v evInside. unfold viewPortClippingLine.
  destruct (end_points_on_line (vpEye v) p (inside_viewport_not_eye p v evInside)) as [He Hp].
  assumption.
Defined.

Definition viewPortClippingPoint (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v) : Point.
refine (
    let lc := viewPortClippingLine p v evInside in
    let lv := vpBackLine v in
      linePairIntersection (linePair lv lc _)
).
  rewrite -> eql_symmetric. apply (line_pair_distinct_point (vpEye v)).
  - apply viewport_clipping_line_contains_eye.
  - destruct v as [e ls eAff evV]. unfold vpEye. unfold vpBackLine in lv. assumption.
Defined.

Lemma vp_clipping_point_not_eye : forall (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v),
  ~eqp (viewPortClippingPoint p v evInside) (vpEye v).
Proof.
  unfold not. intros p v evInside contra.
  assert (H : isPointOnLine (viewPortClippingPoint p v evInside) (vpBackLine v)). { apply intersection_on_lines. }
  apply (equal_points_on_line _ _ _ contra) in H.
  destruct v as [e l evAffE evV].
  contradiction.
Defined.

Lemma vp_clipping_point_not_vertex_a : forall (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v),
  ~eqp (vpVertexA v) (viewPortClippingPoint p v evInside).
Proof.
  unfold not. intros p v evInside contra.
  assert (H : eql (viewPortClippingLine p v evInside) (lineFromLineSeg (viewPortEdgeA v))). {
    apply two_points_characterise_line with (p:=(vpEye v)) (q:=(viewPortClippingPoint p v evInside)).
    - rewrite eqp_symmetric. apply vp_clipping_point_not_eye.
    - apply end_points_on_line.
    - apply intersection_on_lines.
    - apply end_points_on_line.
    - apply (equal_points_on_line _ _ _ contra). apply end_points_on_line.
  }
  assert (H' : isPointOnLine p (lineFromLineSeg (viewPortEdgeA v))). {
    apply (equal_lines_contain_same_points _ _ _ H).
    apply end_points_on_line.
  }
  apply (inside_viewport_not_on_edge_a _ _ evInside H').
Defined.

Lemma clipping_point_affine : forall (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v),
  isAffine (viewPortClippingPoint p v evInside).
Proof.
  intros p v evInside.
  destruct p as [[x y z] evP]. destruct v as [[[x1 y1 z1] evE] [[[x2 y2 z2] evA] [[x3 y3 z3] evB] evL] evAffE evV].
  unfold viewPortClippingPoint. unfold vpBackLine. unfold lineFromLineSeg. unfold linePairIntersection. unfold viewPortClippingLine.
  unfold vpEye. unfold pointPairLine. unfold polar. unfold isAffine. unfold isAffine_b. apply negb_true_iff. apply Qc_eq_bool_correct''.
  unfold det2. unfold not. intros H. unfold not in evV. apply evV. unfold lineFromLineSeg. unfold pointPairLine.
  unfold polar. unfold isPointOnLine. unfold isPointOnLine_b. unfold isOrthogonal_b. apply Qc_eq_bool_correct'''.
Admitted.

Definition vpLineSegClipA (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v) : LineSeg.
refine (
  lineSeg (vpVertexA v) (viewPortClippingPoint p v evInside) (vp_clipping_point_not_vertex_a p v evInside) _ _
).
  - destruct v as [e [a b evABDistinct evAffA evAffB] eAff evV]. assumption.
  - apply clipping_point_affine.
Defined.

Lemma vp_clipping_point_gives_viewport_a : forall (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v),
  ~isPointOnLine (vpEye v) (lineFromLineSeg (vpLineSegClipA p v evInside)).
Proof.
  intros p v evInside.
  assert (H : eql (lineFromLineSeg (vpLineSegClipA p v evInside)) (vpBackLine v)). {
    apply (two_points_characterise_line _ _ (vpVertexA v) (viewPortClippingPoint p v evInside) (vp_clipping_point_not_vertex_a _ _ _)).
    - unfold vpLineSegClipA. apply end_points_on_line.
    - unfold vpLineSegClipA. apply end_points_on_line.
    - destruct v as [e [a b evAB evA evB] evE evV]. apply end_points_on_line.
    - apply intersection_on_lines.
  }
  destruct v as [e ls evAffE evV].
  simpl in H. simpl.
  unfold not. intros contra. unfold not in evV. apply evV.
  apply (equal_lines_contain_same_points _ _ _ H). apply contra.
Defined.

Definition vpClipToSideA (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v) : ViewPort.
refine (
  viewPort (vpEye v) (vpLineSegClipA p v evInside) _ (vp_clipping_point_gives_viewport_a p v evInside)
).
  destruct v. unfold vpEye. assumption.
Defined.

Definition vpClipToSideB (p : Point) (v : ViewPort) (evInside : isPointInsideViewPort p v) : ViewPort :=
  vpClipToSideA p (flipViewPort v) (flipped_viewport_same_inside p v evInside).
