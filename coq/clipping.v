Require Import QArith.
Require Import QArith.Qcanon.
Require Import Lists.List.

From F4 Require Export viewports.

Open Scope list_scope.
Open Scope Qc_scope.
Open Scope program_scope.

Inductive IsClipableResult : Type :=
  | CR_FullyWithin : ViewPort -> LineSeg -> IsClipableResult
  | CR_ThroughEye : ViewPort -> LineSeg -> IsClipableResult
  | CR_ThroughBack : ViewPort -> LineSeg -> IsClipableResult
  | CR_Clipable : IsClipableResult.

Definition isClipable (v : ViewPort) (l : LineSeg) : IsClipableResult :=
  match v, l with
  | viewPort e lv _ _, lineSeg p q _ _ _ =>
    let fullyWithin := isPointInsideViewPort_b p v && isPointInsideViewPort_b q v in
    let throughEye := isPointOnLineSeg_b e l || eqp_b e p || eqp_b e q in
    let throughBack := lineSegMeetsLineSeg_b l lv || isPointOnLineSeg_b p lv || isPointOnLineSeg_b q lv in
      if fullyWithin then CR_FullyWithin v l else
        if throughEye then CR_ThroughEye v l else
          if throughBack then CR_ThroughBack v l else
            CR_Clipable
  end.

Definition clipByOneSide (v : ViewPort) (l : LineSeg) (evClipable : isClipable v l = CR_Clipable) : option ViewPort :=
  match l with
  | lineSeg p q _ _ _ =>
    let pInside := isPointInsideViewPort_b p v in
    let qInside := isPointInsideViewPort_b q v in
    let meetsEA := lineSegMeetsLineSegClosed_b l (viewPortEdgeA v) in
    let meetsEB := lineSegMeetsLineSegClosed_b l (viewPortEdgeB v) in
      match meetsEA, meetsEB with
      | true, false =>
        match pInside as pInside', qInside as qInside'
              return (pInside = pInside' -> qInside = qInside' -> _) with
        | true, _ => fun evPInside _ => Some (vpClipToSideB p v evPInside)
        | _, true => fun _ evQInside => Some (vpClipToSideB q v evQInside)
        | _, _ => fun _ _ => Some v
        end (eq_refl pInside) (eq_refl qInside)
      | false, true =>
        match pInside as pInside', qInside as qInside'
              return (pInside = pInside' -> qInside = qInside' -> _) with
        | true, _ => fun evPInside _ => Some (vpClipToSideA p v evPInside)
        | _, true => fun _ evQInside => Some (vpClipToSideA q v evQInside)
        | _, _ => fun _ _ => Some v
        end (eq_refl pInside) (eq_refl qInside)
      | false, false => Some v
      | true, true => None
      end
  end.

Inductive ClippingResult : Type :=
  | Visible : LineSeg -> ClippingResult
  | Invisible : ClippingResult
  | Unclipable : IsClipableResult -> ClippingResult (* If we wanted to be really pedantic, we could dependently require evidence that not CR_Clipable *)
  | ThroughEye : ClippingResult.

Fixpoint clipByAllSides (v : ViewPort) (ls : list LineSeg) : ClippingResult :=
  match ls with
  | [] => match v with | viewPort e lv evAffE evV => Visible lv end
  | l::ls' =>
    let clipable := isClipable v l in
      match clipable as clipable' return (clipable = clipable' -> _) with
      | CR_Clipable => fun evClipable =>
        match (clipByOneSide v l evClipable) with
        | None => Invisible
        | Some v' => clipByAllSides v' ls'
        end
      | _ => fun _ => Unclipable clipable
      end (eq_refl clipable)
  end.

Inductive AffinePoint :=
  | affinePoint : forall x y : Qc, AffinePoint.

Definition point_from_affine_point (p : AffinePoint) : Point :=
  match p with
  | affinePoint x y => point (triple x y 1) (or_intror (or_intror Qc_1_not_0))
  end.

Lemma affine_point_is_affine : forall p : AffinePoint,
  isAffine (point_from_affine_point p).
Proof. intros [x y]. unfold isAffine. reflexivity. Defined.

Fixpoint edgesFromPointPairs (pqs : list (prod AffinePoint AffinePoint)) : list LineSeg.
refine(
  match pqs with
  | [] => []
  | (p', q')::t =>
    let p := point_from_affine_point p' in
    let q := point_from_affine_point q' in
    let samePoint_b := eqp_b p q in
      match samePoint_b as samePoint_b' return (samePoint_b = samePoint_b' -> _) with
      | true => fun _ => edgesFromPointPairs t
      | false => fun evDistinct => (lineSeg p q _ _ _)::edgesFromPointPairs t
      end (eq_refl samePoint_b)
  end).
  - unfold eqp. unfold samePoint_b in evDistinct. rewrite -> evDistinct. unfold not. intros H. inversion H.
  - apply affine_point_is_affine.
  - apply affine_point_is_affine.
Defined.

Definition getClippingData := allCuts @ edgesFromPointPairs @ zipToPairs @ closeList.

Definition doAllClipping (e : AffinePoint) (ps : list AffinePoint) : list ClippingResult.
refine(
  let eye := point_from_affine_point e in
  let f := fun inst : prod LineSeg (list LineSeg) =>
    match inst with
    | (lv, edges) =>
      let throughEye := isPointOnLine_b eye (lineFromLineSeg lv) in
        match throughEye as throughEye' return (throughEye = throughEye' -> _) with
        | true => fun _ => ThroughEye
        | false => fun evNotThrough => clipByAllSides (viewPort eye lv _ _) edges
        end (eq_refl throughEye)
    end in
  map f (getClippingData ps)
).
  - apply affine_point_is_affine.
  - rewrite <- isPointOnLine_refl. unfold throughEye in evNotThrough. rewrite -> evNotThrough. unfold not. intros H. inversion H.
Defined.

Definition getPointFromCoords (coords : prod Z Z) :=
  match coords with
  | (x, y) => affinePoint (Qc_from_Z x) (Qc_from_Z y)
  end.

Definition getClippingPoints (eye : prod Z Z) (pts : list (prod Z Z)) :=
  (getPointFromCoords eye, map getPointFromCoords pts).

Definition clipPolygon (d : prod (prod Z Z) (list (prod Z Z))) :=
  match d with
  | (eye, pts) =>
    match (getClippingPoints eye pts) with
    | (e, ps) => doAllClipping e ps
    end
  end.
