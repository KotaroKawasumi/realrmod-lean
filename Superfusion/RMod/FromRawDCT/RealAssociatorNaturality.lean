import Superfusion.RMod.FromRawDCT.RealAssociator
import Superfusion.RMod.FromRawDCT.RealAssociatorLaws

/-!
# Naturality of the endpoint-normalized real associator

This concrete proof layer derives naturality from the stored ternary
connector action law.  The connector is never re-evaluated: the only raw
input is `TLaws.hom_left`, specialized to the already-proved zero parity of
the computably shifted real connector.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace RealAssociatorNaturality

universe u

/-! ## The parity-zero connector intertwines arbitrary coefficients -/

/-- At connector parity zero, the homogeneous action law extends to three
arbitrary coefficient-algebra elements by their even/odd decomposition. -/
theorem hom_left_of_parity_zero
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (hp : x.T.parity a b c = 0)
    (u : (x.D.algebra a).carrier)
    (v : (x.D.algebra b).carrier)
    (w : (x.D.algebra c).carrier)
    (m : x.T.LeftCarrier a b c) :
    x.T.hom a b c (x.T.leftRoute.leftPure a b c u v w m) =
      x.T.rightRoute.leftPure a b c u v w (x.T.hom a b c m) := by
  let u0 := (x.D.algebra a).component 0 u
  let u1 := (x.D.algebra a).component 1 u
  let v0 := (x.D.algebra b).component 0 v
  let v1 := (x.D.algebra b).component 1 v
  let w0 := (x.D.algebra c).component 0 w
  let w1 := (x.D.algebra c).component 1 w
  have hu : (x.D.algebra a).add u0 u1 = u := by
    simpa only [u0, u1, zero_add] using
      (hx.D.algebra_laws a).component_complement 0 u
  have hv : (x.D.algebra b).add v0 v1 = v := by
    simpa only [v0, v1, zero_add] using
      (hx.D.algebra_laws b).component_complement 0 v
  have hw : (x.D.algebra c).add w0 w1 = w := by
    simpa only [w0, w1, zero_add] using
      (hx.D.algebra_laws c).component_complement 0 w
  have hu0 : (x.D.algebra a).MemGrade 0 u0 :=
    (hx.D.algebra_laws a).component_idem 0 u
  have hu1 : (x.D.algebra a).MemGrade 1 u1 :=
    (hx.D.algebra_laws a).component_idem 1 u
  have hv0 : (x.D.algebra b).MemGrade 0 v0 :=
    (hx.D.algebra_laws b).component_idem 0 v
  have hv1 : (x.D.algebra b).MemGrade 1 v1 :=
    (hx.D.algebra_laws b).component_idem 1 v
  have hw0 : (x.D.algebra c).MemGrade 0 w0 :=
    (hx.D.algebra_laws c).component_idem 0 w
  have hw1 : (x.D.algebra c).MemGrade 1 w1 :=
    (hx.D.algebra_laws c).component_idem 1 w
  have hhom (i j k : ZMod 2)
      (p : (x.D.algebra a).carrier)
      (q : (x.D.algebra b).carrier)
      (r : (x.D.algebra c).carrier)
      (hp' : (x.D.algebra a).MemGrade i p)
      (hq' : (x.D.algebra b).MemGrade j q)
      (hr' : (x.D.algebra c).MemGrade k r) :
      x.T.hom a b c (x.T.leftRoute.leftPure a b c p q r m) =
        x.T.rightRoute.leftPure a b c p q r (x.T.hom a b c m) := by
    simpa only [hp, zero_mul, RawDCT.shiftParitySign_zero,
      (hx.T.right_route_laws.one_smul)] using
      hx.T.hom_left a b c i j k p q r m hp' hq' hr'
  rw [← hu, ← hv, ← hw]
  simp_rw [hx.T.left_route_laws.left_add_first,
    hx.T.left_route_laws.left_add_second,
    hx.T.left_route_laws.left_add_third,
    hx.T.hom_add]
  rw [hhom 0 0 0 u0 v0 w0 hu0 hv0 hw0,
    hhom 0 0 1 u0 v0 w1 hu0 hv0 hw1,
    hhom 0 1 0 u0 v1 w0 hu0 hv1 hw0,
    hhom 0 1 1 u0 v1 w1 hu0 hv1 hw1,
    hhom 1 0 0 u1 v0 w0 hu1 hv0 hw0,
    hhom 1 0 1 u1 v0 w1 hu1 hv0 hw1,
    hhom 1 1 0 u1 v1 w0 hu1 hv1 hw0,
    hhom 1 1 1 u1 v1 w1 hu1 hv1 hw1]
  simp_rw [hx.T.right_route_laws.left_add_first,
    hx.T.right_route_laws.left_add_second,
    hx.T.right_route_laws.left_add_third]

/-! ## Coordinate form of the same stored connector law -/

@[implicit_reducible]
private def algebraAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier where
  add := d.add
  add_assoc := h.add_assoc
  zero := d.zero
  zero_add := h.zero_add
  add_zero := h.add_zero
  neg := d.neg
  neg_add_cancel := h.neg_add
  add_comm := h.add_comm
  sub := fun x y => d.add x (d.neg y)
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

private theorem mul_zero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (q : d.carrier) :
    d.mul q d.zero = d.zero := by
  let y := d.mul q d.zero
  have hyy : y = d.add y y := by
    calc
      y = d.mul q (d.add d.zero d.zero) := by
        exact congrArg (d.mul q) (h.zero_add d.zero).symm
      _ = d.add y y := h.mul_add q d.zero d.zero
  calc
    y = d.add d.zero y := (h.zero_add y).symm
    _ = d.add (d.add (d.neg y) y) y := by rw [h.neg_add]
    _ = d.add (d.neg y) (d.add y y) := h.add_assoc _ _ _
    _ = d.add (d.neg y) y := by rw [← hyy]
    _ = d.zero := h.neg_add y

private instance algebraAddCommGroupInstance
    (d : SuperAlgebraData ℝ) [h : Fact (SuperAlgebraLaws d)] :
    AddCommGroup d.carrier := algebraAddCommGroup d h.out

private theorem rawFinSum_eq_sum (d : SuperAlgebraData ℝ)
    [Fact (SuperAlgebraLaws d)] {n : ℕ} (f : Fin n → d.carrier) :
    CData.rawFinSum d f = ∑ i, f i := by
  unfold CData.rawFinSum
  exact List.sum_ofFn

/-- A left-route delta collapses a double coefficient sum to its supported
row. -/
private theorem leftDelta_weighted_sum
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c)
    (q : x.C.Index a b → x.C.Index (a + b) c →
      (x.D.algebra (a + b + c)).carrier) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun targetAB =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun targetABC =>
        (x.D.algebra (a + b + c)).mul (q targetAB targetABC)
          (Associator.leftDelta x a b c sourceAB sourceABC
            targetAB targetABC))) = q sourceAB sourceABC := by
  letI : Fact (SuperAlgebraLaws (x.D.algebra (a + b + c))) :=
    ⟨hx.D.algebra_laws (a + b + c)⟩
  rw [rawFinSum_eq_sum (x.D.algebra (a + b + c))]
  simp_rw [rawFinSum_eq_sum (x.D.algebra (a + b + c))]
  classical
  simp only [Associator.leftDelta, apply_ite,
    (hx.D.algebra_laws (a + b + c)).mul_one,
    mul_zero (x.D.algebra (a + b + c))
      (hx.D.algebra_laws (a + b + c))]
  rw [Finset.sum_eq_single sourceAB]
  · simp only [if_pos]
    rw [Finset.sum_eq_single sourceABC]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj]
      rfl
    · simp
  · intro i _ hi
    simp only [if_neg hi]
    change (∑ _ : x.C.Index (a + b) c, (0 :
      (x.D.algebra (a + b + c)).carrier)) = 0
    exact Finset.sum_const_zero
  · simp

/-- Matrix coefficients of the stored connector intertwine the ungraded
threefold left action. -/
theorem homCoefficient_leftRoute_naturality
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (hp : x.T.parity a b c = 0)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c))
    (u : (x.D.algebra a).carrier)
    (v : (x.D.algebra b).carrier)
    (w : (x.D.algebra c).carrier) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleAB =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleABC =>
        (x.D.algebra (a + b + c)).mul
          (Associator.homCoefficient x a b c middleAB middleABC
            targetBC targetABC)
          (RawDCT.leftRouteCoeff x.C a b c middleAB middleABC
            sourceAB sourceABC u v w))) =
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleBC =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleABC =>
        (x.D.algebra (a + b + c)).mul
          (RawDCT.rightRouteCoeff x.C a b c targetBC targetABC
            middleBC middleABC u v w)
          (Associator.homCoefficient x a b c sourceAB sourceABC
            middleBC middleABC))) := by
  let basis := x.T.leftOfCoord a b c
    (Associator.leftDelta x a b c sourceAB sourceABC)
  have hleft (middleAB : x.C.Index a b)
      (middleABC : x.C.Index (a + b) c) :
      x.T.leftToCoord a b c
          (x.T.leftRoute.leftPure a b c u v w basis)
          middleAB middleABC =
        RawDCT.leftRouteCoeff x.C a b c middleAB middleABC
          sourceAB sourceABC u v w := by
    rw [hx.T.left_toCoord_leftPure]
    dsimp only [basis]
    rw [hx.T.left_toCoord_ofCoord]
    exact leftDelta_weighted_sum x hx a b c sourceAB sourceABC
      (fun targetAB targetABC =>
        RawDCT.leftRouteCoeff x.C a b c middleAB middleABC
          targetAB targetABC u v w)
  have h := congrArg
    (fun n => x.T.rightToCoord a b c n targetBC targetABC)
    (hom_left_of_parity_zero x hx a b c hp u v w basis)
  rw [Associator.hom_toCoord_eq_matrix x hx,
    hx.T.right_toCoord_leftPure] at h
  simp_rw [hleft] at h
  simpa only [basis, Associator.homCoefficient] using h

/-! ## Nested tensor coefficients on homogeneous inputs -/

private theorem routeRowTwist_zeroParity_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (u : (dD.algebra a).carrier) :
    RawDCT.routeRowTwist dD a 0 u = u := by
  unfold RawDCT.routeRowTwist
  rw [RawDCT.shiftParitySign_zero, (hD.algebra_laws a).one_smul]
  exact (hD.algebra_laws a).component_complement 0 u

private theorem routeRowTwist_of_memGrade_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (p i : ZMod 2) (u : (dD.algebra a).carrier)
    (hu : (dD.algebra a).MemGrade i u) :
    RawDCT.routeRowTwist dD a p u =
      (dD.algebra a).smul (RawDCT.paritySign (p * i)) u := by
  simpa only [RawDCT.routeRowTwist] using
    RawDCT.routeRowTwist_of_memGrade
      (dD.algebra a) (hD.algebra_laws a) p i u hu

private theorem leftCoeff_smul_left
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b : ZMod 8)
    (target source : dC.Index a b) (r : ℝ)
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).smul r u) v =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source u v) := by
  simpa only [Tensor.coefficient, zero_add, zero_mul,
    RawDCT.shiftParitySign_zero,
    routeRowTwist_zeroParity_at dD hD,
    (hD.algebra_laws (a + b)).one_smul] using
    (Tensor.coefficient_smul_left dD hD dC hC a b
      0 0 0 source target r u v)

private theorem leftCoeff_smul_right
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b : ZMod 8)
    (target source : dC.Index a b) (r : ℝ)
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source u ((dD.algebra b).smul r v) =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source u v) := by
  simpa only [Tensor.coefficient, zero_add, zero_mul,
    RawDCT.shiftParitySign_zero,
    routeRowTwist_zeroParity_at dD hD,
    (hD.algebra_laws (a + b)).one_smul] using
    (Tensor.coefficient_smul_right dD hD dC hC a b
      0 0 0 source target r u v)

/-- The left-nested tensor coefficient is the raw left-route coefficient
times its complete endpoint-shift sign. -/
theorem nested_left_coefficient_of_memGrade
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b c : ZMod 8)
    (sa sa' sb sb' sc sc' i j k : ZMod 2)
    (sourceAB targetAB : dC.Index a b)
    (sourceABC targetABC : dC.Index (a + b) c)
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier)
    (w : (dD.algebra c).carrier)
    (hu : (dD.algebra a).MemGrade (i + sa + sa') u)
    (hv : (dD.algebra b).MemGrade (j + sb + sb') v)
    (hw : (dD.algebra c).MemGrade (k + sc + sc') w) :
    Tensor.coefficient dD dC (a + b) c
        (sa + sb + dC.rowParity a b sourceAB) sc sc'
        sourceABC targetABC
        (Tensor.coefficient dD dC a b sa sb sb'
          sourceAB targetAB u v) w =
      (dD.algebra (a + b + c)).smul
        (RawDCT.paritySign
          ((sa + sb + dC.rowParity a b sourceAB) * (sc + sc') +
            sc' *
              ((i + sa + sa') + (j + sb + sb') +
                dC.rowParity a b sourceAB +
                dC.rowParity a b targetAB) +
            sa * (sb + sb') + sb' * (i + sa + sa') +
            sa * (j + sb + sb') +
            (sa + sb + dC.rowParity a b sourceAB) *
              (k + sc + sc') +
            dC.rowParity a b sourceAB * (k + sc + sc')))
        (RawDCT.leftRouteCoeff dC a b c targetAB targetABC
          sourceAB sourceABC u v w) := by
  let U := i + sa + sa'
  let V := j + sb + sb'
  let W := k + sc + sc'
  let p := dC.rowParity a b sourceAB
  let q := dC.rowParity a b targetAB
  let S := sa + sb + p
  let inner := Tensor.coefficient dD dC a b sa sb sb'
    sourceAB targetAB u v
  have hinner : (dD.algebra (a + b)).MemGrade (U + V + p + q) inner := by
    exact Tensor.coefficient_memGrade dD hD dC hC a b sa sb sb'
      sourceAB targetAB U V u v hu hv
  unfold Tensor.coefficient
  change (dD.algebra (a + b + c)).smul
      (RawDCT.paritySign (S * (sc + sc')))
      (dC.leftCoeff (a + b) c targetABC sourceABC
        (RawDCT.routeRowTwist dD (a + b) sc' inner)
        (RawDCT.routeRowTwist dD c S w)) = _
  rw [routeRowTwist_of_memGrade_at dD hD (a + b)
      sc' (U + V + p + q) inner hinner,
    routeRowTwist_of_memGrade_at dD hD c S W w hw,
    leftCoeff_smul_left dD hD dC hC,
    leftCoeff_smul_right dD hD dC hC]
  dsimp only [inner]
  unfold Tensor.coefficient
  rw [routeRowTwist_of_memGrade_at dD hD a sb' U u hu,
    routeRowTwist_of_memGrade_at dD hD b sa V v hv,
    leftCoeff_smul_left dD hD dC hC,
    leftCoeff_smul_right dD hD dC hC,
    leftCoeff_smul_left dD hD dC hC]
  unfold RawDCT.leftRouteCoeff
  rw [routeRowTwist_of_memGrade_at dD hD c p W w hw]
  simp_rw [leftCoeff_smul_left dD hD dC hC,
    leftCoeff_smul_right dD hD dC hC]
  repeat' rw [← (hD.algebra_laws (a + b + c)).smul_assoc]
  congr 1
  repeat' rw [← RawDCT.shiftParitySign_add]
  congr 1
  dsimp only [U, V, W, p, q, S]
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide,
    show (3 : ZMod 2) = 1 by decide,
    show (4 : ZMod 2) = 0 by decide,
    show (5 : ZMod 2) = 1 by decide]
  ring

private theorem cast_smul (dD : DData) {s t : ZMod 8}
    (h : s = t) (r : ℝ) (u : (dD.algebra s).carrier) :
    cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) h)
        ((dD.algebra s).smul r u) =
      (dD.algebra t).smul r
        (cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) h) u) := by
  subst t
  rfl

private theorem routeCastAssoc_smul (dD : DData)
    (a b c : ZMod 8) (r : ℝ)
    (u : (dD.algebra (a + (b + c))).carrier) :
    RawDCT.routeCastAssoc dD a b c
        ((dD.algebra (a + (b + c))).smul r u) =
      (dD.algebra (a + b + c)).smul r
        (RawDCT.routeCastAssoc dD a b c u) := by
  exact cast_smul dD (_root_.add_assoc a b c).symm r u

/-- The right-nested tensor coefficient is the raw right-route coefficient
times the corresponding complete endpoint-shift sign. -/
theorem nested_right_coefficient_of_memGrade
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b c : ZMod 8)
    (sa sa' sb sb' sc sc' i j k : ZMod 2)
    (sourceBC targetBC : dC.Index b c)
    (sourceABC targetABC : dC.Index a (b + c))
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier)
    (w : (dD.algebra c).carrier)
    (hu : (dD.algebra a).MemGrade (i + sa + sa') u)
    (hv : (dD.algebra b).MemGrade (j + sb + sb') v)
    (hw : (dD.algebra c).MemGrade (k + sc + sc') w) :
    RawDCT.routeCastAssoc dD a b c
      (Tensor.coefficient dD dC a (b + c) sa
        (sb + sc + dC.rowParity b c sourceBC)
        (sb' + sc' + dC.rowParity b c targetBC)
        sourceABC targetABC u
        (Tensor.coefficient dD dC b c sb sc sc'
          sourceBC targetBC v w)) =
      (dD.algebra (a + b + c)).smul
        (RawDCT.paritySign
          (sa *
              ((sb + sc + dC.rowParity b c sourceBC) +
                (sb' + sc' + dC.rowParity b c targetBC)) +
            (sb' + sc' + dC.rowParity b c targetBC) *
              (i + sa + sa') +
            sa *
              ((j + sb + sb') + (k + sc + sc') +
                dC.rowParity b c sourceBC +
                dC.rowParity b c targetBC) +
            sb * (sc + sc') + sc' * (j + sb + sb') +
            sb * (k + sc + sc') +
            dC.rowParity b c targetBC * (i + sa + sa')))
        (RawDCT.rightRouteCoeff dC a b c targetBC targetABC
          sourceBC sourceABC u v w) := by
  let U := i + sa + sa'
  let V := j + sb + sb'
  let W := k + sc + sc'
  let r := dC.rowParity b c sourceBC
  let t := dC.rowParity b c targetBC
  let S := sb + sc + r
  let T := sb' + sc' + t
  let inner := Tensor.coefficient dD dC b c sb sc sc'
    sourceBC targetBC v w
  have hinner : (dD.algebra (b + c)).MemGrade (V + W + r + t) inner := by
    exact Tensor.coefficient_memGrade dD hD dC hC b c sb sc sc'
      sourceBC targetBC V W v w hv hw
  have hraw :
      Tensor.coefficient dD dC a (b + c) sa S T
          sourceABC targetABC u inner =
        (dD.algebra (a + (b + c))).smul
          (RawDCT.paritySign
            (sa * (S + T) + T * U + sa * (V + W + r + t) +
              sb * (sc + sc') + sc' * V + sb * W + t * U))
          (dC.leftCoeff a (b + c) targetABC sourceABC
            (RawDCT.routeRowTwist dD a t u)
            (dC.leftCoeff b c targetBC sourceBC v w)) := by
    unfold Tensor.coefficient
    rw [routeRowTwist_of_memGrade_at dD hD a T U u hu,
      routeRowTwist_of_memGrade_at dD hD (b + c)
        sa (V + W + r + t) inner hinner,
      leftCoeff_smul_left dD hD dC hC,
      leftCoeff_smul_right dD hD dC hC]
    dsimp only [inner]
    unfold Tensor.coefficient
    rw [routeRowTwist_of_memGrade_at dD hD b sc' V v hv,
      routeRowTwist_of_memGrade_at dD hD c sb W w hw,
      leftCoeff_smul_left dD hD dC hC,
      leftCoeff_smul_right dD hD dC hC,
      leftCoeff_smul_right dD hD dC hC]
    rw [routeRowTwist_of_memGrade_at dD hD a t U u hu]
    simp_rw [leftCoeff_smul_left dD hD dC hC,
      leftCoeff_smul_right dD hD dC hC]
    repeat' rw [← (hD.algebra_laws (a + (b + c))).smul_assoc]
    congr 1
    repeat' rw [← RawDCT.shiftParitySign_add]
    congr 1
    ring_nf
    rw [show (2 : ZMod 2) = 0 by decide]
    ring
  rw [hraw, routeCastAssoc_smul]
  unfold RawDCT.rightRouteCoeff
  congr 1

/-! ## The endpoint sign cancels the nesting defect -/

/-- The left and right nested tensor signs agree after multiplying the
target and source associator entries by their endpoint signs respectively. -/
theorem corrected_nested_sign_relation
    (sa sa' sb sb' sc sc' i j k p q r t : ZMod 2) :
    ((sa + sb + p) * (sc + sc') +
          sc' * ((i + sa + sa') + (j + sb + sb') + p + q) +
        sa * (sb + sb') + sb' * (i + sa + sa') +
      sa * (j + sb + sb') +
      (sa + sb + p) * (k + sc + sc') + p * (k + sc + sc')) +
        q * sc' =
    (sa * ((sb + sc + r) + (sb' + sc' + t)) +
          (sb' + sc' + t) * (i + sa + sa') +
        sa * ((j + sb + sb') + (k + sc + sc') + r + t) +
      sb * (sc + sc') + sc' * (j + sb + sb') +
      sb * (k + sc + sc') + t * (i + sa + sa')) +
        p * sc := by
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide,
    show (3 : ZMod 2) = 1 by decide,
    show (4 : ZMod 2) = 0 by decide]
  ring

/-! ## A common normalized sign and the signed connector identity -/

/-- The endpoint-normalized sign is independent of every intermediate
fusion row. -/
def commonExponent
    (sa sa' sb sb' sc sc' i j k p : ZMod 2) : ZMod 2 :=
  sa * ((sb + sc) + (sb' + sc')) +
      (sb' + sc') * (i + sa + sa') +
    sa * ((j + sb + sb') + (k + sc + sc')) +
  sb * (sc + sc') + sc' * (j + sb + sb') +
  sb * (k + sc + sc') + p * sc

private theorem left_endpoint_exponent_eq_common
    (sa sa' sb sb' sc sc' i j k p q : ZMod 2) :
    ((sa + sb + p) * (sc + sc') +
          sc' * ((i + sa + sa') + (j + sb + sb') + p + q) +
        sa * (sb + sb') + sb' * (i + sa + sa') +
      sa * (j + sb + sb') +
      (sa + sb + p) * (k + sc + sc') + p * (k + sc + sc')) +
        q * sc' = commonExponent sa sa' sb sb' sc sc' i j k p := by
  simpa only [commonExponent, zero_add, add_zero, zero_mul] using
    corrected_nested_sign_relation
      sa sa' sb sb' sc sc' i j k p q 0 0

private theorem right_endpoint_exponent_eq_common
    (sa sa' sb sb' sc sc' i j k p r t : ZMod 2) :
    (sa * ((sb + sc + r) + (sb' + sc' + t)) +
          (sb' + sc' + t) * (i + sa + sa') +
        sa * ((j + sb + sb') + (k + sc + sc') + r + t) +
      sb * (sc + sc') + sc' * (j + sb + sb') +
      sb * (k + sc + sc') + t * (i + sa + sa')) +
        p * sc = commonExponent sa sa' sb sb' sc sc' i j k p := by
  have h0 := left_endpoint_exponent_eq_common
    sa sa' sb sb' sc sc' i j k p 0
  have hrel := corrected_nested_sign_relation
    sa sa' sb sb' sc sc' i j k p 0 r t
  simpa only [zero_mul, add_zero] using hrel.symm.trans h0

@[implicit_reducible]
private def algebraModule (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) :
    letI := algebraAddCommGroup d h
    Module ℝ d.carrier := by
  letI := algebraAddCommGroup d h
  exact
    { smul := d.smul
      one_smul := h.one_smul
      mul_smul := h.smul_assoc
      smul_add := h.smul_add
      smul_zero := h.smul_zero
      add_smul := h.add_smul
      zero_smul := h.zero_smul }

private theorem rawFinSum_smul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {n : ℕ} (r : ℝ) (f : Fin n → d.carrier) :
    CData.rawFinSum d (fun i => d.smul r (f i)) =
      d.smul r (CData.rawFinSum d f) := by
  letI := algebraAddCommGroup d h
  letI := algebraModule d h
  unfold CData.rawFinSum
  change (List.ofFn (fun i => r • f i)).sum = r • (List.ofFn f).sum
  rw [List.sum_ofFn, List.sum_ofFn, Finset.smul_sum]

private theorem shiftedReal_parity_eq_zero (a b c : ZMod 8) :
    RealAssociator.shiftedReal.T.parity a b c = 0 := by
  simpa [RealAssociator.shiftedReal, rawParity] using
    realComputableShiftedRawDCT_parity_eq_zero
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      (Multiplicative.ofAdd c)

/-- After endpoint normalization, the nested tensor coefficients intertwine
the actual shifted real connector.  This is the fixed-atom coefficient core
of associator naturality. -/
theorem endpoint_homCoefficient_naturality_of_memGrade
    (a b c : ZMod 8)
    (sa sa' sb sb' sc sc' i j k : ZMod 2)
    (sourceAB : RealAssociator.shiftedReal.C.Index a b)
    (sourceABC : RealAssociator.shiftedReal.C.Index (a + b) c)
    (targetBC : RealAssociator.shiftedReal.C.Index b c)
    (targetABC : RealAssociator.shiftedReal.C.Index a (b + c))
    (u : (RealAssociator.shiftedReal.D.algebra a).carrier)
    (v : (RealAssociator.shiftedReal.D.algebra b).carrier)
    (w : (RealAssociator.shiftedReal.D.algebra c).carrier)
    (hu : (RealAssociator.shiftedReal.D.algebra a).MemGrade
      (i + sa + sa') u)
    (hv : (RealAssociator.shiftedReal.D.algebra b).MemGrade
      (j + sb + sb') v)
    (hw : (RealAssociator.shiftedReal.D.algebra c).MemGrade
      (k + sc + sc') w) :
    CData.rawFinSum
        (RealAssociator.shiftedReal.D.algebra (a + b + c))
        (fun middleAB =>
          CData.rawFinSum
            (RealAssociator.shiftedReal.D.algebra (a + b + c))
            (fun middleABC =>
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                ((RealAssociator.shiftedReal.D.algebra (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity a b middleAB *
                      sc'))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c middleAB middleABC targetBC targetABC))
                (Tensor.coefficient RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C (a + b) c
                  (sa + sb + RealAssociator.shiftedReal.C.rowParity
                    a b sourceAB) sc sc' sourceABC middleABC
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a b sa sb sb'
                    sourceAB middleAB u v) w))) =
      CData.rawFinSum
        (RealAssociator.shiftedReal.D.algebra (a + b + c))
        (fun middleBC =>
          CData.rawFinSum
            (RealAssociator.shiftedReal.D.algebra (a + b + c))
            (fun middleABC =>
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                (RawDCT.routeCastAssoc RealAssociator.shiftedReal.D a b c
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a (b + c) sa
                    (sb + sc + RealAssociator.shiftedReal.C.rowParity
                      b c middleBC)
                    (sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                      b c targetBC)
                    middleABC targetABC u
                    (Tensor.coefficient RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C b c sb sc sc'
                      middleBC targetBC v w)))
                ((RealAssociator.shiftedReal.D.algebra (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity a b sourceAB *
                      sc))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c sourceAB sourceABC middleBC middleABC)))) := by
  let x := RealAssociator.shiftedReal
  let A := x.D.algebra (a + b + c)
  let e := commonExponent sa sa' sb sb' sc sc' i j k
    (x.C.rowParity a b sourceAB)
  have hA := realComputableShiftedRawDCT.laws.D.algebra_laws (a + b + c)
  have hleft (middleAB : x.C.Index a b)
      (middleABC : x.C.Index (a + b) c) :
      A.mul
          (A.smul (RawDCT.paritySign
              (x.C.rowParity a b middleAB * sc'))
            (Associator.homCoefficient x a b c middleAB middleABC
              targetBC targetABC))
          (Tensor.coefficient x.D x.C (a + b) c
            (sa + sb + x.C.rowParity a b sourceAB) sc sc'
            sourceABC middleABC
            (Tensor.coefficient x.D x.C a b sa sb sb'
              sourceAB middleAB u v) w) =
        A.smul (RawDCT.paritySign e)
          (A.mul
            (Associator.homCoefficient x a b c middleAB middleABC
              targetBC targetABC)
            (RawDCT.leftRouteCoeff x.C a b c middleAB middleABC
              sourceAB sourceABC u v w)) := by
    rw [nested_left_coefficient_of_memGrade x.D
      realComputableShiftedRawDCT.laws.D x.C
      realComputableShiftedRawDCT.laws.C a b c
      sa sa' sb sb' sc sc' i j k sourceAB middleAB
      sourceABC middleABC u v w hu hv hw]
    rw [hA.smul_mul, hA.mul_smul, ← hA.smul_assoc,
      ← RawDCT.shiftParitySign_add]
    congr 2
    rw [add_comm]
    exact left_endpoint_exponent_eq_common
      sa sa' sb sb' sc sc' i j k
      (x.C.rowParity a b sourceAB) (x.C.rowParity a b middleAB)
  have hright (middleBC : x.C.Index b c)
      (middleABC : x.C.Index a (b + c)) :
      A.mul
          (RawDCT.routeCastAssoc x.D a b c
            (Tensor.coefficient x.D x.C a (b + c) sa
              (sb + sc + x.C.rowParity b c middleBC)
              (sb' + sc' + x.C.rowParity b c targetBC)
              middleABC targetABC u
              (Tensor.coefficient x.D x.C b c sb sc sc'
                middleBC targetBC v w)))
          (A.smul (RawDCT.paritySign
              (x.C.rowParity a b sourceAB * sc))
            (Associator.homCoefficient x a b c sourceAB sourceABC
              middleBC middleABC)) =
        A.smul (RawDCT.paritySign e)
          (A.mul
            (RawDCT.rightRouteCoeff x.C a b c targetBC targetABC
              middleBC middleABC u v w)
            (Associator.homCoefficient x a b c sourceAB sourceABC
              middleBC middleABC)) := by
    rw [nested_right_coefficient_of_memGrade x.D
      realComputableShiftedRawDCT.laws.D x.C
      realComputableShiftedRawDCT.laws.C a b c
      sa sa' sb sb' sc sc' i j k middleBC targetBC
      middleABC targetABC u v w hu hv hw]
    rw [hA.smul_mul, hA.mul_smul, ← hA.smul_assoc,
      ← RawDCT.shiftParitySign_add]
    congr 2
    exact right_endpoint_exponent_eq_common
      sa sa' sb sb' sc sc' i j k
      (x.C.rowParity a b sourceAB)
      (x.C.rowParity b c middleBC) (x.C.rowParity b c targetBC)
  dsimp only [x, A] at hleft hright
  simp_rw [hleft, hright]
  simp_rw [rawFinSum_smul
    (RealAssociator.shiftedReal.D.algebra (a + b + c))
    (realComputableShiftedRawDCT.laws.D.algebra_laws (a + b + c))]
  exact congrArg (A.smul (RawDCT.paritySign e))
    (homCoefficient_leftRoute_naturality x
      realComputableShiftedRawDCT.laws a b c
      (shiftedReal_parity_eq_zero a b c)
      sourceAB sourceABC targetBC targetABC u v w)

/-! ## Route-slot form of the normalized associator entries -/

@[implicit_reducible]
private def atomHomAddCommGroup (dD : DData) (hD : DLaws dD)
    (X Y : Atom) : AddCommGroup (AtomHom dD X Y) := by
  letI : Zero (AtomHom dD X Y) := ⟨AtomHom.zero dD X Y⟩
  letI : Add (AtomHom dD X Y) := ⟨AtomHom.add⟩
  letI : Neg (AtomHom dD X Y) := ⟨AtomHom.neg⟩
  letI : Sub (AtomHom dD X Y) :=
    ⟨fun f g => AtomHom.add f (AtomHom.neg g)⟩
  exact
    { add_assoc := AtomHom.add_assoc hD
      zero_add := AtomHom.zero_add hD
      add_zero := AtomHom.add_zero hD
      neg_add_cancel := AtomHom.neg_add hD
      add_comm := AtomHom.add_comm hD
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }

private instance atomHomAddCommGroupInstance {X Y : Atom} :
    AddCommGroup (AtomHom RealAssociator.shiftedReal.D X Y) :=
  atomHomAddCommGroup RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D X Y

private theorem atomHom_finSum_eq_sum {X Y : Atom} {n : ℕ}
    (f : Fin n → AtomHom RealAssociator.shiftedReal.D X Y) :
    AtomHom.finSum n f = ∑ i, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [AtomHom.finSum, ih, Fin.sum_univ_castSucc]
      rfl

/-- Reading a fixed endpoint coefficient commutes with a finite sum of
atomic morphisms.  This is the additive bridge from the reindexed matrix
entries back to the raw coefficient sums used by the connector law. -/
private theorem atomHom_sum_coeff {n : ℕ}
    {X Y : Atom} (hXY : X.label = Y.label)
    (f : Fin n → AtomHom RealAssociator.shiftedReal.D X Y) :
    (∑ i, f i).coeff hXY =
      CData.rawFinSum (RealAssociator.shiftedReal.D.algebra X.label)
        (fun i => (f i).coeff hXY) := by
  letI : Fact (SuperAlgebraLaws
      (RealAssociator.shiftedReal.D.algebra X.label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws X.label⟩
  rw [rawFinSum_eq_sum]
  let coeffHom :
      AtomHom RealAssociator.shiftedReal.D X Y →+
        (RealAssociator.shiftedReal.D.algebra X.label).carrier :=
    { toFun := fun q => q.coeff hXY
      map_zero' := AtomHom.coeff_zero hXY
      map_add' := fun p q => AtomHom.coeff_add p q hXY }
  exact _root_.map_sum coeffHom f Finset.univ

/-- A finite sum of zero atomic blocks is the zero block, independently of
the cardinality of the route-index type. -/
private theorem atomHom_sum_zero {I : Type} [Fintype I] {X Y : Atom} :
    (∑ _ : I, AtomHom.zero RealAssociator.shiftedReal.D X Y) =
      AtomHom.zero RealAssociator.shiftedReal.D X Y := by
  change (∑ _ : I, (0 : AtomHom RealAssociator.shiftedReal.D X Y)) = 0
  exact Finset.sum_const_zero

/-- Reindex both binders of a rectangular finite sum.  Keeping this as one
lemma prevents the second reindexing from depending on simplifier traversal
under the first sum. -/
private theorem sum_sum_comp
    {I I' J J' M : Type u} [Fintype I] [Fintype I']
    [Fintype J] [Fintype J'] [AddCommMonoid M]
    (eI : I ≃ I') (eJ : J ≃ J') (f : I' → J' → M) :
    (∑ i' : I', ∑ j' : J', f i' j') =
      ∑ i : I, ∑ j : J, f (eI i) (eJ j) := by
  rw [← eI.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eJ.sum_comp]

/- Transporting algebra expressions between equal endpoint labels is kept
in small proof-only lemmas, so the computational route data itself remains
free of equality witnesses. -/

private theorem cast_cast_eq {A B C : Type} (hAB : A = B) (hBC : B = C)
    (u : A) : cast hBC (cast hAB u) = cast (hAB.trans hBC) u := by
  subst B
  subst C
  rfl

private theorem cast_proof_irrel {A B : Sort u} (h h' : A = B) (x : A) :
    cast h x = cast h' x := by
  rw [Subsingleton.elim h h']

private theorem eq_cast_symm_of_cast_eq {A B : Type} (h : A = B)
    {x : A} {y : B} (hxy : cast h x = y) : x = cast h.symm y := by
  cases h
  exact hxy

private theorem cast_algebra_mul_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (u v : (dD.algebra a).carrier) :
    cast h ((dD.algebra a).mul u v) =
      (dD.algebra b).mul (cast h u) (cast h v) := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem cast_rawFinSum (dD : DData) {a b : ZMod 8}
    (h : a = b) {n : ℕ} (f : Fin n → (dD.algebra a).carrier) :
    cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h)
        (CData.rawFinSum (dD.algebra a) f) =
      CData.rawFinSum (dD.algebra b) (fun i =>
        cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h)
          (f i)) := by
  subst b
  rfl

private theorem rawFinSum_congr (d : SuperAlgebraData ℝ) {n : ℕ}
    {f g : Fin n → d.carrier} (h : ∀ i, f i = g i) :
    CData.rawFinSum d f = CData.rawFinSum d g := by
  exact congrArg (CData.rawFinSum d) (funext h)

/-- Once the two endpoint labels are fixed, a tensor matrix entry is
literally the executable binary coefficient with the target fusion row
transported to the source labels. -/
private theorem tensorEntry_coeff_of_label_eq
    {X X' Y Y' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (q : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y)
    (q' : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X' Y')
    (hA : (X.atom q.left).label = (X'.atom q'.left).label)
    (hB : (Y.atom q.right).label = (Y'.atom q'.right).label)
    (hQ : (Tensor.slotAtom RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y q).label =
        (Tensor.slotAtom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C X' Y' q').label) :
    (Tensor.entry RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C f g q q').coeff hQ =
      Tensor.coefficient RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C
        (X.atom q.left).label (Y.atom q.right).label
        (X.atom q.left).shift (Y.atom q.right).shift
        (Y'.atom q'.right).shift q.fusion
        (Associator.castIndex RealAssociator.shiftedReal
          hA.symm hB.symm q'.fusion)
        ((f q.left q'.left).coeff hA)
        ((g q.right q'.right).coeff hB) := by
  simp [Tensor.entry, hA, hB, Associator.castIndex]

private theorem castIndex_trans (x : RawDCTData)
    {a b a' b' a'' b'' : ZMod 8}
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (r : x.C.Index a b) :
    Associator.castIndex x ha' hb' (Associator.castIndex x ha hb r) =
      Associator.castIndex x (ha.trans ha') (hb.trans hb') r := by
  subst a'
  subst b'
  subst a''
  subst b''
  rfl

private theorem castIndex_proof_irrel (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha ha' : a = a') (hb hb' : b = b')
    (r : x.C.Index a b) :
    Associator.castIndex x ha hb r =
      Associator.castIndex x ha' hb' r := by
  subst a'
  subst b'
  rfl

/-- Transporting a fusion row to new endpoint labels and back is the
identity.  This is only type transport; it does not inspect the fusion
table. -/
@[simp] private theorem castIndex_cancel_symm (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    Associator.castIndex x ha.symm hb.symm
        (Associator.castIndex x ha hb r) = r := by
  subst a'
  subst b'
  rfl

/-- The opposite round trip for fusion-row label transport. -/
@[simp] private theorem castIndex_symm_cancel (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a' b') :
    Associator.castIndex x ha hb
        (Associator.castIndex x ha.symm hb.symm r) = r := by
  subst a'
  subst b'
  rfl

/-- Equality of the two endpoint labels induces a finite equivalence of
the corresponding fusion-row types. -/
private def castIndexEquiv (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b') :
    x.C.Index a b ≃ x.C.Index a' b' where
  toFun := Associator.castIndex x ha hb
  invFun := Associator.castIndex x ha.symm hb.symm
  left_inv := castIndex_cancel_symm x ha hb
  right_inv := castIndex_symm_cancel x ha hb

@[simp] private theorem castIndexEquiv_apply (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    castIndexEquiv x ha hb r = Associator.castIndex x ha hb r :=
  rfl

@[simp] private theorem rowParity_castIndex (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    x.C.rowParity a' b' (Associator.castIndex x ha hb r) =
      x.C.rowParity a b r := by
  subst a'
  subst b'
  rfl

/-- The normalized connector coefficient is invariant under simultaneous
transport of its three external labels and four fusion rows.  The proof is
pure equality elimination and reuses the executable connector coefficient;
it performs no table or coherence computation. -/
private theorem normalizedHomCoefficient_transport
    {a b c a' b' c' : ZMod 8}
    (ha : a = a') (hb : b = b') (hc : c = c') (s : ZMod 2)
    (ab : RealAssociator.shiftedReal.C.Index a b)
    (abc : RealAssociator.shiftedReal.C.Index (a + b) c)
    (bc : RealAssociator.shiftedReal.C.Index b c)
    (a_bc : RealAssociator.shiftedReal.C.Index a (b + c)) :
    cast
        (congrArg
          (fun t : ZMod 8 =>
            (RealAssociator.shiftedReal.D.algebra t).carrier)
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc)).symm
        ((RealAssociator.shiftedReal.D.algebra (a' + b' + c')).smul
          (RawDCT.paritySign
            (RealAssociator.shiftedReal.C.rowParity a' b'
              (Associator.castIndex RealAssociator.shiftedReal ha hb ab) * s))
          (Associator.homCoefficient RealAssociator.shiftedReal a' b' c'
            (Associator.castIndex RealAssociator.shiftedReal ha hb ab)
            (Associator.castIndex RealAssociator.shiftedReal
              (congrArg₂ (· + ·) ha hb) hc abc)
            (Associator.castIndex RealAssociator.shiftedReal hb hc bc)
            (Associator.castIndex RealAssociator.shiftedReal ha
              (congrArg₂ (· + ·) hb hc) a_bc))) =
      (RealAssociator.shiftedReal.D.algebra (a + b + c)).smul
        (RawDCT.paritySign
          (RealAssociator.shiftedReal.C.rowParity a b ab * s))
        (Associator.homCoefficient RealAssociator.shiftedReal a b c
          ab abc bc a_bc) := by
  subst a'
  subst b'
  subst c'
  rfl

private theorem tensorCoefficient_transport
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (s t t' : ZMod 2)
    (source target : RealAssociator.shiftedReal.C.Index a b)
    (u : (RealAssociator.shiftedReal.D.algebra a).carrier)
    (v : (RealAssociator.shiftedReal.D.algebra b).carrier) :
    cast
        (congrArg
          (fun z : ZMod 8 =>
            (RealAssociator.shiftedReal.D.algebra z).carrier)
          (congrArg₂ (· + ·) ha hb))
        (Tensor.coefficient RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C a b s t t' source target u v) =
      Tensor.coefficient RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C a' b' s t t'
        (Associator.castIndex RealAssociator.shiftedReal ha hb source)
        (Associator.castIndex RealAssociator.shiftedReal ha hb target)
        (cast (congrArg (fun z : ZMod 8 =>
          (RealAssociator.shiftedReal.D.algebra z).carrier) ha) u)
        (cast (congrArg (fun z : ZMod 8 =>
          (RealAssociator.shiftedReal.D.algebra z).carrier) hb) v) := by
  subst a'
  subst b'
  rfl

/-- On an explicit left route, the normalization exponent is literally the
inner binary-row parity times the third atom shift. -/
@[simp] theorem endpointSign_leftRouteSlot (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    RealAssociator.endpointSign X Y Z
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc) =
      RawDCT.paritySign
        (RealAssociator.shiftedReal.C.rowParity
          (X.atom i).label (Y.atom j).label ab * (Z.atom k).shift) := by
  unfold RealAssociator.endpointSign RealAssociator.leftInnerParity
  rw [RealAssociatorLaws.leftRouteSlot_inner,
    RealAssociatorLaws.leftRouteSlot_right]
  rfl

/-- The normalized route entry is the stored connector coefficient with
the endpoint scalar inserted before transport to the route label. -/
theorem realHomEntry_route_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    (RealAssociator.homEntry X Y Z
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)).coeff
        (RealAssociatorLaws.routeAssocLabelEq
          X Y Z i j k ab abc bc a_bc) =
      cast
        (congrArg
          (fun t : ZMod 8 =>
            (RealAssociator.shiftedReal.D.algebra t).carrier)
          (RealAssociatorLaws.leftRouteSlot_label
            X Y Z i j k ab abc).symm)
        ((RealAssociator.shiftedReal.D.algebra
            ((X.atom i).label + (Y.atom j).label + (Z.atom k).label)).smul
          (RawDCT.paritySign
            (RealAssociator.shiftedReal.C.rowParity
              (X.atom i).label (Y.atom j).label ab * (Z.atom k).shift))
          (Associator.homCoefficient RealAssociator.shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            ab abc bc a_bc)) := by
  rw [RealAssociator.homEntry, AtomHom.coeff_smul,
    endpointSign_leftRouteSlot,
    RealAssociatorLaws.realHomEntry_route_coeff]
  exact (cast_smul RealAssociator.shiftedReal.D
    (RealAssociatorLaws.leftRouteSlot_label
      X Y Z i j k ab abc).symm _ _).symm

/-- Incompatible first object positions give a zero normalized entry. -/
theorem realHomEntry_zero_of_left_ne (X Y Z : Obj)
    (qL : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z)
    (qR : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z))
    (h : ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get qL.left).left ≠ qR.left) :
    RealAssociator.homEntry X Y Z qL qR =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_left_ne X Y Z qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

/-- Incompatible middle object positions give a zero normalized entry. -/
theorem realHomEntry_zero_of_middle_ne (X Y Z : Obj)
    (qL : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z)
    (qR : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z))
    (h : ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get qL.left).right ≠
        ((Tensor.slots RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z).get qR.right).left) :
    RealAssociator.homEntry X Y Z qL qR =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_middle_ne X Y Z qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

/-- Incompatible third object positions give a zero normalized entry. -/
theorem realHomEntry_zero_of_right_ne (X Y Z : Obj)
    (qL : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z)
    (qR : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z))
    (h : qL.right ≠
        ((Tensor.slots RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z).get qR.right).right) :
    RealAssociator.homEntry X Y Z qL qR =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_right_ne X Y Z qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

/-! ## Reindexing the two naturality composites -/

/-- Canonical matrix position of an explicit left-associated route, stated
with the public concrete `shiftedReal` abbreviation of this data layer. -/
def leftRoutePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    Fin (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z).size :=
  RealAssociatorLaws.slotPosition RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y) Z
    (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)

/-- Canonical matrix position of an explicit right-associated route. -/
def rightRoutePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    Fin (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z)).size :=
  RealAssociatorLaws.slotPosition RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C X
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z)
    (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)

/-- The slot read at the canonical left-route matrix position.  Naming this
coercion keeps the `Obj.size = slots.length` reduction local. -/
def leftRouteAtPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z := by
  exact (Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z).get
        (leftRoutePosition X Y Z i j k ab abc)

@[simp] theorem leftRouteAtPosition_eq (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    leftRouteAtPosition X Y Z i j k ab abc =
      RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc := by
  unfold leftRouteAtPosition leftRoutePosition
  exact RealAssociatorLaws.get_slotPosition _ _ _ _ _

@[simp] theorem leftRouteAtPosition_firstPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
      (leftRouteAtPosition X Y Z i j k ab abc).left).left = i := by
  rw [leftRouteAtPosition_eq, RealAssociatorLaws.leftRouteSlot_inner]
  rfl

@[simp] theorem leftRouteAtPosition_middlePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
      (leftRouteAtPosition X Y Z i j k ab abc).left).right = j := by
  rw [leftRouteAtPosition_eq, RealAssociatorLaws.leftRouteSlot_inner]
  rfl

@[simp] theorem leftRouteAtPosition_thirdPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    (leftRouteAtPosition X Y Z i j k ab abc).right = k := by
  rw [leftRouteAtPosition_eq, RealAssociatorLaws.leftRouteSlot_right]

/-- The slot read at the canonical right-route matrix position. -/
def rightRouteAtPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z) := by
  exact (Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z)).get
        (rightRoutePosition X Y Z i j k bc a_bc)

@[simp] theorem rightRouteAtPosition_eq (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    rightRouteAtPosition X Y Z i j k bc a_bc =
      RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc := by
  unfold rightRouteAtPosition rightRoutePosition
  exact RealAssociatorLaws.get_slotPosition _ _ _ _ _

@[simp] theorem rightRouteAtPosition_firstPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    (rightRouteAtPosition X Y Z i j k bc a_bc).left = i := by
  rw [rightRouteAtPosition_eq, RealAssociatorLaws.rightRouteSlot_left]

@[simp] theorem rightRouteAtPosition_middlePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
      (rightRouteAtPosition X Y Z i j k bc a_bc).right).left = j := by
  rw [rightRouteAtPosition_eq, RealAssociatorLaws.rightRouteSlot_inner]
  rfl

@[simp] theorem rightRouteAtPosition_thirdPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
      (rightRouteAtPosition X Y Z i j k bc a_bc).right).right = k := by
  rw [rightRouteAtPosition_eq, RealAssociatorLaws.rightRouteSlot_inner]
  rfl

/-- Every left-associated matrix position is the canonical position of a
unique explicit three-object route.  Only existence is exposed because the
later naturality proof needs no computational choice of coordinates. -/
theorem exists_eq_leftRoutePosition (X Y Z : Obj)
    (p : Fin (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y) Z).size) :
    ∃ (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
      (ab : RealAssociator.shiftedReal.C.Index
        (X.atom i).label (Y.atom j).label)
      (abc : RealAssociator.shiftedReal.C.Index
        ((X.atom i).label + (Y.atom j).label) (Z.atom k).label),
      p = leftRoutePosition X Y Z i j k ab abc := by
  let q := (Tensor.slots RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y) Z).get p
  rcases RealAssociatorLaws.exists_eq_leftRouteSlot X Y Z q with
    ⟨i, j, k, ab, abc, hq⟩
  refine ⟨i, j, k, ab, abc, ?_⟩
  apply (RealAssociatorLaws.slotsEquiv RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y) Z).injective
  simpa only [RealAssociatorLaws.slotsEquiv_apply, q,
    leftRoutePosition, RealAssociatorLaws.get_slotPosition] using hq

/-- Every right-associated matrix position is likewise represented by one
explicit three-object route. -/
theorem exists_eq_rightRoutePosition (X Y Z : Obj)
    (p : Fin (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z)).size) :
    ∃ (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
      (bc : RealAssociator.shiftedReal.C.Index
        (Y.atom j).label (Z.atom k).label)
      (a_bc : RealAssociator.shiftedReal.C.Index
        (X.atom i).label ((Y.atom j).label + (Z.atom k).label)),
      p = rightRoutePosition X Y Z i j k bc a_bc := by
  let q := (Tensor.slots RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C X
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z)).get p
  rcases RealAssociatorLaws.exists_eq_rightRouteSlot X Y Z q with
    ⟨i, j, k, bc, a_bc, hq⟩
  refine ⟨i, j, k, bc, a_bc, ?_⟩
  apply (RealAssociatorLaws.slotsEquiv RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C X
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z)).injective
  simpa only [RealAssociatorLaws.slotsEquiv_apply, q,
    rightRoutePosition, RealAssociatorLaws.get_slotPosition] using hq

@[simp] private theorem leftRouteSlot_innerShift (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    ((Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).atom
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).left).shift =
      (X.atom i).shift + (Y.atom j).shift +
        RealAssociator.shiftedReal.C.rowParity
          (X.atom i).label (Y.atom j).label ab := by
  change (Tensor.slotAtom RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C X Y
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).left)).shift = _
  rw [RealAssociatorLaws.leftRouteSlot_inner]
  rfl

@[simp] private theorem rightRouteSlot_innerShift (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    ((Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).atom
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).right).shift =
      (Y.atom j).shift + (Z.atom k).shift +
        RealAssociator.shiftedReal.C.rowParity
          (Y.atom j).label (Z.atom k).label bc := by
  change (Tensor.slotAtom RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C Y Z
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).right)).shift = _
  rw [RealAssociatorLaws.rightRouteSlot_inner]
  rfl

/- The following projection lemmas keep the dependent packing equivalences
opaque while exposing only the three original object positions. -/

@[simp] theorem leftSlotPack_firstPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y ⟨i, j, ab⟩).label
      (Z.atom k).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
      (RealAssociatorLaws.leftSlotPack RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y Z
        ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C X Y from ⟨i, j, ab⟩), k, abc⟩).left).left = i := by
  rw [RealAssociatorLaws.leftSlotPack_inner]
  rfl

@[simp] theorem leftSlotPack_middlePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y ⟨i, j, ab⟩).label
      (Z.atom k).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
      (RealAssociatorLaws.leftSlotPack RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y Z
        ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C X Y from ⟨i, j, ab⟩), k, abc⟩).left).right = j := by
  rw [RealAssociatorLaws.leftSlotPack_inner]
  rfl

@[simp] theorem leftSlotPack_thirdPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (abc : RealAssociator.shiftedReal.C.Index
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y ⟨i, j, ab⟩).label
      (Z.atom k).label) :
    (RealAssociatorLaws.leftSlotPack RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y Z
      ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y from ⟨i, j, ab⟩), k, abc⟩).right = k := by
  rw [RealAssociatorLaws.leftSlotPack_right]

@[simp] theorem rightSlotPack_firstPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index (X.atom i).label
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z ⟨j, k, bc⟩).label) :
    (RealAssociatorLaws.rightSlotPack RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y Z
      ⟨i, (show Tensor.Slot RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z from ⟨j, k, bc⟩), a_bc⟩).left = i := by
  rw [RealAssociatorLaws.rightSlotPack_left]

@[simp] theorem rightSlotPack_middlePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index (X.atom i).label
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z ⟨j, k, bc⟩).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
      (RealAssociatorLaws.rightSlotPack RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y Z
        ⟨i, (show Tensor.Slot RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z from ⟨j, k, bc⟩), a_bc⟩).right).left = j := by
  rw [RealAssociatorLaws.rightSlotPack_inner]
  rfl

@[simp] theorem rightSlotPack_thirdPosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (a_bc : RealAssociator.shiftedReal.C.Index (X.atom i).label
      (Tensor.slotAtom RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z ⟨j, k, bc⟩).label) :
    ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
      (RealAssociatorLaws.rightSlotPack RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X Y Z
        ⟨i, (show Tensor.Slot RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z from ⟨j, k, bc⟩), a_bc⟩).right).right = k := by
  rw [RealAssociatorLaws.rightSlotPack_inner]
  rfl

/-- One matrix entry of the left naturality composite is exactly the sum
over the two intermediate left-route rows.  The three intermediate object
positions are forced by the support of the associator entry. -/
theorem leftComposite_entry_as_route_sum
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label)) :
    Hom.comp
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h)
        (RealAssociator.hom X' Y' Z')
        (leftRoutePosition X Y Z i j k
          sourceAB sourceABC)
        (rightRoutePosition X' Y' Z' i' j' k' targetBC targetABC) =
      ∑ middleAB : RealAssociator.shiftedReal.C.Index
          (X'.atom i').label (Y'.atom j').label,
        ∑ middleABC : RealAssociator.shiftedReal.C.Index
          ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label,
          AtomHom.comp
            (Tensor.entry RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C
              (Tensor.hom RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C f g) h
              (leftRouteAtPosition X Y Z i j k sourceAB sourceABC)
              (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
                middleAB middleABC))
            (RealAssociator.homEntry X' Y' Z'
              (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
                middleAB middleABC)
              (rightRouteAtPosition X' Y' Z' i' j' k'
                targetBC targetABC)) := by
  let qSource := leftRouteAtPosition X Y Z i j k sourceAB sourceABC
  let qTarget := rightRouteAtPosition X' Y' Z' i' j' k'
    targetBC targetABC
  change AtomHom.finSum
      (Tensor.slots RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C
        (Tensor.obj RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C X' Y') Z').length
      (fun m => AtomHom.comp
        (Tensor.entry RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h qSource
          ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C
            (Tensor.obj RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C X' Y') Z').get m))
        (RealAssociator.homEntry X' Y' Z'
          ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C
            (Tensor.obj RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C X' Y') Z').get m)
          qTarget)) = _
  rw [atomHom_finSum_eq_sum]
  let F := fun q : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X' Y') Z' =>
    AtomHom.comp
      (Tensor.entry RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f g) h qSource q)
      (RealAssociator.homEntry X' Y' Z' q qTarget)
  change (∑ m, F ((Tensor.slots RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X' Y') Z').get m)) = _
  rw [show (∑ m, F ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X' Y') Z').get m)) = ∑ q, F q by
    simpa only [RealAssociatorLaws.slotsEquiv_apply] using
      (RealAssociatorLaws.slotsEquiv RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C
        (Tensor.obj RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C X' Y') Z').sum_comp F]
  rw [RealAssociatorLaws.sum_leftSlotCoordinates]
  rw [RealAssociatorLaws.sum_slots]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single j']
    · apply Finset.sum_congr rfl
      intro middleAB _
      rw [Finset.sum_eq_single k']
      · let xy : Tensor.Slot RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C X' Y' := ⟨i', j', middleAB⟩
        change (∑ middleABC : RealAssociator.shiftedReal.C.Index
            ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label,
          F (RealAssociatorLaws.leftSlotPack
            RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
            X' Y' Z' ⟨xy, k', middleABC⟩)) = _
        have hpack (middleABC : RealAssociator.shiftedReal.C.Index
            ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label) :
            RealAssociatorLaws.leftSlotPack
                RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                X' Y' Z' ⟨xy, k', middleABC⟩ =
              RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
                middleAB middleABC := by
          simpa only [xy] using
            (RealAssociatorLaws.leftSlotPack_route X' Y' Z'
              i' j' k' middleAB middleABC)
        simp_rw [hpack]
        dsimp only [F, qSource, qTarget]
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro middleABC _
        dsimp only [F]
        rw [realHomEntry_zero_of_right_ne]
        · exact AtomHom.comp_zero realComputableShiftedRawDCT.laws.D _
        · intro heq
          apply hl
          calc
            l = (RealAssociatorLaws.leftSlotPack
                RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                X' Y' Z'
                ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X' Y' from
                    ⟨i', j', middleAB⟩), l, middleABC⟩).right :=
              (leftSlotPack_thirdPosition X' Y' Z'
                i' j' l middleAB middleABC).symm
            _ = ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C Y' Z').get qTarget.right).right := heq
            _ = k' := rightRouteAtPosition_thirdPosition X' Y' Z'
              i' j' k' targetBC targetABC
      · simp
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro middleAB _
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro middleABC _
      dsimp only [F]
      rw [realHomEntry_zero_of_middle_ne]
      · exact AtomHom.comp_zero realComputableShiftedRawDCT.laws.D _
      · intro heq
        apply hl
        calc
          l = ((Tensor.slots RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C X' Y').get
              (RealAssociatorLaws.leftSlotPack
                RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                X' Y' Z'
                ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X' Y' from
                    ⟨i', l, middleAB⟩), s, middleABC⟩).left).right :=
            (leftSlotPack_middlePosition X' Y' Z'
              i' l s middleAB middleABC).symm
          _ = ((Tensor.slots RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C Y' Z').get qTarget.right).left := heq
          _ = j' := rightRouteAtPosition_middlePosition X' Y' Z'
            i' j' k' targetBC targetABC
    · simp
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro middleAB _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro middleABC _
    dsimp only [F]
    rw [realHomEntry_zero_of_left_ne]
    · exact AtomHom.comp_zero realComputableShiftedRawDCT.laws.D _
    · intro heq
      apply hl
      calc
        l = ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C X' Y').get
            (RealAssociatorLaws.leftSlotPack
              RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
              X' Y' Z'
              ⟨(show Tensor.Slot RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C X' Y' from
                  ⟨l, r, middleAB⟩), s, middleABC⟩).left).left :=
          (leftSlotPack_firstPosition X' Y' Z'
            l r s middleAB middleABC).symm
        _ = qTarget.left := heq
        _ = i' := rightRouteAtPosition_firstPosition X' Y' Z'
          i' j' k' targetBC targetABC
  · simp

/-- One matrix entry of the right naturality composite is exactly the sum
over the two intermediate right-route rows.  Here the associator support
forces the three source object positions. -/
theorem rightComposite_entry_as_route_sum
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label)) :
    Hom.comp (RealAssociator.hom X Y Z)
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h))
        (leftRoutePosition X Y Z i j k sourceAB sourceABC)
        (rightRoutePosition X' Y' Z' i' j' k' targetBC targetABC) =
      ∑ middleBC : RealAssociator.shiftedReal.C.Index
          (Y.atom j).label (Z.atom k).label,
        ∑ middleABC : RealAssociator.shiftedReal.C.Index
          (X.atom i).label ((Y.atom j).label + (Z.atom k).label),
          AtomHom.comp
            (RealAssociator.homEntry X Y Z
              (leftRouteAtPosition X Y Z i j k sourceAB sourceABC)
              (RealAssociatorLaws.rightRouteSlot X Y Z i j k
                middleBC middleABC))
            (Tensor.entry RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C f
              (Tensor.hom RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C g h)
              (RealAssociatorLaws.rightRouteSlot X Y Z i j k
                middleBC middleABC)
              (rightRouteAtPosition X' Y' Z' i' j' k'
                targetBC targetABC)) := by
  let qSource := leftRouteAtPosition X Y Z i j k sourceAB sourceABC
  let qTarget := rightRouteAtPosition X' Y' Z' i' j' k'
    targetBC targetABC
  change AtomHom.finSum
      (Tensor.slots RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X
        (Tensor.obj RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z)).length
      (fun m => AtomHom.comp
        (RealAssociator.homEntry X Y Z qSource
          ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C X
            (Tensor.obj RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C Y Z)).get m))
        (Tensor.entry RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h)
          ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C X
            (Tensor.obj RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C Y Z)).get m)
          qTarget)) = _
  rw [atomHom_finSum_eq_sum]
  let F := fun q : Tensor.Slot RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z) =>
    AtomHom.comp (RealAssociator.homEntry X Y Z qSource q)
      (Tensor.entry RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C f
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C g h) q qTarget)
  change (∑ m, F ((Tensor.slots RealAssociator.shiftedReal.D
    RealAssociator.shiftedReal.C X
    (Tensor.obj RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z)).get m)) = _
  rw [show (∑ m, F ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X
      (Tensor.obj RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C Y Z)).get m)) = ∑ q, F q by
    simpa only [RealAssociatorLaws.slotsEquiv_apply] using
      (RealAssociatorLaws.slotsEquiv RealAssociator.shiftedReal.D
        RealAssociator.shiftedReal.C X
        (Tensor.obj RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C Y Z)).sum_comp F]
  rw [RealAssociatorLaws.sum_rightSlotCoordinates]
  rw [Finset.sum_eq_single i]
  · rw [RealAssociatorLaws.sum_slots]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · apply Finset.sum_congr rfl
        intro middleBC _
        let yz : Tensor.Slot RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C Y Z := ⟨j, k, middleBC⟩
        change (∑ middleABC : RealAssociator.shiftedReal.C.Index
            (X.atom i).label ((Y.atom j).label + (Z.atom k).label),
          F (RealAssociatorLaws.rightSlotPack
            RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
            X Y Z ⟨i, yz, middleABC⟩)) = _
        have hpack (middleABC : RealAssociator.shiftedReal.C.Index
            (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
            RealAssociatorLaws.rightSlotPack
                RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                X Y Z ⟨i, yz, middleABC⟩ =
              RealAssociatorLaws.rightRouteSlot X Y Z i j k
                middleBC middleABC := by
          simpa only [yz] using
            (RealAssociatorLaws.rightSlotPack_route X Y Z
              i j k middleBC middleABC)
        simp_rw [hpack]
        dsimp only [F, qSource, qTarget]
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro middleBC _
        apply Finset.sum_eq_zero
        intro middleABC _
        dsimp only [F]
        rw [realHomEntry_zero_of_right_ne]
        · exact AtomHom.zero_comp realComputableShiftedRawDCT.laws.D _
        · intro heq
          apply hl
          calc
            l = ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C Y Z).get
                (RealAssociatorLaws.rightSlotPack
                  RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                  X Y Z
                  ⟨i, (show Tensor.Slot RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C Y Z from
                      ⟨j, l, middleBC⟩), middleABC⟩).right).right :=
              (rightSlotPack_thirdPosition X Y Z
                i j l middleBC middleABC).symm
            _ = qSource.right := heq.symm
            _ = k := leftRouteAtPosition_thirdPosition X Y Z
              i j k sourceAB sourceABC
      · simp
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro middleBC _
      apply Finset.sum_eq_zero
      intro middleABC _
      dsimp only [F]
      rw [realHomEntry_zero_of_middle_ne]
      · exact AtomHom.zero_comp realComputableShiftedRawDCT.laws.D _
      · intro heq
        apply hl
        calc
          l = ((Tensor.slots RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C Y Z).get
              (RealAssociatorLaws.rightSlotPack
                RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
                X Y Z
                ⟨i, (show Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y Z from
                    ⟨l, s, middleBC⟩), middleABC⟩).right).left :=
            (rightSlotPack_middlePosition X Y Z
              i l s middleBC middleABC).symm
          _ = ((Tensor.slots RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C X Y).get qSource.left).right := heq.symm
          _ = j := leftRouteAtPosition_middlePosition X Y Z
            i j k sourceAB sourceABC
    · simp
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro yz _
    apply Finset.sum_eq_zero
    intro middleABC _
    dsimp only [F]
    rw [realHomEntry_zero_of_left_ne]
    · exact AtomHom.zero_comp realComputableShiftedRawDCT.laws.D _
    · intro heq
      apply hl
      calc
        l = (RealAssociatorLaws.rightSlotPack
            RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
            X Y Z ⟨l, yz, middleABC⟩).left :=
          (RealAssociatorLaws.rightSlotPack_left
            RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
            X Y Z ⟨l, yz, middleABC⟩).symm
        _ = ((Tensor.slots RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C X Y).get qSource.left).left := heq.symm
        _ = i := leftRouteAtPosition_firstPosition X Y Z
          i j k sourceAB sourceABC
  · simp

/-! ## Vanishing of nested tensor entries across incompatible labels -/

private theorem leftNestedEntry_zero_of_first_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label (Y'.atom j').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label)
    (hi : (X.atom i).label ≠ (X'.atom i').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f g) h
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k
          sourceAB sourceABC)
        (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
          targetAB targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold Tensor.hom
  apply Tensor.entry_of_left_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  apply AtomHom.eq_of_label_ne
  have hSource := congrArg (fun q => q.left)
    (RealAssociatorLaws.leftRouteSlot_inner X Y Z i j k
      sourceAB sourceABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k
          sourceAB sourceABC).left).left = i at hSource
  have hTarget := congrArg (fun q => q.left)
    (RealAssociatorLaws.leftRouteSlot_inner X' Y' Z' i' j' k'
      targetAB targetABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X' Y').get
        (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
          targetAB targetABC).left).left = i' at hTarget
  simpa only [hSource, hTarget] using hi

private theorem leftNestedEntry_zero_of_middle_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label (Y'.atom j').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label)
    (hj : (Y.atom j).label ≠ (Y'.atom j').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f g) h
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k
          sourceAB sourceABC)
        (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
          targetAB targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold Tensor.hom
  apply Tensor.entry_of_right_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  apply AtomHom.eq_of_label_ne
  have hSource := congrArg (fun q => q.right)
    (RealAssociatorLaws.leftRouteSlot_inner X Y Z i j k
      sourceAB sourceABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X Y).get
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k
          sourceAB sourceABC).left).right = j at hSource
  have hTarget := congrArg (fun q => q.right)
    (RealAssociatorLaws.leftRouteSlot_inner X' Y' Z' i' j' k'
      targetAB targetABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C X' Y').get
        (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
          targetAB targetABC).left).right = j' at hTarget
  simpa only [hSource, hTarget] using hj

private theorem leftNestedEntry_zero_of_third_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label (Y'.atom j').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label)
    (hk : (Z.atom k).label ≠ (Z'.atom k').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f g) h
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k
          sourceAB sourceABC)
        (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
          targetAB targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  simpa only [RealAssociatorLaws.leftRouteSlot_right] using
    (AtomHom.eq_of_label_ne hk (h k k')
      (AtomHom.zero RealAssociator.shiftedReal.D _ _))

private theorem rightNestedEntry_zero_of_first_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceBC : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label))
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label))
    (hi : (X.atom i).label ≠ (X'.atom i').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        f (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C g h)
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k
          sourceBC sourceABC)
        (RealAssociatorLaws.rightRouteSlot X' Y' Z' i' j' k'
          targetBC targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  simpa only [RealAssociatorLaws.rightRouteSlot_left] using
    (AtomHom.eq_of_label_ne hi (f i i')
      (AtomHom.zero RealAssociator.shiftedReal.D _ _))

private theorem rightNestedEntry_zero_of_middle_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceBC : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label))
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label))
    (hj : (Y.atom j).label ≠ (Y'.atom j').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        f (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C g h)
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k
          sourceBC sourceABC)
        (RealAssociatorLaws.rightRouteSlot X' Y' Z' i' j' k'
          targetBC targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold Tensor.hom
  apply Tensor.entry_of_left_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  apply AtomHom.eq_of_label_ne
  have hSource := congrArg (fun q => q.left)
    (RealAssociatorLaws.rightRouteSlot_inner X Y Z i j k
      sourceBC sourceABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k
          sourceBC sourceABC).right).left = j at hSource
  have hTarget := congrArg (fun q => q.left)
    (RealAssociatorLaws.rightRouteSlot_inner X' Y' Z' i' j' k'
      targetBC targetABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y' Z').get
        (RealAssociatorLaws.rightRouteSlot X' Y' Z' i' j' k'
          targetBC targetABC).right).left = j' at hTarget
  simpa only [hSource, hTarget] using hj

private theorem rightNestedEntry_zero_of_third_label_ne
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceBC : RealAssociator.shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label))
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label))
    (hk : (Z.atom k).label ≠ (Z'.atom k').label) :
    Tensor.entry RealAssociator.shiftedReal.D RealAssociator.shiftedReal.C
        f (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C g h)
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k
          sourceBC sourceABC)
        (RealAssociatorLaws.rightRouteSlot X' Y' Z' i' j' k'
          targetBC targetABC) =
      AtomHom.zero RealAssociator.shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold Tensor.hom
  apply Tensor.entry_of_right_eq_zero RealAssociator.shiftedReal.D
    realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  apply AtomHom.eq_of_label_ne
  have hSource := congrArg (fun q => q.right)
    (RealAssociatorLaws.rightRouteSlot_inner X Y Z i j k
      sourceBC sourceABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y Z).get
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k
          sourceBC sourceABC).right).right = k at hSource
  have hTarget := congrArg (fun q => q.right)
    (RealAssociatorLaws.rightRouteSlot_inner X' Y' Z' i' j' k'
      targetBC targetABC)
  change ((Tensor.slots RealAssociator.shiftedReal.D
      RealAssociator.shiftedReal.C Y' Z').get
        (RealAssociatorLaws.rightRouteSlot X' Y' Z' i' j' k'
          targetBC targetABC).right).right = k' at hTarget
  simpa only [hSource, hTarget] using hk

/-! ## Homogeneous equality on one fixed source and target route -/

set_option maxHeartbeats 2000000
/-- On homogeneous input morphisms, the two explicit route sums agree.
The proof first removes the label-incompatible blocks, then identifies the
remaining coefficient sum with the normalized raw connector identity. -/
theorem routeSum_naturality_of_memGrade
    {X X' Y Y' Z Z' : Obj} {pf pg ph : ZMod 2}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (hf : Hom.MemGrade pf f) (hg : Hom.MemGrade pg g)
    (hh : Hom.MemGrade ph h)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X'.size) (j' : Fin Y'.size) (k' : Fin Z'.size)
    (sourceAB : RealAssociator.shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (sourceABC : RealAssociator.shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetBC : RealAssociator.shiftedReal.C.Index
      (Y'.atom j').label (Z'.atom k').label)
    (targetABC : RealAssociator.shiftedReal.C.Index
      (X'.atom i').label ((Y'.atom j').label + (Z'.atom k').label)) :
    (∑ middleAB : RealAssociator.shiftedReal.C.Index
        (X'.atom i').label (Y'.atom j').label,
      ∑ middleABC : RealAssociator.shiftedReal.C.Index
        ((X'.atom i').label + (Y'.atom j').label) (Z'.atom k').label,
        AtomHom.comp
          (Tensor.entry RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C
            (Tensor.hom RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C f g) h
            (leftRouteAtPosition X Y Z i j k sourceAB sourceABC)
            (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
              middleAB middleABC))
          (RealAssociator.homEntry X' Y' Z'
            (RealAssociatorLaws.leftRouteSlot X' Y' Z' i' j' k'
              middleAB middleABC)
            (rightRouteAtPosition X' Y' Z' i' j' k'
              targetBC targetABC))) =
      ∑ middleBC : RealAssociator.shiftedReal.C.Index
        (Y.atom j).label (Z.atom k).label,
      ∑ middleABC : RealAssociator.shiftedReal.C.Index
        (X.atom i).label ((Y.atom j).label + (Z.atom k).label),
        AtomHom.comp
          (RealAssociator.homEntry X Y Z
            (leftRouteAtPosition X Y Z i j k sourceAB sourceABC)
            (RealAssociatorLaws.rightRouteSlot X Y Z i j k
              middleBC middleABC))
          (Tensor.entry RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f
            (Tensor.hom RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C g h)
            (RealAssociatorLaws.rightRouteSlot X Y Z i j k
              middleBC middleABC)
            (rightRouteAtPosition X' Y' Z' i' j' k'
              targetBC targetABC)) := by
  rw [leftRouteAtPosition_eq, rightRouteAtPosition_eq]
  by_cases hA : (X.atom i).label = (X'.atom i').label
  · by_cases hB : (Y.atom j).label = (Y'.atom j').label
    · by_cases hC : (Z.atom k).label = (Z'.atom k').label
      · let a := (X.atom i).label
        let b := (Y.atom j).label
        let c := (Z.atom k).label
        let a' := (X'.atom i').label
        let b' := (Y'.atom j').label
        let c' := (Z'.atom k').label
        let sa := (X.atom i).shift
        let sb := (Y.atom j).shift
        let sc := (Z.atom k).shift
        let sa' := (X'.atom i').shift
        let sb' := (Y'.atom j').shift
        let sc' := (Z'.atom k').shift
        let hAB : a + b = a' + b' := congrArg₂ (· + ·) hA hB
        let hBC : b + c = b' + c' := congrArg₂ (· + ·) hB hC
        let hABC : a + b + c = a' + b' + c' :=
          congrArg₂ (· + ·) hAB hC
        let hA_BC : a + (b + c) = a' + (b' + c') :=
          congrArg₂ (· + ·) hA hBC
        let targetBC₀ := Associator.castIndex RealAssociator.shiftedReal
          hB.symm hC.symm targetBC
        let targetABC₀ := Associator.castIndex RealAssociator.shiftedReal
          hA.symm hBC.symm targetABC
        have htBC : Associator.castIndex RealAssociator.shiftedReal
            hB hC targetBC₀ = targetBC :=
          castIndex_symm_cancel RealAssociator.shiftedReal hB hC targetBC
        have htABC : Associator.castIndex RealAssociator.shiftedReal
            hA hBC targetABC₀ = targetABC :=
          castIndex_symm_cancel RealAssociator.shiftedReal hA hBC targetABC
        let u := (f i i').coeff hA
        let v := (g j j').coeff hB
        let w := (h k k').coeff hC
        have hu : (RealAssociator.shiftedReal.D.algebra a).MemGrade
            (pf + sa + sa') u := by
          simpa only [a, sa, sa', u] using
            hf i i' hA
        have hv : (RealAssociator.shiftedReal.D.algebra b).MemGrade
            (pg + sb + sb') v := by
          simpa only [b, sb, sb', v] using
            hg j j' hB
        have hw : (RealAssociator.shiftedReal.D.algebra c).MemGrade
            (ph + sc + sc') w := by
          simpa only [c, sc, sc', w] using
            hh k k' hC
        rw [← htBC, ← htABC]
        let eAB := castIndexEquiv RealAssociator.shiftedReal hA hB
        let eABC := castIndexEquiv RealAssociator.shiftedReal hAB hC
        rw [sum_sum_comp eAB eABC]
        apply AtomHom.ext
        intro hEnd
        let F := fun t : ZMod 8 =>
          (RealAssociator.shiftedReal.D.algebra t).carrier
        let qLS := RealAssociatorLaws.leftRouteSlot X Y Z
          i j k sourceAB sourceABC
        let qRT := RealAssociatorLaws.rightRouteSlot X' Y' Z'
          i' j' k'
          (Associator.castIndex RealAssociator.shiftedReal
            hB hC targetBC₀)
          (Associator.castIndex RealAssociator.shiftedReal
            hA hBC targetABC₀)
        let hSL := RealAssociatorLaws.leftRouteSlot_label X Y Z
          i j k sourceAB sourceABC
        have hleftTerm
            (middleAB : RealAssociator.shiftedReal.C.Index a b)
            (middleABC : RealAssociator.shiftedReal.C.Index (a + b) c) :
            let qLM := RealAssociatorLaws.leftRouteSlot X' Y' Z'
              i' j' k'
              (Associator.castIndex RealAssociator.shiftedReal
                hA hB middleAB)
              (Associator.castIndex RealAssociator.shiftedReal
                hAB hC middleABC)
            let hML := RealAssociatorLaws.leftRouteSlot_label X' Y' Z'
              i' j' k'
              (Associator.castIndex RealAssociator.shiftedReal
                hA hB middleAB)
              (Associator.castIndex RealAssociator.shiftedReal
                hAB hC middleABC)
            let hLL := hSL.trans (hABC.trans hML.symm)
            let hAT := RealAssociatorLaws.routeAssocLabelEq X' Y' Z'
              i' j' k'
              (Associator.castIndex RealAssociator.shiftedReal
                hA hB middleAB)
              (Associator.castIndex RealAssociator.shiftedReal
                hAB hC middleABC)
              (Associator.castIndex RealAssociator.shiftedReal
                hB hC targetBC₀)
              (Associator.castIndex RealAssociator.shiftedReal
                hA hBC targetABC₀)
            cast (congrArg F hSL)
                ((AtomHom.comp
                  (Tensor.entry RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C
                    (Tensor.hom RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C f g) h qLS qLM)
                  (RealAssociator.homEntry X' Y' Z' qLM qRT)).coeff hEnd) =
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                ((RealAssociator.shiftedReal.D.algebra (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity a b middleAB *
                      sc'))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c middleAB middleABC targetBC₀ targetABC₀))
                (Tensor.coefficient RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C (a + b) c
                  (sa + sb + RealAssociator.shiftedReal.C.rowParity
                    a b sourceAB) sc sc' sourceABC middleABC
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a b sa sb sb'
                    sourceAB middleAB u v) w) := by
          dsimp only
          let qLM := RealAssociatorLaws.leftRouteSlot X' Y' Z'
            i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hA hB middleAB)
            (Associator.castIndex RealAssociator.shiftedReal
              hAB hC middleABC)
          let hML := RealAssociatorLaws.leftRouteSlot_label X' Y' Z'
            i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hA hB middleAB)
            (Associator.castIndex RealAssociator.shiftedReal
              hAB hC middleABC)
          let hLL := hSL.trans (hABC.trans hML.symm)
          let hAT := RealAssociatorLaws.routeAssocLabelEq X' Y' Z'
            i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hA hB middleAB)
            (Associator.castIndex RealAssociator.shiftedReal
              hAB hC middleABC)
            (Associator.castIndex RealAssociator.shiftedReal
              hB hC targetBC₀)
            (Associator.castIndex RealAssociator.shiftedReal
              hA hBC targetABC₀)
          let hInnerS := RealAssociatorLaws.leftRouteSlot_innerLabel
            X Y Z i j k sourceAB sourceABC
          let hInnerM := RealAssociatorLaws.leftRouteSlot_innerLabel
            X' Y' Z' i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hA hB middleAB)
            (Associator.castIndex RealAssociator.shiftedReal
              hAB hC middleABC)
          let hInner := hInnerS.trans (hAB.trans hInnerM.symm)
          have hInnerCoeff :
              cast (congrArg F hInnerS)
                  ((Tensor.hom RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C f g
                    qLS.left qLM.left).coeff hInner) =
                Tensor.coefficient RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C a b sa sb sb'
                  sourceAB middleAB u v := by
            have haux
                (qS : Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X Y)
                (qM : Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X' Y')
                (hqS : qS = ⟨i, j, sourceAB⟩)
                (hqM : qM = ⟨i', j',
                  Associator.castIndex RealAssociator.shiftedReal
                    hA hB middleAB⟩)
                (hQS : (Tensor.slotAtom RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X Y qS).label = a + b)
                (hSM : (Tensor.slotAtom RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X Y qS).label =
                    (Tensor.slotAtom RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C X' Y' qM).label) :
                cast (congrArg F hQS)
                    ((Tensor.entry RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C f g qS qM).coeff hSM) =
                  Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a b sa sb sb'
                    sourceAB middleAB u v := by
              subst qS
              subst qM
              rw [tensorEntry_coeff_of_label_eq f g
                ⟨i, j, sourceAB⟩
                ⟨i', j', Associator.castIndex
                  RealAssociator.shiftedReal hA hB middleAB⟩
                hA hB hSM]
              simp only [a, b, sa, sb, sb',
                Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion,
                Tensor.slotAtom, u, v, castIndex_cancel_symm]
              have hProof : hQS = rfl := Subsingleton.elim _ _
              cases hProof
              rfl
            have hqS :
                (Tensor.slots RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X Y).get qLS.left =
                    ⟨i, j, sourceAB⟩ := by
              simpa only [qLS] using
                RealAssociatorLaws.leftRouteSlot_inner
                  X Y Z i j k sourceAB sourceABC
            have hqM :
                (Tensor.slots RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C X' Y').get qLM.left =
                    ⟨i', j',
                      Associator.castIndex RealAssociator.shiftedReal
                        hA hB middleAB⟩ := by
              simpa only [qLM] using
                RealAssociatorLaws.leftRouteSlot_inner X' Y' Z'
                  i' j' k'
                  (Associator.castIndex RealAssociator.shiftedReal
                    hA hB middleAB)
                  (Associator.castIndex RealAssociator.shiftedReal
                    hAB hC middleABC)
            exact haux
              ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C X Y).get qLS.left)
              ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C X' Y').get qLM.left)
              hqS hqM hInnerS hInner
          have hRightS : (Z.atom qLS.right).label = c := by
            simpa only [qLS, c] using congrArg
              (fun n => (Z.atom n).label)
              (RealAssociatorLaws.leftRouteSlot_right
                X Y Z i j k sourceAB sourceABC)
          have hRightM : (Z'.atom qLM.right).label = c' := by
            simpa only [qLM, c'] using congrArg
              (fun n => (Z'.atom n).label)
              (RealAssociatorLaws.leftRouteSlot_right X' Y' Z'
                i' j' k'
                (Associator.castIndex RealAssociator.shiftedReal
                  hA hB middleAB)
                (Associator.castIndex RealAssociator.shiftedReal
                  hAB hC middleABC))
          let hRightSM := hRightS.trans (hC.trans hRightM.symm)
          have hout := tensorEntry_coeff_of_label_eq
            (Tensor.hom RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C f g) h qLS qLM
            hInner hRightSM hLL
          have hout' :=
            (congrArg (fun z => cast (congrArg F hSL) z) hout).trans
              ((cast_proof_irrel
                (congrArg F hSL)
                (congrArg F
                  (congrArg₂ (· + ·) hInnerS hRightS)) _).trans
                (tensorCoefficient_transport hInnerS hRightS
                  _ _ _ _ _ _ _))
          have hOuterS :
              Associator.castIndex RealAssociator.shiftedReal
                  hInnerS hRightS qLS.fusion = sourceABC := by
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hInnerS rfl qLS.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = sourceABC := by
                simpa only [qLS, hInnerS] using
                  RealAssociatorLaws.leftRouteSlot_outerRow
                    X Y Z i j k sourceAB sourceABC
          have hOuterM :
              Associator.castIndex RealAssociator.shiftedReal
                  hInnerM hRightM qLM.fusion =
                Associator.castIndex RealAssociator.shiftedReal
                  hAB hC middleABC := by
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hInnerM rfl qLM.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = _ := by
                simpa only [qLM, hInnerM] using
                  RealAssociatorLaws.leftRouteSlot_outerRow X' Y' Z'
                    i' j' k'
                    (Associator.castIndex RealAssociator.shiftedReal
                      hA hB middleAB)
                    (Associator.castIndex RealAssociator.shiftedReal
                      hAB hC middleABC)
          have hTargetOuter :
              Associator.castIndex RealAssociator.shiftedReal
                  hInnerS hRightS
                  (Associator.castIndex RealAssociator.shiftedReal
                    hInner.symm hRightSM.symm qLM.fusion) = middleABC := by
            rw [castIndex_trans]
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    (hInnerM.trans hAB.symm)
                    (hRightM.trans hC.symm) qLM.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hAB.symm hC.symm
                    (Associator.castIndex RealAssociator.shiftedReal
                      hInnerM hRightM qLM.fusion) :=
                (castIndex_trans RealAssociator.shiftedReal
                  hInnerM hRightM hAB.symm hC.symm qLM.fusion).symm
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hAB.symm hC.symm
                    (Associator.castIndex RealAssociator.shiftedReal
                      hAB hC middleABC) := congrArg _ hOuterM
              _ = middleABC :=
                castIndex_cancel_symm RealAssociator.shiftedReal
                  hAB hC middleABC
          have hRightCoeff :
              cast (congrArg F hRightS)
                  ((h qLS.right qLM.right).coeff hRightSM) = w := by
            simp only [qLS, qLM,
              RealAssociatorLaws.leftRouteSlot_right, w]
            exact cast_proof_irrel _ rfl _
          rw [hOuterS, hTargetOuter, leftRouteSlot_innerShift,
            hInnerCoeff, hRightCoeff] at hout'
          simp only [qLS, qLM, c, Tensor.Slot.right] at hout'
          have hProof : hEnd = hLL.trans hAT := Subsingleton.elim _ _
          cases hProof
          rw [AtomHom.coeff_comp _ _ hLL hAT]
          rw [cast_algebra_mul_of_label_eq RealAssociator.shiftedReal.D
            hSL (congrArg F hSL)]
          rw [hout']
          rw [realHomEntry_route_coeff]
          have hAssocCast :
              cast (congrArg F hSL)
                  (cast (congrArg F hLL).symm
                    (cast (congrArg F hML).symm
                      ((RealAssociator.shiftedReal.D.algebra
                        (a' + b' + c')).smul
                        (RawDCT.paritySign
                          (RealAssociator.shiftedReal.C.rowParity
                            a' b'
                            (Associator.castIndex
                              RealAssociator.shiftedReal
                              hA hB middleAB) * sc'))
                        (Associator.homCoefficient
                          RealAssociator.shiftedReal a' b' c'
                          (Associator.castIndex
                            RealAssociator.shiftedReal hA hB middleAB)
                          (Associator.castIndex
                            RealAssociator.shiftedReal hAB hC middleABC)
                          (Associator.castIndex
                            RealAssociator.shiftedReal hB hC targetBC₀)
                          (Associator.castIndex
                            RealAssociator.shiftedReal
                            hA hBC targetABC₀))))) =
                (RealAssociator.shiftedReal.D.algebra
                  (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity
                      a b middleAB * sc'))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c middleAB middleABC targetBC₀ targetABC₀) := by
            rw [cast_cast_eq, cast_cast_eq]
            calc
              _ = cast (congrArg F hABC).symm
                    ((RealAssociator.shiftedReal.D.algebra
                      (a' + b' + c')).smul
                      (RawDCT.paritySign
                        (RealAssociator.shiftedReal.C.rowParity a' b'
                          (Associator.castIndex RealAssociator.shiftedReal
                            hA hB middleAB) * sc'))
                      (Associator.homCoefficient
                        RealAssociator.shiftedReal a' b' c'
                        (Associator.castIndex RealAssociator.shiftedReal
                          hA hB middleAB)
                        (Associator.castIndex RealAssociator.shiftedReal
                          hAB hC middleABC)
                        (Associator.castIndex RealAssociator.shiftedReal
                          hB hC targetBC₀)
                        (Associator.castIndex RealAssociator.shiftedReal
                          hA hBC targetABC₀))) :=
                  cast_proof_irrel _ _ _
              _ = _ := normalizedHomCoefficient_transport
                hA hB hC sc' middleAB middleABC targetBC₀ targetABC₀
          exact congrArg₂
            (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
            hAssocCast rfl
        have hrightTerm
            (middleBC : RealAssociator.shiftedReal.C.Index b c)
            (middleABC : RealAssociator.shiftedReal.C.Index a (b + c)) :
            let qRS := RealAssociatorLaws.rightRouteSlot X Y Z
              i j k middleBC middleABC
            let hSR := RealAssociatorLaws.rightRouteSlot_label X Y Z
              i j k middleBC middleABC
            let hAS := RealAssociatorLaws.routeAssocLabelEq X Y Z
              i j k sourceAB sourceABC middleBC middleABC
            let hTR := RealAssociatorLaws.rightRouteSlot_label X' Y' Z'
              i' j' k'
              (Associator.castIndex RealAssociator.shiftedReal
                hB hC targetBC₀)
              (Associator.castIndex RealAssociator.shiftedReal
                hA hBC targetABC₀)
            let hRR := hSR.trans (hA_BC.trans hTR.symm)
            cast (congrArg F hSL)
                ((AtomHom.comp
                  (RealAssociator.homEntry X Y Z qLS qRS)
                  (Tensor.entry RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C f
                    (Tensor.hom RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C g h) qRS qRT)).coeff hEnd) =
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                (RawDCT.routeCastAssoc RealAssociator.shiftedReal.D a b c
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a (b + c) sa
                    (sb + sc + RealAssociator.shiftedReal.C.rowParity
                      b c middleBC)
                    (sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                      b c targetBC₀)
                    middleABC targetABC₀ u
                    (Tensor.coefficient RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C b c sb sc sc'
                      middleBC targetBC₀ v w)))
                ((RealAssociator.shiftedReal.D.algebra (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity
                      a b sourceAB * sc))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c sourceAB sourceABC middleBC middleABC)) := by
          dsimp only
          let qRS := RealAssociatorLaws.rightRouteSlot X Y Z
            i j k middleBC middleABC
          let hSR := RealAssociatorLaws.rightRouteSlot_label X Y Z
            i j k middleBC middleABC
          let hAS := RealAssociatorLaws.routeAssocLabelEq X Y Z
            i j k sourceAB sourceABC middleBC middleABC
          let hTR := RealAssociatorLaws.rightRouteSlot_label X' Y' Z'
            i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hB hC targetBC₀)
            (Associator.castIndex RealAssociator.shiftedReal
              hA hBC targetABC₀)
          let hRR := hSR.trans (hA_BC.trans hTR.symm)
          let hInnerS := RealAssociatorLaws.rightRouteSlot_innerLabel
            X Y Z i j k middleBC middleABC
          let hInnerT := RealAssociatorLaws.rightRouteSlot_innerLabel
            X' Y' Z' i' j' k'
            (Associator.castIndex RealAssociator.shiftedReal
              hB hC targetBC₀)
            (Associator.castIndex RealAssociator.shiftedReal
              hA hBC targetABC₀)
          let hInner := hInnerS.trans (hBC.trans hInnerT.symm)
          have hInnerCoeff :
              cast (congrArg F hInnerS)
                  ((Tensor.hom RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C g h
                    qRS.right qRT.right).coeff hInner) =
                Tensor.coefficient RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C b c sb sc sc'
                  middleBC targetBC₀ v w := by
            have haux
                (qS : Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y Z)
                (qT : Tensor.Slot RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y' Z')
                (hqS : qS = ⟨j, k, middleBC⟩)
                (hqT : qT = ⟨j', k',
                  Associator.castIndex RealAssociator.shiftedReal
                    hB hC targetBC₀⟩)
                (hQS : (Tensor.slotAtom RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y Z qS).label = b + c)
                (hST : (Tensor.slotAtom RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y Z qS).label =
                    (Tensor.slotAtom RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C Y' Z' qT).label) :
                cast (congrArg F hQS)
                    ((Tensor.entry RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C g h qS qT).coeff hST) =
                  Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C b c sb sc sc'
                    middleBC targetBC₀ v w := by
              subst qS
              subst qT
              rw [tensorEntry_coeff_of_label_eq g h
                ⟨j, k, middleBC⟩
                ⟨j', k', Associator.castIndex
                  RealAssociator.shiftedReal hB hC targetBC₀⟩
                hB hC hST]
              simp only [b, c, sb, sc, sc',
                Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion,
                Tensor.slotAtom, v, w, castIndex_cancel_symm]
              have hProof : hQS = rfl := Subsingleton.elim _ _
              cases hProof
              rfl
            have hqS :
                (Tensor.slots RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y Z).get qRS.right =
                    ⟨j, k, middleBC⟩ := by
              simpa only [qRS] using
                RealAssociatorLaws.rightRouteSlot_inner
                  X Y Z i j k middleBC middleABC
            have hqT :
                (Tensor.slots RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C Y' Z').get qRT.right =
                    ⟨j', k',
                      Associator.castIndex RealAssociator.shiftedReal
                        hB hC targetBC₀⟩ := by
              simpa only [qRT] using
                RealAssociatorLaws.rightRouteSlot_inner X' Y' Z'
                  i' j' k'
                  (Associator.castIndex RealAssociator.shiftedReal
                    hB hC targetBC₀)
                  (Associator.castIndex RealAssociator.shiftedReal
                    hA hBC targetABC₀)
            exact haux
              ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C Y Z).get qRS.right)
              ((Tensor.slots RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C Y' Z').get qRT.right)
              hqS hqT hInnerS hInner
          have hLeftS : (X.atom qRS.left).label = a := by
            simpa only [qRS, a] using congrArg
              (fun n => (X.atom n).label)
              (RealAssociatorLaws.rightRouteSlot_left
                X Y Z i j k middleBC middleABC)
          have hLeftT : (X'.atom qRT.left).label = a' := by
            simpa only [qRT, a'] using congrArg
              (fun n => (X'.atom n).label)
              (RealAssociatorLaws.rightRouteSlot_left X' Y' Z'
                i' j' k'
                (Associator.castIndex RealAssociator.shiftedReal
                  hB hC targetBC₀)
                (Associator.castIndex RealAssociator.shiftedReal
                  hA hBC targetABC₀))
          let hLeftST := hLeftS.trans (hA.trans hLeftT.symm)
          have hout := tensorEntry_coeff_of_label_eq f
            (Tensor.hom RealAssociator.shiftedReal.D
              RealAssociator.shiftedReal.C g h) qRS qRT
            hLeftST hInner hRR
          have hout' :=
            (congrArg (fun z => cast (congrArg F hSR) z) hout).trans
              ((cast_proof_irrel
                (congrArg F hSR)
                (congrArg F
                  (congrArg₂ (· + ·) hLeftS hInnerS)) _).trans
                (tensorCoefficient_transport hLeftS hInnerS
                  _ _ _ _ _ _ _))
          have hOuterS :
              Associator.castIndex RealAssociator.shiftedReal
                  hLeftS hInnerS qRS.fusion = middleABC := by
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    rfl hInnerS qRS.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = middleABC := by
                simpa only [qRS, hInnerS] using
                  RealAssociatorLaws.rightRouteSlot_outerRow
                    X Y Z i j k middleBC middleABC
          have hOuterT :
              Associator.castIndex RealAssociator.shiftedReal
                  hLeftT hInnerT qRT.fusion =
                Associator.castIndex RealAssociator.shiftedReal
                  hA hBC targetABC₀ := by
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    rfl hInnerT qRT.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = _ := by
                simpa only [qRT, hInnerT] using
                  RealAssociatorLaws.rightRouteSlot_outerRow X' Y' Z'
                    i' j' k'
                    (Associator.castIndex RealAssociator.shiftedReal
                      hB hC targetBC₀)
                    (Associator.castIndex RealAssociator.shiftedReal
                      hA hBC targetABC₀)
          have hTargetOuter :
              Associator.castIndex RealAssociator.shiftedReal
                  hLeftS hInnerS
                  (Associator.castIndex RealAssociator.shiftedReal
                    hLeftST.symm hInner.symm qRT.fusion) = targetABC₀ := by
            rw [castIndex_trans]
            calc
              _ = Associator.castIndex RealAssociator.shiftedReal
                    (hLeftT.trans hA.symm)
                    (hInnerT.trans hBC.symm) qRT.fusion :=
                castIndex_proof_irrel RealAssociator.shiftedReal _ _ _ _ _
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hA.symm hBC.symm
                    (Associator.castIndex RealAssociator.shiftedReal
                      hLeftT hInnerT qRT.fusion) :=
                (castIndex_trans RealAssociator.shiftedReal
                  hLeftT hInnerT hA.symm hBC.symm qRT.fusion).symm
              _ = Associator.castIndex RealAssociator.shiftedReal
                    hA.symm hBC.symm
                    (Associator.castIndex RealAssociator.shiftedReal
                      hA hBC targetABC₀) := congrArg _ hOuterT
              _ = targetABC₀ :=
                castIndex_cancel_symm RealAssociator.shiftedReal
                  hA hBC targetABC₀
          have hLeftCoeff :
              cast (congrArg F hLeftS)
                  ((f qRS.left qRT.left).coeff hLeftST) = u := by
            simp only [qRS, qRT,
              RealAssociatorLaws.rightRouteSlot_left, u]
            exact cast_proof_irrel _ rfl _
          have hLeftShift : (X.atom qRS.left).shift = sa := by
            simpa only [qRS, sa] using congrArg
              (fun n => (X.atom n).shift)
              (RealAssociatorLaws.rightRouteSlot_left
                X Y Z i j k middleBC middleABC)
          have hTargetInnerShift :
              ((Tensor.obj RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C Y' Z').atom qRT.right).shift =
                sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                  b c targetBC₀ := by
            simpa only [qRT, b, c, b', c', sb', sc',
              rowParity_castIndex] using
              rightRouteSlot_innerShift X' Y' Z' i' j' k'
                (Associator.castIndex RealAssociator.shiftedReal
                  hB hC targetBC₀)
                (Associator.castIndex RealAssociator.shiftedReal
                  hA hBC targetABC₀)
          rw [hOuterS, hTargetOuter, rightRouteSlot_innerShift,
            hInnerCoeff, hLeftCoeff, hLeftShift,
            hTargetInnerShift] at hout'
          simp only [qRS, qRT, a, sa] at hout'
          have hNestedNative :
              (Tensor.entry RealAssociator.shiftedReal.D
                RealAssociator.shiftedReal.C f
                (Tensor.hom RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C g h) qRS qRT).coeff hRR =
                cast (congrArg F hSR).symm
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a (b + c) sa
                    (sb + sc + RealAssociator.shiftedReal.C.rowParity
                      b c middleBC)
                    (sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                      b c targetBC₀)
                    middleABC targetABC₀ u
                    (Tensor.coefficient RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C b c sb sc sc'
                      middleBC targetBC₀ v w)) := by
            calc
              _ = cast (congrArg F hSR).symm
                    (cast (congrArg F hSR)
                      ((Tensor.entry RealAssociator.shiftedReal.D
                        RealAssociator.shiftedReal.C f
                        (Tensor.hom RealAssociator.shiftedReal.D
                          RealAssociator.shiftedReal.C g h)
                        qRS qRT).coeff hRR)) := by
                  rw [cast_cast_eq]
                  exact (cast_proof_irrel _ rfl _).symm
              _ = _ := congrArg _ hout'
          have hNestedCast :
              cast (congrArg F hSL)
                  (cast (congrArg F hAS).symm
                    ((Tensor.entry RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C f
                      (Tensor.hom RealAssociator.shiftedReal.D
                        RealAssociator.shiftedReal.C g h)
                      qRS qRT).coeff hRR)) =
                RawDCT.routeCastAssoc RealAssociator.shiftedReal.D a b c
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a (b + c) sa
                    (sb + sc + RealAssociator.shiftedReal.C.rowParity
                      b c middleBC)
                    (sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                      b c targetBC₀)
                    middleABC targetABC₀ u
                    (Tensor.coefficient RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C b c sb sc sc'
                      middleBC targetBC₀ v w)) := by
            rw [hNestedNative]
            unfold RawDCT.routeCastAssoc
            rw [cast_cast_eq, cast_cast_eq]
          have hProof : hEnd = hAS.trans hRR := Subsingleton.elim _ _
          cases hProof
          rw [AtomHom.coeff_comp _ _ hAS hRR]
          rw [cast_algebra_mul_of_label_eq RealAssociator.shiftedReal.D
            hSL (congrArg F hSL)]
          rw [hNestedCast]
          rw [realHomEntry_route_coeff]
          have hAssocCast :
              cast (congrArg F hSL)
                  (cast (congrArg F hSL).symm
                    ((RealAssociator.shiftedReal.D.algebra
                      (a + b + c)).smul
                      (RawDCT.paritySign
                        (RealAssociator.shiftedReal.C.rowParity
                          a b sourceAB * sc))
                      (Associator.homCoefficient RealAssociator.shiftedReal
                        a b c sourceAB sourceABC middleBC middleABC))) =
                (RealAssociator.shiftedReal.D.algebra
                  (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity
                      a b sourceAB * sc))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c sourceAB sourceABC middleBC middleABC) := by
            rw [cast_cast_eq]
            exact cast_proof_irrel _ rfl _
          exact congrArg₂
            (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
            rfl hAssocCast
        have hleftTerm'
            (middleAB : RealAssociator.shiftedReal.C.Index a b)
            (middleABC : RealAssociator.shiftedReal.C.Index (a + b) c) :=
          eq_cast_symm_of_cast_eq (congrArg F hSL)
            (hleftTerm middleAB middleABC)
        have hrightTerm'
            (middleBC : RealAssociator.shiftedReal.C.Index b c)
            (middleABC : RealAssociator.shiftedReal.C.Index a (b + c)) :=
          eq_cast_symm_of_cast_eq (congrArg F hSL)
            (hrightTerm middleBC middleABC)
        have hleftTerm''
            (middleAB : RealAssociator.shiftedReal.C.Index a b)
            (middleABC : RealAssociator.shiftedReal.C.Index (a + b) c) := by
          simpa only [eAB, eABC, castIndexEquiv_apply] using
            hleftTerm' middleAB middleABC
        simp_rw [atomHom_sum_coeff hEnd]
        have hcore := endpoint_homCoefficient_naturality_of_memGrade
          a b c sa sa' sb sb' sc sc' pf pg ph
          sourceAB sourceABC targetBC₀ targetABC₀ u v w hu hv hw
        have hcast := congrArg
          (fun z => cast (congrArg F hSL).symm z) hcore
        rw [cast_rawFinSum RealAssociator.shiftedReal.D hSL.symm] at hcast
        simp only [eAB, eABC, castIndexEquiv_apply]
        rw [rawFinSum_congr _ (fun middleAB =>
          cast_rawFinSum RealAssociator.shiftedReal.D hSL.symm
            (fun middleABC =>
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                ((RealAssociator.shiftedReal.D.algebra
                  (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity
                      a b middleAB * sc'))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c middleAB middleABC targetBC₀ targetABC₀))
                (Tensor.coefficient RealAssociator.shiftedReal.D
                  RealAssociator.shiftedReal.C (a + b) c
                  (sa + sb + RealAssociator.shiftedReal.C.rowParity
                    a b sourceAB) sc sc' sourceABC middleABC
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a b sa sb sb'
                    sourceAB middleAB u v) w)))] at hcast
        rw [cast_rawFinSum RealAssociator.shiftedReal.D hSL.symm] at hcast
        rw [rawFinSum_congr _ (fun middleBC =>
          cast_rawFinSum RealAssociator.shiftedReal.D hSL.symm
            (fun middleABC =>
              (RealAssociator.shiftedReal.D.algebra (a + b + c)).mul
                (RawDCT.routeCastAssoc RealAssociator.shiftedReal.D a b c
                  (Tensor.coefficient RealAssociator.shiftedReal.D
                    RealAssociator.shiftedReal.C a (b + c) sa
                    (sb + sc + RealAssociator.shiftedReal.C.rowParity
                      b c middleBC)
                    (sb' + sc' + RealAssociator.shiftedReal.C.rowParity
                      b c targetBC₀)
                    middleABC targetABC₀ u
                    (Tensor.coefficient RealAssociator.shiftedReal.D
                      RealAssociator.shiftedReal.C b c sb sc sc'
                      middleBC targetBC₀ v w)))
                ((RealAssociator.shiftedReal.D.algebra
                  (a + b + c)).smul
                  (RawDCT.paritySign
                    (RealAssociator.shiftedReal.C.rowParity
                      a b sourceAB * sc))
                  (Associator.homCoefficient RealAssociator.shiftedReal
                    a b c sourceAB sourceABC middleBC middleABC))))] at hcast
        rw [rawFinSum_congr _ (fun middleAB =>
          rawFinSum_congr _ (fun middleABC =>
            hleftTerm'' middleAB middleABC))]
        rw [rawFinSum_congr _ (fun middleBC =>
          rawFinSum_congr _ (fun middleABC =>
            hrightTerm' middleBC middleABC))]
        exact hcast
      · have hcn : (Z.atom k).label ≠ (Z'.atom k').label := hC
        have hleft (middleAB) (middleABC) :=
          leftNestedEntry_zero_of_third_label_ne f g h
            i j k i' j' k' sourceAB sourceABC middleAB middleABC hcn
        have hright (middleBC) (middleABC) :=
          rightNestedEntry_zero_of_third_label_ne f g h
            i j k i' j' k' middleBC middleABC targetBC targetABC hcn
        simp_rw [hleft, AtomHom.zero_comp
          realComputableShiftedRawDCT.laws.D,
          hright, AtomHom.comp_zero
          realComputableShiftedRawDCT.laws.D]
        simp only [atomHom_sum_zero]
    · have hbn : (Y.atom j).label ≠ (Y'.atom j').label := hB
      have hleft (middleAB) (middleABC) :=
        leftNestedEntry_zero_of_middle_label_ne f g h
          i j k i' j' k' sourceAB sourceABC middleAB middleABC hbn
      have hright (middleBC) (middleABC) :=
        rightNestedEntry_zero_of_middle_label_ne f g h
          i j k i' j' k' middleBC middleABC targetBC targetABC hbn
      simp_rw [hleft, AtomHom.zero_comp
        realComputableShiftedRawDCT.laws.D,
        hright, AtomHom.comp_zero
        realComputableShiftedRawDCT.laws.D]
      simp only [atomHom_sum_zero]
  · have han : (X.atom i).label ≠ (X'.atom i').label := hA
    have hleft (middleAB) (middleABC) :=
      leftNestedEntry_zero_of_first_label_ne f g h
        i j k i' j' k' sourceAB sourceABC middleAB middleABC han
    have hright (middleBC) (middleABC) :=
      rightNestedEntry_zero_of_first_label_ne f g h
        i j k i' j' k' middleBC middleABC targetBC targetABC han
    simp_rw [hleft, AtomHom.zero_comp
      realComputableShiftedRawDCT.laws.D,
      hright, AtomHom.comp_zero
      realComputableShiftedRawDCT.laws.D]
    simp only [atomHom_sum_zero]

/-! ## From fixed routes to homogeneous morphism matrices -/

/-- Naturality for three homogeneous morphism matrices.  Surjectivity of
the canonical route positions reduces every matrix entry to the fixed-route
coefficient identity above. -/
theorem realAssociator_naturality_of_memGrade
    {X X' Y Y' Z Z' : Obj} {pf pg ph : ZMod 2}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (hf : Hom.MemGrade pf f) (hg : Hom.MemGrade pg g)
    (hh : Hom.MemGrade ph h) :
    Hom.comp
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h)
        (RealAssociator.hom X' Y' Z') =
      Hom.comp (RealAssociator.hom X Y Z)
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h)) := by
  apply Hom.ext
  intro p q
  rcases exists_eq_leftRoutePosition X Y Z p with
    ⟨i, j, k, sourceAB, sourceABC, rfl⟩
  rcases exists_eq_rightRoutePosition X' Y' Z' q with
    ⟨i', j', k', targetBC, targetABC, rfl⟩
  rw [leftComposite_entry_as_route_sum f g h
    i j k i' j' k' sourceAB sourceABC targetBC targetABC]
  rw [rightComposite_entry_as_route_sum f g h
    i j k i' j' k' sourceAB sourceABC targetBC targetABC]
  exact routeSum_naturality_of_memGrade f g h hf hg hh
    i j k i' j' k' sourceAB sourceABC targetBC targetABC

/-! ## Additive lift from homogeneous pieces -/

/-- With the first two inputs homogeneous, split the third morphism into
its two stored grade components and use additivity of tensor and
composition. -/
private theorem realAssociator_naturality_of_memGrade_first_second
    {X X' Y Y' Z Z' : Obj} {pf pg : ZMod 2}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (hf : Hom.MemGrade pf f) (hg : Hom.MemGrade pg g) :
    Hom.comp
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h)
        (RealAssociator.hom X' Y' Z') =
      Hom.comp (RealAssociator.hom X Y Z)
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h)) := by
  let h₀ := Hom.component 0 h
  let h₁ := Hom.component 1 h
  have hsplit : Hom.add h₀ h₁ = h := by
    simpa only [h₀, h₁, _root_.zero_add] using
      Hom.component_complement realComputableShiftedRawDCT.laws.D 0 h
  rw [← hsplit]
  simpa only [Tensor.hom_add_left RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Tensor.hom_add_right RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Hom.add_comp realComputableShiftedRawDCT.laws.D,
    Hom.comp_add realComputableShiftedRawDCT.laws.D] using
    congrArg₂ Hom.add
      (realAssociator_naturality_of_memGrade f g h₀ hf hg
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 0 h))
      (realAssociator_naturality_of_memGrade f g h₁ hf hg
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 1 h))

/-- With only the first input homogeneous, split the second input and reuse
the preceding third-input lift. -/
private theorem realAssociator_naturality_of_memGrade_first
    {X X' Y Y' Z Z' : Obj} {pf : ZMod 2}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z')
    (hf : Hom.MemGrade pf f) :
    Hom.comp
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h)
        (RealAssociator.hom X' Y' Z') =
      Hom.comp (RealAssociator.hom X Y Z)
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h)) := by
  let g₀ := Hom.component 0 g
  let g₁ := Hom.component 1 g
  have gsplit : Hom.add g₀ g₁ = g := by
    simpa only [g₀, g₁, _root_.zero_add] using
      Hom.component_complement realComputableShiftedRawDCT.laws.D 0 g
  rw [← gsplit]
  simpa only [Tensor.hom_add_left RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Tensor.hom_add_right RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Hom.add_comp realComputableShiftedRawDCT.laws.D,
    Hom.comp_add realComputableShiftedRawDCT.laws.D] using
    congrArg₂ Hom.add
      (realAssociator_naturality_of_memGrade_first_second f g₀ h hf
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 0 g))
      (realAssociator_naturality_of_memGrade_first_second f g₁ h hf
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 1 g))

/-- Naturality of the endpoint-normalized real associator for arbitrary
morphism matrices.  The statement is fully computable; the proof layer only
uses the canonical even/odd decomposition already stored in `D`. -/
theorem realAssociator_naturality
    {X X' Y Y' Z Z' : Obj}
    (f : Hom RealAssociator.shiftedReal.D X X')
    (g : Hom RealAssociator.shiftedReal.D Y Y')
    (h : Hom RealAssociator.shiftedReal.D Z Z') :
    Hom.comp
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C f g) h)
        (RealAssociator.hom X' Y' Z') =
      Hom.comp (RealAssociator.hom X Y Z)
        (Tensor.hom RealAssociator.shiftedReal.D
          RealAssociator.shiftedReal.C f
          (Tensor.hom RealAssociator.shiftedReal.D
            RealAssociator.shiftedReal.C g h)) := by
  let f₀ := Hom.component 0 f
  let f₁ := Hom.component 1 f
  have fsplit : Hom.add f₀ f₁ = f := by
    simpa only [f₀, f₁, _root_.zero_add] using
      Hom.component_complement realComputableShiftedRawDCT.laws.D 0 f
  rw [← fsplit]
  simpa only [Tensor.hom_add_left RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Tensor.hom_add_right RealAssociator.shiftedReal.D
      realComputableShiftedRawDCT.laws.D RealAssociator.shiftedReal.C
      realComputableShiftedRawDCT.laws.C,
    Hom.add_comp realComputableShiftedRawDCT.laws.D,
    Hom.comp_add realComputableShiftedRawDCT.laws.D] using
    congrArg₂ Hom.add
      (realAssociator_naturality_of_memGrade_first f₀ g h
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 0 f))
      (realAssociator_naturality_of_memGrade_first f₁ g h
        (Hom.component_memGrade realComputableShiftedRawDCT.laws.D 1 f))

end RealAssociatorNaturality

end Superfusion.RMod.FromRawDCT
