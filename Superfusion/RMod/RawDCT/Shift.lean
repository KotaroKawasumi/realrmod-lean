import Superfusion.RMod.RawDCT.NuBeta

/-!
# Parity and scalar shifts of raw DCT data

This file gives the coordinate-level counterpart of the semantic shift of
fusion kernels.  A binary kernel is regraded by `nu`; its left action is
pulled back along the parity automorphism.  The two ternary routes are then
presented in the shifted fusion-row frames, and the connector is rescaled by
`beta⁻¹` in the forward direction and by `beta` in the inverse direction.

The construction is independent of the concrete real tables.  In
particular, all signs below are computed from the stored row parities and no
finite verification is performed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Proof-only notation for stored algebra operations -/

/- These instances expose only the operations already present in one raw
algebra record.  Algebraic axioms are still supplied explicitly through a
`SuperAlgebraLaws` argument below. -/

private instance rawZero (d : SuperAlgebraData ℝ) : Zero d.carrier :=
  ⟨d.zero⟩

private instance rawAdd (d : SuperAlgebraData ℝ) : Add d.carrier :=
  ⟨d.add⟩

private instance rawNeg (d : SuperAlgebraData ℝ) : Neg d.carrier :=
  ⟨d.neg⟩

private instance rawSub (d : SuperAlgebraData ℝ) : Sub d.carrier :=
  ⟨fun x y => d.add x (d.neg y)⟩

private instance rawScalar (d : SuperAlgebraData ℝ) : SMul ℝ d.carrier :=
  ⟨d.smul⟩

@[implicit_reducible]
private def rawAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier where
  add_assoc := h.add_assoc
  zero_add := h.zero_add
  add_zero := h.add_zero
  neg_add_cancel := h.neg_add
  add_comm := h.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

@[implicit_reducible]
private def rawModule (d : SuperAlgebraData ℝ) (h : SuperAlgebraLaws d) :
    letI := rawAddCommGroup d h
    Module ℝ d.carrier := by
  letI := rawAddCommGroup d h
  exact
    { one_smul := h.one_smul
      mul_smul := h.smul_assoc
      smul_add := h.smul_add
      smul_zero := h.smul_zero
      add_smul := h.add_smul
      zero_smul := h.zero_smul }

/-! ## Additive-label forms of the shift cochains -/

/-- Evaluate the parity two-cochain on additive labels. -/
def shiftNu (n : NuBetaData) (a b : ZMod 8) : ZMod 2 :=
  n.nu (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

/-- Evaluate the scalar three-cochain on additive labels. -/
def shiftBeta (n : NuBetaData) (a b c : ZMod 8) : ℝˣ :=
  n.beta (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    (Multiplicative.ofAdd c)

/-- Total regrading along the left-associated ternary route. -/
def leftRouteShift (n : NuBetaData) (a b c : ZMod 8) : ZMod 2 :=
  shiftNu n a b + shiftNu n (a + b) c

/-- Total regrading along the right-associated ternary route. -/
def rightRouteShift (n : NuBetaData) (a b c : ZMod 8) : ZMod 2 :=
  shiftNu n b c + shiftNu n a (b + c)

/-! ## Generic parity-sign and parity-twist lemmas -/

private theorem shiftZMod2_add_self (i : ZMod 2) : i + i = 0 := by
  rcases zmod2_cases i with rfl | rfl <;> decide

private theorem shiftZMod2_sub_eq_add (i j : ZMod 2) : i - j = i + j := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;> decide

@[simp] theorem shiftParitySign_zero : paritySign 0 = 1 := by
  simp [paritySign]

theorem shiftParitySign_add (i j : ZMod 2) :
    paritySign (i + j) = paritySign i * paritySign j := by
  rcases zmod2_cases i with rfl | rfl <;>
    rcases zmod2_cases j with rfl | rfl <;>
      simp [paritySign, shiftZMod2_add_self]

theorem shiftParitySign_mul_self (i : ZMod 2) :
    paritySign i * paritySign i = 1 := by
  rw [← shiftParitySign_add, shiftZMod2_add_self, shiftParitySign_zero]

theorem shiftParitySign_mul (p i j : ZMod 2) :
    paritySign (p * (i + j)) =
      paritySign (p * i) * paritySign (p * j) := by
  rw [mul_add, shiftParitySign_add]

private theorem component_other_eq_zero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (i : ZMod 2) (x : d.carrier)
    (hx : d.MemGrade i x) : d.component (i + 1) x = d.zero := by
  letI := rawAddCommGroup d h
  have hc := h.component_complement i x
  change d.component i x + d.component (i + 1) x = x at hc
  change d.component i x = x at hx
  rw [hx] at hc
  apply add_left_cancel (a := x)
  change x + d.component (i + 1) x = x + (0 : d.carrier)
  exact hc.trans (add_zero x).symm

/-- On a homogeneous coefficient, the raw parity twist is its expected
Koszul sign. -/
theorem routeRowTwist_of_memGrade (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p i : ZMod 2) (x : d.carrier)
    (hx : d.MemGrade i x) :
    routeRowTwist { algebra := fun _ => d } 0 p x =
      d.smul (paritySign (p * i)) x := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · have hother := component_other_eq_zero d h 0 x hx
    have hother' : d.component 1 x = d.zero := by
      simpa using hother
    unfold routeRowTwist
    change d.add (d.component 0 x)
      (d.smul (paritySign p) (d.component 1 x)) = _
    rw [hx, hother', h.smul_zero, h.add_zero]
    simpa [paritySign] using (h.one_smul x).symm
  · have hother := component_other_eq_zero d h 1 x hx
    have hzero : d.component 0 x = d.zero := by
      simpa [shiftZMod2_add_self] using hother
    unfold routeRowTwist
    change d.add (d.component 0 x)
      (d.smul (paritySign p) (d.component 1 x)) = _
    rw [hzero, hx, h.zero_add]
    simp

/-- The raw parity twist is additive. -/
theorem routeRowTwist_add (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) (x y : d.carrier) :
    routeRowTwist { algebra := fun _ => d } 0 p (d.add x y) =
      d.add (routeRowTwist { algebra := fun _ => d } 0 p x)
        (routeRowTwist { algebra := fun _ => d } 0 p y) := by
  letI := rawAddCommGroup d h
  letI := rawModule d h
  unfold routeRowTwist
  change d.add (d.component 0 (d.add x y))
      (d.smul (paritySign p) (d.component 1 (d.add x y))) =
    d.add
      (d.add (d.component 0 x) (d.smul (paritySign p) (d.component 1 x)))
      (d.add (d.component 0 y) (d.smul (paritySign p) (d.component 1 y)))
  rw [h.component_add, h.component_add, h.smul_add]
  let x0 := d.component 0 x
  let y0 := d.component 0 y
  let x1 := d.smul (paritySign p) (d.component 1 x)
  let y1 := d.smul (paritySign p) (d.component 1 y)
  change d.add (d.add x0 y0) (d.add x1 y1) =
    d.add (d.add x0 x1) (d.add y0 y1)
  calc
    d.add (d.add x0 y0) (d.add x1 y1) =
        d.add x0 (d.add y0 (d.add x1 y1)) := h.add_assoc _ _ _
    _ = d.add x0 (d.add (d.add y0 x1) y1) := by
      rw [h.add_assoc y0 x1 y1]
    _ = d.add x0 (d.add (d.add x1 y0) y1) := by
      rw [h.add_comm y0 x1]
    _ = d.add x0 (d.add x1 (d.add y0 y1)) := by
      rw [h.add_assoc x1 y0 y1]
    _ = d.add (d.add x0 x1) (d.add y0 y1) :=
      (h.add_assoc _ _ _).symm

/-- The raw parity twist commutes with real scalar multiplication. -/
theorem routeRowTwist_smul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) (q : ℝ) (x : d.carrier) :
    routeRowTwist { algebra := fun _ => d } 0 p (d.smul q x) =
      d.smul q (routeRowTwist { algebra := fun _ => d } 0 p x) := by
  letI := rawAddCommGroup d h
  letI := rawModule d h
  unfold routeRowTwist
  change d.add (d.component 0 (d.smul q x))
      (d.smul (paritySign p) (d.component 1 (d.smul q x))) =
    d.smul q
      (d.add (d.component 0 x) (d.smul (paritySign p) (d.component 1 x)))
  rw [h.component_smul, h.component_smul]
  change q • d.component 0 x + paritySign p • (q • d.component 1 x) =
    q • (d.component 0 x + paritySign p • d.component 1 x)
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  rw [mul_comm]

/-- The raw parity twist fixes zero. -/
theorem routeRowTwist_zero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) :
    routeRowTwist { algebra := fun _ => d } 0 p d.zero = d.zero := by
  unfold routeRowTwist
  rw [h.component_zero, h.component_zero, h.smul_zero, h.add_zero]

/-- The raw parity twist fixes the multiplicative unit. -/
theorem routeRowTwist_one (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) :
    routeRowTwist { algebra := fun _ => d } 0 p d.one = d.one := by
  rw [routeRowTwist_of_memGrade d h p 0 d.one h.one_mem]
  simpa [paritySign] using h.one_smul d.one

/-- Parity twisting preserves the degree of a homogeneous coefficient. -/
theorem routeRowTwist_memGrade (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p i : ZMod 2) (x : d.carrier)
    (hx : d.MemGrade i x) :
    d.MemGrade i (routeRowTwist { algebra := fun _ => d } 0 p x) := by
  rw [routeRowTwist_of_memGrade d h p i x hx]
  unfold SuperAlgebraData.MemGrade
  rw [h.component_smul, hx]

/-- Exponent zero gives the identity parity twist. -/
theorem routeRowTwist_zeroParity (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    routeRowTwist { algebra := fun _ => d } 0 0 x = x := by
  unfold routeRowTwist
  rw [shiftParitySign_zero, h.one_smul]
  change d.add (d.component 0 x) (d.component 1 x) = x
  exact h.component_complement 0 x

private theorem rawAddMedial (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (a b c e : d.carrier) :
    d.add (d.add a b) (d.add c e) =
      d.add (d.add a c) (d.add b e) := by
  calc
    d.add (d.add a b) (d.add c e) =
        d.add a (d.add b (d.add c e)) := h.add_assoc _ _ _
    _ = d.add a (d.add (d.add b c) e) := by
      rw [h.add_assoc b c e]
    _ = d.add a (d.add (d.add c b) e) := by
      rw [h.add_comm b c]
    _ = d.add a (d.add c (d.add b e)) := by
      rw [h.add_assoc c b e]
    _ = d.add (d.add a c) (d.add b e) :=
      (h.add_assoc _ _ _).symm

/-- The raw parity twist is multiplicative. -/
theorem routeRowTwist_mul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) (x y : d.carrier) :
    routeRowTwist { algebra := fun _ => d } 0 p (d.mul x y) =
      d.mul (routeRowTwist { algebra := fun _ => d } 0 p x)
        (routeRowTwist { algebra := fun _ => d } 0 p y) := by
  rcases zmod2_cases p with hp | hp <;> subst hp
  · rw [routeRowTwist_zeroParity d h, routeRowTwist_zeroParity d h,
      routeRowTwist_zeroParity d h]
  · let x0 := d.component 0 x
    let x1 := d.component 1 x
    let y0 := d.component 0 y
    let y1 := d.component 1 y
    have hx0 : d.MemGrade 0 x0 := h.component_idem 0 x
    have hx1 : d.MemGrade 1 x1 := h.component_idem 1 x
    have hy0 : d.MemGrade 0 y0 := h.component_idem 0 y
    have hy1 : d.MemGrade 1 y1 := h.component_idem 1 y
    have hx0y0 : d.MemGrade 0 (d.mul x0 y0) := by
      simpa using h.mul_mem 0 0 x0 y0 hx0 hy0
    have hx1y0 : d.MemGrade 1 (d.mul x1 y0) := by
      simpa using h.mul_mem 1 0 x1 y0 hx1 hy0
    have hx0y1 : d.MemGrade 1 (d.mul x0 y1) := by
      simpa using h.mul_mem 0 1 x0 y1 hx0 hy1
    have hx1y1 : d.MemGrade 0 (d.mul x1 y1) := by
      simpa [shiftZMod2_add_self] using h.mul_mem 1 1 x1 y1 hx1 hy1
    have hx : d.add x0 x1 = x := h.component_complement 0 x
    have hy : d.add y0 y1 = y := h.component_complement 0 y
    calc
      routeRowTwist { algebra := fun _ => d } 0 1 (d.mul x y) =
          routeRowTwist { algebra := fun _ => d } 0 1
            (d.mul (d.add x0 x1) (d.add y0 y1)) := by rw [hx, hy]
      _ = d.add
          (d.add (d.mul x0 y0) (d.smul (-1) (d.mul x1 y0)))
          (d.add (d.smul (-1) (d.mul x0 y1)) (d.mul x1 y1)) := by
        rw [h.mul_add, h.add_mul, h.add_mul,
          routeRowTwist_add d h, routeRowTwist_add d h,
          routeRowTwist_add d h,
          routeRowTwist_of_memGrade d h 1 0 (d.mul x0 y0) hx0y0,
          routeRowTwist_of_memGrade d h 1 1 (d.mul x1 y0) hx1y0,
          routeRowTwist_of_memGrade d h 1 1 (d.mul x0 y1) hx0y1,
          routeRowTwist_of_memGrade d h 1 0 (d.mul x1 y1) hx1y1]
        norm_num [paritySign]
        rw [h.one_smul, h.one_smul]
      _ = d.add
          (d.add (d.mul x0 y0) (d.smul (-1) (d.mul x0 y1)))
          (d.add (d.smul (-1) (d.mul x1 y0)) (d.mul x1 y1)) := by
        exact rawAddMedial d h _ _ _ _
      _ = d.mul
          (d.add x0 (d.smul (-1) x1))
          (d.add y0 (d.smul (-1) y1)) := by
        rw [h.mul_add, h.add_mul, h.add_mul, h.mul_smul, h.smul_mul,
          h.smul_mul, h.mul_smul, ← h.smul_assoc]
        norm_num
        rw [h.one_smul]
        exact rawAddMedial d h _ _ _ _
      _ = d.mul
          (routeRowTwist { algebra := fun _ => d } 0 1 (d.add x0 x1))
          (routeRowTwist { algebra := fun _ => d } 0 1 (d.add y0 y1)) := by
        rw [routeRowTwist_add d h, routeRowTwist_add d h,
          routeRowTwist_of_memGrade d h 1 0 x0 hx0,
          routeRowTwist_of_memGrade d h 1 1 x1 hx1,
          routeRowTwist_of_memGrade d h 1 0 y0 hy0,
          routeRowTwist_of_memGrade d h 1 1 y1 hy1]
        norm_num [paritySign]
        rw [h.one_smul, h.one_smul]
      _ = d.mul
          (routeRowTwist { algebra := fun _ => d } 0 1 x)
          (routeRowTwist { algebra := fun _ => d } 0 1 y) := by rw [hx, hy]

/-- Two identical parity twists cancel. -/
theorem routeRowTwist_involutive (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (p : ZMod 2) (x : d.carrier) :
    routeRowTwist { algebra := fun _ => d } 0 p
        (routeRowTwist { algebra := fun _ => d } 0 p x) = x := by
  letI := rawAddCommGroup d h
  letI := rawModule d h
  rcases zmod2_cases p with hp | hp <;> subst hp
  · rw [routeRowTwist_zeroParity d h, routeRowTwist_zeroParity d h]
  · let x0 := d.component 0 x
    let x1 := d.component 1 x
    have hx0 : d.MemGrade 0 x0 := h.component_idem 0 x
    have hx1 : d.MemGrade 1 x1 := h.component_idem 1 x
    rw [show routeRowTwist { algebra := fun _ => d } 0 1 x =
        d.add x0 (d.smul (-1) x1) by rfl]
    rw [routeRowTwist_add d h, routeRowTwist_smul d h,
      routeRowTwist_of_memGrade d h 1 0 x0 hx0,
      routeRowTwist_of_memGrade d h 1 1 x1 hx1]
    change (1 : ℝ) • x0 + (-1 : ℝ) • ((-1 : ℝ) • x1) = x
    rw [one_smul, smul_smul]
    norm_num
    change d.add (d.component 0 x) (d.component 1 x) = x
    exact h.component_complement 0 x

/- The following wrappers state the generic algebra lemmas directly for a
member of a stored coefficient family. -/

private theorem routeRowTwist_add_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2)
    (x y : (dD.algebra a).carrier) :
    routeRowTwist dD a p ((dD.algebra a).add x y) =
      (dD.algebra a).add (routeRowTwist dD a p x)
        (routeRowTwist dD a p y) :=
  routeRowTwist_add (dD.algebra a) (hD.algebra_laws a) p x y

private theorem routeRowTwist_smul_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) (q : ℝ)
    (x : (dD.algebra a).carrier) :
    routeRowTwist dD a p ((dD.algebra a).smul q x) =
      (dD.algebra a).smul q (routeRowTwist dD a p x) :=
  routeRowTwist_smul (dD.algebra a) (hD.algebra_laws a) p q x

private theorem routeRowTwist_zero_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) :
    routeRowTwist dD a p (dD.algebra a).zero = (dD.algebra a).zero :=
  routeRowTwist_zero (dD.algebra a) (hD.algebra_laws a) p

private theorem routeRowTwist_one_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) :
    routeRowTwist dD a p (dD.algebra a).one = (dD.algebra a).one :=
  routeRowTwist_one (dD.algebra a) (hD.algebra_laws a) p

private theorem routeRowTwist_mul_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2)
    (x y : (dD.algebra a).carrier) :
    routeRowTwist dD a p ((dD.algebra a).mul x y) =
      (dD.algebra a).mul (routeRowTwist dD a p x)
        (routeRowTwist dD a p y) :=
  routeRowTwist_mul (dD.algebra a) (hD.algebra_laws a) p x y

private theorem routeRowTwist_memGrade_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    (dD.algebra a).MemGrade i (routeRowTwist dD a p x) :=
  routeRowTwist_memGrade (dD.algebra a) (hD.algebra_laws a) p i x hx

private theorem routeRowTwist_of_memGrade_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    routeRowTwist dD a p x =
      (dD.algebra a).smul (paritySign (p * i)) x :=
  routeRowTwist_of_memGrade (dD.algebra a) (hD.algebra_laws a) p i x hx

private theorem routeRowTwist_zeroParity_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (x : (dD.algebra a).carrier) :
    routeRowTwist dD a 0 x = x :=
  routeRowTwist_zeroParity (dD.algebra a) (hD.algebra_laws a) x

private theorem routeRowTwist_involutive_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) (x : (dD.algebra a).carrier) :
    routeRowTwist dD a p (routeRowTwist dD a p x) = x :=
  routeRowTwist_involutive (dD.algebra a) (hD.algebra_laws a) p x

private theorem routeRowTwist_compose_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p q : ZMod 2) (x : (dD.algebra a).carrier) :
    routeRowTwist dD a p (routeRowTwist dD a q x) =
      routeRowTwist dD a (p + q) x := by
  rcases zmod2_cases p with hp | hp <;>
    rcases zmod2_cases q with hq | hq <;>
      subst hp <;> subst hq
  · simp only [zero_add]
    rw [routeRowTwist_zeroParity_at dD hD,
      routeRowTwist_zeroParity_at dD hD]
  · simp only [zero_add]
    rw [routeRowTwist_zeroParity_at dD hD]
  · simp only [add_zero]
    rw [routeRowTwist_zeroParity_at dD hD]
  · rw [shiftZMod2_add_self, routeRowTwist_involutive_at dD hD,
      routeRowTwist_zeroParity_at dD hD]

/-! ## Binary kernel data -/

/-- Regrade one raw fusion-kernel family by a parity two-cochain.

The coordinate carrier and strict right action do not change.  The grading
is shifted, while the left action is restricted along the parity twist on
both coefficient factors. -/
def shiftCData (dD : DData) (dC : CData dD) (n : NuBetaData) : CData dD where
  rank := dC.rank
  rowParity a b r := dC.rowParity a b r + shiftNu n a b
  leftCoeff a b target source x y :=
    dC.leftCoeff a b target source
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y)
  carrier := dC.carrier
  toCoord := dC.toCoord
  ofCoord := dC.ofCoord
  zero := dC.zero
  add := dC.add
  neg := dC.neg
  smul := dC.smul
  component a b i x := dC.component a b (i + shiftNu n a b) x
  left a b x y m :=
    dC.left a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m
  right := dC.right

/-- Regrading and parity-twisting preserve all binary-kernel laws. -/
theorem shiftCLaws (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (n : NuBetaData) :
    CLaws dD hD (shiftCData dD dC n) where
  ofCoord_toCoord := by
    intro a b x
    exact hC.ofCoord_toCoord a b x
  toCoord_ofCoord := by
    intro a b x
    exact hC.toCoord_ofCoord a b x
  toCoord_zero := by
    intro a b
    exact hC.toCoord_zero a b
  toCoord_add := by
    intro a b x y
    exact hC.toCoord_add a b x y
  toCoord_neg := by
    intro a b x
    exact hC.toCoord_neg a b x
  toCoord_smul := by
    intro a b q x
    exact hC.toCoord_smul a b q x
  toCoord_component := by
    intro a b i x
    simpa only [shiftCData, add_assoc, add_comm, add_left_comm] using
      hC.toCoord_component a b (i + shiftNu n a b) x
  toCoord_left := by
    intro a b x y m
    exact hC.toCoord_left a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m
  toCoord_right := by
    intro a b m x
    exact hC.toCoord_right a b m x
  add_assoc := hC.add_assoc
  add_comm := hC.add_comm
  zero_add := hC.zero_add
  add_zero := hC.add_zero
  neg_add := hC.neg_add
  add_neg := hC.add_neg
  one_smul := hC.one_smul
  smul_assoc := hC.smul_assoc
  add_smul := hC.add_smul
  smul_add := hC.smul_add
  zero_smul := hC.zero_smul
  smul_zero := hC.smul_zero
  component_zero := by
    intro a b i
    exact hC.component_zero a b (i + shiftNu n a b)
  component_add := by
    intro a b i x y
    exact hC.component_add a b (i + shiftNu n a b) x y
  component_neg := by
    intro a b i x
    exact hC.component_neg a b (i + shiftNu n a b) x
  component_smul := by
    intro a b i r x
    exact hC.component_smul a b (i + shiftNu n a b) r x
  component_idem := by
    intro a b i x
    exact hC.component_idem a b (i + shiftNu n a b) x
  component_complement := by
    intro a b i x
    simpa only [shiftCData, add_assoc, add_comm, add_left_comm] using
      hC.component_complement a b (i + shiftNu n a b) x
  grade_disjoint := by
    intro a b i x hi hi1
    apply hC.grade_disjoint a b (i + shiftNu n a b) x hi
    simpa only [shiftCData, CData.MemGrade, add_assoc, add_comm,
      add_left_comm] using hi1
  left_zero_left := by
    intro a b y m
    simp only [shiftCData]
    rw [routeRowTwist_zero_at dD hD a (shiftNu n a b)]
    exact hC.left_zero_left a b
      (routeRowTwist dD b (shiftNu n a b) y) m
  left_zero_right := by
    intro a b x m
    simp only [shiftCData]
    rw [routeRowTwist_zero_at dD hD b (shiftNu n a b)]
    exact hC.left_zero_right a b
      (routeRowTwist dD a (shiftNu n a b) x) m
  left_zero_module := by
    intro a b x y
    exact hC.left_zero_module a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y)
  left_add_left := by
    intro a b x x' y m
    simp only [shiftCData]
    rw [routeRowTwist_add_at dD hD a (shiftNu n a b)]
    exact hC.left_add_left a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD a (shiftNu n a b) x')
      (routeRowTwist dD b (shiftNu n a b) y) m
  left_add_right := by
    intro a b x y y' m
    simp only [shiftCData]
    rw [routeRowTwist_add_at dD hD b (shiftNu n a b)]
    exact hC.left_add_right a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y)
      (routeRowTwist dD b (shiftNu n a b) y') m
  left_add_module := by
    intro a b x y m m'
    exact hC.left_add_module a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m m'
  left_smul_left := by
    intro a b r x y m
    simp only [shiftCData]
    rw [routeRowTwist_smul_at dD hD a (shiftNu n a b)]
    exact hC.left_smul_left a b r
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m
  left_smul_right := by
    intro a b r x y m
    simp only [shiftCData]
    rw [routeRowTwist_smul_at dD hD b (shiftNu n a b)]
    exact hC.left_smul_right a b r
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m
  left_smul_module := by
    intro a b r x y m
    exact hC.left_smul_module a b r
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m
  left_one := by
    intro a b m
    simp only [shiftCData]
    rw [routeRowTwist_one_at dD hD a (shiftNu n a b),
      routeRowTwist_one_at dD hD b (shiftNu n a b)]
    exact hC.left_one a b m
  left_mul := by
    intro a b i j x x' y y' m hy hx'
    have hyT := routeRowTwist_memGrade_at dD hD b (shiftNu n a b) j y hy
    have hxT := routeRowTwist_memGrade_at dD hD a (shiftNu n a b) i x' hx'
    simp only [shiftCData]
    rw [routeRowTwist_mul_at dD hD a (shiftNu n a b),
      routeRowTwist_mul_at dD hD b (shiftNu n a b)]
    exact hC.left_mul a b i j
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD a (shiftNu n a b) x')
      (routeRowTwist dD b (shiftNu n a b) y)
      (routeRowTwist dD b (shiftNu n a b) y') m hyT hxT
  left_memGrade := by
    intro a b i j k x y m hx hy hm
    have hxT := routeRowTwist_memGrade_at dD hD a (shiftNu n a b) i x hx
    have hyT := routeRowTwist_memGrade_at dD hD b (shiftNu n a b) j y hy
    have h := hC.left_memGrade a b i j (k + shiftNu n a b)
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m hxT hyT hm
    simpa only [shiftCData, CData.MemGrade, add_assoc, add_comm,
      add_left_comm] using h
  right_zero_module := hC.right_zero_module
  right_zero_algebra := hC.right_zero_algebra
  right_add_module := hC.right_add_module
  right_add_algebra := hC.right_add_algebra
  right_smul_module := hC.right_smul_module
  right_smul_algebra := hC.right_smul_algebra
  right_one := hC.right_one
  right_assoc := hC.right_assoc
  right_memGrade := by
    intro a b i j m x hm hx
    have h := hC.right_memGrade a b (i + shiftNu n a b) j m x hm hx
    simpa only [shiftCData, CData.MemGrade, add_assoc, add_comm,
      add_left_comm] using h
  actions_comm := by
    intro a b x y m z
    exact hC.actions_comm a b
      (routeRowTwist dD a (shiftNu n a b) x)
      (routeRowTwist dD b (shiftNu n a b) y) m z

/-! ### Binary coefficient consequences -/

private theorem rawMulZero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    d.mul x d.zero = d.zero := by
  letI := rawAddCommGroup d h
  let v := d.mul x d.zero
  have hm := h.mul_add x d.zero d.zero
  rw [h.zero_add] at hm
  change v = d.add v v at hm
  apply add_left_cancel (a := v)
  change d.add v v = d.add v d.zero
  rw [← hm, h.add_zero]

private theorem rawFinSum_mul_single (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {m : ℕ} (source : Fin m)
    (f : Fin m → d.carrier) :
    CData.rawFinSum d (fun r =>
      d.mul (f r) (if r = source then d.one else d.zero)) = f source := by
  letI := rawAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn fun r =>
    d.mul (f r) (if r = source then d.one else d.zero)).sum = f source
  rw [List.sum_ofFn]
  classical
  simp only [apply_ite, rawMulZero d h, h.mul_one]
  change (∑ x, if x = source then f x else (0 : d.carrier)) = f source
  simp

private theorem rawFinSum_smul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {m : ℕ} (q : ℝ) (f : Fin m → d.carrier) :
    CData.rawFinSum d (fun i => d.smul q (f i)) =
      d.smul q (CData.rawFinSum d f) := by
  letI := rawAddCommGroup d h
  letI := rawModule d h
  unfold CData.rawFinSum
  change (List.ofFn (fun i => q • f i)).sum = q • (List.ofFn f).sum
  rw [List.sum_ofFn, List.sum_ofFn, Finset.smul_sum]

private theorem frameMulCancel (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (targetBit sourceBit : ZMod 2)
    (x y : d.carrier) :
    d.mul
        (d.smul (paritySign targetBit * paritySign sourceBit) x)
        (d.smul (paritySign sourceBit) y) =
      d.smul (paritySign targetBit) (d.mul x y) := by
  rw [h.smul_mul, h.mul_smul, ← h.smul_assoc]
  congr 1
  rw [mul_assoc, shiftParitySign_mul_self, mul_one]

/-- In a two-stage coordinate sum, the source-frame sign occurs once in
the action coefficient and once in the coordinate.  These two copies
cancel, leaving only the target-frame sign outside the whole sum. -/
private theorem framedDoubleSum (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {m n : ℕ} (targetBit : ZMod 2)
    (sourceBit : Fin m → ZMod 2) (coeff coord : Fin m → Fin n → d.carrier) :
    CData.rawFinSum d (fun sourceOuter =>
        CData.rawFinSum d (fun sourceInner =>
          d.mul
            (d.smul
              (paritySign targetBit * paritySign (sourceBit sourceOuter))
              (coeff sourceOuter sourceInner))
            (d.smul (paritySign (sourceBit sourceOuter))
              (coord sourceOuter sourceInner)))) =
      d.smul (paritySign targetBit)
        (CData.rawFinSum d (fun sourceOuter =>
          CData.rawFinSum d (fun sourceInner =>
            d.mul (coeff sourceOuter sourceInner)
              (coord sourceOuter sourceInner)))) := by
  calc
    _ = CData.rawFinSum d (fun sourceOuter =>
          CData.rawFinSum d (fun sourceInner =>
            d.smul (paritySign targetBit)
              (d.mul (coeff sourceOuter sourceInner)
                (coord sourceOuter sourceInner)))) := by
      congr 1
      funext sourceOuter
      congr 1
      funext sourceInner
      exact frameMulCancel d h targetBit (sourceBit sourceOuter)
        (coeff sourceOuter sourceInner) (coord sourceOuter sourceInner)
    _ = CData.rawFinSum d (fun sourceOuter =>
          d.smul (paritySign targetBit)
            (CData.rawFinSum d (fun sourceInner =>
              d.mul (coeff sourceOuter sourceInner)
                (coord sourceOuter sourceInner)))) := by
      congr 1
      funext sourceOuter
      exact rawFinSum_smul d h _ _
    _ = _ := rawFinSum_smul d h _ _

/-- A coordinate vector supported at one fusion row with coefficient one. -/
private def kernelRowBasis (dD : DData) (dC : CData dD)
    (a b : ZMod 8) (source : dC.Index a b) : dC.carrier a b :=
  dC.ofCoord a b fun r =>
    if r = source then (dD.algebra (a + b)).one
    else (dD.algebra (a + b)).zero

private theorem cToCoord_injective (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (a b : ZMod 8) :
    Function.Injective (dC.toCoord a b) := by
  intro x y hxy
  rw [← hC.ofCoord_toCoord a b x, ← hC.ofCoord_toCoord a b y, hxy]

private theorem kernelRowBasis_toCoord (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (source : dC.Index a b) :
    dC.toCoord a b (kernelRowBasis dD dC a b source) = fun r =>
      if r = source then (dD.algebra (a + b)).one
      else (dD.algebra (a + b)).zero := by
  exact hC.toCoord_ofCoord a b _

private theorem kernelRowBasis_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (source : dC.Index a b) :
    dC.MemGrade a b (dC.rowParity a b source)
      (kernelRowBasis dD dC a b source) := by
  unfold CData.MemGrade
  apply cToCoord_injective dD hD dC hC a b
  rw [hC.toCoord_component,
    kernelRowBasis_toCoord dD hD dC hC]
  funext r
  by_cases hr : r = source
  · subst r
    simp only [ite_true, shiftZMod2_add_self]
    exact (hD.algebra_laws (a + b)).one_mem
  · simp only [hr, ite_false]
    exact (hD.algebra_laws (a + b)).component_zero _

private theorem leftCoeff_on_rowBasis (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.toCoord a b
        (dC.left a b x y (kernelRowBasis dD dC a b source)) target =
      dC.leftCoeff a b target source x y := by
  rw [hC.toCoord_left,
    kernelRowBasis_toCoord dD hD dC hC]
  exact rawFinSum_mul_single (dD.algebra (a + b))
    (hD.algebra_laws (a + b)) source
    (fun r => dC.leftCoeff a b target r x y)

/-- Every binary action coefficient has the degree forced by its source and
target fusion rows. -/
theorem leftCoeff_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (i j : ZMod 2) (x : (dD.algebra a).carrier)
    (y : (dD.algebra b).carrier)
    (hx : (dD.algebra a).MemGrade i x)
    (hy : (dD.algebra b).MemGrade j y) :
    (dD.algebra (a + b)).MemGrade
      (i + j + dC.rowParity a b source + dC.rowParity a b target)
      (dC.leftCoeff a b target source x y) := by
  let m := kernelRowBasis dD dC a b source
  have hm : dC.MemGrade a b (dC.rowParity a b source) m :=
    kernelRowBasis_memGrade dD hD dC hC a b source
  have hout := hC.left_memGrade a b i j (dC.rowParity a b source)
    x y m hx hy hm
  have hcoord := congrArg
    (fun q => dC.toCoord a b q target) hout
  rw [hC.toCoord_component] at hcoord
  change (dD.algebra (a + b)).component
      (i + j + dC.rowParity a b source + dC.rowParity a b target)
      (dC.toCoord a b (dC.left a b x y m) target) =
    dC.toCoord a b (dC.left a b x y m) target at hcoord
  rw [leftCoeff_on_rowBasis dD hD dC hC] at hcoord
  exact hcoord

private theorem leftCoeff_add_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x x' : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).add x x') y =
      (dD.algebra (a + b)).add
        (dC.leftCoeff a b target source x y)
        (dC.leftCoeff a b target source x' y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_add_left a b x x' y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_add] at h
  change dC.leftCoeff a b target source ((dD.algebra a).add x x') y =
    (dD.algebra (a + b)).add
      (dC.toCoord a b (dC.left a b x y m) target)
      (dC.toCoord a b (dC.left a b x' y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC,
    leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_add_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x : (dD.algebra a).carrier) (y y' : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source x ((dD.algebra b).add y y') =
      (dD.algebra (a + b)).add
        (dC.leftCoeff a b target source x y)
        (dC.leftCoeff a b target source x y') := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_add_right a b x y y' m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_add] at h
  change dC.leftCoeff a b target source x ((dD.algebra b).add y y') =
    (dD.algebra (a + b)).add
      (dC.toCoord a b (dC.left a b x y m) target)
      (dC.toCoord a b (dC.left a b x y' m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC,
    leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_smul_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b) (q : ℝ)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).smul q x) y =
      (dD.algebra (a + b)).smul q
        (dC.leftCoeff a b target source x y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun z => dC.toCoord a b z target)
    (hC.left_smul_left a b q x y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_smul] at h
  change dC.leftCoeff a b target source ((dD.algebra a).smul q x) y =
    (dD.algebra (a + b)).smul q
      (dC.toCoord a b (dC.left a b x y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_smul_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b) (q : ℝ)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source x ((dD.algebra b).smul q y) =
      (dD.algebra (a + b)).smul q
        (dC.leftCoeff a b target source x y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun z => dC.toCoord a b z target)
    (hC.left_smul_right a b q x y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_smul] at h
  change dC.leftCoeff a b target source x ((dD.algebra b).smul q y) =
    (dD.algebra (a + b)).smul q
      (dC.toCoord a b (dC.left a b x y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_twist_of_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (p i j : ZMod 2) (x : (dD.algebra a).carrier)
    (y : (dD.algebra b).carrier)
    (hx : (dD.algebra a).MemGrade i x)
    (hy : (dD.algebra b).MemGrade j y) :
    routeRowTwist dD (a + b) p (dC.leftCoeff a b target source x y) =
      (dD.algebra (a + b)).smul
        (paritySign
          (p * (dC.rowParity a b source + dC.rowParity a b target)))
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x) (routeRowTwist dD b p y)) := by
  have hc := leftCoeff_memGrade dD hD dC hC a b target source i j x y hx hy
  rw [routeRowTwist_of_memGrade_at dD hD (a + b) p
      (i + j + dC.rowParity a b source + dC.rowParity a b target) _ hc,
    routeRowTwist_of_memGrade_at dD hD a p i x hx,
    routeRowTwist_of_memGrade_at dD hD b p j y hy,
    leftCoeff_smul_left dD hD dC hC,
    leftCoeff_smul_right dD hD dC hC,
    ← (hD.algebra_laws (a + b)).smul_assoc,
    ← (hD.algebra_laws (a + b)).smul_assoc]
  congr 1
  rw [show p *
        (i + j + dC.rowParity a b source + dC.rowParity a b target) =
      p * (dC.rowParity a b source + dC.rowParity a b target) +
        p * i + p * j by ring]
  rw [shiftParitySign_add, shiftParitySign_add]

private theorem leftCoeff_twist_homogeneous_left (dD : DData)
    (hD : DLaws dD) (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (y : (dD.algebra b).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    routeRowTwist dD (a + b) p (dC.leftCoeff a b target source x y) =
      (dD.algebra (a + b)).smul
        (paritySign
          (p * (dC.rowParity a b source + dC.rowParity a b target)))
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x) (routeRowTwist dD b p y)) := by
  let y0 := (dD.algebra b).component 0 y
  let y1 := (dD.algebra b).component 1 y
  have hy0 : (dD.algebra b).MemGrade 0 y0 :=
    (hD.algebra_laws b).component_idem 0 y
  have hy1 : (dD.algebra b).MemGrade 1 y1 :=
    (hD.algebra_laws b).component_idem 1 y
  have hy : (dD.algebra b).add y0 y1 = y :=
    (hD.algebra_laws b).component_complement 0 y
  let rowSign := paritySign
    (p * (dC.rowParity a b source + dC.rowParity a b target))
  calc
    routeRowTwist dD (a + b) p (dC.leftCoeff a b target source x y) =
        routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source x ((dD.algebra b).add y0 y1)) := by
      rw [hy]
    _ = routeRowTwist dD (a + b) p
        ((dD.algebra (a + b)).add
          (dC.leftCoeff a b target source x y0)
          (dC.leftCoeff a b target source x y1)) := by
      rw [leftCoeff_add_right dD hD dC hC]
    _ = (dD.algebra (a + b)).add
        (routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source x y0))
        (routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source x y1)) := by
      rw [routeRowTwist_add_at dD hD]
    _ = (dD.algebra (a + b)).add
        ((dD.algebra (a + b)).smul rowSign
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x) (routeRowTwist dD b p y0)))
        ((dD.algebra (a + b)).smul rowSign
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x) (routeRowTwist dD b p y1))) := by
      rw [leftCoeff_twist_of_memGrade dD hD dC hC
          a b target source p i 0 x y0 hx hy0,
        leftCoeff_twist_of_memGrade dD hD dC hC
          a b target source p i 1 x y1 hx hy1]
    _ = (dD.algebra (a + b)).smul rowSign
        ((dD.algebra (a + b)).add
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x) (routeRowTwist dD b p y0))
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x) (routeRowTwist dD b p y1))) := by
      rw [(hD.algebra_laws (a + b)).smul_add]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x)
          ((dD.algebra b).add
            (routeRowTwist dD b p y0) (routeRowTwist dD b p y1))) := by
      rw [leftCoeff_add_right dD hD dC hC]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x)
          (routeRowTwist dD b p ((dD.algebra b).add y0 y1))) := by
      rw [routeRowTwist_add_at dD hD]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x) (routeRowTwist dD b p y)) := by
      rw [hy]

/-- Parity twist covariance of every binary action coefficient. -/
theorem leftCoeff_twist (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (p : ZMod 2) (x : (dD.algebra a).carrier)
    (y : (dD.algebra b).carrier) :
    routeRowTwist dD (a + b) p (dC.leftCoeff a b target source x y) =
      (dD.algebra (a + b)).smul
        (paritySign
          (p * (dC.rowParity a b source + dC.rowParity a b target)))
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x) (routeRowTwist dD b p y)) := by
  let x0 := (dD.algebra a).component 0 x
  let x1 := (dD.algebra a).component 1 x
  have hx0 : (dD.algebra a).MemGrade 0 x0 :=
    (hD.algebra_laws a).component_idem 0 x
  have hx1 : (dD.algebra a).MemGrade 1 x1 :=
    (hD.algebra_laws a).component_idem 1 x
  have hx : (dD.algebra a).add x0 x1 = x :=
    (hD.algebra_laws a).component_complement 0 x
  let rowSign := paritySign
    (p * (dC.rowParity a b source + dC.rowParity a b target))
  calc
    routeRowTwist dD (a + b) p (dC.leftCoeff a b target source x y) =
        routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source ((dD.algebra a).add x0 x1) y) := by
      rw [hx]
    _ = routeRowTwist dD (a + b) p
        ((dD.algebra (a + b)).add
          (dC.leftCoeff a b target source x0 y)
          (dC.leftCoeff a b target source x1 y)) := by
      rw [leftCoeff_add_left dD hD dC hC]
    _ = (dD.algebra (a + b)).add
        (routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source x0 y))
        (routeRowTwist dD (a + b) p
          (dC.leftCoeff a b target source x1 y)) := by
      rw [routeRowTwist_add_at dD hD]
    _ = (dD.algebra (a + b)).add
        ((dD.algebra (a + b)).smul rowSign
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x0) (routeRowTwist dD b p y)))
        ((dD.algebra (a + b)).smul rowSign
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x1) (routeRowTwist dD b p y))) := by
      rw [leftCoeff_twist_homogeneous_left dD hD dC hC
          a b target source p 0 x0 y hx0,
        leftCoeff_twist_homogeneous_left dD hD dC hC
          a b target source p 1 x1 y hx1]
    _ = (dD.algebra (a + b)).smul rowSign
        ((dD.algebra (a + b)).add
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x0) (routeRowTwist dD b p y))
          (dC.leftCoeff a b target source
            (routeRowTwist dD a p x1) (routeRowTwist dD b p y))) := by
      rw [(hD.algebra_laws (a + b)).smul_add]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          ((dD.algebra a).add
            (routeRowTwist dD a p x0) (routeRowTwist dD a p x1))
          (routeRowTwist dD b p y)) := by
      rw [leftCoeff_add_left dD hD dC hC]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p ((dD.algebra a).add x0 x1))
          (routeRowTwist dD b p y)) := by
      rw [routeRowTwist_add_at dD hD]
    _ = (dD.algebra (a + b)).smul rowSign
        (dC.leftCoeff a b target source
          (routeRowTwist dD a p x) (routeRowTwist dD b p y)) := by
      rw [hx]

/-! ## Overall shifts of ternary route data -/

/-- Shift a ternary route by a label-dependent parity.

This is the raw-data version of shifting a graded bimodule: only the
grading and parity-twisted left action change. -/
def shiftTripleRouteData (dD : DData) (dR : TripleRouteData dD)
    (s : ZMod 8 → ZMod 8 → ZMod 8 → ZMod 2) : TripleRouteData dD where
  carrier := dR.carrier
  zero := dR.zero
  add := dR.add
  neg := dR.neg
  smul := dR.smul
  component a b c i m := dR.component a b c (i + s a b c) m
  leftPure a b c x y z m :=
    dR.leftPure a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  right := dR.right

/-- Overall parity shifts preserve all abstract ternary-route laws. -/
theorem shiftTripleRouteLaws (dD : DData) (hD : DLaws dD)
    (dR : TripleRouteData dD) (hR : TripleRouteLaws dD hD dR)
    (s : ZMod 8 → ZMod 8 → ZMod 8 → ZMod 2) :
    TripleRouteLaws dD hD (shiftTripleRouteData dD dR s) where
  add_assoc := hR.add_assoc
  add_comm := hR.add_comm
  zero_add := hR.zero_add
  add_zero := hR.add_zero
  neg_add := hR.neg_add
  add_neg := hR.add_neg
  one_smul := hR.one_smul
  smul_assoc := hR.smul_assoc
  add_smul := hR.add_smul
  smul_add := hR.smul_add
  zero_smul := hR.zero_smul
  smul_zero := hR.smul_zero
  component_zero := by
    intro a b c i
    exact hR.component_zero a b c (i + s a b c)
  component_add := by
    intro a b c i x y
    exact hR.component_add a b c (i + s a b c) x y
  component_neg := by
    intro a b c i x
    exact hR.component_neg a b c (i + s a b c) x
  component_smul := by
    intro a b c i r x
    exact hR.component_smul a b c (i + s a b c) r x
  component_idem := by
    intro a b c i x
    exact hR.component_idem a b c (i + s a b c) x
  component_complement := by
    intro a b c i x
    simpa only [shiftTripleRouteData, add_assoc, add_comm, add_left_comm] using
      hR.component_complement a b c (i + s a b c) x
  grade_disjoint := by
    intro a b c i x hi hi1
    apply hR.grade_disjoint a b c (i + s a b c) x hi
    simpa only [shiftTripleRouteData, TripleRouteData.MemGrade, add_assoc,
      add_comm, add_left_comm] using hi1
  left_zero_first := by
    intro a b c y z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_zero_at dD hD a (s a b c)]
    exact hR.left_zero_first a b c
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_zero_second := by
    intro a b c x z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_zero_at dD hD b (s a b c)]
    exact hR.left_zero_second a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD c (s a b c) z) m
  left_zero_third := by
    intro a b c x y m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_zero_at dD hD c (s a b c)]
    exact hR.left_zero_third a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y) m
  left_zero_module := by
    intro a b c x y z
    exact hR.left_zero_module a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z)
  left_add_first := by
    intro a b c x x' y z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_add_at dD hD a (s a b c)]
    exact hR.left_add_first a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD a (s a b c) x')
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_add_second := by
    intro a b c x y y' z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_add_at dD hD b (s a b c)]
    exact hR.left_add_second a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD b (s a b c) y')
      (routeRowTwist dD c (s a b c) z) m
  left_add_third := by
    intro a b c x y z z' m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_add_at dD hD c (s a b c)]
    exact hR.left_add_third a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z)
      (routeRowTwist dD c (s a b c) z') m
  left_add_module := by
    intro a b c x y z m m'
    exact hR.left_add_module a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m m'
  left_smul_first := by
    intro a b c r x y z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_smul_at dD hD a (s a b c)]
    exact hR.left_smul_first a b c r
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_smul_second := by
    intro a b c r x y z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_smul_at dD hD b (s a b c)]
    exact hR.left_smul_second a b c r
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_smul_third := by
    intro a b c r x y z m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_smul_at dD hD c (s a b c)]
    exact hR.left_smul_third a b c r
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_smul_module := by
    intro a b c r x y z m
    exact hR.left_smul_module a b c r
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m
  left_one := by
    intro a b c m
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_one_at dD hD a (s a b c),
      routeRowTwist_one_at dD hD b (s a b c),
      routeRowTwist_one_at dD hD c (s a b c)]
    exact hR.left_one a b c m
  left_mul := by
    intro a b c i' j k j' x x' y y' z z' m hy hz hx' hy'
    have hyT := routeRowTwist_memGrade_at dD hD b (s a b c) j y hy
    have hzT := routeRowTwist_memGrade_at dD hD c (s a b c) k z hz
    have hxT := routeRowTwist_memGrade_at dD hD a (s a b c) i' x' hx'
    have hyT' := routeRowTwist_memGrade_at dD hD b (s a b c) j' y' hy'
    simp only [shiftTripleRouteData]
    rw [routeRowTwist_mul_at dD hD a (s a b c),
      routeRowTwist_mul_at dD hD b (s a b c),
      routeRowTwist_mul_at dD hD c (s a b c)]
    exact hR.left_mul a b c i' j k j'
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD a (s a b c) x')
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD b (s a b c) y')
      (routeRowTwist dD c (s a b c) z)
      (routeRowTwist dD c (s a b c) z') m hyT hzT hxT hyT'
  left_memGrade := by
    intro a b c i j k l x y z m hx hy hz hm
    have hxT := routeRowTwist_memGrade_at dD hD a (s a b c) i x hx
    have hyT := routeRowTwist_memGrade_at dD hD b (s a b c) j y hy
    have hzT := routeRowTwist_memGrade_at dD hD c (s a b c) k z hz
    have h := hR.left_memGrade a b c i j k (l + s a b c)
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m hxT hyT hzT hm
    simpa only [shiftTripleRouteData, TripleRouteData.MemGrade, add_assoc,
      add_comm, add_left_comm] using h
  right_zero_module := hR.right_zero_module
  right_zero_algebra := hR.right_zero_algebra
  right_add_module := hR.right_add_module
  right_add_algebra := hR.right_add_algebra
  right_smul_module := hR.right_smul_module
  right_smul_algebra := hR.right_smul_algebra
  right_one := hR.right_one
  right_assoc := hR.right_assoc
  right_memGrade := by
    intro a b c i j m x hm hx
    have h := hR.right_memGrade a b c (i + s a b c) j m x hm hx
    simpa only [shiftTripleRouteData, TripleRouteData.MemGrade, add_assoc,
      add_comm, add_left_comm] using h
  actions_comm := by
    intro a b c x y z m q
    exact hR.actions_comm a b c
      (routeRowTwist dD a (s a b c) x)
      (routeRowTwist dD b (s a b c) y)
      (routeRowTwist dD c (s a b c) z) m q

private theorem algebra_smul_neg (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (q : ℝ) (x : d.carrier) :
    d.smul q (d.neg x) = d.neg (d.smul q x) := by
  letI := rawAddCommGroup d h
  letI := rawModule d h
  change q • (-x) = -(q • x)
  exact smul_neg q x

private theorem tripleRoute_smul_neg (dD : DData) (hD : DLaws dD)
    (dR : TripleRouteData dD) (hR : TripleRouteLaws dD hD dR)
    (a b c : ZMod 8) (q : ℝ) (x : dR.carrier a b c) :
    dR.smul a b c q (dR.neg a b c x) =
      dR.neg a b c (dR.smul a b c q x) := by
  letI : Zero (dR.carrier a b c) := ⟨dR.zero a b c⟩
  letI : Add (dR.carrier a b c) := ⟨dR.add a b c⟩
  letI : Neg (dR.carrier a b c) := ⟨dR.neg a b c⟩
  letI : Sub (dR.carrier a b c) :=
    ⟨fun u v => dR.add a b c u (dR.neg a b c v)⟩
  letI : SMul ℝ (dR.carrier a b c) := ⟨dR.smul a b c⟩
  letI : AddCommGroup (dR.carrier a b c) :=
    { add_assoc := hR.add_assoc a b c
      zero_add := hR.zero_add a b c
      add_zero := hR.add_zero a b c
      neg_add_cancel := hR.neg_add a b c
      add_comm := hR.add_comm a b c
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }
  letI : Module ℝ (dR.carrier a b c) :=
    { one_smul := hR.one_smul a b c
      mul_smul := hR.smul_assoc a b c
      smul_add := hR.smul_add a b c
      smul_zero := hR.smul_zero a b c
      add_smul := hR.add_smul a b c
      zero_smul := hR.zero_smul a b c }
  change q • (-x) = -(q • x)
  exact smul_neg q x

private theorem tripleLeftPure_twist_of_memGrade (dD : DData)
    (hD : DLaws dD) (dR : TripleRouteData dD)
    (hR : TripleRouteLaws dD hD dR)
    (a b c : ZMod 8) (s i j k : ZMod 2)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) (m : dR.carrier a b c)
    (hx : (dD.algebra a).MemGrade i x)
    (hy : (dD.algebra b).MemGrade j y)
    (hz : (dD.algebra c).MemGrade k z) :
    dR.leftPure a b c (routeRowTwist dD a s x)
        (routeRowTwist dD b s y) (routeRowTwist dD c s z) m =
      dR.smul a b c (paritySign (s * (i + j + k)))
        (dR.leftPure a b c x y z m) := by
  rw [routeRowTwist_of_memGrade_at dD hD a s i x hx,
    routeRowTwist_of_memGrade_at dD hD b s j y hy,
    routeRowTwist_of_memGrade_at dD hD c s k z hz,
    hR.left_smul_first, hR.left_smul_second, hR.left_smul_third,
    ← hR.smul_assoc, ← hR.smul_assoc]
  congr 1
  rw [show s * (i + j + k) = s * i + s * j + s * k by ring,
    shiftParitySign_add, shiftParitySign_add]

/-- The two route regradings transport the old connector sign to the new
connector degree.  The right-route twist appears on both sides and hence
cancels in characteristic two. -/
private theorem shiftedConnectorSign (p sLeft sRight i : ZMod 2) :
    paritySign (sLeft * i) * paritySign (p * i) =
      paritySign ((p + sLeft + sRight) * i) *
        paritySign (sRight * i) := by
  rw [← shiftParitySign_add, ← shiftParitySign_add]
  congr 1
  rw [add_mul, add_mul]
  calc
    sLeft * i + p * i = p * i + sLeft * i := add_comm _ _
    _ = (p * i + sLeft * i) + 0 := (add_zero _).symm
    _ = (p * i + sLeft * i) + (sRight * i + sRight * i) := by
      rw [shiftZMod2_add_self]
    _ = p * i + sLeft * i + sRight * i + sRight * i := by
      ac_rfl

private theorem shiftedConnectorSign_symm (p sLeft sRight i : ZMod 2) :
    paritySign (sRight * i) * paritySign (p * i) =
      paritySign ((p + sLeft + sRight) * i) *
        paritySign (sLeft * i) := by
  simpa only [add_assoc, add_comm, add_left_comm] using
    shiftedConnectorSign p sRight sLeft i

private theorem shiftedHomIndex (i p sLeft sRight : ZMod 2) :
    i + sLeft + p = i + (p + sLeft + sRight) + sRight := by
  calc
    i + sLeft + p = (i + p + sLeft) + 0 := by ac_rfl
    _ = (i + p + sLeft) + (sRight + sRight) := by
      rw [shiftZMod2_add_self]
    _ = i + (p + sLeft + sRight) + sRight := by ac_rfl

private theorem shiftedInvIndex (i p sLeft sRight : ZMod 2) :
    i + sRight + p = i + (p + sLeft + sRight) + sLeft := by
  calc
    i + sRight + p = (i + p + sRight) + 0 := by ac_rfl
    _ = (i + p + sRight) + (sLeft + sLeft) := by
      rw [shiftZMod2_add_self]
    _ = i + (p + sLeft + sRight) + sLeft := by ac_rfl

/-! ## Shifted ternary coordinate frames -/

/-- The left-route comparison sign.  Only the inner `(a,b)` fusion row
crosses the shift of the outer `(a+b,c)` kernel. -/
def leftRouteFrameSign {dD : DData} (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8) (r : dC.Index a b) : ℝ :=
  paritySign (shiftNu n (a + b) c * dC.rowParity a b r)

/-- The right-route comparison sign.  Only the inner `(b,c)` fusion row
crosses the shift of the outer `(a,b+c)` kernel. -/
def rightRouteFrameSign {dD : DData} (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8) (r : dC.Index b c) : ℝ :=
  paritySign (shiftNu n a (b + c) * dC.rowParity b c r)

/-- Change left-route coordinates by the diagonal raw-to-shifted frame
comparison.  The same map is its inverse. -/
def leftRouteFrame (dD : DData) (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8) (q : LeftRouteCoordinates dC a b c) :
    LeftRouteCoordinates (shiftCData dD dC n) a b c :=
  fun r s => (dD.algebra (a + b + c)).smul
    (leftRouteFrameSign dC n a b c r) (q r s)

/-- The inverse left-route frame comparison.  It has the same pointwise
formula because every parity sign squares to one. -/
def leftRouteFrameInv (dD : DData) (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8)
    (q : LeftRouteCoordinates (shiftCData dD dC n) a b c) :
    LeftRouteCoordinates dC a b c :=
  fun r s => (dD.algebra (a + b + c)).smul
    (leftRouteFrameSign dC n a b c r) (q r s)

/-- Change right-route coordinates by the diagonal raw-to-shifted frame
comparison.  The same map is its inverse. -/
def rightRouteFrame (dD : DData) (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8) (q : RightRouteCoordinates dC a b c) :
    RightRouteCoordinates (shiftCData dD dC n) a b c :=
  fun r s => (dD.algebra (a + b + c)).smul
    (rightRouteFrameSign dC n a b c r) (q r s)

/-- The inverse right-route frame comparison.  It has the same pointwise
formula because every parity sign squares to one. -/
def rightRouteFrameInv (dD : DData) (dC : CData dD) (n : NuBetaData)
    (a b c : ZMod 8)
    (q : RightRouteCoordinates (shiftCData dD dC n) a b c) :
    RightRouteCoordinates dC a b c :=
  fun r s => (dD.algebra (a + b + c)).smul
    (rightRouteFrameSign dC n a b c r) (q r s)

/-! ### The diagonal frame comparisons are involutions -/

theorem leftRouteFrameInv_frame (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (n : NuBetaData) (a b c : ZMod 8)
    (q : LeftRouteCoordinates dC a b c) :
    leftRouteFrameInv dD dC n a b c
      (leftRouteFrame dD dC n a b c q) = q := by
  funext r s
  unfold leftRouteFrameInv leftRouteFrame leftRouteFrameSign
  rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
    shiftParitySign_mul_self,
    (hD.algebra_laws (a + b + c)).one_smul]

theorem leftRouteFrame_frameInv (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (n : NuBetaData) (a b c : ZMod 8)
    (q : LeftRouteCoordinates (shiftCData dD dC n) a b c) :
    leftRouteFrame dD dC n a b c
      (leftRouteFrameInv dD dC n a b c q) = q := by
  funext r s
  unfold leftRouteFrameInv leftRouteFrame leftRouteFrameSign
  rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
    shiftParitySign_mul_self,
    (hD.algebra_laws (a + b + c)).one_smul]

theorem rightRouteFrameInv_frame (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (n : NuBetaData) (a b c : ZMod 8)
    (q : RightRouteCoordinates dC a b c) :
    rightRouteFrameInv dD dC n a b c
      (rightRouteFrame dD dC n a b c q) = q := by
  funext r s
  unfold rightRouteFrameInv rightRouteFrame rightRouteFrameSign
  rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
    shiftParitySign_mul_self,
    (hD.algebra_laws (a + b + c)).one_smul]

theorem rightRouteFrame_frameInv (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (n : NuBetaData) (a b c : ZMod 8)
    (q : RightRouteCoordinates (shiftCData dD dC n) a b c) :
    rightRouteFrame dD dC n a b c
      (rightRouteFrameInv dD dC n a b c q) = q := by
  funext r s
  unfold rightRouteFrameInv rightRouteFrame rightRouteFrameSign
  rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
    shiftParitySign_mul_self,
    (hD.algebra_laws (a + b + c)).one_smul]

/-! ### Route coefficients in the shifted frames -/

private theorem leftRouteCoeff_shift (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (n : NuBetaData)
    (a b c : ZMod 8)
    (targetAB : dC.Index a b) (targetABC : dC.Index (a + b) c)
    (sourceAB : dC.Index a b) (sourceABC : dC.Index (a + b) c)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) :
    leftRouteCoeff (shiftCData dD dC n) a b c
        targetAB targetABC sourceAB sourceABC x y z =
      (dD.algebra (a + b + c)).smul
        (leftRouteFrameSign dC n a b c targetAB *
          leftRouteFrameSign dC n a b c sourceAB)
        (leftRouteCoeff dC a b c targetAB targetABC sourceAB sourceABC
          (routeRowTwist dD a (leftRouteShift n a b c) x)
          (routeRowTwist dD b (leftRouteShift n a b c) y)
          (routeRowTwist dD c (leftRouteShift n a b c) z)) := by
  let nAB := shiftNu n a b
  let u := shiftNu n (a + b) c
  have hinner := leftCoeff_twist dD hD dC hC a b targetAB sourceAB u
    (routeRowTwist dD a nAB x) (routeRowTwist dD b nAB y)
  unfold leftRouteCoeff shiftCData
  change dC.leftCoeff (a + b) c targetABC sourceABC
      (routeRowTwist dD (a + b) u
        (dC.leftCoeff a b targetAB sourceAB
          (routeRowTwist dD a nAB x) (routeRowTwist dD b nAB y)))
      (routeRowTwist dD c u
        (routeRowTwist dD c (dC.rowParity a b sourceAB + nAB) z)) = _
  rw [hinner,
    leftCoeff_smul_left dD hD dC hC,
    routeRowTwist_compose_at dD hD a,
    routeRowTwist_compose_at dD hD b,
    routeRowTwist_compose_at dD hD c]
  rw [show u + nAB = leftRouteShift n a b c by
      simp only [leftRouteShift, nAB, u]; ac_rfl]
  rw [show u + (dC.rowParity a b sourceAB + nAB) =
      dC.rowParity a b sourceAB + leftRouteShift n a b c by
      simp only [leftRouteShift, nAB, u]; ac_rfl]
  rw [← routeRowTwist_compose_at dD hD c]
  unfold leftRouteFrameSign
  rw [shiftParitySign_mul]
  congr 1
  rw [mul_comm u (dC.rowParity a b sourceAB),
    mul_comm u (dC.rowParity a b targetAB)]
  ring

private theorem castAlgebra_smul (dD : DData) {u v : ZMod 8}
    (e : u = v) (q : ℝ) (x : (dD.algebra u).carrier) :
    cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) e)
        ((dD.algebra u).smul q x) =
      (dD.algebra v).smul q
        (cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) e) x) := by
  cases e
  rfl

private theorem routeCastAssoc_smul (dD : DData) (a b c : ZMod 8)
    (q : ℝ) (x : (dD.algebra (a + (b + c))).carrier) :
    routeCastAssoc dD a b c ((dD.algebra (a + (b + c))).smul q x) =
      (dD.algebra (a + b + c)).smul q (routeCastAssoc dD a b c x) :=
  castAlgebra_smul dD (_root_.add_assoc a b c).symm q x

private theorem rightRouteCoeff_shift (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (n : NuBetaData)
    (a b c : ZMod 8)
    (targetBC : dC.Index b c) (targetABC : dC.Index a (b + c))
    (sourceBC : dC.Index b c) (sourceABC : dC.Index a (b + c))
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) :
    rightRouteCoeff (shiftCData dD dC n) a b c
        targetBC targetABC sourceBC sourceABC x y z =
      (dD.algebra (a + b + c)).smul
        (rightRouteFrameSign dC n a b c targetBC *
          rightRouteFrameSign dC n a b c sourceBC)
        (rightRouteCoeff dC a b c targetBC targetABC sourceBC sourceABC
          (routeRowTwist dD a (rightRouteShift n a b c) x)
          (routeRowTwist dD b (rightRouteShift n a b c) y)
          (routeRowTwist dD c (rightRouteShift n a b c) z)) := by
  let nBC := shiftNu n b c
  let u := shiftNu n a (b + c)
  have hinner := leftCoeff_twist dD hD dC hC b c targetBC sourceBC u
    (routeRowTwist dD b nBC y) (routeRowTwist dD c nBC z)
  unfold rightRouteCoeff shiftCData
  change routeCastAssoc dD a b c
    (dC.leftCoeff a (b + c) targetABC sourceABC
      (routeRowTwist dD a u
        (routeRowTwist dD a (dC.rowParity b c targetBC + nBC) x))
      (routeRowTwist dD (b + c) u
        (dC.leftCoeff b c targetBC sourceBC
          (routeRowTwist dD b nBC y) (routeRowTwist dD c nBC z)))) = _
  rw [hinner,
    leftCoeff_smul_right dD hD dC hC,
    routeCastAssoc_smul,
    routeRowTwist_compose_at dD hD a,
    routeRowTwist_compose_at dD hD b,
    routeRowTwist_compose_at dD hD c]
  rw [show u + nBC = rightRouteShift n a b c by
      simp only [rightRouteShift, nBC, u]; ac_rfl]
  rw [show u + (dC.rowParity b c targetBC + nBC) =
      dC.rowParity b c targetBC + rightRouteShift n a b c by
      simp only [rightRouteShift, nBC, u]; ac_rfl]
  rw [← routeRowTwist_compose_at dD hD a]
  unfold rightRouteFrameSign
  rw [shiftParitySign_mul]
  congr 1
  rw [mul_comm u (dC.rowParity b c sourceBC),
    mul_comm u (dC.rowParity b c targetBC)]
  ring

/-! ## Shifted connector data -/

/-- Shift and rescale a raw ternary connector.

The route comparison signs are carried by `leftToCoord` and
`rightToCoord`; they must not be inserted a second time in `hom` or `inv`.
Thus the carrier maps are simply the old connector scaled by `beta⁻¹` and
its old inverse scaled by `beta`. -/
def shiftTData (dD : DData) (dC : CData dD) (dT : TData dD dC)
    (n : NuBetaData) : TData dD (shiftCData dD dC n) where
  leftRoute := shiftTripleRouteData dD dT.leftRoute (leftRouteShift n)
  rightRoute := shiftTripleRouteData dD dT.rightRoute (rightRouteShift n)
  leftToCoord a b c m :=
    leftRouteFrame dD dC n a b c (dT.leftToCoord a b c m)
  leftOfCoord a b c q :=
    dT.leftOfCoord a b c (leftRouteFrameInv dD dC n a b c q)
  rightToCoord a b c m :=
    rightRouteFrame dD dC n a b c (dT.rightToCoord a b c m)
  rightOfCoord a b c q :=
    dT.rightOfCoord a b c (rightRouteFrameInv dD dC n a b c q)
  parity a b c :=
    dT.parity a b c + leftRouteShift n a b c + rightRouteShift n a b c
  hom a b c m :=
    dT.rightRoute.smul a b c (↑(shiftBeta n a b c)⁻¹ : ℝ)
      (dT.hom a b c m)
  inv a b c m :=
    dT.leftRoute.smul a b c (↑(shiftBeta n a b c) : ℝ)
      (dT.inv a b c m)

/-- The shifted connector degree is the old degree plus the coboundary of
the binary regrading cochain. -/
theorem shiftTData_parity (dD : DData) (dC : CData dD)
    (dT : TData dD dC) (n : NuBetaData) (a b c : ZMod 8) :
    (shiftTData dD dC dT n).parity a b c =
      dT.parity a b c +
        Superfusion.d₂ n.nu (Multiplicative.ofAdd a)
          (Multiplicative.ofAdd b) (Multiplicative.ofAdd c) := by
  simp only [shiftTData, leftRouteShift, rightRouteShift, shiftNu,
    Superfusion.d₂, shiftZMod2_sub_eq_add]
  ac_rfl

/-! ### Coordinate covariance of the shifted pure actions -/

private theorem shiftT_left_toCoord_leftPure (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (dT : TData dD dC) (hT : TLaws dD hD dC hC dT)
    (n : NuBetaData) (a b c : ZMod 8)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) (m : dT.LeftCarrier a b c) :
    (shiftTData dD dC dT n).leftToCoord a b c
        ((shiftTData dD dC dT n).leftRoute.leftPure a b c x y z m) =
      fun targetAB targetABC =>
        CData.rawFinSum (dD.algebra (a + b + c)) fun sourceAB =>
          CData.rawFinSum (dD.algebra (a + b + c)) fun sourceABC =>
            (dD.algebra (a + b + c)).mul
              (leftRouteCoeff (shiftCData dD dC n) a b c
                targetAB targetABC sourceAB sourceABC x y z)
              ((shiftTData dD dC dT n).leftToCoord a b c m
                sourceAB sourceABC) := by
  simp only [shiftTData, shiftTripleRouteData]
  rw [hT.left_toCoord_leftPure]
  funext targetAB targetABC
  unfold leftRouteFrame
  simp_rw [leftRouteCoeff_shift dD hD dC hC n]
  unfold leftRouteFrameSign
  exact (framedDoubleSum (dD.algebra (a + b + c))
    (hD.algebra_laws (a + b + c))
    (shiftNu n (a + b) c * dC.rowParity a b targetAB)
    (fun sourceAB =>
      shiftNu n (a + b) c * dC.rowParity a b sourceAB)
    (fun sourceAB sourceABC =>
      leftRouteCoeff dC a b c targetAB targetABC sourceAB sourceABC
        (routeRowTwist dD a (leftRouteShift n a b c) x)
        (routeRowTwist dD b (leftRouteShift n a b c) y)
        (routeRowTwist dD c (leftRouteShift n a b c) z))
    (fun sourceAB sourceABC =>
      dT.leftToCoord a b c m sourceAB sourceABC)).symm

private theorem shiftT_right_toCoord_leftPure (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (dT : TData dD dC) (hT : TLaws dD hD dC hC dT)
    (n : NuBetaData) (a b c : ZMod 8)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) (m : dT.RightCarrier a b c) :
    (shiftTData dD dC dT n).rightToCoord a b c
        ((shiftTData dD dC dT n).rightRoute.leftPure a b c x y z m) =
      fun targetBC targetABC =>
        CData.rawFinSum (dD.algebra (a + b + c)) fun sourceBC =>
          CData.rawFinSum (dD.algebra (a + b + c)) fun sourceABC =>
            (dD.algebra (a + b + c)).mul
              (rightRouteCoeff (shiftCData dD dC n) a b c
                targetBC targetABC sourceBC sourceABC x y z)
              ((shiftTData dD dC dT n).rightToCoord a b c m
                sourceBC sourceABC) := by
  simp only [shiftTData, shiftTripleRouteData]
  rw [hT.right_toCoord_leftPure]
  funext targetBC targetABC
  unfold rightRouteFrame
  simp_rw [rightRouteCoeff_shift dD hD dC hC n]
  unfold rightRouteFrameSign
  exact (framedDoubleSum (dD.algebra (a + b + c))
    (hD.algebra_laws (a + b + c))
    (shiftNu n a (b + c) * dC.rowParity b c targetBC)
    (fun sourceBC =>
      shiftNu n a (b + c) * dC.rowParity b c sourceBC)
    (fun sourceBC sourceABC =>
      rightRouteCoeff dC a b c targetBC targetABC sourceBC sourceABC
        (routeRowTwist dD a (rightRouteShift n a b c) x)
        (routeRowTwist dD b (rightRouteShift n a b c) y)
        (routeRowTwist dD c (rightRouteShift n a b c) z))
    (fun sourceBC sourceABC =>
      dT.rightToCoord a b c m sourceBC sourceABC)).symm

/-! ### Graded equivariance of the rescaled connector -/

private theorem shiftT_hom_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (dT : TData dD dC) (hT : TLaws dD hD dC hC dT)
    (n : NuBetaData) (a b c : ZMod 8) (i j k : ZMod 2)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) (m : dT.LeftCarrier a b c)
    (hx : (dD.algebra a).MemGrade i x)
    (hy : (dD.algebra b).MemGrade j y)
    (hz : (dD.algebra c).MemGrade k z) :
    (shiftTData dD dC dT n).hom a b c
        ((shiftTData dD dC dT n).leftRoute.leftPure a b c x y z m) =
      (shiftTData dD dC dT n).rightRoute.smul a b c
        (paritySign
          ((shiftTData dD dC dT n).parity a b c * (i + j + k)))
        ((shiftTData dD dC dT n).rightRoute.leftPure a b c x y z
          ((shiftTData dD dC dT n).hom a b c m)) := by
  let sLeft := leftRouteShift n a b c
  let sRight := rightRouteShift n a b c
  let total := i + j + k
  have hxT := routeRowTwist_memGrade_at dD hD a sLeft i x hx
  have hyT := routeRowTwist_memGrade_at dD hD b sLeft j y hy
  have hzT := routeRowTwist_memGrade_at dD hD c sLeft k z hz
  simp only [shiftTData, shiftTripleRouteData]
  rw [hT.hom_left a b c i j k
      (routeRowTwist dD a sLeft x)
      (routeRowTwist dD b sLeft y)
      (routeRowTwist dD c sLeft z) m hxT hyT hzT,
    tripleLeftPure_twist_of_memGrade dD hD dT.rightRoute
      hT.right_route_laws a b c sLeft i j k x y z (dT.hom a b c m)
      hx hy hz,
    hT.right_route_laws.left_smul_module,
    tripleLeftPure_twist_of_memGrade dD hD dT.rightRoute
      hT.right_route_laws a b c sRight i j k x y z (dT.hom a b c m)
      hx hy hz]
  repeat rw [← hT.right_route_laws.smul_assoc]
  congr 1
  calc
    ((↑(shiftBeta n a b c)⁻¹ : ℝ) *
          paritySign (dT.parity a b c * total)) *
        paritySign (sLeft * total) =
      (↑(shiftBeta n a b c)⁻¹ : ℝ) *
        (paritySign (sLeft * total) *
          paritySign (dT.parity a b c * total)) := by ring
    _ = (↑(shiftBeta n a b c)⁻¹ : ℝ) *
        (paritySign ((dT.parity a b c + sLeft + sRight) * total) *
          paritySign (sRight * total)) := by
      rw [shiftedConnectorSign]
    _ = (paritySign ((dT.parity a b c + sLeft + sRight) * total) *
          (↑(shiftBeta n a b c)⁻¹ : ℝ)) *
        paritySign (sRight * total) := by ring

private theorem shiftT_inv_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (dT : TData dD dC) (hT : TLaws dD hD dC hC dT)
    (n : NuBetaData) (a b c : ZMod 8) (i j k : ZMod 2)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) (m : dT.RightCarrier a b c)
    (hx : (dD.algebra a).MemGrade i x)
    (hy : (dD.algebra b).MemGrade j y)
    (hz : (dD.algebra c).MemGrade k z) :
    (shiftTData dD dC dT n).inv a b c
        ((shiftTData dD dC dT n).rightRoute.leftPure a b c x y z m) =
      (shiftTData dD dC dT n).leftRoute.smul a b c
        (paritySign
          ((shiftTData dD dC dT n).parity a b c * (i + j + k)))
        ((shiftTData dD dC dT n).leftRoute.leftPure a b c x y z
          ((shiftTData dD dC dT n).inv a b c m)) := by
  let sLeft := leftRouteShift n a b c
  let sRight := rightRouteShift n a b c
  let total := i + j + k
  have hxT := routeRowTwist_memGrade_at dD hD a sRight i x hx
  have hyT := routeRowTwist_memGrade_at dD hD b sRight j y hy
  have hzT := routeRowTwist_memGrade_at dD hD c sRight k z hz
  simp only [shiftTData, shiftTripleRouteData]
  rw [hT.inv_left a b c i j k
      (routeRowTwist dD a sRight x)
      (routeRowTwist dD b sRight y)
      (routeRowTwist dD c sRight z) m hxT hyT hzT,
    tripleLeftPure_twist_of_memGrade dD hD dT.leftRoute
      hT.left_route_laws a b c sRight i j k x y z (dT.inv a b c m)
      hx hy hz,
    hT.left_route_laws.left_smul_module,
    tripleLeftPure_twist_of_memGrade dD hD dT.leftRoute
      hT.left_route_laws a b c sLeft i j k x y z (dT.inv a b c m)
      hx hy hz]
  repeat rw [← hT.left_route_laws.smul_assoc]
  congr 1
  calc
    ((↑(shiftBeta n a b c) : ℝ) *
          paritySign (dT.parity a b c * total)) *
        paritySign (sRight * total) =
      (↑(shiftBeta n a b c) : ℝ) *
        (paritySign (sRight * total) *
          paritySign (dT.parity a b c * total)) := by ring
    _ = (↑(shiftBeta n a b c) : ℝ) *
        (paritySign ((dT.parity a b c + sLeft + sRight) * total) *
          paritySign (sLeft * total)) := by
      rw [shiftedConnectorSign_symm]
    _ = (paritySign ((dT.parity a b c + sLeft + sRight) * total) *
          (↑(shiftBeta n a b c) : ℝ)) *
        paritySign (sLeft * total) := by ring

/-! ### All laws of the shifted connector -/

/-- Regrading the two routes, changing coordinate frames, and rescaling the
connector preserve every abstract ternary-connector law. -/
theorem shiftTLaws (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (dT : TData dD dC) (hT : TLaws dD hD dC hC dT)
    (n : NuBetaData) :
    TLaws dD hD (shiftCData dD dC n) (shiftCLaws dD hD dC hC n)
      (shiftTData dD dC dT n) where
  left_route_laws := shiftTripleRouteLaws dD hD dT.leftRoute
    hT.left_route_laws (leftRouteShift n)
  right_route_laws := shiftTripleRouteLaws dD hD dT.rightRoute
    hT.right_route_laws (rightRouteShift n)
  left_ofCoord_toCoord := by
    intro a b c x
    simp only [shiftTData]
    rw [leftRouteFrameInv_frame dD hD dC n, hT.left_ofCoord_toCoord]
  left_toCoord_ofCoord := by
    intro a b c x
    simp only [shiftTData]
    rw [hT.left_toCoord_ofCoord,
      leftRouteFrame_frameInv dD hD dC n]
  right_ofCoord_toCoord := by
    intro a b c x
    simp only [shiftTData]
    rw [rightRouteFrameInv_frame dD hD dC n, hT.right_ofCoord_toCoord]
  right_toCoord_ofCoord := by
    intro a b c x
    simp only [shiftTData]
    rw [hT.right_toCoord_ofCoord,
      rightRouteFrame_frameInv dD hD dC n]
  left_toCoord_zero := by
    intro a b c
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_zero]
    funext r s
    unfold leftRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_zero]
  left_toCoord_add := by
    intro a b c x y
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_add]
    funext r s
    unfold leftRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_add]
  left_toCoord_neg := by
    intro a b c x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_neg]
    funext r s
    unfold leftRouteFrame
    exact algebra_smul_neg (dD.algebra (a + b + c))
      (hD.algebra_laws (a + b + c)) _ _
  left_toCoord_smul := by
    intro a b c q x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_smul]
    funext r s
    unfold leftRouteFrame
    rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
      ← (hD.algebra_laws (a + b + c)).smul_assoc]
    congr 1
    ring
  left_toCoord_component := by
    intro a b c i x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_component]
    funext r s
    unfold leftRouteFrame
    rw [(hD.algebra_laws (a + b + c)).component_smul]
    congr 1
    simp only [shiftCData, leftRouteShift]
    ac_rfl
  left_toCoord_leftPure := by
    intro a b c x y z m
    exact shiftT_left_toCoord_leftPure dD hD dC hC dT hT n
      a b c x y z m
  left_toCoord_right := by
    intro a b c m x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.left_toCoord_right]
    funext r s
    unfold leftRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_mul]
  right_toCoord_zero := by
    intro a b c
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_zero]
    funext r s
    unfold rightRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_zero]
  right_toCoord_add := by
    intro a b c x y
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_add]
    funext r s
    unfold rightRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_add]
  right_toCoord_neg := by
    intro a b c x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_neg]
    funext r s
    unfold rightRouteFrame
    exact algebra_smul_neg (dD.algebra (a + b + c))
      (hD.algebra_laws (a + b + c)) _ _
  right_toCoord_smul := by
    intro a b c q x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_smul]
    funext r s
    unfold rightRouteFrame
    rw [← (hD.algebra_laws (a + b + c)).smul_assoc,
      ← (hD.algebra_laws (a + b + c)).smul_assoc]
    congr 1
    ring
  right_toCoord_component := by
    intro a b c i x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_component]
    funext r s
    unfold rightRouteFrame
    rw [(hD.algebra_laws (a + b + c)).component_smul]
    congr 1
    simp only [shiftCData, rightRouteShift]
    ac_rfl
  right_toCoord_leftPure := by
    intro a b c x y z m
    exact shiftT_right_toCoord_leftPure dD hD dC hC dT hT n
      a b c x y z m
  right_toCoord_right := by
    intro a b c m x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.right_toCoord_right]
    funext r s
    unfold rightRouteFrame
    rw [(hD.algebra_laws (a + b + c)).smul_mul]
  hom_zero := by
    intro a b c
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_zero, hT.right_route_laws.smul_zero]
  hom_add := by
    intro a b c x y
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_add, hT.right_route_laws.smul_add]
  hom_neg := by
    intro a b c x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_neg]
    exact tripleRoute_smul_neg dD hD dT.rightRoute
      hT.right_route_laws a b c _ _
  hom_smul := by
    intro a b c r x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_smul,
      ← hT.right_route_laws.smul_assoc,
      ← hT.right_route_laws.smul_assoc]
    congr 1
    ring
  inv_zero := by
    intro a b c
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_zero, hT.left_route_laws.smul_zero]
  inv_add := by
    intro a b c x y
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_add, hT.left_route_laws.smul_add]
  inv_neg := by
    intro a b c x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_neg]
    exact tripleRoute_smul_neg dD hD dT.leftRoute
      hT.left_route_laws a b c _ _
  inv_smul := by
    intro a b c r x
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_smul,
      ← hT.left_route_laws.smul_assoc,
      ← hT.left_route_laws.smul_assoc]
    congr 1
    ring
  hom_right := by
    intro a b c m q
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_right, hT.right_route_laws.right_smul_module]
  inv_right := by
    intro a b c m q
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_right, hT.left_route_laws.right_smul_module]
  hom_left := by
    intro a b c i j k x y z m hx hy hz
    exact shiftT_hom_left dD hD dC hC dT hT n
      a b c i j k x y z m hx hy hz
  inv_left := by
    intro a b c i j k x y z m hx hy hz
    exact shiftT_inv_left dD hD dC hC dT hT n
      a b c i j k x y z m hx hy hz
  hom_component := by
    intro a b c i m
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_component,
      hT.right_route_laws.component_smul,
      shiftedHomIndex]
  inv_component := by
    intro a b c i m
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_component,
      hT.left_route_laws.component_smul,
      shiftedInvIndex]
  hom_grade := by
    intro a b c i m hm
    simp only [shiftTData, shiftTripleRouteData,
      TripleRouteData.MemGrade] at hm ⊢
    have h := hT.hom_grade a b c (i + leftRouteShift n a b c) m hm
    rw [hT.right_route_laws.component_smul,
      ← shiftedHomIndex, h]
  inv_grade := by
    intro a b c i m hm
    simp only [shiftTData, shiftTripleRouteData,
      TripleRouteData.MemGrade] at hm ⊢
    have h := hT.inv_grade a b c (i + rightRouteShift n a b c) m hm
    rw [hT.left_route_laws.component_smul,
      ← shiftedInvIndex, h]
  hom_inv_id := by
    intro a b c m
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.hom_smul,
      ← hT.right_route_laws.smul_assoc,
      hT.hom_inv_id]
    rw [show (↑(shiftBeta n a b c)⁻¹ : ℝ) *
        (↑(shiftBeta n a b c) : ℝ) = 1 by simp,
      hT.right_route_laws.one_smul]
  inv_hom_id := by
    intro a b c m
    simp only [shiftTData, shiftTripleRouteData]
    rw [hT.inv_smul,
      ← hT.left_route_laws.smul_assoc,
      hT.inv_hom_id]
    rw [show (↑(shiftBeta n a b c) : ℝ) *
        (↑(shiftBeta n a b c)⁻¹ : ℝ) = 1 by simp,
      hT.left_route_laws.one_smul]

/-! ## Shifted raw bundle and data--laws package -/

/-- Apply the coordinate shift to all three raw layers. -/
def shiftRawDCTData (x : RawDCTData) (n : NuBetaData) : RawDCTData where
  D := x.D
  C := shiftCData x.D x.C n
  T := shiftTData x.D x.C x.T n

/-- The three generic preservation theorems assemble into laws for the
shifted raw DCT data. -/
theorem shiftRawDCTLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (n : NuBetaData) : RawDCTLaws (shiftRawDCTData x n) where
  D := hx.D
  C := shiftCLaws x.D hx.D x.C hx.C n
  T := shiftTLaws x.D hx.D x.C hx.C x.T hx.T n

/-- Computational parameters of a shift of one fixed raw DCT. -/
structure ShiftData (x : RawDCTData) extends NuBetaData

namespace ShiftData

/-- Regard any pair of shift cochains as source-indexed shift data. -/
def ofNuBetaData (x : RawDCTData) (n : NuBetaData) : ShiftData x where
  nu := n.nu
  beta := n.beta

/-- Forget the source-indexed wrapper and retain the two cochains. -/
def cochains {x : RawDCTData} (d : ShiftData x) : NuBetaData :=
  d.toNuBetaData

/-- The raw DCT data computed from a shift prescription. -/
def shifted {x : RawDCTData} (d : ShiftData x) : RawDCTData :=
  shiftRawDCTData x d.cochains

end ShiftData

/-- Laws asserting that the computed shifted data is again a raw DCT. -/
structure ShiftLaws (x : RawDCTData) (hx : RawDCTLaws x)
    (d : ShiftData x) : Prop where
  shifted_laws : RawDCTLaws d.shifted

/-- Canonical laws for the source-indexed shift data associated with any
pair of raw shift cochains. -/
def shiftLawsOfNuBetaData (x : RawDCTData) (hx : RawDCTLaws x)
    (n : NuBetaData) :
    ShiftLaws x hx (ShiftData.ofNuBetaData x n) where
  shifted_laws := shiftRawDCTLaws x hx n

/-- A completed shift prescription for a completed raw DCT. -/
structure Shift (X : RawDCT) where
  data : ShiftData X.data
  laws : ShiftLaws X.data X.laws data

/-- Canonical completed shift determined by arbitrary computable shift
cochains. -/
def shiftOfNuBetaData (X : RawDCT) (n : NuBetaData) : Shift X where
  data := ShiftData.ofNuBetaData X.data n
  laws := shiftLawsOfNuBetaData X.data X.laws n

namespace Shift

/-- The completed shifted raw DCT carried by a completed shift. -/
def shifted {X : RawDCT} (s : Shift X) : RawDCT where
  data := s.data.shifted
  laws := s.laws.shifted_laws

end Shift

end Superfusion.RMod.RawDCT
