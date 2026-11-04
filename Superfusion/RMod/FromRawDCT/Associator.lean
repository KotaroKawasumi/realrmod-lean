import Mathlib.Algebra.BigOperators.Fin
import Superfusion.RMod.FromRawDCT.Tensor

/-!
# Associator data read directly from the stored raw connector

This abstract file constructs the two associator matrices of the finite
coordinate envelope.  A matrix coefficient is obtained by inserting a
single coordinate vector into one stored ternary route, applying the stored
connector `T.hom` or `T.inv`, and reading one coordinate in the other route.

Consequently an already shifted raw DCT is used exactly as stored.  No
separate `beta`, route sign, connector table, or inverse normalization is
applied at this boundary.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Abstract associator structure -/

/-- The two executable directions of an associator for fixed tensor data. -/
structure AssociatorData (dD : DData) (tensor : TensorData dD) where
  associatorHom : (X Y Z : Obj) →
    Hom dD (tensor.tensorObj (tensor.tensorObj X Y) Z)
      (tensor.tensorObj X (tensor.tensorObj Y Z))
  associatorInv : (X Y Z : Obj) →
    Hom dD (tensor.tensorObj X (tensor.tensorObj Y Z))
      (tensor.tensorObj (tensor.tensorObj X Y) Z)

/-- Inverse, degree, naturality, and pentagon laws for the exact maps stored
in `d`.  The parent tensor laws are parameters rather than data fields. -/
structure AssociatorLaws (dD : DData) (_hD : DLaws dD)
    (tensor : TensorData dD) (_hTensor : TensorLaws dD _hD tensor)
    (d : AssociatorData dD tensor) : Prop where
  associator_hom_inv : ∀ X Y Z,
    Hom.comp (d.associatorHom X Y Z) (d.associatorInv X Y Z) =
      Hom.id dD (tensor.tensorObj (tensor.tensorObj X Y) Z)
  associator_inv_hom : ∀ X Y Z,
    Hom.comp (d.associatorInv X Y Z) (d.associatorHom X Y Z) =
      Hom.id dD (tensor.tensorObj X (tensor.tensorObj Y Z))
  associator_hom_even : ∀ X Y Z,
    Hom.MemGrade 0 (d.associatorHom X Y Z)
  associator_inv_even : ∀ X Y Z,
    Hom.MemGrade 0 (d.associatorInv X Y Z)
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃}
    (f₁ : Hom dD X₁ Y₁) (f₂ : Hom dD X₂ Y₂)
    (f₃ : Hom dD X₃ Y₃),
    Hom.comp (tensor.tensorHom (tensor.tensorHom f₁ f₂) f₃)
        (d.associatorHom Y₁ Y₂ Y₃) =
      Hom.comp (d.associatorHom X₁ X₂ X₃)
        (tensor.tensorHom f₁ (tensor.tensorHom f₂ f₃))
  pentagon : ∀ W X Y Z,
    Hom.comp
      (Hom.comp
        (tensor.tensorHom (d.associatorHom W X Y) (Hom.id dD Z))
        (d.associatorHom W (tensor.tensorObj X Y) Z))
      (tensor.tensorHom (Hom.id dD W) (d.associatorHom X Y Z)) =
        Hom.comp
          (d.associatorHom (tensor.tensorObj W X) Y Z)
          (d.associatorHom W X (tensor.tensorObj Y Z))

/-- Completed associator over a completed tensor structure. -/
structure Associator (D : D) (tensor : Tensor D) where
  data : AssociatorData D.data tensor.data
  laws : AssociatorLaws D.data D.laws tensor.data tensor.laws data

namespace Associator

/-! ## Delta coordinates of the two ternary routes -/

/-- A coordinate vector supported at one left-associated route position. -/
def leftDelta (x : RawDCTData) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c) :
    LeftRouteCoordinates x.C a b c :=
  fun targetAB targetABC =>
    if targetAB = sourceAB then
      if targetABC = sourceABC then
        (x.D.algebra (a + b + c)).one
      else
        (x.D.algebra (a + b + c)).zero
    else
      (x.D.algebra (a + b + c)).zero

/-- A coordinate vector supported at one right-associated route position. -/
def rightDelta (x : RawDCTData) (a b c : ZMod 8)
    (sourceBC : x.C.Index b c) (sourceABC : x.C.Index a (b + c)) :
    RightRouteCoordinates x.C a b c :=
  fun targetBC targetABC =>
    if targetBC = sourceBC then
      if targetABC = sourceABC then
        (x.D.algebra (a + b + c)).one
      else
        (x.D.algebra (a + b + c)).zero
    else
      (x.D.algebra (a + b + c)).zero

/-! ## Delta-coordinate evaluation -/

@[simp] theorem leftDelta_source (x : RawDCTData) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c) :
    leftDelta x a b c sourceAB sourceABC sourceAB sourceABC =
      (x.D.algebra (a + b + c)).one := by
  simp [leftDelta]

theorem leftDelta_off_first (x : RawDCTData) (a b c : ZMod 8)
    (sourceAB targetAB : x.C.Index a b)
    (sourceABC targetABC : x.C.Index (a + b) c)
    (h : targetAB ≠ sourceAB) :
    leftDelta x a b c sourceAB sourceABC targetAB targetABC =
      (x.D.algebra (a + b + c)).zero := by
  simp [leftDelta, h]

theorem leftDelta_off_second (x : RawDCTData) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b)
    (sourceABC targetABC : x.C.Index (a + b) c)
    (h : targetABC ≠ sourceABC) :
    leftDelta x a b c sourceAB sourceABC sourceAB targetABC =
      (x.D.algebra (a + b + c)).zero := by
  simp [leftDelta, h]

@[simp] theorem rightDelta_source (x : RawDCTData) (a b c : ZMod 8)
    (sourceBC : x.C.Index b c) (sourceABC : x.C.Index a (b + c)) :
    rightDelta x a b c sourceBC sourceABC sourceBC sourceABC =
      (x.D.algebra (a + b + c)).one := by
  simp [rightDelta]

theorem rightDelta_off_first (x : RawDCTData) (a b c : ZMod 8)
    (sourceBC targetBC : x.C.Index b c)
    (sourceABC targetABC : x.C.Index a (b + c))
    (h : targetBC ≠ sourceBC) :
    rightDelta x a b c sourceBC sourceABC targetBC targetABC =
      (x.D.algebra (a + b + c)).zero := by
  simp [rightDelta, h]

theorem rightDelta_off_second (x : RawDCTData) (a b c : ZMod 8)
    (sourceBC : x.C.Index b c)
    (sourceABC targetABC : x.C.Index a (b + c))
    (h : targetABC ≠ sourceABC) :
    rightDelta x a b c sourceBC sourceABC sourceBC targetABC =
      (x.D.algebra (a + b + c)).zero := by
  simp [rightDelta, h]

/-! ## Fixed-order sums in route coordinates -/

/-- A fixed-order finite sum for a carrier with explicitly supplied zero and
addition.  This is used only to transport the stored route operations through
their coordinate presentations. -/
private def routeFinSum {M : Type} (zero : M) (add : M → M → M)
    {n : ℕ} (f : Fin n → M) : M :=
  (List.ofFn f).foldr add zero

private theorem map_list_foldr {M N : Type}
    (zeroM : M) (addM : M → M → M)
    (zeroN : N) (addN : N → N → N) (φ : M → N)
    (hzero : φ zeroM = zeroN)
    (hadd : ∀ x y, φ (addM x y) = addN (φ x) (φ y))
    (l : List M) :
    φ (l.foldr addM zeroM) = (l.map φ).foldr addN zeroN := by
  induction l with
  | nil => exact hzero
  | cons x xs ih =>
      simp only [List.foldr_cons, List.map_cons]
      rw [hadd, ih]

private theorem map_routeFinSum {M N : Type}
    (zeroM : M) (addM : M → M → M)
    (zeroN : N) (addN : N → N → N) (φ : M → N)
    (hzero : φ zeroM = zeroN)
    (hadd : ∀ x y, φ (addM x y) = addN (φ x) (φ y))
    {n : ℕ} (f : Fin n → M) :
    φ (routeFinSum zeroM addM f) =
      routeFinSum zeroN addN (fun i => φ (f i)) := by
  unfold routeFinSum
  simpa only [List.ofFn_comp'] using
    map_list_foldr zeroM addM zeroN addN φ hzero hadd (List.ofFn f)

/- These proof-only instances expose the stored additive operations solely
to reuse the standard finite-sum theorem. -/
private instance coordinateZero (d : SuperAlgebraData ℝ) : Zero d.carrier :=
  ⟨d.zero⟩

private instance coordinateAdd (d : SuperAlgebraData ℝ) : Add d.carrier :=
  ⟨d.add⟩

private instance coordinateNeg (d : SuperAlgebraData ℝ) : Neg d.carrier :=
  ⟨d.neg⟩

private instance coordinateSub (d : SuperAlgebraData ℝ) : Sub d.carrier :=
  ⟨fun x y => d.add x (d.neg y)⟩

@[implicit_reducible]
private def coordinateAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier where
  add_assoc := h.add_assoc
  zero_add := h.zero_add
  add_zero := h.add_zero
  neg_add_cancel := h.neg_add
  add_comm := h.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

private theorem algebra_zero_mul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    d.mul d.zero x = d.zero := by
  let y := d.mul d.zero x
  have hyy : y = d.add y y := by
    calc
      y = d.mul (d.add d.zero d.zero) x := by
        exact congrArg (fun z => d.mul z x) (h.zero_add d.zero).symm
      _ = d.add y y := h.add_mul d.zero d.zero x
  calc
    y = d.add d.zero y := (h.zero_add y).symm
    _ = d.add (d.add (d.neg y) y) y := by rw [h.neg_add]
    _ = d.add (d.neg y) (d.add y y) := h.add_assoc _ _ _
    _ = d.add (d.neg y) y := by rw [← hyy]
    _ = d.zero := h.neg_add y

private theorem rawFinSum_zero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {n : ℕ} :
    CData.rawFinSum d (fun _ : Fin n => d.zero) = d.zero := by
  letI := coordinateAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn (fun _ : Fin n => (0 : d.carrier))).sum = 0
  rw [List.sum_ofFn]
  simp

private theorem rawFinSum_single (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {n : ℕ} (source : Fin n)
    (f : Fin n → d.carrier) :
    CData.rawFinSum d (fun i => if source = i then f i else d.zero) =
      f source := by
  letI := coordinateAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn (fun i => if source = i then f i else (0 : d.carrier))).sum =
    f source
  rw [List.sum_ofFn]
  classical
  simp

private theorem rawFinSum_delta_mul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {n : ℕ} (source : Fin n)
    (f : Fin n → d.carrier) :
    CData.rawFinSum d (fun i =>
      d.mul (if source = i then d.one else d.zero) (f i)) = f source := by
  letI := coordinateAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn (fun i =>
    d.mul (if source = i then d.one else d.zero) (f i))).sum = f source
  rw [List.sum_ofFn]
  classical
  have hterm :
      (fun i : Fin n =>
        d.mul (if source = i then d.one else d.zero) (f i)) =
        (fun i => if source = i then f i else d.zero) := by
    funext i
    by_cases hi : source = i
    · rw [if_pos hi, if_pos hi, h.one_mul]
    · rw [if_neg hi, if_neg hi, algebra_zero_mul d h]
  rw [hterm]
  change (∑ i, if source = i then f i else (0 : d.carrier)) = f source
  simp

private theorem rawFinSum_congr (d : SuperAlgebraData ℝ) {n : ℕ}
    {f g : Fin n → d.carrier} (h : ∀ i, f i = g i) :
    CData.rawFinSum d f = CData.rawFinSum d g := by
  exact congrArg (CData.rawFinSum d) (funext h)

/-- A double right-route delta sum selects exactly one coordinate. -/
private theorem rightDelta_weighted_sum (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (q : x.C.Index b c → x.C.Index a (b + c) →
      (x.D.algebra (a + b + c)).carrier)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceBC =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
        (x.D.algebra (a + b + c)).mul
          (rightDelta x a b c sourceBC sourceABC targetBC targetABC)
          (q sourceBC sourceABC))) = q targetBC targetABC := by
  let A := x.D.algebra (a + b + c)
  let hA := hx.D.algebra_laws (a + b + c)
  calc
    _ = CData.rawFinSum A (fun sourceBC =>
        if targetBC = sourceBC then q sourceBC targetABC else A.zero) := by
      apply rawFinSum_congr
      intro sourceBC
      by_cases hBC : targetBC = sourceBC
      · simp only [rightDelta, hBC, if_pos]
        exact rawFinSum_delta_mul A hA targetABC (q sourceBC)
      · simp only [rightDelta, hBC, if_false]
        calc
          _ = CData.rawFinSum A (fun _ => A.zero) := by
            apply rawFinSum_congr
            intro sourceABC
            exact algebra_zero_mul A hA (q sourceBC sourceABC)
          _ = A.zero := rawFinSum_zero A hA
    _ = q targetBC targetABC :=
      rawFinSum_single A hA targetBC (fun sourceBC => q sourceBC targetABC)

/-- A double left-route delta sum selects exactly one coordinate. -/
private theorem leftDelta_weighted_sum (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (q : x.C.Index a b → x.C.Index (a + b) c →
      (x.D.algebra (a + b + c)).carrier)
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceAB =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
        (x.D.algebra (a + b + c)).mul
          (leftDelta x a b c sourceAB sourceABC targetAB targetABC)
          (q sourceAB sourceABC))) = q targetAB targetABC := by
  let A := x.D.algebra (a + b + c)
  let hA := hx.D.algebra_laws (a + b + c)
  calc
    _ = CData.rawFinSum A (fun sourceAB =>
        if targetAB = sourceAB then q sourceAB targetABC else A.zero) := by
      apply rawFinSum_congr
      intro sourceAB
      by_cases hAB : targetAB = sourceAB
      · simp only [leftDelta, hAB, if_pos]
        exact rawFinSum_delta_mul A hA targetABC (q sourceAB)
      · simp only [leftDelta, hAB, if_false]
        calc
          _ = CData.rawFinSum A (fun _ => A.zero) := by
            apply rawFinSum_congr
            intro sourceABC
            exact algebra_zero_mul A hA (q sourceAB sourceABC)
          _ = A.zero := rawFinSum_zero A hA
    _ = q targetAB targetABC :=
      rawFinSum_single A hA targetAB (fun sourceAB => q sourceAB targetABC)

/-! ## Route sums and coordinate presentations -/

private theorem leftToCoord_routeFinSum (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) {n : ℕ}
    (f : Fin n → x.T.LeftCarrier a b c)
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    x.T.leftToCoord a b c
        (routeFinSum (x.T.leftRoute.zero a b c)
          (x.T.leftRoute.add a b c) f) targetAB targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun i =>
        x.T.leftToCoord a b c (f i) targetAB targetABC) := by
  change _ = routeFinSum (x.D.algebra (a + b + c)).zero
    (x.D.algebra (a + b + c)).add _
  apply map_routeFinSum
    (x.T.leftRoute.zero a b c) (x.T.leftRoute.add a b c)
    (x.D.algebra (a + b + c)).zero
    (x.D.algebra (a + b + c)).add
    (fun m => x.T.leftToCoord a b c m targetAB targetABC)
  · exact congrFun (congrFun (hx.T.left_toCoord_zero a b c)
      targetAB) targetABC
  · intro m m'
    exact congrFun (congrFun (hx.T.left_toCoord_add a b c m m')
      targetAB) targetABC

private theorem rightToCoord_routeFinSum (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) {n : ℕ}
    (f : Fin n → x.T.RightCarrier a b c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    x.T.rightToCoord a b c
        (routeFinSum (x.T.rightRoute.zero a b c)
          (x.T.rightRoute.add a b c) f) targetBC targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun i =>
        x.T.rightToCoord a b c (f i) targetBC targetABC) := by
  change _ = routeFinSum (x.D.algebra (a + b + c)).zero
    (x.D.algebra (a + b + c)).add _
  apply map_routeFinSum
    (x.T.rightRoute.zero a b c) (x.T.rightRoute.add a b c)
    (x.D.algebra (a + b + c)).zero
    (x.D.algebra (a + b + c)).add
    (fun m => x.T.rightToCoord a b c m targetBC targetABC)
  · exact congrFun (congrFun (hx.T.right_toCoord_zero a b c)
      targetBC) targetABC
  · intro m m'
    exact congrFun (congrFun (hx.T.right_toCoord_add a b c m m')
      targetBC) targetABC

private theorem inv_routeFinSum (x : RawDCTData) (hx : RawDCTLaws x)
    (a b c : ZMod 8) {n : ℕ} (f : Fin n → x.T.RightCarrier a b c) :
    x.T.inv a b c
        (routeFinSum (x.T.rightRoute.zero a b c)
          (x.T.rightRoute.add a b c) f) =
      routeFinSum (x.T.leftRoute.zero a b c)
        (x.T.leftRoute.add a b c) (fun i => x.T.inv a b c (f i)) := by
  apply map_routeFinSum
  · exact hx.T.inv_zero a b c
  · exact hx.T.inv_add a b c

private theorem hom_routeFinSum (x : RawDCTData) (hx : RawDCTLaws x)
    (a b c : ZMod 8) {n : ℕ} (f : Fin n → x.T.LeftCarrier a b c) :
    x.T.hom a b c
        (routeFinSum (x.T.leftRoute.zero a b c)
          (x.T.leftRoute.add a b c) f) =
      routeFinSum (x.T.rightRoute.zero a b c)
        (x.T.rightRoute.add a b c) (fun i => x.T.hom a b c (f i)) := by
  apply map_routeFinSum
  · exact hx.T.hom_zero a b c
  · exact hx.T.hom_add a b c

private theorem leftToCoord_injective (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) :
    Function.Injective (x.T.leftToCoord a b c) := by
  intro m m' hmm'
  rw [← hx.T.left_ofCoord_toCoord a b c m,
    ← hx.T.left_ofCoord_toCoord a b c m', hmm']

private theorem rightToCoord_injective (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) :
    Function.Injective (x.T.rightToCoord a b c) := by
  intro m m' hmm'
  rw [← hx.T.right_ofCoord_toCoord a b c m,
    ← hx.T.right_ofCoord_toCoord a b c m', hmm']

private theorem leftToCoord_ofCoord_apply (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (q : LeftRouteCoordinates x.C a b c)
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    x.T.leftToCoord a b c (x.T.leftOfCoord a b c q)
      targetAB targetABC = q targetAB targetABC := by
  exact congrFun (congrFun (hx.T.left_toCoord_ofCoord a b c q)
    targetAB) targetABC

private theorem rightToCoord_ofCoord_apply (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (q : RightRouteCoordinates x.C a b c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    x.T.rightToCoord a b c (x.T.rightOfCoord a b c q)
      targetBC targetABC = q targetBC targetABC := by
  exact congrFun (congrFun (hx.T.right_toCoord_ofCoord a b c q)
    targetBC) targetABC

private theorem leftToCoord_right_apply (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (m : x.T.LeftCarrier a b c)
    (q : (x.D.algebra (a + b + c)).carrier)
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    x.T.leftToCoord a b c (x.T.leftRoute.right a b c m q)
      targetAB targetABC =
      (x.D.algebra (a + b + c)).mul
        (x.T.leftToCoord a b c m targetAB targetABC) q := by
  exact congrFun (congrFun (hx.T.left_toCoord_right a b c m q)
    targetAB) targetABC

private theorem rightToCoord_right_apply (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (m : x.T.RightCarrier a b c)
    (q : (x.D.algebra (a + b + c)).carrier)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    x.T.rightToCoord a b c (x.T.rightRoute.right a b c m q)
      targetBC targetABC =
      (x.D.algebra (a + b + c)).mul
        (x.T.rightToCoord a b c m targetBC targetABC) q := by
  exact congrFun (congrFun (hx.T.right_toCoord_right a b c m q)
    targetBC) targetABC

/-- Every right-route vector is the fixed-order sum of its delta-coordinate
vectors, with its stored coefficients acting on the right. -/
private theorem rightRoute_coordinate_expansion (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (m : x.T.RightCarrier a b c) :
    m = routeFinSum (x.T.rightRoute.zero a b c)
      (x.T.rightRoute.add a b c) (fun sourceBC =>
        routeFinSum (x.T.rightRoute.zero a b c)
          (x.T.rightRoute.add a b c) (fun sourceABC =>
            x.T.rightRoute.right a b c
              (x.T.rightOfCoord a b c
                (rightDelta x a b c sourceBC sourceABC))
              (x.T.rightToCoord a b c m sourceBC sourceABC))) := by
  apply rightToCoord_injective x hx a b c
  funext targetBC targetABC
  symm
  calc
    x.T.rightToCoord a b c
        (routeFinSum (x.T.rightRoute.zero a b c)
          (x.T.rightRoute.add a b c) (fun sourceBC =>
            routeFinSum (x.T.rightRoute.zero a b c)
              (x.T.rightRoute.add a b c) (fun sourceABC =>
                x.T.rightRoute.right a b c
                  (x.T.rightOfCoord a b c
                    (rightDelta x a b c sourceBC sourceABC))
                  (x.T.rightToCoord a b c m sourceBC sourceABC))))
        targetBC targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceBC =>
        x.T.rightToCoord a b c
          (routeFinSum (x.T.rightRoute.zero a b c)
            (x.T.rightRoute.add a b c) (fun sourceABC =>
              x.T.rightRoute.right a b c
                (x.T.rightOfCoord a b c
                  (rightDelta x a b c sourceBC sourceABC))
                (x.T.rightToCoord a b c m sourceBC sourceABC)))
          targetBC targetABC) :=
        rightToCoord_routeFinSum x hx a b c _ targetBC targetABC
    _ = CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceBC =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          x.T.rightToCoord a b c
            (x.T.rightRoute.right a b c
              (x.T.rightOfCoord a b c
                (rightDelta x a b c sourceBC sourceABC))
              (x.T.rightToCoord a b c m sourceBC sourceABC))
            targetBC targetABC)) := by
      apply rawFinSum_congr
      intro sourceBC
      exact rightToCoord_routeFinSum x hx a b c _ targetBC targetABC
    _ = CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceBC =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          (x.D.algebra (a + b + c)).mul
            (rightDelta x a b c sourceBC sourceABC targetBC targetABC)
            (x.T.rightToCoord a b c m sourceBC sourceABC))) := by
      apply rawFinSum_congr
      intro sourceBC
      apply rawFinSum_congr
      intro sourceABC
      rw [rightToCoord_right_apply x hx, rightToCoord_ofCoord_apply x hx]
    _ = x.T.rightToCoord a b c m targetBC targetABC :=
      rightDelta_weighted_sum x hx a b c
        (x.T.rightToCoord a b c m) targetBC targetABC

/-- Every left-route vector is the analogous fixed-order sum of its stored
left delta coordinates. -/
private theorem leftRoute_coordinate_expansion (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (m : x.T.LeftCarrier a b c) :
    m = routeFinSum (x.T.leftRoute.zero a b c)
      (x.T.leftRoute.add a b c) (fun sourceAB =>
        routeFinSum (x.T.leftRoute.zero a b c)
          (x.T.leftRoute.add a b c) (fun sourceABC =>
            x.T.leftRoute.right a b c
              (x.T.leftOfCoord a b c
                (leftDelta x a b c sourceAB sourceABC))
              (x.T.leftToCoord a b c m sourceAB sourceABC))) := by
  apply leftToCoord_injective x hx a b c
  funext targetAB targetABC
  symm
  calc
    x.T.leftToCoord a b c
        (routeFinSum (x.T.leftRoute.zero a b c)
          (x.T.leftRoute.add a b c) (fun sourceAB =>
            routeFinSum (x.T.leftRoute.zero a b c)
              (x.T.leftRoute.add a b c) (fun sourceABC =>
                x.T.leftRoute.right a b c
                  (x.T.leftOfCoord a b c
                    (leftDelta x a b c sourceAB sourceABC))
                  (x.T.leftToCoord a b c m sourceAB sourceABC))))
        targetAB targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceAB =>
        x.T.leftToCoord a b c
          (routeFinSum (x.T.leftRoute.zero a b c)
            (x.T.leftRoute.add a b c) (fun sourceABC =>
              x.T.leftRoute.right a b c
                (x.T.leftOfCoord a b c
                  (leftDelta x a b c sourceAB sourceABC))
                (x.T.leftToCoord a b c m sourceAB sourceABC)))
          targetAB targetABC) :=
        leftToCoord_routeFinSum x hx a b c _ targetAB targetABC
    _ = CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceAB =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          x.T.leftToCoord a b c
            (x.T.leftRoute.right a b c
              (x.T.leftOfCoord a b c
                (leftDelta x a b c sourceAB sourceABC))
              (x.T.leftToCoord a b c m sourceAB sourceABC))
            targetAB targetABC)) := by
      apply rawFinSum_congr
      intro sourceAB
      exact leftToCoord_routeFinSum x hx a b c _ targetAB targetABC
    _ = CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceAB =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          (x.D.algebra (a + b + c)).mul
            (leftDelta x a b c sourceAB sourceABC targetAB targetABC)
            (x.T.leftToCoord a b c m sourceAB sourceABC))) := by
      apply rawFinSum_congr
      intro sourceAB
      apply rawFinSum_congr
      intro sourceABC
      rw [leftToCoord_right_apply x hx, leftToCoord_ofCoord_apply x hx]
    _ = x.T.leftToCoord a b c m targetAB targetABC :=
      leftDelta_weighted_sum x hx a b c
        (x.T.leftToCoord a b c m) targetAB targetABC

/-! ## Connector coefficients -/

/-- One forward connector coefficient, evaluated through the actual stored
left route, forward connector, and right coordinate presentation. -/
def homCoefficient (x : RawDCTData) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    (x.D.algebra (a + b + c)).carrier :=
  x.T.rightToCoord a b c
    (x.T.hom a b c
      (x.T.leftOfCoord a b c
        (leftDelta x a b c sourceAB sourceABC)))
    targetBC targetABC

/-- One inverse connector coefficient, evaluated through the actual stored
right route, inverse connector, and left coordinate presentation. -/
def invCoefficient (x : RawDCTData) (a b c : ZMod 8)
    (sourceBC : x.C.Index b c) (sourceABC : x.C.Index a (b + c))
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    (x.D.algebra (a + b + c)).carrier :=
  x.T.leftToCoord a b c
    (x.T.inv a b c
      (x.T.rightOfCoord a b c
        (rightDelta x a b c sourceBC sourceABC)))
    targetAB targetABC

/-! ## Connector matrices act on stored route coordinates -/

/-- Applying the inverse connector and reading a left coordinate is matrix
multiplication by the stored `invCoefficient` columns. -/
theorem inv_toCoord_eq_matrix (x : RawDCTData) (hx : RawDCTLaws x)
    (a b c : ZMod 8) (m : x.T.RightCarrier a b c)
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    x.T.leftToCoord a b c (x.T.inv a b c m) targetAB targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceBC =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          (x.D.algebra (a + b + c)).mul
            (invCoefficient x a b c sourceBC sourceABC targetAB targetABC)
            (x.T.rightToCoord a b c m sourceBC sourceABC))) := by
  nth_rewrite 1 [rightRoute_coordinate_expansion x hx a b c m]
  rw [inv_routeFinSum x hx]
  rw [leftToCoord_routeFinSum x hx]
  apply rawFinSum_congr
  intro sourceBC
  rw [inv_routeFinSum x hx]
  rw [leftToCoord_routeFinSum x hx]
  apply rawFinSum_congr
  intro sourceABC
  rw [hx.T.inv_right]
  rw [leftToCoord_right_apply x hx]
  rfl

/-- Applying the forward connector and reading a right coordinate is matrix
multiplication by the stored `homCoefficient` columns. -/
theorem hom_toCoord_eq_matrix (x : RawDCTData) (hx : RawDCTLaws x)
    (a b c : ZMod 8) (m : x.T.LeftCarrier a b c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    x.T.rightToCoord a b c (x.T.hom a b c m) targetBC targetABC =
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceAB =>
        CData.rawFinSum (x.D.algebra (a + b + c)) (fun sourceABC =>
          (x.D.algebra (a + b + c)).mul
            (homCoefficient x a b c sourceAB sourceABC targetBC targetABC)
            (x.T.leftToCoord a b c m sourceAB sourceABC))) := by
  nth_rewrite 1 [leftRoute_coordinate_expansion x hx a b c m]
  rw [hom_routeFinSum x hx]
  rw [rightToCoord_routeFinSum x hx]
  apply rawFinSum_congr
  intro sourceAB
  rw [hom_routeFinSum x hx]
  rw [rightToCoord_routeFinSum x hx]
  apply rawFinSum_congr
  intro sourceABC
  rw [hx.T.hom_right]
  rw [rightToCoord_right_apply x hx]
  rfl

/-! ## Two-sided finite matrix inverse identities -/

/-- The inverse matrix multiplied by the forward matrix is the left-route
Kronecker delta.  This is the coordinate form of `T.inv_hom_id`. -/
theorem inv_homCoefficient_matrix_identity
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (sourceAB targetAB : x.C.Index a b)
    (sourceABC targetABC : x.C.Index (a + b) c) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleBC =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleABC =>
        (x.D.algebra (a + b + c)).mul
          (invCoefficient x a b c middleBC middleABC targetAB targetABC)
          (homCoefficient x a b c sourceAB sourceABC middleBC middleABC))) =
      leftDelta x a b c sourceAB sourceABC targetAB targetABC := by
  let basis := x.T.leftOfCoord a b c
    (leftDelta x a b c sourceAB sourceABC)
  calc
    _ = x.T.leftToCoord a b c
        (x.T.inv a b c (x.T.hom a b c basis)) targetAB targetABC := by
      simpa only [basis, homCoefficient] using
        (inv_toCoord_eq_matrix x hx a b c
          (x.T.hom a b c basis) targetAB targetABC).symm
    _ = x.T.leftToCoord a b c basis targetAB targetABC := by
      rw [hx.T.inv_hom_id]
    _ = leftDelta x a b c sourceAB sourceABC targetAB targetABC := by
      exact leftToCoord_ofCoord_apply x hx a b c _ targetAB targetABC

/-- The forward matrix multiplied by the inverse matrix is the right-route
Kronecker delta, the coordinate form of `T.hom_inv_id`. -/
theorem hom_invCoefficient_matrix_identity
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (sourceBC targetBC : x.C.Index b c)
    (sourceABC targetABC : x.C.Index a (b + c)) :
    CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleAB =>
      CData.rawFinSum (x.D.algebra (a + b + c)) (fun middleABC =>
        (x.D.algebra (a + b + c)).mul
          (homCoefficient x a b c middleAB middleABC targetBC targetABC)
          (invCoefficient x a b c sourceBC sourceABC middleAB middleABC))) =
      rightDelta x a b c sourceBC sourceABC targetBC targetABC := by
  let basis := x.T.rightOfCoord a b c
    (rightDelta x a b c sourceBC sourceABC)
  calc
    _ = x.T.rightToCoord a b c
        (x.T.hom a b c (x.T.inv a b c basis)) targetBC targetABC := by
      simpa only [basis, invCoefficient] using
        (hom_toCoord_eq_matrix x hx a b c
          (x.T.inv a b c basis) targetBC targetABC).symm
    _ = x.T.rightToCoord a b c basis targetBC targetABC := by
      rw [hx.T.hom_inv_id]
    _ = rightDelta x a b c sourceBC sourceABC targetBC targetABC := by
      exact rightToCoord_ofCoord_apply x hx a b c _ targetBC targetABC

/-! ## Index transport -/

/-- Transport one stored fusion-row index along equal endpoint labels. -/
def castIndex (x : RawDCTData) {a b a' b' : ZMod 8}
    (ha : a = a') (hb : b = b') : x.C.Index a b → x.C.Index a' b' :=
  fun r => cast (congrArg₂ x.C.Index ha hb) r

/-! ## Associator matrix entries -/

/-- One entry of the forward associator matrix.  It vanishes unless the two
nested tensor slots have the same three original object indices. -/
def homEntry (x : RawDCTData) (X Y Z : Obj)
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Y) Z)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Y Z)) :
    AtomHom x.D
      (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Y) Z qL)
      (Tensor.slotAtom x.D x.C X (Tensor.obj x.D x.C Y Z) qR) := by
  let xy := (Tensor.slots x.D x.C X Y).get qL.left
  let yz := (Tensor.slots x.D x.C Y Z).get qR.right
  by_cases hX : xy.left = qR.left
  · by_cases hY : xy.right = yz.left
    · by_cases hZ : qL.right = yz.right
      · let a := X.atom xy.left
        let b := Y.atom xy.right
        let c := Z.atom qL.right
        have hBCLeft : (Y.atom yz.left).label = b.label := by
          simpa [b] using congrArg (fun i => (Y.atom i).label) hY.symm
        have hBCRight : (Z.atom yz.right).label = c.label := by
          simpa [c] using congrArg (fun i => (Z.atom i).label) hZ.symm
        let bc : x.C.Index b.label c.label :=
          castIndex x hBCLeft hBCRight yz.fusion
        have hALeft : (X.atom qR.left).label = a.label := by
          simpa [a] using congrArg (fun i => (X.atom i).label) hX.symm
        have hYZLabel : ((Tensor.obj x.D x.C Y Z).atom qR.right).label =
            b.label + c.label := by
          change (Y.atom yz.left).label + (Z.atom yz.right).label = _
          rw [hBCLeft, hBCRight]
        let a_bc : x.C.Index a.label (b.label + c.label) :=
          castIndex x hALeft hYZLabel qR.fusion
        have hXYLabel : ((Tensor.obj x.D x.C X Y).atom qL.left).label =
            a.label + b.label := by
          rfl
        let abc : x.C.Index (a.label + b.label) c.label :=
          castIndex x hXYLabel rfl qL.fusion
        have hLabel :
            (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Y) Z qL).label =
              (Tensor.slotAtom x.D x.C X (Tensor.obj x.D x.C Y Z) qR).label := by
          change ((Tensor.obj x.D x.C X Y).atom qL.left).label +
                (Z.atom qL.right).label =
            (X.atom qR.left).label +
              ((Tensor.obj x.D x.C Y Z).atom qR.right).label
          rw [hXYLabel, hYZLabel, hALeft]
          exact _root_.add_assoc _ _ _
        exact AtomHom.ofLabelEq hLabel
          (homCoefficient x a.label b.label c.label
            xy.fusion abc bc a_bc)
      · exact AtomHom.zero x.D _ _
    · exact AtomHom.zero x.D _ _
  · exact AtomHom.zero x.D _ _

/-- One entry of the backward associator matrix. -/
def invEntry (x : RawDCTData) (X Y Z : Obj)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Y Z))
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Y) Z) :
    AtomHom x.D
      (Tensor.slotAtom x.D x.C X (Tensor.obj x.D x.C Y Z) qR)
      (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Y) Z qL) := by
  let xy := (Tensor.slots x.D x.C X Y).get qL.left
  let yz := (Tensor.slots x.D x.C Y Z).get qR.right
  by_cases hX : xy.left = qR.left
  · by_cases hY : xy.right = yz.left
    · by_cases hZ : qL.right = yz.right
      · let a := X.atom xy.left
        let b := Y.atom xy.right
        let c := Z.atom qL.right
        have hBCLeft : (Y.atom yz.left).label = b.label := by
          simpa [b] using congrArg (fun i => (Y.atom i).label) hY.symm
        have hBCRight : (Z.atom yz.right).label = c.label := by
          simpa [c] using congrArg (fun i => (Z.atom i).label) hZ.symm
        let bc : x.C.Index b.label c.label :=
          castIndex x hBCLeft hBCRight yz.fusion
        have hALeft : (X.atom qR.left).label = a.label := by
          simpa [a] using congrArg (fun i => (X.atom i).label) hX.symm
        have hYZLabel : ((Tensor.obj x.D x.C Y Z).atom qR.right).label =
            b.label + c.label := by
          change (Y.atom yz.left).label + (Z.atom yz.right).label = _
          rw [hBCLeft, hBCRight]
        let a_bc : x.C.Index a.label (b.label + c.label) :=
          castIndex x hALeft hYZLabel qR.fusion
        have hXYLabel : ((Tensor.obj x.D x.C X Y).atom qL.left).label =
            a.label + b.label := by
          rfl
        let abc : x.C.Index (a.label + b.label) c.label :=
          castIndex x hXYLabel rfl qL.fusion
        have hLabel :
            (Tensor.slotAtom x.D x.C X (Tensor.obj x.D x.C Y Z) qR).label =
              (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Y) Z qL).label := by
          change (X.atom qR.left).label +
                ((Tensor.obj x.D x.C Y Z).atom qR.right).label =
            ((Tensor.obj x.D x.C X Y).atom qL.left).label +
              (Z.atom qL.right).label
          rw [hXYLabel, hYZLabel, hALeft]
          exact (_root_.add_assoc _ _ _).symm
        exact AtomHom.ofLabelEq hLabel
          (cast
            (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
              hLabel).symm
            (invCoefficient x a.label b.label c.label bc a_bc
              xy.fusion abc))
      · exact AtomHom.zero x.D _ _
    · exact AtomHom.zero x.D _ _
  · exact AtomHom.zero x.D _ _

/-! ## Associator matrices -/

/-- Forward associator on arbitrary finite coordinate objects. -/
def hom (x : RawDCTData) (X Y Z : Obj) :
    Hom x.D (Tensor.obj x.D x.C (Tensor.obj x.D x.C X Y) Z)
      (Tensor.obj x.D x.C X (Tensor.obj x.D x.C Y Z)) :=
  fun i j => homEntry x X Y Z
    ((Tensor.slots x.D x.C (Tensor.obj x.D x.C X Y) Z).get i)
    ((Tensor.slots x.D x.C X (Tensor.obj x.D x.C Y Z)).get j)

/-- Explicit backward associator on arbitrary finite coordinate objects. -/
def inv (x : RawDCTData) (X Y Z : Obj) :
    Hom x.D (Tensor.obj x.D x.C X (Tensor.obj x.D x.C Y Z))
      (Tensor.obj x.D x.C (Tensor.obj x.D x.C X Y) Z) :=
  fun i j => invEntry x X Y Z
    ((Tensor.slots x.D x.C X (Tensor.obj x.D x.C Y Z)).get i)
    ((Tensor.slots x.D x.C (Tensor.obj x.D x.C X Y) Z).get j)

/-! ## Canonical associator data -/

/-- Associator maps extracted from the actual connector stored in `x`. -/
def canonicalData (x : RawDCTData) :
    AssociatorData x.D (Tensor.canonicalData x.D x.C) where
  associatorHom := hom x
  associatorInv := inv x

end Associator

end Superfusion.RMod.FromRawDCT
