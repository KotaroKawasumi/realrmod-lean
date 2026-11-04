import RMod.BrundanEllis.StackingReferenceShiftedKernelHom
import Superfusion.RMod.FromRawDCT.TensorIndexEquiv

/-! Coordinates of the actual tensor of two finite families at fixed labels.
The stored lexicographic tensor enumeration is retained, with no choice of
summand representatives or additive decompositions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Tensor two finite families of shifted atoms at fixed labels. -/
def rowTensorObject {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) : Obj :=
  Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (rowObject a p) (rowObject b q)

/-- The actual tensor enumeration retains both input positions and the fusion row. -/
def rowTensorIndex {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Fin (rowTensorObject a b p q).size ≃ (Fin n × Fin m × FusionTable.Index a b) :=
  (Tensor.slotIndexEquiv realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (rowObject a p) (rowObject b q)).trans
      { toFun := fun z => (z.1, z.2.1, z.2.2)
        invFun := fun z => ⟨z.1, z.2.1, z.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- Reading a tensor row returns the input shifts and the stored kernel shift. -/
theorem rowTensorObject_atom {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (z : Fin (rowTensorObject a b p q).size) :
    (rowTensorObject a b p q).atom z =
      (a + b, p (rowTensorIndex a b p q z).1 + q (rowTensorIndex a b p q z).2.1 +
        kernelRowParity a b (rowTensorIndex a b p q z).2.2) := rfl

/-- View the concrete tensor as a row object without changing its enumeration. -/
theorem rowTensorObject_eq {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    rowObject (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift) =
      rowTensorObject a b p q := rfl

/-- Coordinate vectors are precisely matrices of fusion-kernel vectors. -/
def rowTensorCoordinates {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (V : Type) [AddCommGroup V] [Module ℝ V] :
    (Fin (rowTensorObject a b p q).size → V) ≃ₗ[ℝ] (Fin n → Fin m → FusionTable.Index a b → V) where
  toFun v i j r := v ((rowTensorIndex a b p q).symm (i, j, r))
  invFun w z := w (rowTensorIndex a b p q z).1 (rowTensorIndex a b p q z).2.1
    (rowTensorIndex a b p q z).2.2
  left_inv v := by
    funext z
    change v ((rowTensorIndex a b p q).symm (rowTensorIndex a b p q z)) = v z
    rw [Equiv.symm_apply_apply]
  right_inv w := by
    funext i j r
    dsimp only
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual row grading is the componentwise grading of the tensor blocks. -/
theorem rowTensorGrade_iff {n m : ℕ} (a b c : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (d : ZMod 2) (v : Fin (rowTensorObject a b p q).size → Coeff c) :
    RowGrade c (fun z => (rowTensorObject a b p q).atom z |>.shift) d v ↔
      ∀ i j, RowGrade c (fun r => p i + q j + kernelRowParity a b r) d
        (rowTensorCoordinates a b p q (Coeff c) v i j) := by
  constructor
  · intro h i j r
    have hh := h ((rowTensorIndex a b p q).symm (i, j, r))
    dsimp only at hh
    rw [rowTensorObject_atom, Equiv.apply_symm_apply] at hh
    exact hh
  · intro h z
    have hh := h (rowTensorIndex a b p q z).1 (rowTensorIndex a b p q z).2.1
      (rowTensorIndex a b p q z).2.2
    change (realDData.algebra c).MemGrade
      (d + (p (rowTensorIndex a b p q z).1 + q (rowTensorIndex a b p q z).2.1 +
        kernelRowParity a b (rowTensorIndex a b p q z).2.2))
      (v ((rowTensorIndex a b p q).symm (rowTensorIndex a b p q z))) at hh
    rw [Equiv.symm_apply_apply] at hh
    simpa only [rowTensorObject_atom, Atom.shift] using hh

/-- The tensor row `(i,j)` is exchanged with `(j,i)` using its actual endpoint shifts. -/
def blockExchange {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    (Fin n → Fin m → RealCCarrier a b) ≃ₗ[ℝ]
      (Fin m → Fin n → FusionTable.Index b a → Coeff (a + b)) where
  toFun v j i := shiftedCommonKernelEquiv a b (p i) (q j) (v i j)
  invFun w i j := (shiftedCommonKernelEquiv a b (p i) (q j)).symm (w j i)
  left_inv v := by
    funext i j
    exact (shiftedCommonKernelEquiv a b (p i) (q j)).symm_apply_apply _
  right_inv w := by
    funext j i
    exact (shiftedCommonKernelEquiv a b (p i) (q j)).apply_symm_apply _
  map_add' v w := by
    funext j i
    exact map_add (shiftedCommonKernelEquiv a b (p i) (q j)) _ _
  map_smul' r v := by
    funext j i
    exact map_smul (shiftedCommonKernelEquiv a b (p i) (q j)) _ _

/-- The full finite tensor exchange, using the actual tensor indices on both sides. -/
def rowTensorEquiv {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    (Fin (rowTensorObject a b p q).size → Coeff (a + b)) ≃ₗ[ℝ]
      (Fin (rowTensorObject b a q p).size → Coeff (a + b)) :=
  (rowTensorCoordinates a b p q (Coeff (a + b))).trans
    ((blockExchange a b p q).trans (rowTensorCoordinates b a q p (Coeff (a + b))).symm)

/-- Tensor coordinate extraction commutes with the strict right action. -/
theorem rowTensorCoordinates_right {n m : ℕ} (a b c : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff c) (x : Coeff c) (i : Fin n) (j : Fin m) :
    rowTensorCoordinates a b p q (Coeff c) (rowRight c v x) i j =
      rowRight c (rowTensorCoordinates a b p q (Coeff c) v i j) x := rfl

/-- Every output block is the specified shifted exchange of its input block. -/
theorem rowTensorEquiv_coordinate {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b)) (j : Fin m) (i : Fin n) :
    rowTensorCoordinates b a q p (Coeff (a + b)) (rowTensorEquiv a b p q v) j i =
      shiftedCommonKernelEquiv a b (p i) (q j) (rowTensorCoordinates a b p q (Coeff (a + b)) v i j) := by
  change (rowTensorCoordinates b a q p (Coeff (a + b)))
    ((rowTensorCoordinates b a q p (Coeff (a + b))).symm
      (blockExchange a b p q (rowTensorCoordinates a b p q (Coeff (a + b)) v))) j i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The inverse has the corresponding inverse block on each pair of positions. -/
theorem rowTensorEquiv_symm_coordinate {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject b a q p).size → Coeff (a + b)) (i : Fin n) (j : Fin m) :
    rowTensorCoordinates a b p q (Coeff (a + b)) ((rowTensorEquiv a b p q).symm v) i j =
      (shiftedCommonKernelEquiv a b (p i) (q j)).symm
        (rowTensorCoordinates b a q p (Coeff (a + b)) v j i) := by
  change (rowTensorCoordinates a b p q (Coeff (a + b)))
    ((rowTensorCoordinates a b p q (Coeff (a + b))).symm
      ((blockExchange a b p q).symm (rowTensorCoordinates b a q p (Coeff (a + b)) v))) i j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The finite tensor exchange is linear over the common right algebra. -/
theorem rowTensorEquiv_right {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b)) (x : Coeff (a + b)) :
    rowTensorEquiv a b p q (rowRight (a + b) v x) =
      rowRight (a + b) (rowTensorEquiv a b p q v) x := by
  apply (rowTensorCoordinates b a q p (Coeff (a + b))).injective
  funext j i
  rw [rowTensorEquiv_coordinate, rowTensorCoordinates_right,
    rowTensorCoordinates_right, rowTensorEquiv_coordinate, shiftedCommonKernelEquiv_right]

/-- The exchange of all finite rows has the same degree as each fusion block. -/
theorem rowTensorEquiv_grade {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (d : ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b))
    (hv : RowGrade (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift) d v) :
    RowGrade (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift) (d + degree a b)
      (rowTensorEquiv a b p q v) := by
  have hsource := (rowTensorGrade_iff a b (a + b) p q d v).mp hv
  apply (rowTensorGrade_iff b a (a + b) q p _ _).mpr
  intro j i
  rw [rowTensorEquiv_coordinate]
  exact shiftedCommonKernelEquiv_grade a b (p i) (q j) d _ (hsource i j)

theorem rowTensorEquiv_symm_grade {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (d : ZMod 2)
    (v : Fin (rowTensorObject b a q p).size → Coeff (a + b))
    (hv : RowGrade (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift) d v) :
    RowGrade (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift) (d + degree a b)
      ((rowTensorEquiv a b p q).symm v) := by
  have hsource := (rowTensorGrade_iff b a (a + b) q p d v).mp hv
  apply (rowTensorGrade_iff a b (a + b) p q _ _).mpr
  intro i j
  rw [rowTensorEquiv_symm_coordinate]
  exact shiftedCommonKernelEquiv_symm_grade a b (p i) (q j) d _ (hsource j i)

/-- The reversed tensor rows have the same endpoint algebra label. -/
theorem rowTensorObject_target {n m : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    rowObject (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift) =
      rowTensorObject b a q p := by
  rw [add_comm a b]
  exact rowTensorObject_eq b a q p

/-- The actual raw exchange on arbitrary finite families at two fixed labels. -/
def tensorExchange {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom realDData (rowTensorObject a b p q) (rowTensorObject b a q p) :=
  homTransport (rowTensorObject_eq a b p q) (rowTensorObject_target a b p q)
    (rowHom (a + b) _ _ (rowMatrixOf (a + b) (rowTensorEquiv a b p q).toLinearMap))

def tensorExchangeInv {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom realDData (rowTensorObject b a q p) (rowTensorObject a b p q) :=
  homTransport (rowTensorObject_target a b p q) (rowTensorObject_eq a b p q)
    (rowHom (a + b) _ _ (rowMatrixOf (a + b) (rowTensorEquiv a b p q).symm.toLinearMap))

theorem tensorExchange_grade {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom.MemGrade (degree a b) (tensorExchange a b p q) :=
  homTransport_grade _ _ _ _ (rowHom_matrixOf_grade (a + b) _ _ _ _ (rowTensorEquiv_grade a b p q))

theorem tensorExchangeInv_grade {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom.MemGrade (degree a b) (tensorExchangeInv a b p q) :=
  homTransport_grade _ _ _ _ (rowHom_matrixOf_grade (a + b) _ _ _ _ (rowTensorEquiv_symm_grade a b p q))

theorem tensorExchange_inverse {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom.comp (tensorExchange a b p q) (tensorExchangeInv a b p q) =
        Hom.id realDData (rowTensorObject a b p q) ∧
      Hom.comp (tensorExchangeInv a b p q) (tensorExchange a b p q) =
        Hom.id realDData (rowTensorObject b a q p) := by
  have h := rowHom_equiv_inverse (a + b)
    (fun z => (rowTensorObject a b p q).atom z |>.shift)
    (fun z => (rowTensorObject b a q p).atom z |>.shift)
    (rowTensorEquiv a b p q) (rowTensorEquiv_right a b p q)
  exact homTransport_inverse _ _ _ _ h.1 h.2

/-- Two shifted copies of type 1 tensored with type 3 produce four rows. -/
example : (rowTensorObject 1 3 (fun i : Fin 2 => (i.val : ZMod 2)) (fun _ : Fin 1 => 1)).size = 4 := rfl

/-- The same non-simple input admits the required odd exchange. -/
example : Hom.MemGrade 1
    (tensorExchange 1 3 (fun i : Fin 2 => (i.val : ZMod 2)) (fun _ : Fin 1 => 1)) :=
  tensorExchange_grade 1 3 _ _

end RMod.BrundanEllis.Stacking.ReferenceCommutor
