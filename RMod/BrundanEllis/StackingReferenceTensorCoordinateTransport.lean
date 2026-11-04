import RMod.BrundanEllis.StackingReferenceUniformTensorOperator
import RMod.BrundanEllis.StackingReferenceInnerRightOperator
import RMod.BrundanEllis.StackingReferenceAssociatorOperator

/-! Coordinate changes for inner tensor legs preserve both fusion rows and
division-algebra coefficients. Tensoring with an unshifted identity removes
the endpoint signs, leaving the given kernel action. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
attribute [local irreducible] Tensor.slotIndexEquiv Tensor.slots

/-- Label transport simultaneously casts a fusion row and its endpoint coefficient. -/
theorem kernelLabelCast_apply {a b c d : ZMod 8} (h : a = b) (k : c = d)
    (v : RealCCarrier a c) (r : FusionTable.Index b d) :
    kernelLabelCast h k v r = coefficientCast (congrArg₂ (· + ·) h k)
      (v (Fin.cast (congrArg₂ RealPChiKernel.fusionRank h k).symm r)) := by
  cases h
  cases k
  rfl

/-- The existing kernel action is invariant under transport of its labels. -/
theorem kernelLabelCast_leftOperator {a b c d : ZMod 8} (h : a = b) (k : c = d)
    (x : Coeff a) (y : Coeff c) (v : RealCCarrier a c) :
    kernelLabelCast h k (leftOperator a c x y v) =
      leftOperator b d (coefficientCast h x) (coefficientCast k y) (kernelLabelCast h k v) := by
  cases h
  cases k
  rfl

/-- Transport preserves the actual division-algebra unit. -/
theorem coefficientCast_one {a b : ZMod 8} (h : a = b) :
    coefficientCast h (Coeff.one a) = Coeff.one b := by
  cases h
  rfl

/-- Changing the first uniform label transports each fusion-kernel block. -/
theorem uniformTensorCoordinates_leftCast {a a' : ZMod 8} (h : a = a') (b : ZMod 8)
    (X Y : Obj) (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (v : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff (a + b))
    (i : Fin X.size) (j : Fin Y.size) :
    uniformTensorCoordinates a' b (a' + b) X Y (fun i => (hX i).trans h) hY
      (rowCoefficientCast (congrArg (fun z => z + b) h) v) i j =
      kernelLabelCast h rfl (uniformTensorCoordinates a b (a + b) X Y hX hY v i j) := by
  cases h
  rfl

/-- Changing the second uniform label has the corresponding blockwise transport. -/
theorem uniformTensorCoordinates_rightCast (a : ZMod 8) {b b' : ZMod 8} (h : b = b')
    (X Y : Obj) (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (v : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff (a + b))
    (i : Fin X.size) (j : Fin Y.size) :
    uniformTensorCoordinates a b' (a + b') X Y hX (fun j => (hY j).trans h)
      (rowCoefficientCast (congrArg (fun z => a + z) h) v) i j =
      kernelLabelCast rfl h (uniformTensorCoordinates a b (a + b) X Y hX hY v i j) := by
  cases h
  rfl

/-- An identity in the second tensor slot leaves the first coefficient action unchanged. -/
theorem shiftedTensorOperator_right_one (a b : ZMod 8) (p : ZMod 2) (x : Coeff a) :
    shiftedTensorOperator a b p 0 0 x (Coeff.one b) = leftOperator a b x (Coeff.one b) := by
  have hx : routeRowTwist realDData a 0 x = x :=
    routeRowTwist_zeroParity (realDData.algebra a) (realDLaws.algebra_laws a) x
  have hy : routeRowTwist realDData b p (Coeff.one b) = Coeff.one b :=
    routeRowTwist_one (realDData.algebra b) (realDLaws.algebra_laws b) p
  simp only [shiftedTensorOperator, hx, hy, zero_add, mul_zero,
    (show paritySign (0 : ZMod 2) = (1 : ℝ) from rfl), one_smul]

/-- An unshifted identity in the first slot similarly leaves the second coefficient action. -/
theorem shiftedTensorOperator_left_one (a b : ZMod 8) (q q' : ZMod 2) (y : Coeff b) :
    shiftedTensorOperator a b 0 q q' (Coeff.one a) y = leftOperator a b (Coeff.one a) y := by
  have hx : routeRowTwist realDData a q' (Coeff.one a) = Coeff.one a :=
    routeRowTwist_one (realDData.algebra a) (realDLaws.algebra_laws a) q'
  have hy : routeRowTwist realDData b 0 y = y :=
    routeRowTwist_zeroParity (realDData.algebra b) (realDLaws.algebra_laws b) y
  simp only [shiftedTensorOperator, hx, hy, zero_mul,
    (show paritySign (0 : ZMod 2) = (1 : ℝ) from rfl), one_smul]

/-- Left-associated triple coordinates are the uniform tensor coordinates at the inner fusion row. -/
theorem uniformTensorCoordinates_leftAtom (a b c d : ZMod 8)
    (v : Fin (leftAtomTensor a b c).size → Coeff d) (r : FusionTable.Index a b)
    (s : FusionTable.Index (a + b) c) :
    uniformTensorCoordinates (a + b) c d (atomTensor a b) (Obj.singleton (c, 0))
      (fun _ => rfl) (fun _ => rfl) v ((atomRowIndex a b).symm r) (0 : Fin 1) s =
      v ((leftAtomIndex a b c).symm (r, s)) := rfl

/-- The same identification holds on the right-associated route. -/
theorem uniformTensorCoordinates_rightAtom (a b c d : ZMod 8)
    (v : Fin (rightAtomTensor a b c).size → Coeff d) (r : FusionTable.Index b c)
    (s : FusionTable.Index a (b + c)) :
    uniformTensorCoordinates a (b + c) d (Obj.singleton (a, 0)) (atomTensor b c)
      (fun _ => rfl) (fun _ => rfl) v (0 : Fin 1) ((atomRowIndex b c).symm r) s =
      v ((rightAtomIndex a b c).symm (r, s)) := rfl

/-- Read one complete left kernel block from the triple coordinates. -/
theorem leftTripleCoordinates_uniform (a b c : ZMod 8)
    (v : Fin (leftAtomTensor a b c).size → Coeff (a + b + c)) (r : FusionTable.Index a b) :
    leftTripleCoordinates a b c v r =
      uniformTensorCoordinates (a + b) c (a + b + c) (atomTensor a b) (Obj.singleton (c, 0))
        (fun _ => rfl) (fun _ => rfl) v ((atomRowIndex a b).symm r) (0 : Fin 1) := by
  funext s
  exact (uniformTensorCoordinates_leftAtom a b c (a + b + c) v r s).symm

/-- An arbitrary input row reads the corresponding left triple block. -/
theorem uniformTensorCoordinates_leftTriple_symm (a b c : ZMod 8)
    (v : LeftCarrier a b c) (i : Fin (atomTensor a b).size) :
    uniformTensorCoordinates (a + b) c (a + b + c) (atomTensor a b) (Obj.singleton (c, 0))
      (fun _ => rfl) (fun _ => rfl) ((leftTripleCoordinates a b c).symm v) i (0 : Fin 1) =
      v (atomRowIndex a b i) := by
  have h := leftTripleCoordinates_uniform a b c ((leftTripleCoordinates a b c).symm v)
    (atomRowIndex a b i)
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The only matrix coefficient of an unshifted singleton identity is its algebra unit. -/
theorem singleton_id_coefficient (a : ZMod 8) :
    (Hom.id realDData (Obj.singleton (a, 0)) (0 : Fin 1) (0 : Fin 1)).coeff rfl = Coeff.one a := by
  simp [Hom.id, AtomHom.id]
  rfl

/-- Rowwise coefficient transports compose using the original equality transports. -/
theorem rowCoefficientCast_trans {a b c : ZMod 8} {n : ℕ}
    (h : a = b) (k : b = c) (v : Fin n → Coeff a) :
    rowCoefficientCast k (rowCoefficientCast h v) = rowCoefficientCast (h.trans k) v := by
  cases h
  cases k
  rfl

/-- Extracting tensor blocks commutes with transport of their endpoint coefficient algebra. -/
theorem uniformTensorCoordinates_coefficientCast (a b : ZMod 8) {c d : ZMod 8} (h : c = d)
    (X Y : Obj) (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b)
    (v : Fin (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y).size → Coeff c)
    (i : Fin X.size) (j : Fin Y.size) (r : FusionTable.Index a b) :
    uniformTensorCoordinates a b d X Y hX hY (rowCoefficientCast h v) i j r =
      coefficientCast h (uniformTensorCoordinates a b c X Y hX hY v i j r) := by
  cases h
  rfl

/-- A right triple block becomes the natural kernel block after endpoint reassociation. -/
theorem rightTripleCoordinates_uniform_cast (a b c : ZMod 8)
    (v : Fin (rightAtomTensor a b c).size → Coeff (a + b + c)) (r : FusionTable.Index b c) :
    rightSliceCoordinates a b c (rightTripleCoordinates a b c v r) =
      uniformTensorCoordinates a (b + c) (a + (b + c)) (Obj.singleton (a, 0)) (atomTensor b c)
        (fun _ => rfl) (fun _ => rfl) (rowCoefficientCast (add_assoc a b c) v)
        (0 : Fin 1) ((atomRowIndex b c).symm r) := by
  funext s
  rw [uniformTensorCoordinates_coefficientCast, uniformTensorCoordinates_rightAtom]
  rfl

/-- Right triple input rows retain their fusion index and the reassociated coefficient. -/
theorem uniformTensorCoordinates_rightTriple_symm (a b c : ZMod 8)
    (v : RightCarrier a b c) (i : Fin (atomTensor b c).size) :
    uniformTensorCoordinates a (b + c) (a + (b + c)) (Obj.singleton (a, 0)) (atomTensor b c)
      (fun _ => rfl) (fun _ => rfl)
      (rowCoefficientCast (add_assoc a b c) ((rightTripleCoordinates a b c).symm v)) (0 : Fin 1) i =
      rightSliceCoordinates a b c (v (atomRowIndex b c i)) := by
  have h := rightTripleCoordinates_uniform_cast a b c ((rightTripleCoordinates a b c).symm v)
    (atomRowIndex b c i)
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor
