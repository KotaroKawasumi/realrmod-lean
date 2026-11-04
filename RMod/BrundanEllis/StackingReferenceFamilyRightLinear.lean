import RMod.BrundanEllis.StackingReferenceTensorColumns

/-! The finite tensor actions commute with the strict right algebra action.
This makes their unit-column matrices compatible with composition in the
actual reference category. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Right multiplication is a real-linear operator on finite row vectors. -/
def rowRightLinear {n : ℕ} (a : ZMod 8) (x : Coeff a) :
    (Fin n → Coeff a) →ₗ[ℝ] (Fin n → Coeff a) where
  toFun v := rowRight a v x
  map_add' v w := by
    funext i
    with_unfolding_all exact Coeff.add_mul a (v i) (w i) x
  map_smul' r v := rowRight_smul a r v x

theorem rowRight_sum {n : ℕ} {I : Type} [Fintype I] (a : ZMod 8)
    (v : I → Fin n → Coeff a) (x : Coeff a) :
    rowRight a (∑ i, v i) x = ∑ i, rowRight a (v i) x :=
  map_sum (rowRightLinear a x) v Finset.univ

/-- The forward finite tensor action is right-linear. -/
theorem familyTensorOperator_right {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b)) (x : Coeff (a + b)) :
    familyTensorOperator a b p p' q q' F G (rowRight (a + b) v x) =
      rowRight (a + b) (familyTensorOperator a b p p' q q' F G v) x := by
  apply (rowTensorCoordinates a b p' q' (Coeff (a + b))).injective
  funext i' j'
  rw [familyTensorOperator_coordinate, rowTensorCoordinates_right, familyTensorOperator_coordinate]
  simp_rw [rowTensorCoordinates_right, shiftedTensorOperator_right, rowRight_sum]

/-- Coordinates of the reversed finite tensor action retain its stated block sum. -/
theorem reversedFamilyTensorOperator_coordinate {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin (rowTensorObject b a q p).size → Coeff (a + b)) (j' : Fin m') (i' : Fin n') :
    rowTensorCoordinates b a q' p' (Coeff (a + b)) (reversedFamilyTensorOperator a b p p' q q' F G v) j' i' =
      ∑ i : Fin n, ∑ j : Fin m,
        reversedTensorOperator a b (q j) (p i) (p' i') (G j j') (F i i')
          (rowTensorCoordinates b a q p (Coeff (a + b)) v j i) := by
  change (rowTensorCoordinates b a q' p' (Coeff (a + b)))
    ((rowTensorCoordinates b a q' p' (Coeff (a + b))).symm
      (reversedBlockTensorOperator a b p p' q F G (rowTensorCoordinates b a q p (Coeff (a + b)) v))) j' i' = _
  rw [LinearEquiv.apply_symm_apply, reversedBlockTensorOperator_apply]

/-- The reversed finite tensor action uses the same strict right algebra. -/
theorem reversedFamilyTensorOperator_right {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin (rowTensorObject b a q p).size → Coeff (a + b)) (x : Coeff (a + b)) :
    reversedFamilyTensorOperator a b p p' q q' F G (rowRight (a + b) v x) =
      rowRight (a + b) (reversedFamilyTensorOperator a b p p' q q' F G v) x := by
  apply (rowTensorCoordinates b a q' p' (Coeff (a + b))).injective
  funext j' i'
  rw [reversedFamilyTensorOperator_coordinate, rowTensorCoordinates_right, reversedFamilyTensorOperator_coordinate]
  simp_rw [rowTensorCoordinates_right, reversedTensorOperator_right, rowRight_sum]

/-- The untransported exchange is already a morphism between the actual row presentations. -/
def exchangeRows {n m : ℕ} (a b : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Hom realDData (rowTensorObject a b p q)
      (rowObject (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift)) :=
  rowHom (a + b) _ _ (rowMatrixOf (a + b) (rowTensorEquiv a b p q).toLinearMap)

/-- Common-algebra row presentation of the reversed tensor morphism. -/
def reversedFamilyHom {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    Hom realDData (rowObject (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift))
      (rowObject (a + b) (fun z => (rowTensorObject b a q' p').atom z |>.shift)) :=
  rowHom (a + b) _ _ (rowMatrixOf (a + b) (reversedFamilyTensorOperator a b p p' q q' F G))

/-- Naturality is now an equality of compositions of actual raw morphisms. -/
theorem familyExchange_rows_naturality {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) (d e : ZMod 2)
    (hF : ∀ i i', (realDData.algebra a).MemGrade (d + p i + p' i') (F i i'))
    (hG : ∀ j j', (realDData.algebra b).MemGrade (e + q j + q' j') (G j j')) :
    Hom.comp
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j')))
      (exchangeRows a b p' q') =
    Hom.smul (paritySign (degree a b * (d + e) + d * e))
      (Hom.comp (exchangeRows a b p q) (reversedFamilyHom a b p p' q q' F G)) := by
  rw [← familyTensorOperator_actual]
  change Hom.comp
    (rowHom (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift)
      (fun z => (rowTensorObject a b p' q').atom z |>.shift)
      (rowMatrixOf (a + b) (familyTensorOperator a b p p' q q' F G)))
    (rowHom (a + b) (fun z => (rowTensorObject a b p' q').atom z |>.shift)
      (fun z => (rowTensorObject b a q' p').atom z |>.shift)
      (rowMatrixOf (a + b) (rowTensorEquiv a b p' q').toLinearMap)) =
    Hom.smul (paritySign (degree a b * (d + e) + d * e))
      (Hom.comp
        (rowHom (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift)
          (fun z => (rowTensorObject b a q p).atom z |>.shift)
          (rowMatrixOf (a + b) (rowTensorEquiv a b p q).toLinearMap))
        (rowHom (a + b) (fun z => (rowTensorObject b a q p).atom z |>.shift)
          (fun z => (rowTensorObject b a q' p').atom z |>.shift)
          (rowMatrixOf (a + b) (reversedFamilyTensorOperator a b p p' q q' F G))))
  rw [rowHom_comp, rowHom_comp, rowHom_smul]
  apply congrArg (rowHom (a + b) _ _)
  rw [← rowMatrixOf_comp (a + b) _ _ (familyTensorOperator_right a b p p' q q' F G)
    (rowTensorEquiv_right a b p' q'),
    ← rowMatrixOf_comp (a + b) _ _ (rowTensorEquiv_right a b p q)
      (reversedFamilyTensorOperator_right a b p p' q q' F G)]
  rw [rowTensorEquiv_naturality a b p p' q q' F G d e hF hG]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
