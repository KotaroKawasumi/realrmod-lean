import RMod.BrundanEllis.StackingReferenceFiniteNaturality

/-! Identify the finite-family tensor operator with the actual raw tensor
coefficients by evaluating all unit columns. This ties the blockwise
naturality calculations to the given reference tensor, not a replacement tensor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Reindexing a unit column gives a unit column in exactly one tensor block. -/
theorem rowTensorCoordinates_single {n m : ℕ} (a b c : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (z : Fin (rowTensorObject a b p q).size) (x : Coeff c) (i : Fin n) (j : Fin m) :
    rowTensorCoordinates a b p q (Coeff c) (Pi.single z x) i j =
      if i = (rowTensorIndex a b p q z).1 then
        if j = (rowTensorIndex a b p q z).2.1 then Pi.single (rowTensorIndex a b p q z).2.2 x else 0
      else 0 := by
  funext r
  change (Pi.single z x : Fin (rowTensorObject a b p q).size → Coeff c)
    ((rowTensorIndex a b p q).symm (i, j, r)) = _
  rw [Pi.single_apply]
  have he : (rowTensorIndex a b p q).symm (i, j, r) = z ↔ (i, j, r) = rowTensorIndex a b p q z := by
    constructor
    · intro h
      simpa only [Equiv.apply_symm_apply] using congrArg (rowTensorIndex a b p q) h
    · intro h
      apply (rowTensorIndex a b p q).injective
      simpa only [Equiv.apply_symm_apply] using h
  simp only [he, Prod.ext_iff, Pi.single_apply, ite_apply, Pi.zero_apply]
  split_ifs <;> simp_all

/-- Coordinates at the reindexed position recover the original vector entry. -/
theorem rowTensorCoordinates_at {n m : ℕ} (a b c : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (v : Fin (rowTensorObject a b p q).size → Coeff c) (z : Fin (rowTensorObject a b p q).size) :
    rowTensorCoordinates a b p q (Coeff c) v (rowTensorIndex a b p q z).1
      (rowTensorIndex a b p q z).2.1 (rowTensorIndex a b p q z).2.2 = v z := by
  change v ((rowTensorIndex a b p q).symm (rowTensorIndex a b p q z)) = v z
  rw [Equiv.symm_apply_apply]

/-- The flattened operator has the specified sum in each output block. -/
theorem familyTensorOperator_coordinate {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (v : Fin (rowTensorObject a b p q).size → Coeff (a + b)) (i' : Fin n') (j' : Fin m') :
    rowTensorCoordinates a b p' q' (Coeff (a + b)) (familyTensorOperator a b p p' q q' F G v) i' j' =
      ∑ i : Fin n, ∑ j : Fin m,
        shiftedTensorOperator a b (p i) (q j) (q' j') (F i i') (G j j')
          (rowTensorCoordinates a b p q (Coeff (a + b)) v i j) := by
  change (rowTensorCoordinates a b p' q' (Coeff (a + b)))
    ((rowTensorCoordinates a b p' q' (Coeff (a + b))).symm
      (blockTensorOperator a b p q q' F G (rowTensorCoordinates a b p q (Coeff (a + b)) v))) i' j' = _
  rw [LinearEquiv.apply_symm_apply, blockTensorOperator_apply]

/-- A unit column of the finite-family operator is exactly the stored tensor coefficient. -/
theorem familyTensorOperator_unit_column {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (s : Fin (rowTensorObject a b p q).size) (t : Fin (rowTensorObject a b p' q').size) :
    familyTensorOperator a b p p' q q' F G (Pi.single s (Coeff.one (a + b))) t =
      Tensor.coefficient realDData (shiftCData realDData realCData realComputableNuBeta.data) a b
        (p (rowTensorIndex a b p q s).1) (q (rowTensorIndex a b p q s).2.1)
        (q' (rowTensorIndex a b p' q' t).2.1)
        (rowTensorIndex a b p q s).2.2 (rowTensorIndex a b p' q' t).2.2
        (F (rowTensorIndex a b p q s).1 (rowTensorIndex a b p' q' t).1)
        (G (rowTensorIndex a b p q s).2.1 (rowTensorIndex a b p' q' t).2.1) := by
  have h := familyTensorOperator_coordinate a b p p' q q' F G
    (Pi.single s (Coeff.one (a + b))) (rowTensorIndex a b p' q' t).1 (rowTensorIndex a b p' q' t).2.1
  simp_rw [rowTensorCoordinates_single, apply_ite, map_zero] at h
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  have hh := congrFun h (rowTensorIndex a b p' q' t).2.2
  rw [rowTensorCoordinates_at, shiftedTensorOperator_unit_column] at hh
  exact hh

/-- A raw tensor entry for constant-label families is the specified coefficient. -/
theorem tensor_entry_rows {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (i : Fin n) (j : Fin m) (r : FusionTable.Index a b)
    (i' : Fin n') (j' : Fin m') (r' : FusionTable.Index a b) :
    @Eq (Coeff (a + b))
      ((Tensor.entry realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j'))
        ⟨i, j, r⟩ ⟨i', j', r'⟩).coeff rfl)
      (Tensor.coefficient realDData (shiftCData realDData realCData realComputableNuBeta.data)
        a b (p i) (q j) (q' j') r r' (F i i') (G j j')) := by
  simp only [Tensor.entry, rowObject, Obj.atom, Atom.label, Atom.shift,
    Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion, rowHom,
    dif_pos rfl, dite_true, cast_eq, AtomHom.coeff_ofLabelEq]

/-- Flattening the tensor slots retains exactly those raw tensor coefficients. -/
theorem tensor_hom_rows_coeff {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b)
    (s : Fin (rowTensorObject a b p q).size) (t : Fin (rowTensorObject a b p' q').size) :
    @Eq (Coeff (a + b))
      ((Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j')) s t).coeff rfl)
      (Tensor.coefficient realDData (shiftCData realDData realCData realComputableNuBeta.data) a b
        (p (rowTensorIndex a b p q s).1) (q (rowTensorIndex a b p q s).2.1)
        (q' (rowTensorIndex a b p' q' t).2.1)
        (rowTensorIndex a b p q s).2.2 (rowTensorIndex a b p' q' t).2.2
        (F (rowTensorIndex a b p q s).1 (rowTensorIndex a b p' q' t).1)
        (G (rowTensorIndex a b p q s).2.1 (rowTensorIndex a b p' q' t).2.1)) :=
  tensor_entry_rows a b p p' q q' F G _ _ _ _ _ _

/-- The operator used in finite naturality is the actual reference tensor morphism. -/
theorem familyTensorOperator_actual {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (F : Fin n → Fin n' → Coeff a) (G : Fin m → Fin m' → Coeff b) :
    rowHom (a + b) (fun z => (rowTensorObject a b p q).atom z |>.shift)
      (fun z => (rowTensorObject a b p' q').atom z |>.shift)
      (rowMatrixOf (a + b) (familyTensorOperator a b p p' q q' F G)) =
    Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (rowHom a p p' (fun i' i => F i i')) (rowHom b q q' (fun j' j => G j j')) := by
  funext s t
  apply AtomHom.ext_same_label
  rw [rowHom_coeff]
  exact (familyTensorOperator_unit_column a b p p' q q' F G s t).trans
    (tensor_hom_rows_coeff a b p p' q q' F G s t).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor
