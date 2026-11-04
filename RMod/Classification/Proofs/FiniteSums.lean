import RMod.Classification.Abstract.FiniteSums
import RMod.Classification.Proofs.Components

/-!
# Choosing actual finite sums from the reference property

Existence of sums is already a categorical law. The new constructor
isolates classical choice in the computational data and then proves the
biproduct equations for exactly those chosen objects and maps. The
classification statement therefore needs no extra finite-sum hypothesis.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0})
  (hC : WeaklyPointedSuperfusionLaws C.toWeaklyPointedSuperfusionData)

include hC

theorem exists_biproduct_data {n : ℕ} (S : Fin n → C.Obj) :
    ∃ b : BiproductData C S, BiproductLaws C S b := by
  obtain ⟨X, i, p, hi, hp, hd, ho, ht⟩ := hC.has_finite_biproducts S
  exact ⟨⟨X, i, p⟩, ⟨hi, hp, hd, ho, ht⟩⟩

noncomputable def finiteSumsData : FiniteSumsData C where
  sum S := Classical.choose (exists_biproduct_data C hC S)

theorem finiteSumsLaws : FiniteSumsLaws C (finiteSumsData C hC) where
  sum S := Classical.choose_spec (exists_biproduct_data C hC S)

noncomputable def finiteSums : FiniteSums C where
  data := finiteSumsData C hC
  laws := finiteSumsLaws C hC

/-- The selected object really has the specified decomposition. -/
theorem finiteSums_decomposition {n : ℕ} (S : Fin n → C.Obj) :
    C.HasDecomposition ((finiteSumsData C hC).sum S).object S := by
  let b := (finiteSumsData C hC).sum S
  have hb := (finiteSumsLaws C hC).sum S
  exact ⟨b.inclusion, b.projection, hb.inclusion_even, hb.projection_even,
    hb.diagonal, hb.off_diagonal, hb.total⟩

omit hC in
/-- Choosing a finite sum does not leave its intrinsic type component. -/
theorem finiteSums_inComponent (hP : ReferenceProperty C) {n : ℕ} (S : Fin n → C.Obj)
    (r : ZMod 8) (hS : ∀ i, InComponent C.toWeaklyPointedSuperfusionData r (S i)) :
    InComponent C.toWeaklyPointedSuperfusionData r
      ((finiteSumsData C hP.toWeaklyPointedSuperfusionLaws).sum S).object :=
  InComponent.of_decomposition hP hS
    (finiteSums_decomposition C hP.toWeaklyPointedSuperfusionLaws S)

end RMod.Classification
