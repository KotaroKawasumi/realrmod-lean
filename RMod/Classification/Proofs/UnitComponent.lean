import RMod.Classification.Proofs.Endomorphisms
import RMod.Classification.Proofs.Components

/-!
# The tensor unit has Clifford type zero

The rank-zero case of the existing Clifford tower identifies Cl(0,0) with
the purely even real field. Composing with the proved scalar-unit algebra
isomorphism gives the raw Clifford witness required by Challenge.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem unitEndEquiv_mem_grade_iff (a : ZMod 2) (r : ℝ) :
    unitEndEquiv C r ∈ LinearCategory.grade C C.data.tensorUnit C.data.tensorUnit a ↔
      r ∈ Superfusion.evenGrading ℝ ℝ a := by
  rcases parity_cases a with rfl | rfl
  · simp only [Superfusion.evenGrading_zero, Submodule.mem_top, iff_true]
    exact unit_end_even C _
  · rw [Superfusion.evenGrading_one, Submodule.mem_bot]
    change C.data.IsHomogeneous 1 (unitEndEquiv C r) ↔ r = 0
    rw [unit_end_odd_iff C]
    change unitEndEquiv C r = 0 ↔ r = 0
    exact map_eq_zero_iff (unitEndEquiv C) (unitEndEquiv C).injective

/-- The unit realizes Cl(0,0), with both algebra operations and grades checked. -/
theorem hasCliffordEnd_unit : HasCliffordEnd C.data C.data.tensorUnit 0 := by
  let t : ℝ ≃ₐ[ℝ] CliffordAlgebra (Superfusion.diagForm (-1 : ℝ) 0) :=
    Superfusion.towerCliffordEquiv (-1 : ℝ) 0 (by norm_num)
  apply (hasCliffordEnd_iff C C.data.tensorUnit 0).mpr
  refine ⟨t.symm.trans (unitEndEquiv C), ?_⟩
  intro a x
  have hg : (Superfusion.evenGrading ℝ ℝ a).map t.toLinearMap =
      CliffordAlgebra.evenOdd (Superfusion.diagForm (-1 : ℝ) 0) a :=
    Superfusion.towerCliffordHom_map_grading (-1 : ℝ) 0 (by norm_num) a
  change x ∈ CliffordAlgebra.evenOdd (Superfusion.diagForm (-1 : ℝ) 0) a ↔
    unitEndEquiv C (t.symm x) ∈ LinearCategory.grade C _ _ a
  rw [unitEndEquiv_mem_grade_iff C, ← hg]
  exact Submodule.mem_map_equiv (Superfusion.evenGrading ℝ ℝ a) (e := t.toLinearEquiv)

theorem hasBWType_unit : HasBWType C.data C.data.tensorUnit 0 := by
  refine ⟨1, fun _ => C.data.tensorUnit, C.data.tensorUnit, Nat.zero_lt_one,
    fun _ => SameParityOrbit.refl C.laws _, decomposition_singleton C.laws _, ?_⟩
  exact hasCliffordEnd_unit C

/-- The unit's membership in the neutral component follows from the
category's split-unit laws; P is used only by the component interface. -/
theorem InComponent.tensor_unit {D : PiSuperfusionData.{0, 0}} (hD : ReferenceProperty D) :
    InComponent D.toWeaklyPointedSuperfusionData 0 D.tensorUnit :=
  InComponent.of_simple hD hD.simple_unit
    (hasBWType_unit ⟨D.toWeaklyPointedSuperfusionData, hD.toWeaklyPointedSuperfusionLaws⟩)

/-- The specified parity object belongs to the neutral component as well,
using its actual odd isomorphism to the unit. -/
theorem InComponent.parity_object {D : PiSuperfusionData.{0, 0}} (hD : ReferenceProperty D) :
    InComponent D.toWeaklyPointedSuperfusionData 0 D.pi.object :=
  InComponent.of_iso hD (InComponent.tensor_unit hD) D.pi.inv
    ⟨D.pi.hom, hD.pi.inv_hom, hD.pi.hom_inv⟩

end RMod.Classification
