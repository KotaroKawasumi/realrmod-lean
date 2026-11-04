import RMod.Classification.Proofs.SimpleSplitting
import RMod.Classification.Proofs.Endomorphisms

/-!
# Nonzero maps to and from the split unit

Semisimple decompositions detect a nonzero component. Graded Schur then
provides its homogeneous inverse, giving a retraction or a section at the
unit. For an inhomogeneous map, the opposite-parity contribution vanishes
because End(1) is purely even. These results supply the perfect composition
pairing used in the tensor-endomorphism argument.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem homogeneous_unit_retraction {V : C.data.Obj} {a : ZMod 2}
    (f : C.data.Hom C.data.tensorUnit V) (hf : C.data.IsHomogeneous a f)
    (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom V C.data.tensorUnit,
      C.data.comp f g = C.data.id C.data.tensorUnit ∧ C.data.IsHomogeneous a g :=
  homogeneous_simple_retraction C C.laws.simple_unit f hf hne

theorem homogeneous_unit_section {V : C.data.Obj} {a : ZMod 2}
    (f : C.data.Hom V C.data.tensorUnit) (hf : C.data.IsHomogeneous a f)
    (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom C.data.tensorUnit V,
      C.data.comp g f = C.data.id C.data.tensorUnit ∧ C.data.IsHomogeneous a g :=
  homogeneous_simple_section C C.laws.simple_unit f hf hne

/-- A retraction exists for every nonzero map out of the split unit. -/
theorem unit_retraction {V : C.data.Obj} (f : C.data.Hom C.data.tensorUnit V)
    (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom V C.data.tensorUnit, C.data.comp f g = C.data.id C.data.tensorUnit := by
  obtain ⟨f₀, f₁, h₀, h₁, hs⟩ := C.laws.grade_decomposition f
  by_cases hzero : f₀ = C.data.zero
  · have he : f₁ = f := by rw [hzero, C.laws.zero_add] at hs; exact hs
    exact (homogeneous_unit_retraction C f₁ h₁ (he ▸ hne)).imp
      (fun _ h => he ▸ h.1)
  · obtain ⟨g, hg, hge⟩ := homogeneous_unit_retraction C f₀ h₀ hzero
    have ho : C.data.comp f₁ g = C.data.zero := by
      apply (unit_end_odd_iff C _).mp
      have h := C.laws.comp_grade _ _ h₁ hge
      rw [add_zero] at h
      exact h
    exact ⟨g, by rw [← hs, C.laws.add_comp, hg, ho, C.laws.add_zero]⟩

/-- The corresponding assertion for maps into the split unit. -/
theorem unit_section {V : C.data.Obj} (f : C.data.Hom V C.data.tensorUnit)
    (hne : f ≠ C.data.zero) :
    ∃ g : C.data.Hom C.data.tensorUnit V, C.data.comp g f = C.data.id C.data.tensorUnit := by
  obtain ⟨f₀, f₁, h₀, h₁, hs⟩ := C.laws.grade_decomposition f
  by_cases hzero : f₀ = C.data.zero
  · have he : f₁ = f := by rw [hzero, C.laws.zero_add] at hs; exact hs
    exact (homogeneous_unit_section C f₁ h₁ (he ▸ hne)).imp
      (fun _ h => he ▸ h.1)
  · obtain ⟨g, hg, hge⟩ := homogeneous_unit_section C f₀ h₀ hzero
    have ho : C.data.comp g f₁ = C.data.zero := by
      apply (unit_end_odd_iff C _).mp
      have h := C.laws.comp_grade _ _ hge h₁
      rw [zero_add] at h
      exact h
    exact ⟨g, by rw [← hs, C.laws.comp_add, hg, ho, C.laws.add_zero]⟩

end RMod.Classification
