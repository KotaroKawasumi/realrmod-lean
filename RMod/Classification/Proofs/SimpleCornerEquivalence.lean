import RMod.Classification.Instances.SimpleCornerEquivalence

/-!
# Grading of the transported corner algebra equivalence

The forward and inverse compression formulas preserve degree because
all retract maps are even and the ambient algebra equivalence preserves
and reflects the grading. Thus the corner equivalence is graded in both
directions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C} {Y : LinearCategory D}
  (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
  (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))
  (hφ : ∀ {a : ZMod 2} (f : End X), D.data.IsHomogeneous a (φ f) ↔ C.data.IsHomogeneous a f)

include hφ

theorem simpleCornerEquivalence_grade {a : ZMod 2} (f : @End (LinearCategory C) _ d.data.object)
    (hf : C.data.IsHomogeneous a f) : D.data.IsHomogeneous a (simpleCornerEquivalence d t φ hproj f) :=
  simpleCornerMap_grade d t φ (fun hf => (hφ _).mpr hf) f hf

theorem simpleCornerEquivalence_grade_iff {a : ZMod 2} (f : @End (LinearCategory C) _ d.data.object) :
    D.data.IsHomogeneous a (simpleCornerEquivalence d t φ hproj f) ↔ C.data.IsHomogeneous a f := by
  refine ⟨fun hf => ?_, simpleCornerEquivalence_grade d t φ hproj hφ f⟩
  have hφi : ∀ {b : ZMod 2} {g : End Y}, D.data.IsHomogeneous b g →
      C.data.IsHomogeneous b (φ.symm g) := by
    intro b g hg
    apply (hφ (φ.symm g)).mp
    rw [AlgEquiv.apply_symm_apply]
    exact hg
  have h := simpleCornerMap_grade t d φ.symm hφi (simpleCornerEquivalence d t φ hproj f) hf
  change C.data.IsHomogeneous a ((simpleCornerEquivalence d t φ hproj).symm
    (simpleCornerEquivalence d t φ hproj f)) at h
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

end RMod.Classification
