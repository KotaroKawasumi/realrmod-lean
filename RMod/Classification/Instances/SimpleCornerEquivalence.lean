import RMod.Classification.Proofs.SimpleCornerMap

/-!
# The actual equivalence between the two corner algebras

The inverse is the same compression formula using the inverse ambient
algebra equivalence. The proved inverse and algebra identities complete
these specified linear maps to Mathlib's algebra-equivalence bundle.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def simpleCornerEquivalence {C D : WeaklyPointedSuperfusion.{0, 0}}
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
    (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data)) :
    @End (LinearCategory C) _ d.data.object ≃ₐ[ℝ] @End (LinearCategory D) _ t.data.object :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofLinear (simpleCornerMap C D d.data t.data φ)
      (simpleCornerMap D C t.data d.data φ.symm)
      (LinearMap.ext (simpleCornerMap_inverse t d φ.symm (by
        rw [hproj, AlgEquiv.symm_apply_apply])))
      (LinearMap.ext (simpleCornerMap_inverse d t φ hproj)))
    (simpleCornerMap_id d t φ hproj)
    (fun f g => simpleCornerMap_comp d t φ hproj g f)

theorem simpleCornerEquivalence_apply {C D : WeaklyPointedSuperfusion.{0, 0}}
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
    (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))
    (f : @End (LinearCategory C) _ d.data.object) :
    simpleCornerEquivalence d t φ hproj f = simpleCornerMap C D d.data t.data φ f := rfl

theorem simpleCornerEquivalence_symm_apply {C D : WeaklyPointedSuperfusion.{0, 0}}
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
    (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))
    (f : @End (LinearCategory D) _ t.data.object) :
    (simpleCornerEquivalence d t φ hproj).symm f = simpleCornerMap D C t.data d.data φ.symm f := rfl

end RMod.Classification
