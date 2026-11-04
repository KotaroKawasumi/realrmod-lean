import RMod.Classification.Proofs.PullbackSimples

/-!
# The simple split real unit of the pullback

The tensor unit is supported at the identity element and its supported
coordinate is C's unit. Simplicity and the scalar description of its full
endomorphism algebra follow from the corresponding original laws.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem pullbackUnit_supported (g : t.group) (hg : g ≠ 1) :
    C.id (pullbackUnitObj C hC t g).val = C.zero := by
  rw [pullbackUnitObj, supportedObj_ne_one C hC t _ _ g hg]
  exact pullbackZero_id C hC t g

theorem twistedPullback_simple_unit :
    (twistedPullbackData C hC t ht).IsSimple (twistedPullbackData C hC t ht).tensorUnit := by
  apply twistedPullback_supported_simple C hC t ht _ 1
  · exact pullbackUnit_supported C hC t
  · change C.IsSimple (pullbackUnitObj C hC t 1).val
    rw [pullbackUnitObj, supportedObj_one]
    exact hC.simple_unit

theorem twistedPullback_unit_end_scalar_injective (r s : ℝ)
    (he : (twistedPullbackData C hC t ht).smul r
      ((twistedPullbackData C hC t ht).id (twistedPullbackData C hC t ht).tensorUnit) =
      (twistedPullbackData C hC t ht).smul s
      ((twistedPullbackData C hC t ht).id (twistedPullbackData C hC t ht).tensorUnit)) : r = s := by
  have h := congrFun he 1
  change C.smul r (C.id (pullbackUnitObj C hC t 1).val) =
    C.smul s (C.id (pullbackUnitObj C hC t 1).val) at h
  rw [pullbackUnitObj, supportedObj_one] at h
  exact hC.unit_end_scalar_injective r s h

theorem twistedPullback_unit_end_scalar_surjective
    (f : (twistedPullbackData C hC t ht).Hom (twistedPullbackData C hC t ht).tensorUnit
      (twistedPullbackData C hC t ht).tensorUnit) :
    ∃ r : ℝ, (twistedPullbackData C hC t ht).smul r
      ((twistedPullbackData C hC t ht).id (twistedPullbackData C hC t ht).tensorUnit) = f := by
  have hs : ∀ q : C.Hom (pullbackUnitObj C hC t 1).val (pullbackUnitObj C hC t 1).val,
      ∃ r : ℝ, C.smul r (C.id (pullbackUnitObj C hC t 1).val) = q := by
    rw [pullbackUnitObj, supportedObj_one]
    exact hC.unit_end_scalar_surjective
  obtain ⟨r, hr⟩ := hs (f 1)
  refine ⟨r, ?_⟩
  exact hom_ext_of_supported_source C t 1 hC.toWeaklyPointedSuperfusionLaws
    (pullbackUnit_supported C hC t) _ f hr

end RMod.Classification
