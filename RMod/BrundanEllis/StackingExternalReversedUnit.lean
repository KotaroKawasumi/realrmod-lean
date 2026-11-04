import RMod.BrundanEllis.StackingExternalReversed
import RMod.BrundanEllis.StackingExternalUnit

/-! The unit comparison for the reversed exterior order.  Away from the
identity label the coordinate is zero; at the identity it is the actual
reference unitor. This fixes the unit data before its coherence laws. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- The reversed exterior product of the two units is the external unit. -/
def reversedExteriorUnitIso (s t : Twist) :
    evenObj (exteriorModel s t) ((reversedExteriorPairing s t).obj
      (ForgetEnrichment.to SuperVec (𝟙_ (Even (pullback s))),
       ForgetEnrichment.to SuperVec (𝟙_ (Even (pullback t))))) ≅
      𝟙_ (Even (exteriorModel s t)) := by
  apply supportedFamilyIso (exteriorTwist s t).val 1 _ _
  · rintro ⟨g, h⟩ hgh
    have hswap : (h, g) ≠ (1, 1) := by
      intro he
      apply hgh
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    have hs := exteriorGenerator_support t s 1 1 (h, g) hswap
    change reference.data.id
      (reference.data.tensorObj ((pullbackSimple t 1) h).val ((pullbackSimple s 1) g).val) =
        reference.data.zero at hs
    rw [pullbackSimple_one, pullbackSimple_one] at hs
    exact hs
  · exact pullbackUnit_supported reference.data referenceProperty
      (oldTwist (exteriorTwist s t).val).data
  · change evenObj referenceCategory
      (reference.data.tensorObj (((𝟙_ (Even (pullback t))) (1 : t.group)).val)
        (((𝟙_ (Even (pullback s))) (1 : s.group)).val)) ≅
      evenObj referenceCategory (((𝟙_ (Even (pullback (exteriorTwist s t).val))) 1).val)
    rw [pullback_unit_coordinate, pullback_unit_coordinate, pullback_unit_coordinate]
    exact λ_ (𝟙_ (Even referenceCategory))

end RMod.BrundanEllis.Stacking
