import RMod.BrundanEllis.StackingSupportedIso

/-! The exterior pairing sends the pair of tensor units to the external
unit up to the reference left unitor at the identity label and the unique
maps between zero objects away from it. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

theorem pullback_unit_coordinate (s : Twist) :
    ((𝟙_ (Even (pullback s))) (1 : s.group)).val = reference.data.tensorUnit := by
  change (pullbackUnitObj reference.data referenceProperty (oldTwist s).data 1).val = _
  rw [pullbackUnitObj, supportedObj_one]

theorem pullback_simple_one_coordinate (s : Twist) :
    ((pullbackSimple s 1) (1 : s.group)).val = reference.data.tensorUnit :=
  (congrArg (fun X : Even (pullback s) => (X 1).val) (pullbackSimple_one s)).trans
    (pullback_unit_coordinate s)

/-- The only nonzero component comparison is the reference unit constraint. -/
def exteriorUnitIso (s t : Twist) :
    evenObj (exteriorModel s t) ((exteriorPairing s t).obj
      (ForgetEnrichment.to SuperVec (𝟙_ (Even (pullback s))),
       ForgetEnrichment.to SuperVec (𝟙_ (Even (pullback t))))) ≅
      𝟙_ (Even (exteriorModel s t)) := by
  have e : exteriorGenerator s t 1 1 ≅ 𝟙_ (Even (exteriorModel s t)) := by
    apply supportedFamilyIso (exteriorTwist s t).val 1 _ _
      (exteriorGenerator_support s t 1 1)
      (pullbackUnit_supported reference.data referenceProperty (oldTwist (exteriorTwist s t).val).data)
    change evenObj referenceCategory
      (reference.data.tensorObj ((pullbackSimple s 1) 1).val ((pullbackSimple t 1) 1).val) ≅
      evenObj referenceCategory (((𝟙_ (Even (pullback (exteriorTwist s t).val))) 1).val)
    rw [pullback_simple_one_coordinate, pullback_simple_one_coordinate, pullback_unit_coordinate]
    exact λ_ (𝟙_ (Even referenceCategory))
  simp only [exteriorGenerator, pullbackSimple_one] at e
  exact e

end RMod.BrundanEllis.Stacking
