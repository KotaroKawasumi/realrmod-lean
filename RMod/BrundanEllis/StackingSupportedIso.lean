import RMod.BrundanEllis.StackingExternalSupport
import RMod.Hierarchy.Bridge.OldEquivalenceData

/-! An even isomorphism in the unique nonzero coordinate extends to an
isomorphism of supported pullback objects. The extension is by zero and
its inverse laws are checked at the support coordinate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy.Hierarchy

/-- Supported families inherit their even isomorphisms from the reference coordinate. -/
def supportedFamilyIso (s : Twist) (k : s.group) (X Y : Even (pullback s))
    (hX : ∀ j, j ≠ k → reference.data.id (X j).val = reference.data.zero)
    (hY : ∀ j, j ≠ k → reference.data.id (Y j).val = reference.data.zero)
    (e : evenObj referenceCategory (X k).val ≅ evenObj referenceCategory (Y k).val) : X ≅ Y := by
  let J := evenForget reference.toWeaklyPointedSuperfusion
  let d := J.mapIso e
  let f := singleComponentHom reference.data (oldTwist s).data k d.hom.hom
  let g := singleComponentHom reference.data (oldTwist s).data k d.inv.hom
  apply ofOldEvenIso (oldPullback s).toWeaklyPointedSuperfusion f g
  · exact singleComponentHom_grade reference.data (oldTwist s).data k
      referenceProperty.toWeaklyPointedSuperfusionLaws d.hom.hom d.hom.property
  · exact singleComponentHom_grade reference.data (oldTwist s).data k
      referenceProperty.toWeaklyPointedSuperfusionLaws d.inv.hom d.inv.property
  · apply hom_ext_of_supported_source reference.data (oldTwist s).data k
      referenceProperty.toWeaklyPointedSuperfusionLaws hX
    change reference.data.comp (f k) (g k) = reference.data.id (X k).val
    simp only [f, g, singleComponentHom_at]
    exact congrArg (fun h => h.hom) d.hom_inv_id
  · apply hom_ext_of_supported_source reference.data (oldTwist s).data k
      referenceProperty.toWeaklyPointedSuperfusionLaws hY
    change reference.data.comp (g k) (f k) = reference.data.id (Y k).val
    simp only [f, g, singleComponentHom_at]
    exact congrArg (fun h => h.hom) d.inv_hom_id

end RMod.BrundanEllis.Stacking
