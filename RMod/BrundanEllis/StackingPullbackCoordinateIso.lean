import RMod.BrundanEllis.StackingSupportedIso

/-! A family of even reference isomorphisms is an even isomorphism of
pullback objects. Both maps are retained coordinatewise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy.Hierarchy

/-- Assemble all reference-coordinate isomorphisms, including zero coordinates. -/
def pullbackCoordinateIso (s : Twist) (X Y : Even (pullback s))
    (e : ∀ g : s.group,
      referenceEvenObj reference.data referenceProperty (X g).val ≅
        referenceEvenObj reference.data referenceProperty (Y g).val) : X ≅ Y :=
  ofOldEvenIso (oldPullback s).toWeaklyPointedSuperfusion
    (fun g => (e g).hom.hom) (fun g => (e g).inv.hom)
    (fun g => (e g).hom.property) (fun g => (e g).inv.property)
    (by funext g; exact congrArg (fun f => f.hom) (e g).hom_inv_id)
    (by funext g; exact congrArg (fun f => f.hom) (e g).inv_hom_id)

/-- Coordinate evaluation of the assembled forward map is the specified map. -/
theorem pullbackCoordinateIso_hom (s : Twist) (X Y : Even (pullback s))
    (e : ∀ g : s.group,
      referenceEvenObj reference.data referenceProperty (X g).val ≅
        referenceEvenObj reference.data referenceProperty (Y g).val) (g : s.group) :
    (evenHomEquiv (oldPullback s).toWeaklyPointedSuperfusion X Y
      (pullbackCoordinateIso s X Y e).hom).hom g = (e g).hom.hom := by
  rw [pullbackCoordinateIso, ofOldEvenIso_hom]

end RMod.BrundanEllis.Stacking
