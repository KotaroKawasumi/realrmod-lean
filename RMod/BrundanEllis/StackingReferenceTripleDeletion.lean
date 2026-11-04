import RMod.BrundanEllis.StackingReferenceTripleData

/-! The target parity deletion is an actual homogeneous isomorphism, so it detects equality of comparison routes. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "raw" => reference.data.toWeaklyPointedSuperfusionData
local notation "tensor" => reference.data.tensorObj
local notation "pi" => reference.data.pi

/-- The target deletion has the total parity of the two original triples
and a retained genuine inverse, so it can detect equality of the routes. -/
theorem referenceTripleTargetDeletionLaws (A B C D E F : reference.data.Obj)
    (p₂₃ pR q₂₃ qR : ZMod 2) :
    HomogeneousIsoLaws raw ((q₂₃ + qR) + (p₂₃ + pR))
      (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR) :=
  HomogeneousIsoLaws.tensor referenceProperty.toWeaklyPointedSuperfusionLaws
    (referenceProperty.pi.orderedRightDeletion_homogeneousIso
      referenceProperty.toWeaklyPointedSuperfusionLaws A C E q₂₃ qR)
    (referenceProperty.pi.orderedRightDeletion_homogeneousIso
      referenceProperty.toWeaklyPointedSuperfusionLaws B D F p₂₃ pR)

/-- The forward target map is the tensor of the actual ordered deletions. -/
theorem referenceTripleTargetDeletion_hom (A B C D E F : reference.data.Obj)
    (p₂₃ pR q₂₃ qR : ZMod 2) :
    (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).hom =
      reference.data.tensorHom
        (reference.data.comp
          (reference.data.tensorHom
            (reference.data.tensorHom (reference.data.id A) ((pi).rightFactorDeletion (tensor C E) q₂₃).hom)
            (reference.data.id ((pi).factor qR)))
          ((pi).rightFactorDeletion (tensor A (tensor C E)) qR).hom)
        (reference.data.comp
          (reference.data.tensorHom
            (reference.data.tensorHom (reference.data.id B) ((pi).rightFactorDeletion (tensor D F) p₂₃).hom)
            (reference.data.id ((pi).factor pR)))
          ((pi).rightFactorDeletion (tensor B (tensor D F)) pR).hom) := rfl

end RMod.BrundanEllis.Stacking
