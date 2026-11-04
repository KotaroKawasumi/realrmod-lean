import RMod.Classification.Instances.ReconstructionTensorator

/-! # Inverse identities and evenness of the actual global tensorator -/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionTensorator_evenIso (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    EvenIsoLaws C.toWeaklyPointedSuperfusion.data (reconstructionTensoratorData A C hC X Y k) :=
  evenIsoLaws_ofEvenIso C.toWeaklyPointedSuperfusion (reconstructionTensoratorEvenIso A C hC X Y k)

end RMod.Classification
