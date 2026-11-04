import RMod.Classification.Instances.ReconstructionOmega
import RMod.Classification.Instances.ReconstructionMappedTensorBicone
import RMod.Classification.Instances.ReconstructionUnderlyingEquivalence
import RMod.Classification.Instances.ConvolutionBiproduct

/-!
# The actual even tensorator on one pair of source components

Apply the already constructed binary comparison to the component objects
selected by the global equivalence. Its target is the realization of
their ambient tensor in the chosen product component. Identity changes
of simple-span generators do not change this underlying object or map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def reconstructionTensorBlock (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    referenceEvenObj C.data hC (twistSummand C.data (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) g h) ≅
    referenceEvenObj C.data hC ((reconstructionComponentRealization A C hC (g * h)).obj
      (reconstructionTensorSpanObject A X Y g h)) :=
  ((reconstructionTensorComparison A C hC g h).data.app
    ((reconstructionSourceEquivalence A).inverse.obj X g)
    ((reconstructionSourceEquivalence A).inverse.obj Y h)).toEvenIso C.toWeaklyPointedSuperfusion
      ((reconstructionTensorComparison A C hC g h).laws.iso _ _)

end RMod.Classification
