import RMod.Classification.Proofs.ReconstructionParity
import RMod.Classification.Instances.ConvolutionAssociatorOfParity
import RMod.Classification.Instances.ConvolutionUnitorsOfParity

/-!
# Reconstruction's structural maps before scalar coherence

The extracted parity laws already construct actual even associators and
unitors. These are exactly the maps of the eventual twisted model; their
construction does not assume the unproved normalization or pentagon for
the extracted omega.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionAssociatorData
    (X Y Z : PullbackObj C.data (reconstructionTwistData A C hC))
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  convolutionAssociatorDataOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstruction_normalizer_parity A C hC) X Y Z k

noncomputable def reconstructionLeftUnitorData
    (X : PullbackObj C.data (reconstructionTwistData A C hC))
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  convolutionLeftUnitorDataOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstructionNu_one_left A C hC) X k

noncomputable def reconstructionRightUnitorData
    (X : PullbackObj C.data (reconstructionTwistData A C hC))
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :=
  convolutionRightUnitorDataOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstructionNu_one_right A C hC) X k

end RMod.Classification
