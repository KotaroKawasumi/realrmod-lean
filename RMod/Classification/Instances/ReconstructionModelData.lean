import RMod.Classification.Instances.ConvolutionDataOfParity
import RMod.Classification.Proofs.ReconstructionParity

/-!
# Reconstruction's actual model data for coherence reflection

The extracted normalized parity and cocycle provide the raw model.
No scalar law is assumed and no universal reference data are consulted.
The even category will transfer coherence for exactly these operations.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionModelData (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) :
    PiSuperfusionData.{0, 0} :=
  convolutionDataOfParity C.data hC (reconstructionTwistData A C hC)
    (reconstruction_normalizer_parity A C hC)
    (reconstructionNu_one_left A C hC) (reconstructionNu_one_right A C hC)


end RMod.Classification
