import RMod.Classification.Instances.BiconeSelectGraph
import RMod.Classification.Proofs.ReconstructionTensorProjection

/-!
# The convolution presentation of the selected tensor component

The k component of X tensor Y has exactly the summands X_g tensor
Y_(g^-1*k). Its inclusion and projection maps are the selected tensor
maps composed with the k component projection and inclusion. The same
presentation is then viewed in the full homogeneous span of k.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
  (k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionTensorComponentBiconeRaw :=
  biconeSelectGraph (reconstructionTensorBicone A X Y) (fun g => g⁻¹ * k)
    ((reconstructionSourceBicone A (A.data.tensorObj X Y)).ι k)
    ((reconstructionSourceBicone A (A.data.tensorObj X Y)).π k)
    (reconstructionTensorProjection_graph A X Y k)

noncomputable def reconstructionTensorComponentBicone :
    Bicone (reconstructionTensorOutputSpan A X Y k) where
  pt := (reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) k
  π g := ObjectProperty.homMk ((reconstructionTensorComponentBiconeRaw A X Y k).π g)
  ι g := ObjectProperty.homMk ((reconstructionTensorComponentBiconeRaw A X Y k).ι g)
  ι_π i j := by
    classical
    split_ifs with h
    · subst j
      apply ObjectProperty.hom_ext
      exact bicone_ι_π_self (reconstructionTensorComponentBiconeRaw A X Y k) i
    · apply ObjectProperty.hom_ext
      exact bicone_ι_π_ne (reconstructionTensorComponentBiconeRaw A X Y k) h

end RMod.Classification
