import RMod.Classification.Instances.ReconstructionSourceBicone
import RMod.Classification.Abstract.Normalizers

/-!
# The actual comparison with a selected source component

The inclusion and projection already belong to the chosen component
presentation. They become inverse maps when the object is supported in
that component; no new inverse or decomposition is chosen here.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionSourceComponentIsoData (A : PiSuperfusion.{0, 0})
    (X : LinearCategory A.toWeaklyPointedSuperfusion)
    (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    IsoData A.toWeaklyPointedSuperfusion.data
      ((reconstructionSourceEquivalence A).inverse.obj X k).obj X where
  hom := (reconstructionSourceBicone A X).ι k
  inv := (reconstructionSourceBicone A X).π k

end RMod.Classification
