import RMod.Classification.Instances.ReconstructionSourceEquivalence
import RMod.Classification.Instances.BiconeTransportPoint

/-!
# The selected component presentation of each source object

The inverse source equivalence already selects a family of components.
Move its actual even finite sum to the given object by the retained
counit. Thus the component inclusions and projections agree with the
global reconstruction functor's selected object data.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

noncomputable def reconstructionSourceBicone (A : PiSuperfusion.{0, 0})
    (X : LinearCategory A.toWeaklyPointedSuperfusion) :
    Bicone (C := LinearCategory A.toWeaklyPointedSuperfusion)
      (fun g => ((reconstructionSourceEquivalence A).inverse.obj X g).obj) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact biconeTransportPoint
    (evenBiproductFullBicone A.toWeaklyPointedSuperfusion
      (spanFamilyEvenObjects A.toWeaklyPointedSuperfusion _
        ((reconstructionSourceEquivalence A).inverse.obj X)))
    ((reconstructionSourceEquivalence A).counitIso.app X)

end RMod.Classification
