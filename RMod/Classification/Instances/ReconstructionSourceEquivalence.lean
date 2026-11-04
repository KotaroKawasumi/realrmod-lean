import RMod.Classification.Instances.SpanFamilySumEquivalence
import RMod.Classification.Proofs.SimpleOrbitRepresentativeCoverage
import RMod.Classification.Abstract.Pi

/-!
# The source category as the sum of its intrinsic simple components

This names the actual component-sum equivalence used in reconstruction.
Its inverse retains the grouped simple decomposition of each object.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def reconstructionSourceEquivalence (A : PiSuperfusion.{0, 0}) :
    SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object) ≌
        LinearCategory A.toWeaklyPointedSuperfusion := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence A.toWeaklyPointedSuperfusion
    (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)
    (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).laws.simple)
    (simpleOrbitRepresentatives_separate A.toWeaklyPointedSuperfusion)
    (simpleOrbitRepresentatives_cover A.toWeaklyPointedSuperfusion)

end RMod.Classification
