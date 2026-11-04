import RMod.Classification.Instances.ReconstructionSourceEquivalence
import RMod.Classification.Instances.ReconstructionPullbackSpans

/-!
# The actual ordinary equivalence underlying reconstruction

Resolve an arbitrary source object into its simple-orbit components,
apply the chosen component equivalences, and view the result in the
pullback carrier. The inverse takes the selected component inverses and
their even direct sum. This construction does not assume laws for omega;
linearity, grading, monoidal and parity comparisons are further laws.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def reconstructionUnderlyingEquivalence (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) :
    LinearCategory A.toWeaklyPointedSuperfusion ≌
      PullbackCategory C.data hC (reconstructionTwistData A C hC) :=
  (reconstructionSourceEquivalence A).symm.trans (reconstructionPullbackFamilyEquivalence A C hC).symm

end RMod.Classification
