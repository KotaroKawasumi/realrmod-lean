import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Instances.SimpleRetract

/-!
# Transporting homogeneous matrix units through a simple corner

First express each source inclusion and projection as an ambient
endomorphism using the source retract maps. Apply the given algebra
equivalence and compose with the target retract maps. The copied parity
sequence and these explicit maps form the target presentation data.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

def retractSumTransportData (C D : WeaklyPointedSuperfusion.{0, 0})
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetractData C.data X) (t : SimpleRetractData D.data Y)
    (φ : End X ≃ₐ[ℝ] End Y) {n : ℕ} (A : HomogeneousSumData C.data d.object X n) :
    HomogeneousSumData D.data t.object Y n where
  parity := A.parity
  inclusion i := D.data.comp t.inclusion (φ (C.data.comp d.projection (A.inclusion i)))
  projection i := D.data.comp (φ (C.data.comp (A.projection i) d.inclusion)) t.projection

end RMod.Classification
