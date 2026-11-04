import RMod.BrundanEllis.StackingReferenceTripleCoherence
import RMod.BrundanEllis.StackingReferenceTripleCochain
import RMod.BrundanEllis.StackingComparisonTwist

/-! The concrete binary comparison satisfies local triple coherence for comparisonTwist, conditional only on the stated reference hexagon equations. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open Superfusion RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData

/-- The parity cocycle in the bracketing convention of the actual local
associator, with its group labels held fixed. -/
theorem fixedNu_associative {G : FiniteGrp.{0}} (s : TwistOn G) (g h k : G) :
    fixedNu s g h + fixedNu s (g * h) k = fixedNu s h k + fixedNu s g (h * k) := by
  have hc := fixedNu_cocycle s g h k
  simp only [d₂, CharTwo.sub_eq_add] at hc
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc

/-- The auxiliary twist is precisely the output of the actual chosen
binary comparison, at the level of each triple of reference objects.
The concrete reference hexagon certificates remain explicit hypotheses. -/
theorem comparisonTwist_referenceTripleCoherence {G : FiniteGrp.{0}}
    (s t : TwistOn G) (g h k : G)
    (hl : ReferenceCommutor.LeftEquation (fixedRho s g).toAdd (fixedRho t h).toAdd (fixedRho t k).toAdd)
    (hr : ReferenceCommutor.RightEquation (fixedRho s g).toAdd (fixedRho s h).toAdd (fixedRho t k).toAdd)
    (A B C D E F : (R).Obj)
    (hB : InComponent R (fixedRho s g).toAdd B)
    (hC : InComponent R (fixedRho t h).toAdd C)
    (hD : InComponent R (fixedRho s h).toAdd D)
    (hE : InComponent R (fixedRho t k).toAdd E) :
    (referenceTripleLeftData (fixedRho s g).toAdd (fixedRho t h).toAdd
      (fixedRho s h).toAdd (fixedRho t k).toAdd A B C D E F hB hC hD hE
      (fixedNu s g h) (fixedNu s (g * h) k) (fixedNu s h k) (fixedNu s g (h * k))
      (fixedNu t g h) (fixedNu t (g * h) k) (fixedNu t h k) (fixedNu t g (h * k))
      (fixedNu_associative s g h k) (fixedNu_associative t g h k)
      (fixedOmega s g h k) (fixedOmega t g h k)).hom =
    (referenceTripleRightData (fixedRho s g).toAdd (fixedRho t h).toAdd
      (fixedRho s h).toAdd (fixedRho t k).toAdd A B C D E F hB hC hD hE
      (fixedNu s g h) (fixedNu s (g * h) k) (fixedNu s h k) (fixedNu s g (h * k))
      (fixedNu t g h) (fixedNu t (g * h) k) (fixedNu t h k) (fixedNu t g (h * k))
      (fixedNu_associative s g h k) (fixedNu_associative t g h k)
      (fixedOmega (comparisonTwist s t) g h k)).hom := by
  apply referenceTriple_coherence _ _ _ _ hl hr
  rw [(comparisonTwist_data s t).2.2]
  have hsign (a : ZMod 2) : (realSign a : ℝ) = (-1 : ℝ) ^ a.val :=
    RMod.Classification.realSign_coe a
  simp only [Units.val_mul, hsign]
  rw [deletionCorrection_eq_referenceTriple (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t)
    g h k (fixedNu_associative s g h k) (fixedNu_associative t g h k)]
  rw [mul_comm (fixedOmega s g h k).val (fixedOmega t g h k).val]

end RMod.BrundanEllis.Stacking
