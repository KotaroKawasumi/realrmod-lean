import RMod.BrundanEllis.StackingReferenceWeightedTriple
import RMod.BrundanEllis.StackingComparisonTwistTriple

/-! The explicit binary gauge cancels the auxiliary omega correction. The corrected local triple comparison therefore respects the original twistMul. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open Superfusion RMod.Classification

/-- The explicit binary gauge cancels the change of omega in the triple
comparison. Thus scaling the chosen binary maps returns to twistMul. -/
theorem comparisonGauge_triple_scalar {G : FiniteGrp.{0}} (s t : TwistOn G) (g h k : G) :
    (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h)).val *
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) (g * h) k)).val *
      (fixedOmega (comparisonTwist s t) g h k).val =
    (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) h k)).val *
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g (h * k))).val *
      (fixedOmega (twistMul s t) g h k).val := by
  have hsign (a : ZMod 2) : (realSign a : ℝ) = (-1 : ℝ) ^ a.val :=
    RMod.Classification.realSign_coe a
  rw [(comparisonTwist_data s t).2.2, fixedOmega_mul]
  dsimp only [stackOmega]
  simp only [Units.val_mul, hsign]
  rw [← deletionCorrection_from_prescribed (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t)
    (fixedNu_cocycle s) (fixedNu_cocycle t)]
  simp only [d₂, CharTwo.sub_eq_add]
  have hm (x y a b : ℝ) : x * y * (a * b) = a * (x * y * b) := by ring
  conv_lhs => rw [hm]
  conv_rhs => rw [hm]
  simp only [← parity_power_add]
  congr 2
  congr 1
  ring_nf
  simp [CharTwo.two_eq_zero]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open Superfusion RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws

/-- The explicitly gauge-corrected binary comparisons give precisely the
original twistMul associator on each triple of reference objects.
The concrete reference hexagon certificates remain explicit hypotheses. -/
theorem twistMul_referenceTripleCoherence {G : FiniteGrp.{0}}
    (s t : TwistOn G) (g h k : G)
    (hl : ReferenceCommutor.LeftEquation (fixedRho s g).toAdd (fixedRho t h).toAdd (fixedRho t k).toAdd)
    (hr : ReferenceCommutor.RightEquation (fixedRho s g).toAdd (fixedRho s h).toAdd (fixedRho t k).toAdd)
    (A B C D E F : (R).Obj)
    (hB : InComponent R (fixedRho s g).toAdd B)
    (hC : InComponent R (fixedRho t h).toAdd C)
    (hD : InComponent R (fixedRho s h).toAdd D)
    (hE : InComponent R (fixedRho t k).toAdd E) :
    (referenceWeightedTripleLeftData (fixedRho s g).toAdd (fixedRho t h).toAdd
      (fixedRho s h).toAdd (fixedRho t k).toAdd A B C D E F hB hC hD hE
      (fixedNu s g h) (fixedNu s (g * h) k) (fixedNu s h k) (fixedNu s g (h * k))
      (fixedNu t g h) (fixedNu t (g * h) k) (fixedNu t h k) (fixedNu t g (h * k))
      (fixedNu_associative s g h k) (fixedNu_associative t g h k)
      (fixedOmega s g h k) (fixedOmega t g h k)
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g h))
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) (g * h) k))).hom =
    (referenceWeightedTripleRightData (fixedRho s g).toAdd (fixedRho t h).toAdd
      (fixedRho s h).toAdd (fixedRho t k).toAdd A B C D E F hB hC hD hE
      (fixedNu s g h) (fixedNu s (g * h) k) (fixedNu s h k) (fixedNu s g (h * k))
      (fixedNu t g h) (fixedNu t (g * h) k) (fixedNu t h k) (fixedNu t g (h * k))
      (fixedNu_associative s g h k) (fixedNu_associative t g h k)
      (fixedOmega (twistMul s t) g h k)
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) h k))
      (realSign (comparisonGaugeExponent (fixedRho s) (fixedRho t) (fixedNu s) (fixedNu t) g (h * k)))).hom := by
  rw [referenceWeightedTripleLeft_hom, referenceWeightedTripleRight_hom,
    comparisonTwist_referenceTripleCoherence s t g h k hl hr]
  conv_lhs => rw [referenceTripleRight_scalar]
  conv_rhs => rw [referenceTripleRight_scalar]
  simp only [← (hR).mul_smul]
  rw [comparisonGauge_triple_scalar]

end RMod.BrundanEllis.Stacking
