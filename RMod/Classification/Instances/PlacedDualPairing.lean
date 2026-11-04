import RMod.Classification.Proofs.ComponentPlacement
import RMod.Classification.Proofs.DualComponents
import RMod.Classification.Proofs.Parameters
import RMod.Classification.Proofs.ParityDualNormalizers
import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Proofs.SingleComponentHom
import RMod.Classification.Instances.TwistedPullbackData

/-!
# The actual pairing maps for a placed object

The dual is placed at the inverse group degree with the specified right
parity factor. Coevaluation includes the matching convolution summand at
the identity; evaluation projects onto the reverse summand and uses the
prescribed inverse omega scalar. Every other coordinate is explicitly
zero. Grading and both snake laws are proved separately for these maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

noncomputable def placedRightDualObj : PullbackObj C t :=
  placedObj C hC t g⁻¹ (C.tensorObj Y (C.pi.factor (t.nu g g⁻¹))) (by
    have hy := InComponent.right_dual hC q hX
    have hp := InComponent.tensor hC hy (InComponent.parity_factor hC (t.nu g g⁻¹))
    simpa only [map_inv, toAdd_inv, add_zero] using hp)

noncomputable def placedCoevaluationBlock :
    C.Hom (pullbackUnitObj C hC t 1).val
      (twistSummand C t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) g (g⁻¹ * 1)) := by
  simpa only [twistSummand, mul_one, placedRightDualObj, placedObj, if_pos rfl, ite_true,
    pullbackUnitObj, supportedObj_one] using C.pi.twistedCoevaluation q.data (t.nu g g⁻¹)

include ht in
noncomputable def placedEvaluationBlock :
    C.Hom (twistSummand C t (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX) g⁻¹ (g⁻¹⁻¹ * 1))
      (pullbackUnitObj C hC t 1).val := by
  simpa only [twistSummand, mul_one, inv_inv, placedRightDualObj, placedObj, if_pos rfl, ite_true,
    pullbackUnitObj, supportedObj_one, ← ht.inverse_parity g] using
      C.pi.twistedEvaluation q.data (t.nu g g⁻¹) (t.omega g g⁻¹ g)

noncomputable def placedTwistedCoevaluation :
    PullbackHom C t (pullbackUnitObj C hC t)
      (convolutionObj C hC t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q)) :=
  singleComponentHom C t 1 (C.comp (placedCoevaluationBlock C hC t g hX q)
    (convolutionInclusion C hC t (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) 1 g))

noncomputable def placedTwistedEvaluation :
    PullbackHom C t
      (convolutionObj C hC t (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX))
      (pullbackUnitObj C hC t) :=
  singleComponentHom C t 1 (C.comp
    (convolutionProjection C hC t (placedRightDualObj C hC t g hX q) (placedObj C hC t g X hX) 1 g⁻¹)
      (placedEvaluationBlock C hC t ht g hX q))

noncomputable def placedTwistedPairingData :
    DualPairingData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (placedObj C hC t g X hX) (placedRightDualObj C hC t g hX q) where
  coeval := placedTwistedCoevaluation C hC t g hX q
  eval := placedTwistedEvaluation C hC t ht g hX q

end RMod.Classification
