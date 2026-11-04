import RMod.Classification.Instances.PlacedDualPairing

/-!
# Grading of the supported pairing maps

Only the matching summand at the group identity occurs. Its inclusion
and projection are even, as are the specified local dual maps. Equality
transport changes their Hom types but preserves this grading.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedTwistedCoevaluation_even :
    ∀ k, C.IsHomogeneous 0 (placedTwistedCoevaluation C hC t g hX q k) := by
  unfold placedTwistedCoevaluation placedCoevaluationBlock
  apply singleComponentHom_grade C t 1 hC.toWeaklyPointedSuperfusionLaws
  apply comp_even hC.toWeaklyPointedSuperfusionLaws
  · apply HomTransport.grade C.toWeaklyPointedSuperfusionData
      (by simp [pullbackUnitObj, supportedObj_one])
      (by simp [twistSummand, placedRightDualObj, placedObj])
    exact hC.pi.twistedCoevaluation_even hC.toWeaklyPointedSuperfusionLaws q.laws _
  · exact convolutionInclusion_grade C hC t _ _ 1 g

theorem placedTwistedEvaluation_even :
    ∀ k, C.IsHomogeneous 0 (placedTwistedEvaluation C hC t ht g hX q k) := by
  unfold placedTwistedEvaluation placedEvaluationBlock
  apply singleComponentHom_grade C t 1 hC.toWeaklyPointedSuperfusionLaws
  apply comp_even hC.toWeaklyPointedSuperfusionLaws
  · exact convolutionProjection_grade C hC t _ _ 1 g⁻¹
  · apply HomTransport.grade C.toWeaklyPointedSuperfusionData
      (by simp [twistSummand, placedRightDualObj, placedObj, ← ht.inverse_parity g])
      (by simp [pullbackUnitObj, supportedObj_one])
    exact hC.pi.twistedEvaluation_even hC.toWeaklyPointedSuperfusionLaws q.laws _ _

end RMod.Classification
