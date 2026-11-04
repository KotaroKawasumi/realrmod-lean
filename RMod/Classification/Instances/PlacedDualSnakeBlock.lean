import RMod.Classification.Instances.PlacedDualPairing
import RMod.Classification.Instances.ConvolutionInversePairBlock

/-!
# The surviving block of the normalized first snake

This endomorphism follows the actual unit, coevaluation, associator and
evaluation blocks at the support degree. The inverse-pair equality is
retained explicitly in the associator comparison. The remaining
evaluation coordinate is written before simplifying g⁻¹*g to the identity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

noncomputable def placedFirstSnakeBlock :
    C.Hom (placedObj C hC t g X hX g).val (placedObj C hC t g X hX g).val :=
  let A := placedObj C hC t g X hX
  let B := placedRightDualObj C hC t g hX q
  C.comp (convolutionLeftUnitBlock C hC t ht A g).inv.hom
    (C.comp
      (C.tensorHom (C.tensorHom (placedCoevaluationBlock C hC t g hX q) (C.id (A (1⁻¹ * g)).val))
        (C.id (C.pi.factor (t.nu 1 (1⁻¹ * g)))))
      (C.comp (convolutionInversePairBlock C hC t ht A B A g g).hom.hom
        (C.comp
          (C.tensorHom (C.tensorHom (C.id (A g).val)
            (C.comp (convolutionInclusion C hC t B A (g⁻¹ * g) g⁻¹)
              (placedTwistedEvaluation C hC t ht g hX q (g⁻¹ * g))))
            (C.id (C.pi.factor (t.nu g (g⁻¹ * g)))))
          (convolutionRightUnitBlock C hC t ht A g).hom.hom)))

end RMod.Classification
