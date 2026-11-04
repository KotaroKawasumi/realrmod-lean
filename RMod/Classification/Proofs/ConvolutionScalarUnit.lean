import RMod.Classification.Proofs.ConvolutionScalarMap
import RMod.Classification.Proofs.ConvolutionUnitSupport

/-!
# Normalized scalar comparisons act identically on unit convolutions

The surviving left and right summands have scalar one. All other
summands have zero identity, so their full Hom maps vanish. Hence the
actual chosen convolution automorphism is the identity, including on
families with zero coordinates.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (beta : t.group → t.group → ℝˣ)

theorem convolutionScalar_unit_left (hbeta : ∀ g, beta 1 g = 1)
    (X : PullbackObj C t) (k : t.group) :
    (convolutionScalarData C hC t beta (pullbackUnitObj C hC t) X k).hom =
      C.id (convolutionObj C hC t (pullbackUnitObj C hC t) X k).val := by
  apply hom_ext_of_convolutionInclusions C hC t (pullbackUnitObj C hC t) X k
  intro g
  by_cases hg : g = 1
  · subst g
    rw [convolutionScalar_inclusion, hbeta, Units.val_one, hC.one_smul, hC.comp_id]
  · have hz : C.id (twistSummand C t (pullbackUnitObj C hC t) X g (g⁻¹ * k)) = C.zero :=
      tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
          (pullbackUnit_id_zero C hC t g hg) _) _
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).symm

theorem convolutionScalar_unit_right (hbeta : ∀ g, beta g 1 = 1)
    (X : PullbackObj C t) (k : t.group) :
    (convolutionScalarData C hC t beta X (pullbackUnitObj C hC t) k).hom =
      C.id (convolutionObj C hC t X (pullbackUnitObj C hC t) k).val := by
  apply hom_ext_of_convolutionInclusions C hC t X (pullbackUnitObj C hC t) k
  intro g
  by_cases hg : g = k
  · subst g
    have hb : beta k (k⁻¹ * k) = 1 := (congrArg (beta k) (inv_mul_cancel k)).trans (hbeta k)
    rw [convolutionScalar_inclusion, hb, Units.val_one, hC.one_smul, hC.comp_id]
  · have hz : C.id (twistSummand C t X (pullbackUnitObj C hC t) g (g⁻¹ * k)) = C.zero :=
      tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_right hC.toWeaklyPointedSuperfusionLaws _
          (pullbackUnit_id_zero C hC t (g⁻¹ * k) (fun he => hg (inv_mul_eq_one.mp he)))) _
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).trans
      (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _).symm

end RMod.Classification
