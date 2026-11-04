import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Proofs.ZeroObjects

/-!
# Multiplication of supports under convolution

If the factors are supported at g and h, each summand away from gh has
a zero factor. The actual convolution inclusions detect maps, so these
zero summands force the entire coordinate to have zero identity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolution_support {X Y : PullbackObj C t} (g h : t.group)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero)
    (hY : ∀ k, k ≠ h → C.id (Y k).val = C.zero)
    (k : t.group) (hk : k ≠ g * h) : C.id (convolutionObj C hC t X Y k).val = C.zero := by
  apply hom_ext_of_convolutionInclusions C hC t X Y k
  intro b
  have hz : C.id (twistSummand C t X Y b (b⁻¹ * k)) = C.zero := by
    by_cases hb : b = g
    · subst b
      have he : g⁻¹ * k ≠ h := by
        intro he
        apply hk
        exact (inv_mul_eq_iff_eq_mul.mp he)
      exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_right hC.toWeaklyPointedSuperfusionLaws _ (hY _ he)) _
    · exact tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws (hX b hb) _) _
  rw [hC.comp_id, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws]
  exact hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _

end RMod.Classification
