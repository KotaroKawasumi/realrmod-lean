import RMod.Classification.Proofs.ConvolutionSupport
import RMod.Classification.Proofs.IsoCalculus

/-!
# A supported factor makes its convolution inclusion invertible

When the left factor is supported at g, every other summand is a zero
object. The specified projection and inclusion at g are therefore mutual
inverses at every output degree. The proof uses the existing summand
detector on all morphisms, retaining the actual maps of the model.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProjection_inclusion_of_left_support
    (X Y : PullbackObj C t) (g : t.group)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero) (k : t.group) :
    C.comp (convolutionProjection C hC t X Y k g) (convolutionInclusion C hC t X Y k g) =
      C.id (convolutionObj C hC t X Y k).val := by
  apply hom_ext_of_convolutionInclusions C hC t X Y k
  intro b
  rw [← hC.comp_assoc, hC.comp_id]
  by_cases hb : b = g
  · subst b
    rw [convolutionInclusion_projection, hC.id_comp]
  · rw [convolutionInclusion_projection_ne C hC t X Y k b g hb,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]
    exact (hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws
      (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws
        (tensor_id_zero_left hC.toWeaklyPointedSuperfusionLaws (hX b hb) _) _) _).symm

theorem convolutionSupportedInclusion_evenIso
    (X Y : PullbackObj C t) (g : t.group)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero) (k : t.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData
      (⟨convolutionInclusion C hC t X Y k g, convolutionProjection C hC t X Y k g⟩ :
        IsoData C.toWeaklyPointedSuperfusionData _ _) :=
  ⟨⟨convolutionInclusion_projection C hC t X Y k g,
    convolutionProjection_inclusion_of_left_support C hC t X Y g hX k⟩,
    convolutionInclusion_grade C hC t X Y k g, convolutionProjection_grade C hC t X Y k g⟩

end RMod.Classification
