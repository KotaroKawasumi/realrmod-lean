import RMod.Classification.Instances.ConvolutionProductInsertions
import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Proofs.IndexedMorphismEquality
import RMod.Classification.Proofs.IsoCalculus

/-!
# Naturality and detection for product-indexed convolution inclusions

The source comparison in a product-indexed inclusion is natural for
families of arbitrary component morphisms. Consequently these inclusions
satisfy the same summand map equation as the fixed-output inclusions.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProductInclusion_grade (X Y : PullbackObj C t) (g h : t.group) :
    C.IsHomogeneous 0 (convolutionProductInclusion C hC t X Y g h) :=
  comp_even hC.toWeaklyPointedSuperfusionLaws
    (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _).hom_even
    (convolutionInclusion_grade C hC t X Y (g * h) g)

theorem convolutionProductInclusion_map {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (q : PullbackHom C t Y Y') (g h : t.group) :
    C.comp (convolutionProductInclusion C hC t X Y g h) (convolutionHom C hC t f q (g * h)) =
      C.comp (twistSummandHom C t f q g h) (convolutionProductInclusion C hC t X' Y' g h) := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let e : h = g⁻¹ * (g * h) := (inv_mul_cancel_left g h).symm
  have hn := indexed_morphism_eq_naturality A
    (twistSummand C t X Y g) (twistSummand C t X' Y' g)
    (twistSummandHom C t f q g) e
    (congrArg (twistSummand C t X Y g) e)
    (congrArg (twistSummand C t X' Y' g) e)
  change C.comp (C.comp _ (convolutionInclusion C hC t X Y (g * h) g)) _ = C.comp _ (C.comp _ _)
  rw [hC.comp_assoc, convolutionInclusion_map, ← hC.comp_assoc, ← hn, hC.comp_assoc]

end RMod.Classification
