import RMod.Classification.Instances.ConvolutionIndexedComparisons
import RMod.Classification.Proofs.ConvolutionIndexedProducts
import RMod.Classification.Proofs.ConvolutionComponentReindex

/-!
# Evaluation cancels the actual indexed summand inclusion

After inclusion, the binary comparison is exactly deletion of that
summand's parity factor. For supported families both maps have the
specified inverse laws. These identities allow triple comparison
equations to be tested on the original convolution summands.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionComponentReindex_inclusion (X Y : PullbackObj C t)
    (k g h : t.group) (e : g⁻¹ * k = h) :
    C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (twistSummand C t X Y g) e.symm)).hom (convolutionInclusion C hC t X Y k g))
      (convolutionComponentReindexData C hC t X Y k g h e).hom =
      (C.pi.rightFactorDeletion (C.tensorObj (X g).val (Y h).val) (t.nu g h)).hom := by
  cases e
  simp only [convolutionComponentReindexData, convolutionComponentComparisonData,
    IsoData.trans, IsoData.ofEq, IsoData.refl, hC.comp_id, hC.id_comp,
    ← hC.comp_assoc, convolutionInclusion_projection]

theorem convolutionIndexedComparison_inclusion (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    C.comp (convolutionIndexedProductInclusion C hC t X Y g h u e)
      (convolutionIndexedComparisonData C hC t X Y g h u e).hom =
      (C.pi.rightFactorDeletion (C.tensorObj (X g).val (Y h).val) (t.nu g h)).hom := by
  rw [convolutionIndexedProductInclusion_eq C hC t X Y g h u e
    (inv_mul_eq_iff_eq_mul.mpr e.symm).symm]
  exact convolutionComponentReindex_inclusion C hC t X Y u g h _

theorem convolutionIndexedInclusionData_hom (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    (convolutionIndexedInclusionData C hC t X Y g h u e).hom =
      convolutionIndexedProductInclusion C hC t X Y g h u e :=
  (convolutionIndexedProductInclusion_eq C hC t X Y g h u e
    (inv_mul_eq_iff_eq_mul.mpr e.symm).symm).symm

theorem convolutionIndexedInclusion_grade (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u) :
    C.IsHomogeneous 0 (convolutionIndexedProductInclusion C hC t X Y g h u e) := by
  rw [convolutionIndexedProductInclusion_eq C hC t X Y g h u e
    (inv_mul_eq_iff_eq_mul.mpr e.symm).symm]
  exact comp_even hC.toWeaklyPointedSuperfusionLaws
    (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _).hom_even
    (convolutionInclusion_grade C hC t X Y u g)

theorem convolutionIndexedInclusion_evenIso (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (convolutionIndexedInclusionData C hC t X Y g h u e) :=
  (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _).trans hC.toWeaklyPointedSuperfusionLaws
    (convolutionSupportedInclusion_evenIso C hC t X Y g hX u)

theorem convolutionIndexedComparison_homogeneousIso (X Y : PullbackObj C t)
    (g h u : t.group) (e : g * h = u)
    (hX : ∀ k, k ≠ g → C.id (X k).val = C.zero) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData (t.nu g h)
      (convolutionIndexedComparisonData C hC t X Y g h u e) :=
  convolutionComponentReindex_homogeneousIso C hC t X Y u g h _ hX

theorem convolutionIndexedComparison_naturality
    {X X' Y Y' : PullbackObj C t} {a b : ZMod 2}
    (f : PullbackHom C t X X') (q : PullbackHom C t Y Y')
    (hf : ∀ k, C.IsHomogeneous a (f k)) (hq : ∀ k, C.IsHomogeneous b (q k))
    (g h u : t.group) (e : g * h = u) :
    C.comp (convolutionHom C hC t f q u)
      (convolutionIndexedComparisonData C hC t X' Y' g h u e).hom =
      C.smul ((-1 : ℝ) ^ (t.nu g h * (a + b)).val)
        (C.comp (convolutionIndexedComparisonData C hC t X Y g h u e).hom
          (C.tensorHom (f g) (q h))) :=
  convolutionComponentReindex_naturality C hC t f q hf hq u g h _

end RMod.Classification
