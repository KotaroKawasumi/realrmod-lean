import RMod.Classification.Instances.ConvolutionBiproducts
import RMod.Classification.Abstract.Decomposition

/-!
# Finite decompositions as biproduct comparisons in convolution

The supplied inclusions and projections are retained as the bicone maps.
Their separated matrix laws make this bicone a bilimit, so Mathlib's
uniqueness comparison identifies its vertex with the chosen biproduct.
No rigidity assumption on convolution is used.
-/

set_option autoImplicit false

namespace RMod.Classification.ConvolutionCategory

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  {A : ConvolutionCategory C hC t ht} {n : ℕ} {S : Fin n → ConvolutionCategory C hC t ht}
  (d : DecompositionData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData A S)
  (hd : DecompositionLaws d)

noncomputable def evenDecompositionBicone : Bicone (fun i => evenObj ℝ (ConvolutionCategory C hC t ht) (S i)) where
  pt := evenObj ℝ (ConvolutionCategory C hC t ht) A
  π i := ⟨d.projection i, hd.projection_even i⟩
  ι i := ⟨d.inclusion i, hd.inclusion_even i⟩
  ι_π i j := by
    by_cases he : i = j
    · subst j
      simp only [dite_true, eqToHom_refl]
      exact WideSubcategory.hom_ext _ (hd.diagonal i)
    · rw [dif_neg he]
      exact WideSubcategory.hom_ext _ (hd.off_diagonal i j he)

noncomputable def evenDecompositionIsBilimit : (evenDecompositionBicone C hC t ht d hd).IsBilimit := by
  apply isBilimitOfTotal
  apply WideSubcategory.hom_ext
  have hs := hd.total
  rw [PullbackCategory.finSum_eq_sum C hC t ht] at hs
  have hm := (wideSubcategoryInclusion (evenMorphismProperty ℝ (ConvolutionCategory C hC t ht))).map_sum
    (fun i => (evenDecompositionBicone C hC t ht d hd).π i ≫
      (evenDecompositionBicone C hC t ht d hd).ι i) Finset.univ
  exact hm.trans hs

noncomputable def evenDecompositionIso :
    evenObj ℝ (ConvolutionCategory C hC t ht) A ≅
      ⨁ (fun i => evenObj ℝ (ConvolutionCategory C hC t ht) (S i)) :=
  biproduct.uniqueUpToIso _ (evenDecompositionIsBilimit C hC t ht d hd)

end RMod.Classification.ConvolutionCategory
