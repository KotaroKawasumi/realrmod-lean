import RMod.Classification.Instances.ConvolutionMonoidal
import RMod.Classification.Proofs.PullbackSums
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The actual finite sums in the even convolution category

The coordinatewise sum data and their proved matrix laws give a Mathlib
bicone and bilimit. This makes existing finite-biproduct constructions,
including the direct sum of exact pairings, available on the convolution
category without assuming its rigidity in advance.
-/

set_option autoImplicit false

namespace RMod.Classification.ConvolutionCategory

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

noncomputable def evenSumBicone {n : ℕ}
    (S : Fin n → EvenSubcategory ℝ (ConvolutionCategory C hC t ht)) : Bicone S where
  pt := ⟨(pullbackSumData C hC t ht (fun i => (S i).obj)).object⟩
  π i := ⟨(pullbackSumData C hC t ht (fun i => (S i).obj)).projection i,
    (pullbackSumLaws C hC t ht (fun i => (S i).obj)).projection_even i⟩
  ι i := ⟨(pullbackSumData C hC t ht (fun i => (S i).obj)).inclusion i,
    (pullbackSumLaws C hC t ht (fun i => (S i).obj)).inclusion_even i⟩
  ι_π i j := by
    by_cases he : i = j
    · subst j
      simp only [dite_true, eqToHom_refl]
      apply WideSubcategory.hom_ext
      exact (pullbackSumLaws C hC t ht (fun i => (S i).obj)).diagonal i
    · rw [dif_neg he]
      apply WideSubcategory.hom_ext
      exact (pullbackSumLaws C hC t ht (fun i => (S i).obj)).off_diagonal i j he

noncomputable def evenSumIsBilimit {n : ℕ}
    (S : Fin n → EvenSubcategory ℝ (ConvolutionCategory C hC t ht)) :
    (evenSumBicone C hC t ht S).IsBilimit := by
  apply isBilimitOfTotal
  apply WideSubcategory.hom_ext
  have hs := (pullbackSumLaws C hC t ht (fun i => (S i).obj)).total
  rw [PullbackCategory.finSum_eq_sum C hC t ht] at hs
  have hm := (wideSubcategoryInclusion (evenMorphismProperty ℝ (ConvolutionCategory C hC t ht))).map_sum
    (fun i => (evenSumBicone C hC t ht S).π i ≫ (evenSumBicone C hC t ht S).ι i) Finset.univ
  exact hm.trans hs

instance evenHasFiniteBiproducts : HasFiniteBiproducts (EvenSubcategory ℝ (ConvolutionCategory C hC t ht)) where
  out _ := ⟨fun S => HasBiproduct.mk ⟨evenSumBicone C hC t ht S, evenSumIsBilimit C hC t ht S⟩⟩

end RMod.Classification.ConvolutionCategory
