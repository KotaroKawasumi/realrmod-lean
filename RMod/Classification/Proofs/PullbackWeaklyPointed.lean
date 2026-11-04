import RMod.Classification.Proofs.PullbackRightDuals
import RMod.Classification.Proofs.PullbackSuperMultiplicity
import RMod.Classification.Proofs.ConvolutionSupport

/-!
# Weak pointedness of the actual abstract pullback

An arbitrary simple is evenly isomorphic to a placed simple. Transport
its specified right pairing along that isomorphism. The first member is
supported at g and the second at its inverse, so their tensor product is
supported at the identity. Its neutral coordinate is a super-multiple of
the unit, and exact pairing makes that multiple nonempty.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_weakly_pointed (A : PullbackObj C t)
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    (twistedPullbackData C hC t ht).IsWeaklyInvertible A := by
  obtain ⟨g, X, hX, hs, f, j, hfj, hjf, hf, hj⟩ :=
    twistedPullback_simple_iso_placed C hC t ht A hA
  let C₀ : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let q := (dualChoices C₀).rightPairing X
  let B : ConvolutionCategory C hC t ht := placedRightDualObj C hC t g hX q
  let p₀ := ConvolutionCategory.superPairing C hC t ht (placedTwistedPairingData C hC t ht g hX q)
    (placedSimpleTwistedPairingLaws C hC t ht g hX q hs)
  let e : evenObj ℝ (ConvolutionCategory C hC t ht) A ≅
      evenObj ℝ (ConvolutionCategory C hC t ht) (placedObj C hC t g X hX) :=
    ⟨⟨j, hj⟩, ⟨f, hf⟩, WideSubcategory.hom_ext _ hjf, WideSubcategory.hom_ext _ hfj⟩
  letI := p₀.toEven
  let p : SuperExactPairing ℝ (C := ConvolutionCategory C hC t ht) A B :=
    SuperExactPairing.ofEven (exactPairingCongrLeft e)
  have hAs : ∀ k, k ≠ g → C.id (A k).val = C.zero := by
    intro k hk
    have hz : C.id (placedObj C hC t g X hX k).val = C.zero := by
      rw [placedObj_away C hC t g X hX k hk]
      exact pullbackZero_id C hC t k
    have he := congrFun hjf k
    change C.comp (j k) (f k) = C.id (A k).val at he
    rw [hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz (f k),
      raw_comp_zero hC.toWeaklyPointedSuperfusionLaws] at he
    exact he.symm
  have hBs : ∀ k, k ≠ g⁻¹ → C.id (B k).val = C.zero := by
    intro k hk
    dsimp only [B, placedRightDualObj]
    rw [placedObj_away C hC t g⁻¹ _ _ k hk]
    exact pullbackZero_id C hC t k
  have hAB : ∀ k, k ≠ 1 → C.id (convolutionObj C hC t A B k).val = C.zero := by
    intro k hk
    exact convolution_support C hC t g g⁻¹ hAs hBs k (by simpa only [mul_inv_cancel] using hk)
  obtain ⟨m, n, hm⟩ := twistedPullback_supported_superMultiplicity C hC t ht (convolutionObj C hC t A B) hAB
  have hne := twistedPullback_pairing_tensor_nonzero C hC t ht p
    (twistedPullback_simple_id_ne_zero C hC t ht hA)
  exact ⟨B, ConvolutionCategory.hasExactPairing_of_super C hC t ht p, m, n,
    twistedPullback_superMultiplicity_positive C hC t ht hne hm, hm⟩

end RMod.Classification
