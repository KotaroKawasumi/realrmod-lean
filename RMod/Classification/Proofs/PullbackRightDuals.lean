import RMod.Classification.Proofs.PlacedDualSnakes
import RMod.Classification.Proofs.PullbackSimpleSupport
import RMod.Classification.Proofs.PullbackSemisimple
import RMod.Classification.Instances.ConvolutionDecomposition

/-!
# Right duals for every object of the abstract convolution

The specified placed pairing first gives right duals of placed simples.
Every other simple is evenly isomorphic to one of these. The already
proved semisimple decomposition, interpreted as a Mathlib biproduct,
then extends these exact pairings to every object, including zero.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_placed_has_right_dual (g : t.group) (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
    (hs : C.IsSimple X) :
    ∃ Y, (twistedPullbackData C hC t ht).HasExactPairing (placedObj C hC t g X hX) Y := by
  let C₀ : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let q := (dualChoices C₀).rightPairing X
  let d := placedTwistedPairingData C hC t ht g hX q
  have hd := placedSimpleTwistedPairingLaws C hC t ht g hX q hs
  exact ⟨placedRightDualObj C hC t g hX q, d.coeval, d.eval,
    hd.coeval_even, hd.eval_even, hd.snake_right, hd.snake_left⟩

theorem twistedPullback_simple_has_right_dual (A : PullbackObj C t)
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    ∃ B, (twistedPullbackData C hC t ht).HasExactPairing A B := by
  obtain ⟨g, X, hX, hs, f, j, hfj, hjf, hf, hj⟩ :=
    twistedPullback_simple_iso_placed C hC t ht A hA
  obtain ⟨B, hB⟩ := twistedPullback_placed_has_right_dual C hC t ht g X hX hs
  obtain ⟨p⟩ := (ConvolutionCategory.hasExactPairing_iff_super C hC t ht).mp hB
  let e : evenObj ℝ (ConvolutionCategory C hC t ht) A ≅
      evenObj ℝ (ConvolutionCategory C hC t ht) (placedObj C hC t g X hX) :=
    ⟨⟨j, hj⟩, ⟨f, hf⟩, WideSubcategory.hom_ext _ hjf, WideSubcategory.hom_ext _ hfj⟩
  letI := p.toEven
  exact ⟨B, ConvolutionCategory.hasExactPairing_of_super C hC t ht
    (SuperExactPairing.ofEven (exactPairingCongrLeft e))⟩

theorem twistedPullback_has_right_dual (A : PullbackObj C t) :
    ∃ B, (twistedPullbackData C hC t ht).HasExactPairing A B := by
  classical
  obtain ⟨n, S, hs, i, p, hi, hp, hd, ho, hh⟩ := twistedPullback_semisimple C hC t ht A
  choose B hB using fun j => twistedPullback_simple_has_right_dual C hC t ht (S j) (hs j)
  let q (j : Fin n) : SuperExactPairing ℝ (C := ConvolutionCategory C hC t ht) (S j) (B j) :=
    Classical.choice ((ConvolutionCategory.hasExactPairing_iff_super C hC t ht).mp (hB j))
  let d : DecompositionData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData A S := ⟨i, p⟩
  have hl : DecompositionLaws d := ⟨hi, hp, hd, ho, hh⟩
  let e := ConvolutionCategory.evenDecompositionIso C hC t ht d hl
  letI := (SuperExactPairing.biproduct q).toEven
  exact ⟨superBiproduct (K := ℝ) (C := ConvolutionCategory C hC t ht) B,
    ConvolutionCategory.hasExactPairing_of_super C hC t ht
    (SuperExactPairing.ofEven (exactPairingCongrLeft e))⟩

end RMod.Classification
