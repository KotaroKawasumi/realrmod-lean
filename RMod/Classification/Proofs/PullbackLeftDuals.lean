import RMod.Classification.Proofs.PullbackRightDuals
import RMod.Classification.Proofs.DualNonzero
import RMod.Classification.Proofs.ParityFactorIso
import RMod.Classification.Proofs.PlacedIso

/-!
# Left duals from simultaneous homogeneous transport

Place an original left pairing in the inverse group degree. Its second
member is the desired simple with a right parity factor. Moving that
factor simultaneously across both members uses the same homogeneous
degree, so the existing signed transport theorem preserves exactness.
Even isomorphisms and finite biproducts then give left duals of all objects.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem twistedPullback_placed_has_left_dual (g : t.group) (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
    (hs : C.IsSimple X) :
    ∃ Y, (twistedPullbackData C hC t ht).HasExactPairing Y (placedObj C hC t g X hX) := by
  let C₀ : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let q := (dualChoices C₀).leftPairing X
  let L := (dualChoices C₀).data.leftObj X
  let a := t.nu g⁻¹ g
  have hL : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g⁻¹)) L := by
    simpa only [map_inv, toAdd_inv] using InComponent.left_dual hC q hX
  have hLp : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g⁻¹))
      (C.tensorObj L (C.pi.factor a)) := by
    simpa only [add_zero] using InComponent.tensor hC hL (InComponent.parity_factor hC a)
  have hXp : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g))
      (C.tensorObj X (C.pi.factor a)) := by
    simpa only [add_zero] using InComponent.tensor hC hX (InComponent.parity_factor hC a)
  have hLne : C.id L ≠ C.zero := q.left_id_ne_zero (simple_id_ne_zero C₀.laws hs)
  have hXSchur := simple_even_schur C₀ hs
  let p := ConvolutionCategory.superPairing C hC t ht (placedTwistedPairingData C hC t ht g⁻¹ hL q)
    (placedTwistedPairingLaws C hC t ht g⁻¹ hL q hLne hXSchur)
  obtain ⟨f, j, hfj, hjf, hf, hj⟩ := right_factor_homogeneous_iso C₀ C.pi hC.pi L a
  obtain ⟨i⟩ := placed_homogeneous_iso C hC t ht g⁻¹ hLp hL ⟨j, f, hjf, hfj, hj, hf⟩
  have hj' : Nonempty (HomogeneousIso ℝ (C := ConvolutionCategory C hC t ht) a
      (placedObj C hC t g X hX) (placedRightDualObj C hC t g⁻¹ hL q)) := by
    have he : placedRightDualObj C hC t g⁻¹ hL q =
        placedObj C hC t g (C.tensorObj X (C.pi.factor a)) hXp := by
      funext k
      apply Subtype.ext
      simp only [placedRightDualObj, placedObj, inv_inv, a]
      rw [inv_inv]
    rw [he]
    exact placed_homogeneous_iso C hC t ht g hX hXp (right_factor_homogeneous_iso C₀ C.pi hC.pi X a)
  obtain ⟨j'⟩ := hj'
  let A : ConvolutionCategory C hC t ht := placedObj C hC t g⁻¹ (C.tensorObj L (C.pi.factor a)) hLp
  let B : ConvolutionCategory C hC t ht := placedObj C hC t g X hX
  have hA : 𝟙 A ≠ 0 := placed_id_ne_zero C hC t ht g⁻¹ hLp
    (right_factor_id_ne_zero C₀ C.pi hC.pi L a hLne)
  have hB : ∀ k : B ⟶ B, k ∈ homGrade ℝ B B 0 → k ≠ 0 → IsIso k := by
    intro k hk hne
    obtain ⟨_, s, _, hks, hsk⟩ := twistedPullback_placed_even_schur C hC t ht g X hX hXSchur k hk hne
    exact ⟨⟨s, hks, hsk⟩⟩
  exact ⟨A, ConvolutionCategory.hasExactPairing_of_super C hC t ht
    (SuperExactPairing.congrHomogeneousOfEvenSchur i j' p hA hB)⟩

theorem twistedPullback_simple_has_left_dual (A : PullbackObj C t)
    (hA : (twistedPullbackData C hC t ht).IsSimple A) :
    ∃ B, (twistedPullbackData C hC t ht).HasExactPairing B A := by
  obtain ⟨g, X, hX, hs, f, j, hfj, hjf, hf, hj⟩ :=
    twistedPullback_simple_iso_placed C hC t ht A hA
  obtain ⟨B, hB⟩ := twistedPullback_placed_has_left_dual C hC t ht g X hX hs
  obtain ⟨p⟩ := (ConvolutionCategory.hasExactPairing_iff_super C hC t ht).mp hB
  let e : evenObj ℝ (ConvolutionCategory C hC t ht) A ≅
      evenObj ℝ (ConvolutionCategory C hC t ht) (placedObj C hC t g X hX) :=
    ⟨⟨j, hj⟩, ⟨f, hf⟩, WideSubcategory.hom_ext _ hjf, WideSubcategory.hom_ext _ hfj⟩
  letI := p.toEven
  exact ⟨B, ConvolutionCategory.hasExactPairing_of_super C hC t ht
    (SuperExactPairing.ofEven (exactPairingCongrRight e))⟩

theorem twistedPullback_has_left_dual (A : PullbackObj C t) :
    ∃ B, (twistedPullbackData C hC t ht).HasExactPairing B A := by
  classical
  obtain ⟨n, S, hs, i, p, hi, hp, hd, ho, hh⟩ := twistedPullback_semisimple C hC t ht A
  choose B hB using fun j => twistedPullback_simple_has_left_dual C hC t ht (S j) (hs j)
  let q (j : Fin n) : SuperExactPairing ℝ (C := ConvolutionCategory C hC t ht) (B j) (S j) :=
    Classical.choice ((ConvolutionCategory.hasExactPairing_iff_super C hC t ht).mp (hB j))
  let d : DecompositionData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData A S := ⟨i, p⟩
  have hl : DecompositionLaws d := ⟨hi, hp, hd, ho, hh⟩
  let e := ConvolutionCategory.evenDecompositionIso C hC t ht d hl
  letI := (SuperExactPairing.biproduct q).toEven
  exact ⟨superBiproduct (K := ℝ) (C := ConvolutionCategory C hC t ht) B,
    ConvolutionCategory.hasExactPairing_of_super C hC t ht
      (SuperExactPairing.ofEven (exactPairingCongrRight e))⟩

end RMod.Classification
