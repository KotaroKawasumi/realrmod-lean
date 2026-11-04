import RMod.Classification.Proofs.PlacedDualPairing
import RMod.Classification.Proofs.PullbackSchur
import RMod.Classification.Instances.ConvolutionPairings

/-!
# Completing the actual placed pairing from its first snake

The already proved convolution pentagon permits the existing pairing
completion theorem to derive the second snake from the first. The
opposite object's even Schur property is proved by parity conjugation
and extension of its inverse at the unique support coordinate. The
resulting laws concern the original, specified coevaluation and evaluation.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  (g : t.group) {X Y : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (q : DualPairing ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ X Y)

theorem placedTwistedPairingLaws_of_first
    (hXne : C.id X ≠ C.zero)
    (hY : ∀ f : C.Hom Y Y, C.IsHomogeneous 0 f → f ≠ C.zero → C.IsEvenIso f)
    (hfirst : normalizedXSnake (D := ConvolutionCategory C hC t ht)
      (placedTwistedCoevaluation C hC t g hX q) (placedTwistedEvaluation C hC t ht g hX q) =
        @CategoryStruct.id (ConvolutionCategory C hC t ht) _ (placedObj C hC t g X hX)) :
    DualPairingLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (placedTwistedPairingData C hC t ht g hX q) := by
  let A : ConvolutionCategory C hC t ht := placedObj C hC t g X hX
  let B : ConvolutionCategory C hC t ht := placedRightDualObj C hC t g hX q
  let η : 𝟙_ (ConvolutionCategory C hC t ht) ⟶ A ⊗ B := placedTwistedCoevaluation C hC t g hX q
  let ε : B ⊗ A ⟶ 𝟙_ (ConvolutionCategory C hC t ht) := placedTwistedEvaluation C hC t ht g hX q
  have hA : 𝟙 A ≠ 0 := by
    intro hz
    have hh := congrFun hz g
    change C.id (placedObj C hC t g X hX g).val = C.zero at hh
    rw [placedObj_at] at hh
    exact hXne hh
  have hBtype : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g⁻¹))
      (C.tensorObj Y (C.pi.factor (t.nu g g⁻¹))) := by
    have hy := InComponent.right_dual hC q hX
    have hp := InComponent.tensor hC hy (InComponent.parity_factor hC (t.nu g g⁻¹))
    simpa only [map_inv, toAdd_inv, add_zero] using hp
  have hB : ∀ f : B ⟶ B, f ∈ homGrade ℝ B B 0 → f ≠ 0 → IsIso f := by
    intro f hf hne
    have hs := right_factor_even_schur
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ C.pi hC.pi hY (t.nu g g⁻¹)
    obtain ⟨_, s, _, hfs, hsf⟩ := twistedPullback_placed_even_schur C hC t ht g⁻¹
      (C.tensorObj Y (C.pi.factor (t.nu g g⁻¹))) hBtype hs f hf hne
    exact ⟨⟨s, hfs, hsf⟩⟩
  let p : SuperExactPairing ℝ A B := SuperExactPairing.ofNormalizedXSnakeOfEvenSchur η ε
    (placedTwistedCoevaluation_even C hC t g hX q)
    (placedTwistedEvaluation_even C hC t ht g hX q) hfirst hA hB
  exact ConvolutionCategory.pairingLaws C hC t ht p

end RMod.Classification
