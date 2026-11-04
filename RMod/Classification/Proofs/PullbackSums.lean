import RMod.Classification.Instances.PullbackSums
import RMod.Classification.Instances.PullbackLinearCategory

/-!
# Biproduct laws of the actual pullback

The evenness and matrix-unit equations hold in every coordinate.
Evaluation commutes with the stored finite sum, so C's total identity
proves the pullback total identity as an equality of whole morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem pullbackSumLaws {n : ℕ} (S : Fin n → PullbackObj C t) :
    BiproductLaws (twistedPullbackData C hC t ht) S (pullbackSumData C hC t ht S) where
  inclusion_even i g := ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun j => (S j g).val)).inclusion_even i
  projection_even i g := ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun j => (S j g).val)).projection_even i
  diagonal i := funext fun g => ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun j => (S j g).val)).diagonal i
  off_diagonal i j hij := funext fun g => ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum
    (fun l => (S l g).val)).off_diagonal i j hij
  total := by
    apply funext
    intro g
    rw [PullbackCategory.finSum_apply C hC t ht]
    exact ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum (fun i => (S i g).val)).total

theorem twistedPullback_hasFiniteBiproduct {n : ℕ} (S : Fin n → PullbackObj C t) :
    (twistedPullbackData C hC t ht).HasFiniteBiproduct S := by
  let d := pullbackSumData C hC t ht S
  have hd := pullbackSumLaws C hC t ht S
  exact ⟨d.object, d.inclusion, d.projection, hd.inclusion_even, hd.projection_even,
    hd.diagonal, hd.off_diagonal, hd.total⟩

end RMod.Classification
