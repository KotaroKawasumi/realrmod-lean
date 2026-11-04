import RMod.Classification.Instances.ConvolutionBiproducts
import RMod.Classification.Abstract.Duals
import Superfusion.Category.ExactPairingBiproduct
import Superfusion.Category.ExactPairingCompletion

/-!
# Returning exact pairings to the separated pullback interface

Existing super exact pairings retain their actual coevaluation and
evaluation maps. The data adapter projects those maps; the laws adapter
uses both existing snake identities with the required parenthesization.
This permits reuse of the biproduct and pairing-completion theorems.
-/

set_option autoImplicit false

namespace RMod.Classification.ConvolutionCategory

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
  {X Y : ConvolutionCategory C hC t ht}

def pairingData (p : SuperExactPairing ℝ X Y) :
    DualPairingData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X Y where
  coeval := p.coeval
  eval := p.eval

theorem pairingLaws (p : SuperExactPairing ℝ X Y) :
    DualPairingLaws (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData
      (pairingData C hC t ht p) where
  coeval_even := p.coeval_mem
  eval_even := p.eval_mem
  snake_right := (Category.assoc _ _ _).trans p.coevaluation_evaluation
  snake_left := (Category.assoc _ _ _).trans p.evaluation_coevaluation

theorem hasExactPairing_of_super (p : SuperExactPairing ℝ X Y) :
    (twistedPullbackData C hC t ht).HasExactPairing X Y := by
  let d := pairingData C hC t ht p
  have hd := pairingLaws C hC t ht p
  exact ⟨d.coeval, d.eval, hd.coeval_even, hd.eval_even, hd.snake_right, hd.snake_left⟩

/-- Reuse an existing super pairing only after the laws on its precise raw maps are proved. -/
def superPairing (d : DualPairingData (twistedPullbackData C hC t ht).toWeaklyPointedSuperfusionData X Y)
    (hd : DualPairingLaws _ d) : SuperExactPairing ℝ X Y where
  coeval := d.coeval
  eval := d.eval
  coeval_mem := hd.coeval_even
  eval_mem := hd.eval_even
  coevaluation_evaluation := (Category.assoc _ _ _).symm.trans hd.snake_right
  evaluation_coevaluation := (Category.assoc _ _ _).symm.trans hd.snake_left

theorem hasExactPairing_iff_super :
    (twistedPullbackData C hC t ht).HasExactPairing X Y ↔ Nonempty (SuperExactPairing ℝ X Y) := by
  constructor
  · rintro ⟨η, ε, hη, hε, hr, hl⟩
    exact ⟨superPairing C hC t ht ⟨η, ε⟩ ⟨hη, hε, hr, hl⟩⟩
  · rintro ⟨p⟩
    exact hasExactPairing_of_super C hC t ht p

end RMod.Classification.ConvolutionCategory
