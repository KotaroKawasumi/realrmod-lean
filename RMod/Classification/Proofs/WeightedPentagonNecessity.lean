import RMod.Classification.Proofs.WeightedPentagon
import RMod.Classification.Proofs.ParityPentagonRoutes
import RMod.Classification.Proofs.ScalarFaithfulness

/-!
# The actual pentagon forces its fermionic scalar equation

Extract the five weights from the two routes and apply the proved parity
crossing equation. The unweighted route is invertible; a nonzero source
therefore allows cancellation of that route in its real Hom space.
This is the converse needed when reconstructing omega from tensorators.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem localAssociator_pentagon_scalar_of_eq (W X Y Z : C.data.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) (ω₁ ω₂ ω₃ ω₄ ω₅ : ℝˣ)
    (hne : C.data.id (C.data.tensorObj (C.data.tensorObj
      (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) (p.factor a)) Y)
        (p.factor b)) Z) (p.factor t)) ≠ C.data.zero)
    (heq : (p.weightedParityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅ ω₁ ω₂ ω₅).hom =
      (p.weightedParityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄ ω₃ ω₄).hom) :
    (ω₁ : ℝ) * (ω₅ : ℝ) * (ω₂ : ℝ) =
      ((-1 : ℝ) ^ (a * e).val) * ((ω₄ : ℝ) * (ω₃ : ℝ)) := by
  rw [weightedParityPentagonThree_hom C.laws, weightedParityPentagonTwo_hom C.laws,
    parityPentagon_sign C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₃ h₄ h₅,
    ← C.laws.mul_smul] at heq
  have hi := (hp.parityPentagonThree_evenIso C.laws W X Y Z a b c d e f q r s t h₁ h₂ h₅).toIsoLaws
  have hs := raw_smul_injective C _ (iso_hom_ne_zero C hi hne) heq
  exact hs.trans (mul_comm _ _)

theorem localAssociator_pentagon_unit_scalar_of_eq (W X Y Z : C.data.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) (ω₁ ω₂ ω₃ ω₄ ω₅ : ℝˣ)
    (hne : C.data.id (C.data.tensorObj (C.data.tensorObj
      (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj (C.data.tensorObj W X) (p.factor a)) Y)
        (p.factor b)) Z) (p.factor t)) ≠ C.data.zero)
    (heq : (p.weightedParityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅ ω₁ ω₂ ω₅).hom =
      (p.weightedParityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄ ω₃ ω₄).hom) :
    ω₂ * ω₅ * ω₁ = realSign (a * e) * (ω₄ * ω₃) := by
  apply Units.ext
  simp only [Units.val_mul, realSign_coe]
  calc
    _ = (ω₁ : ℝ) * (ω₅ : ℝ) * (ω₂ : ℝ) := by ac_rfl
    _ = _ := localAssociator_pentagon_scalar_of_eq C p hp W X Y Z a b c d e f q r s t
      h₁ h₂ h₃ h₄ h₅ ω₁ ω₂ ω₃ ω₄ ω₅ hne heq

end RMod.Classification
