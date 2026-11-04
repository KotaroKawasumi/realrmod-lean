import RMod.Classification.Instances.WeightedPentagonRoutes
import RMod.Classification.Proofs.ParityPentagon
import RMod.Classification.Proofs.Parameters

/-!
# Scalar-weighted pentagon for the specified local associators

Bilinearity extracts the three weights on the long route and the two on
the short route. The fermionic cocycle equation supplies precisely the
scalar discrepancy of the underlying parity routes, so their weighted
maps agree on arbitrary ordinary objects.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

section ScalarExtraction

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
  (p : PiData C)

include hC

theorem weightedParityPentagonThree_hom (W X Y Z : C.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₅ : d + t = f + s) (ω₁ ω₂ ω₅ : ℝˣ) :
    (p.weightedParityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅ ω₁ ω₂ ω₅).hom =
      C.smul ((ω₁ : ℝ) * (ω₅ : ℝ) * (ω₂ : ℝ))
        (p.parityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅).hom := by
  simp only [PiData.weightedParityPentagonThree, PiData.parityPentagonThree,
    IsoData.trans, IsoData.tensor, IsoData.refl, PiData.localAssociator, IsoData.scale,
    Units.val_one, hC.one_smul, hC.tensor_smul_left, hC.tensor_smul_right,
    hC.smul_comp, hC.comp_smul, ← hC.mul_smul]

theorem weightedParityPentagonTwo_hom (W X Y Z : C.Obj) (a b c d e f q r s t : ZMod 2)
    (h₃ : a + r = q + s) (h₄ : b + t = e + r) (ω₃ ω₄ : ℝˣ) :
    (p.weightedParityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄ ω₃ ω₄).hom =
      C.smul ((ω₄ : ℝ) * (ω₃ : ℝ))
        (p.parityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄).hom := by
  simp only [PiData.weightedParityPentagonTwo, PiData.parityPentagonTwo,
    IsoData.trans, PiData.localAssociator, IsoData.scale, Units.val_one, hC.one_smul,
    hC.smul_comp, hC.comp_smul, ← hC.mul_smul]

end ScalarExtraction

section WeightedIdentity

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

/-- The five scalar weights cancel the unique parity crossing sign. -/
theorem localAssociator_pentagon (W X Y Z : C.data.Obj) (a b c d e f q r s t : ZMod 2)
    (h₁ : a + b = c + d) (h₂ : c + f = e + q) (h₃ : a + r = q + s)
    (h₄ : b + t = e + r) (h₅ : d + t = f + s) (ω₁ ω₂ ω₃ ω₄ ω₅ : ℝˣ)
    (hω : (ω₁ : ℝ) * (ω₅ : ℝ) * (ω₂ : ℝ) =
      ((-1 : ℝ) ^ (a * e).val) * ((ω₄ : ℝ) * (ω₃ : ℝ))) :
    (p.weightedParityPentagonThree W X Y Z a b c d e f q r s t h₁ h₂ h₅ ω₁ ω₂ ω₅).hom =
      (p.weightedParityPentagonTwo W X Y Z a b c d e f q r s t h₃ h₄ ω₃ ω₄).hom := by
  rw [weightedParityPentagonThree_hom C.laws, weightedParityPentagonTwo_hom C.laws,
    parityPentagon_sign C p hp W X Y Z a b c d e f q r s t h₁ h₂ h₃ h₄ h₅,
    ← C.laws.mul_smul, hω, mul_comm ((-1 : ℝ) ^ (a * e).val)]

end WeightedIdentity

/-- The unit-valued sign in the parameter interface is the same real
scalar as the one computed by the center crossing. -/
theorem realSign_coe (a : ZMod 2) : (realSign a : ℝ) = (-1 : ℝ) ^ a.val := by
  rcases parity_cases a with rfl | rfl
  · rfl
  · simp only [realSign, if_neg one_ne_zero, Units.val_neg, Units.val_one]
    change (-1 : ℝ) = (-1 : ℝ) ^ 1
    rw [pow_one]

/-- The parameter pentagon has the scalar order required by the actual
three-edge and two-edge compositions. -/
theorem TwistLaws.pentagon_scalar {t : TwistData} (ht : TwistLaws t) (g h k l : t.group) :
    (t.omega g h k : ℝ) * (t.omega g (h * k) l : ℝ) * (t.omega h k l : ℝ) =
      ((-1 : ℝ) ^ (t.nu g h * t.nu k l).val) *
        ((t.omega (g * h) k l : ℝ) * (t.omega g h (k * l) : ℝ)) := by
  have he := congrArg (fun x : ℝˣ => (x : ℝ)) (ht.pentagon g h k l)
  simp only [Units.val_mul, realSign_coe] at he
  calc
    _ = (t.omega h k l : ℝ) * (t.omega g (h * k) l : ℝ) * (t.omega g h k : ℝ) := by ac_rfl
    _ = _ := he

end RMod.Classification
