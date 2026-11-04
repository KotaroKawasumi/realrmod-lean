import RMod.Classification.Proofs.TensorComparisonChangeComposition

/-!
# Binary scalar ratios on the two triple routes

Cancel the intermediate selected comparison and use the two binary scalar
identities. The only extra coefficient is the crossing already proved
for changed comparisons. All maps and inverse laws remain explicit.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem tensorComparisonRatio_left
    {X X' Y Y' Z Z' V V' : C.Obj} {a n : ZMod 2}
    (i : IsoData C X X') (hi : IsoLaws C i) (j : C.Hom Z Z')
    (k : C.Hom X Y) (l : C.Hom Y Y') (o : C.Hom V' V) (p : C.Hom V (C.tensorObj X Z))
    (q : C.Hom X' Y') (r : C.Hom V' (C.tensorObj X' Z')) (c₁ c₂ : ℝ)
    (hj : C.IsHomogeneous a j) (hk : C.IsHomogeneous n k)
    (h₁ : C.comp i.inv (C.comp k l) = C.smul c₁ q)
    (h₂ : C.comp (C.comp o p) (C.tensorHom i.hom j) = C.smul c₂ r) :
    C.comp (C.comp o p) (C.comp (C.tensorHom k (C.id Z)) (C.tensorHom l j)) =
      C.smul (c₂ * c₁ * (-1 : ℝ) ^ (a * n).val)
        (C.comp r (C.tensorHom q (C.id Z'))) := by
  have he := congrArg (C.comp (C.comp o p)) (tensorComparisonChange_left hC i hi j k l hj hk)
  rw [← hC.comp_assoc, h₂, h₁, hC.tensor_smul_left,
    hC.smul_comp, hC.comp_smul, ← hC.mul_smul, hC.comp_smul] at he
  have hh := congrArg (C.smul ((-1 : ℝ) ^ (a * n).val)) he
  rw [← hC.mul_smul, ← hC.mul_smul, parity_power_mul_self, hC.one_smul] at hh
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh.symm

theorem tensorComparisonRatio_right
    {X X' Y Y' Z Z' V V' : C.Obj} {a n : ZMod 2}
    (i : C.Hom X X') (j : IsoData C Y Y') (hj : IsoLaws C j)
    (k : C.Hom Y Z) (l : C.Hom Z Z') (o : C.Hom V' V) (p : C.Hom V (C.tensorObj X Y))
    (q : C.Hom Y' Z') (r : C.Hom V' (C.tensorObj X' Y')) (c₁ c₂ : ℝ)
    (hi : C.IsHomogeneous a i) (hk : C.IsHomogeneous n (C.comp j.inv (C.comp k l)))
    (h₁ : C.comp j.inv (C.comp k l) = C.smul c₁ q)
    (h₂ : C.comp (C.comp o p) (C.tensorHom i j.hom) = C.smul c₂ r) :
    C.comp (C.comp o p) (C.comp (C.tensorHom (C.id X) k) (C.tensorHom i l)) =
      C.smul (c₂ * c₁ * (-1 : ℝ) ^ (a * n).val)
        (C.comp r (C.tensorHom (C.id X') q)) := by
  have he := congrArg (C.comp (C.comp o p)) (tensorComparisonChange_right hC i j hj k l hi hk)
  rw [← hC.comp_assoc, h₂, h₁, hC.tensor_smul_right,
    hC.smul_comp, hC.comp_smul, ← hC.mul_smul, hC.comp_smul] at he
  have hh := congrArg (C.smul ((-1 : ℝ) ^ (a * n).val)) he
  rw [← hC.mul_smul, ← hC.mul_smul, parity_power_mul_self, hC.one_smul] at hh
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh.symm

end RMod.Classification
