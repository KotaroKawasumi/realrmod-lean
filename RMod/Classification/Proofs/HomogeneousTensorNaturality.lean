import RMod.Classification.Proofs.TensorCalculus
import RMod.Classification.Proofs.ParityPowers

/-!
# Signed naturality when a homogeneous comparison is whiskered

Tensoring a degree-a comparison with an identity still has degree a.
Super-interchange contributes the missing sign from the other input
morphism. The resulting naturality sign uses the sum of both input
degrees, as required for composing binary comparisons into triple routes.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem signed_naturality_trans {X X' Y Y' Z Z' : C.Obj}
    {f : C.Hom X X'} {g : C.Hom Y Y'} {h : C.Hom Z Z'}
    {i : C.Hom X Y} {i' : C.Hom X' Y'} {j : C.Hom Y Z} {j' : C.Hom Y' Z'} {r s : ℝ}
    (hi : C.comp f i' = C.smul r (C.comp i g))
    (hj : C.comp g j' = C.smul s (C.comp j h)) :
    C.comp f (C.comp i' j') = C.smul (r * s) (C.comp (C.comp i j) h) := by
  rw [← hC.comp_assoc, hi, hC.smul_comp, hC.comp_assoc, hj, hC.comp_smul,
    ← hC.mul_smul, ← hC.comp_assoc]

theorem signed_naturality_whiskerRight {X X' Y Y' Z Z' : C.Obj} {a b c : ZMod 2}
    (i : C.Hom X Y) (i' : C.Hom X' Y') (f : C.Hom X X') (g : C.Hom Y Y') (h : C.Hom Z Z')
    (hi : C.IsHomogeneous a i) (hh : C.IsHomogeneous c h)
    (hn : C.comp f i' = C.smul ((-1 : ℝ) ^ (a * b).val) (C.comp i g)) :
    C.comp (C.tensorHom f h) (C.tensorHom i' (C.id Z')) =
      C.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (C.comp (C.tensorHom i (C.id Z)) (C.tensorHom g h)) := by
  rw [interchange_second_even hC _ _ _ _ (hC.id_even Z'), hC.comp_id, hn, hC.tensor_smul_left]
  rw [hC.super_interchange g h i (C.id Z) hh hi, hC.id_comp, ← hC.mul_smul]
  congr 1
  rw [mul_add, parity_power_add, mul_comm c a, mul_assoc, parity_power_mul_self, mul_one]

theorem signed_naturality_whiskerLeft {X X' Y Y' Z Z' : C.Obj} {a b c : ZMod 2}
    (i : C.Hom X Y) (i' : C.Hom X' Y') (f : C.Hom Z Z') (g : C.Hom X X') (h : C.Hom Y Y')
    (hi : C.IsHomogeneous a i') (hf : C.IsHomogeneous b f)
    (hn : C.comp g i' = C.smul ((-1 : ℝ) ^ (a * c).val) (C.comp i h)) :
    C.comp (C.tensorHom f g) (C.tensorHom (C.id Z') i') =
      C.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (C.comp (C.tensorHom (C.id Z) i) (C.tensorHom f h)) := by
  rw [hC.super_interchange (C.id Z') i' f g hi hf, hC.comp_id, hn, hC.tensor_smul_right,
    ← hC.mul_smul]
  rw [interchange_first_even hC _ _ _ _ (hC.id_even Z), hC.id_comp]
  rw [mul_add, parity_power_add]

end RMod.Classification
