import RMod.Classification.Proofs.Parity
import Mathlib.Tactic.NormNum

/-!
# Transport between the two tensor sign conventions

The old interface uses the crossing of the first incoming map with the
second outgoing map. Mathlib's chronological enriched composition crosses
the second incoming map with the first outgoing map. Multiplying the tensor
of homogeneous maps by their Koszul sign converts the former to the latter.
This correction retains composition and all even structural maps.
-/

set_option autoImplicit false
namespace RMod.Legacy.Hierarchy

variable (C : WeaklyPointedSuperfusionData.{0, 0})

def chronologicalTensor {X X' Y Y' : C.Obj} (a b : ZMod 2)
    (f : C.Hom X X') (g : C.Hom Y Y') : C.Hom (C.tensorObj X Y) (C.tensorObj X' Y') :=
  C.smul ((-1 : ℝ) ^ (a * b).val) (C.tensorHom f g)

theorem chronologicalTensor_interchange (hC : WeaklyPointedSuperfusionLaws C)
    {X X' X'' Y Y' Y'' : C.Obj} (a b c d : ZMod 2)
    (f : C.Hom X X') (g : C.Hom Y Y') (f' : C.Hom X' X'') (g' : C.Hom Y' Y'')
    (hf : C.IsHomogeneous a f) (hg' : C.IsHomogeneous d g') :
    C.comp (chronologicalTensor C a b f g) (chronologicalTensor C c d f' g') =
      C.smul ((-1 : ℝ) ^ (b * c).val)
        (chronologicalTensor C (a + c) (b + d) (C.comp f f') (C.comp g g')) := by
  unfold chronologicalTensor
  rw [hC.smul_comp, hC.comp_smul, hC.super_interchange f' g' f g hg' hf]
  simp only [← hC.mul_smul]
  congr 1
  rcases Classification.parity_cases a with rfl | rfl <;>
    rcases Classification.parity_cases b with rfl | rfl <;>
    rcases Classification.parity_cases c with rfl | rfl <;>
    rcases Classification.parity_cases d with rfl | rfl <;>
    norm_num [ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_one]

theorem chronologicalTensor_even_left (hC : WeaklyPointedSuperfusionLaws C)
    {X X' Y Y' : C.Obj} (b : ZMod 2) (f : C.Hom X X') (g : C.Hom Y Y') :
    chronologicalTensor C 0 b f g = C.tensorHom f g := by
  simp only [chronologicalTensor, zero_mul, ZMod.val_zero, pow_zero, hC.one_smul]

theorem chronologicalTensor_even_right (hC : WeaklyPointedSuperfusionLaws C)
    {X X' Y Y' : C.Obj} (a : ZMod 2) (f : C.Hom X X') (g : C.Hom Y Y') :
    chronologicalTensor C a 0 f g = C.tensorHom f g := by
  simp only [chronologicalTensor, mul_zero, ZMod.val_zero, pow_zero, hC.one_smul]

end RMod.Legacy.Hierarchy
