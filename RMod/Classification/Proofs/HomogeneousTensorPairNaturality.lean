import RMod.Classification.Proofs.HomogeneousTensorNaturality

/-!
# Signed naturality of the tensor of two homogeneous comparisons

Apply the two single-factor squares successively. The chosen order makes
intermediate interchange sign-free, while the two naturality signs add
both comparison parities.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem signed_naturality_tensor {X X' Y Y' Z Z' W W' : C.Obj} {a b c d : ZMod 2}
    (i : C.Hom X Y) (i' : C.Hom X' Y') (j : C.Hom Z W) (j' : C.Hom Z' W')
    (f : C.Hom X X') (f' : C.Hom Y Y') (g : C.Hom Z Z') (g' : C.Hom W W')
    (hi : C.IsHomogeneous a i) (hj' : C.IsHomogeneous b j')
    (hf : C.IsHomogeneous c f) (hg' : C.IsHomogeneous d g')
    (hfi : C.comp f i' = C.smul ((-1 : ℝ) ^ (a * c).val) (C.comp i f'))
    (hgj : C.comp g j' = C.smul ((-1 : ℝ) ^ (b * d).val) (C.comp j g')) :
    C.comp (C.tensorHom f g) (C.tensorHom i' j') =
      C.smul ((-1 : ℝ) ^ ((a + b) * (c + d)).val)
        (C.comp (C.tensorHom i j) (C.tensorHom f' g')) := by
  have hn := signed_naturality_trans hC
    (signed_naturality_whiskerLeft hC j j' f g g' hj' hf hgj)
    (signed_naturality_whiskerRight hC i i' f f' g' hi hg' hfi)
  rw [interchange_second_even hC i' (C.id W') (C.id X') j' (hC.id_even W'),
    interchange_second_even hC i (C.id W) (C.id X) j (hC.id_even W),
    hC.id_comp, hC.comp_id, hC.id_comp, hC.comp_id,
    ← parity_power_add, ← add_mul, add_comm b a] at hn
  exact hn

end RMod.Classification
