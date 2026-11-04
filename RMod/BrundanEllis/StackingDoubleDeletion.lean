import RMod.Classification.Proofs.RightFactorDeletion
import RMod.Classification.Proofs.TensorCalculus

/-! Move outer parity deletions past homogeneous whiskered comparison maps with the exact signed naturality factor. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
universe u v
variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
include hC

/-- Whiskering on either side preserves composition when the other map
is an identity, including for homogeneous maps of nonzero degree. -/
theorem tensor_id_comp {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) (W : C.Obj) :
    C.tensorHom (C.comp f g) (C.id W) =
      C.comp (C.tensorHom f (C.id W)) (C.tensorHom g (C.id W)) := by
  rw [interchange_second_even hC _ _ _ _ (hC.id_even W), hC.id_comp]

theorem id_tensor_comp {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) (W : C.Obj) :
    C.tensorHom (C.id W) (C.comp f g) =
      C.comp (C.tensorHom (C.id W) f) (C.tensorHom (C.id W) g) := by
  rw [interchange_first_even hC _ _ _ _ (hC.id_even W), hC.id_comp]

variable {P : PiData C} (hP : PiLaws C P)
include hP

/-- Moving the outer deletion past a right-whiskered comparison contributes
its parity times the comparison degree. -/
theorem doubleRightDeletion {U V : C.Obj} (Z : C.Obj) (a b c : ZMod 2)
    (f : C.Hom U V) (hf : C.IsHomogeneous c f) :
    C.comp
      (C.tensorHom (C.tensorHom (C.comp (P.rightFactorDeletion U a).hom f) (C.id Z))
        (C.id (P.factor b)))
      (P.rightFactorDeletion (C.tensorObj V Z) b).hom =
    C.smul ((-1 : ℝ) ^ (b * c).val)
      (C.comp
        (C.tensorHom (C.tensorHom (P.rightFactorDeletion U a).hom (C.id Z))
          (C.id (P.factor b)))
        (C.comp (P.rightFactorDeletion (C.tensorObj U Z) b).hom
          (C.tensorHom f (C.id Z)))) := by
  have hh : C.IsHomogeneous c (C.tensorHom f (C.id Z)) := by
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, add_zero] using hC.tensor_grade f (C.id Z) hf (hC.id_even Z)
  rw [tensor_id_comp hC, tensor_id_comp hC, hC.comp_assoc,
    (hP).rightFactorDeletion_naturality hC b _ hh, hC.comp_smul]

/-- The same outer deletion calculation for a left-whiskered comparison. -/
theorem doubleLeftDeletion {U V : C.Obj} (Z : C.Obj) (a b c : ZMod 2)
    (f : C.Hom U V) (hf : C.IsHomogeneous c f) :
    C.comp
      (C.tensorHom (C.tensorHom (C.id Z) (C.comp (P.rightFactorDeletion U a).hom f))
        (C.id (P.factor b)))
      (P.rightFactorDeletion (C.tensorObj Z V) b).hom =
    C.smul ((-1 : ℝ) ^ (b * c).val)
      (C.comp
        (C.tensorHom (C.tensorHom (C.id Z) (P.rightFactorDeletion U a).hom)
          (C.id (P.factor b)))
        (C.comp (P.rightFactorDeletion (C.tensorObj Z U) b).hom
          (C.tensorHom (C.id Z) f))) := by
  have hh : C.IsHomogeneous c (C.tensorHom (C.id Z) f) := by
    simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, zero_add] using hC.tensor_grade (C.id Z) f (hC.id_even Z) hf
  rw [id_tensor_comp hC, tensor_id_comp hC, hC.comp_assoc,
    (hP).rightFactorDeletion_naturality hC b _ hh, hC.comp_smul]

end RMod.BrundanEllis.Stacking
