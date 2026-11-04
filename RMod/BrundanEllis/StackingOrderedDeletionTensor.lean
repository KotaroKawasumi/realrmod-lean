import RMod.Classification.Proofs.OrderedParityDeletion
import RMod.Classification.Proofs.TensorCalculus

/-! Evaluate paired local associators and expand paired ordered deletions with their explicit super-interchange signs. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
universe u v

/-- The two even local associators can be evaluated against their ordered
parity deletions together, with exactly the product of the original scalars. -/
theorem tensor_localAssociator_orderedDeletion
    {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
    {P : PiData C} (hP : PiLaws C P) (X Y Z U V W : C.Obj)
    (a b c d e f g h : ZMod 2) (hab : a + b = c + d) (hef : e + f = g + h)
    (ω η : ℝˣ) :
    C.comp
      (C.tensorHom (P.localAssociator X Y Z a b c d hab ω).hom
        (P.localAssociator U V W e f g h hef η).hom)
      (C.tensorHom (P.orderedRightDeletion X Y Z c d).hom
        (P.orderedRightDeletion U V W g h).hom) =
    C.smul (ω.val * η.val)
      (C.tensorHom (P.orderedLeftDeletion X Y Z a b).hom
        (P.orderedLeftDeletion U V W e f).hom) := by
  rw [interchange_first_even hC _ _ _ _
    ((hP).localAssociator_evenIso hC X Y Z a b c d hab ω).hom_even,
    (hP).localAssociator_orderedDeletion hC, (hP).localAssociator_orderedDeletion hC,
    hC.tensor_smul_left, hC.tensor_smul_right, ← hC.mul_smul]

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
universe u v
variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
include hC

/-- The same super-interchange identity in the direction needed to unpack
paired ordered deletions. -/
theorem tensor_comp_signed {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C.Obj}
    (f : C.Hom Y₁ Z₁) (g : C.Hom Y₂ Z₂) (h : C.Hom X₁ Y₁) (k : C.Hom X₂ Y₂)
    (a b : ZMod 2) (hg : C.IsHomogeneous a g) (hh : C.IsHomogeneous b h) :
    C.tensorHom (C.comp h f) (C.comp k g) =
      C.smul ((-1 : ℝ) ^ (a * b).val)
        (C.comp (C.tensorHom h k) (C.tensorHom f g)) := by
  rw [hC.super_interchange f g h k hg hh, ← hC.mul_smul,
    parity_power_mul_self, hC.one_smul]

variable {P : PiData C} (hP : PiLaws C P)
include hP

/-- Expanding the two right ordered deletions contributes precisely the
outer parity of the second triple times the inner parity of the first. -/
theorem tensor_orderedRightDeletion (X Y Z U V W : C.Obj) (a b c d : ZMod 2) :
    C.tensorHom (P.orderedRightDeletion X Y Z a b).hom
      (P.orderedRightDeletion U V W c d).hom =
    C.smul ((-1 : ℝ) ^ (d * a).val)
      (C.comp
        (C.tensorHom
          (C.tensorHom (C.tensorHom (C.id X) (P.rightFactorDeletion (C.tensorObj Y Z) a).hom)
            (C.id (P.factor b)))
          (C.tensorHom (C.tensorHom (C.id U) (P.rightFactorDeletion (C.tensorObj V W) c).hom)
            (C.id (P.factor d))))
        (C.tensorHom (P.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) b).hom
          (P.rightFactorDeletion (C.tensorObj U (C.tensorObj V W)) d).hom)) := by
  exact tensor_comp_signed hC _ _ _ _ d a
    ((hP).rightFactorDeletion_homogeneousIso hC _ d).hom_grade
    ((((hP).rightFactorDeletion_homogeneousIso hC _ a).whiskerLeft hC X).whiskerRight hC
      (P.factor b)).hom_grade

/-- The same expansion for the left bracketings retains the two original
associators after the ordered deletions, with the same crossing sign. -/
theorem tensor_orderedLeftDeletion (X Y Z U V W : C.Obj) (a b c d : ZMod 2) :
    C.tensorHom (P.orderedLeftDeletion X Y Z a b).hom
      (P.orderedLeftDeletion U V W c d).hom =
    C.smul ((-1 : ℝ) ^ (d * a).val)
      (C.comp
        (C.tensorHom
          (C.tensorHom (C.tensorHom (P.rightFactorDeletion (C.tensorObj X Y) a).hom (C.id Z))
            (C.id (P.factor b)))
          (C.tensorHom (C.tensorHom (P.rightFactorDeletion (C.tensorObj U V) c).hom (C.id W))
            (C.id (P.factor d))))
        (C.comp
          (C.tensorHom (P.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) Z) b).hom
            (P.rightFactorDeletion (C.tensorObj (C.tensorObj U V) W) d).hom)
          (C.tensorHom (C.associatorHom X Y Z) (C.associatorHom U V W)))) := by
  have hh : C.IsHomogeneous a
      (C.tensorHom (C.tensorHom (P.rightFactorDeletion (C.tensorObj X Y) a).hom (C.id Z))
        (C.id (P.factor b))) :=
    ((((hP).rightFactorDeletion_homogeneousIso hC (C.tensorObj X Y) a).whiskerRight hC Z).whiskerRight hC
      (P.factor b)).hom_grade
  dsimp only [PiData.orderedLeftDeletion, IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.assoc]
  rw [← interchange_second_even hC _ _ _ _ (hC.associator_hom_even U V W),
    tensor_comp_signed hC _ _ _ _ d a
      ((hP).rightFactorDeletion_homogeneousIso hC (C.tensorObj (C.tensorObj U V) W) d).hom_grade hh,
    hC.smul_comp, hC.comp_assoc]

end RMod.BrundanEllis.Stacking
