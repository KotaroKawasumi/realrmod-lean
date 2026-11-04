import RMod.Hierarchy.Bridge.MonoidalLaws
import RMod.Classification.Instances.Duals

/-!
# The even equivalence is monoidal and preserves duality

Its tensor and unit comparisons are identity isomorphisms, because the
object operations were retained. Mathlib then reflects exact pairings
along this fully faithful monoidal functor.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

instance ofOldEvenMonoidal : MonoidalCategory (Even (ofOldSupercategory C)) :=
  evenCategoryMonoidal (ofOldMonoidalSupercategory C)

def evenForgetCoreMonoidal : (evenForget C).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left {X Y} f Z := by
    change evenHomEquiv C _ _ f ▷ oldEvenObj C Z ≫ 𝟙 _ =
      𝟙 _ ≫ evenHomEquiv C _ _ (eTensor (ofOldMonoidalStructureData C) f
        ((ofOldSupercategoryData C).id Z))
    rw [Category.comp_id, Category.id_comp, evenHomEquiv_tensor,
      evenHomEquiv_id, tensorHom_id]
  μIso_hom_natural_right {X Y} Z f := by
    change oldEvenObj C Z ◁ evenHomEquiv C _ _ f ≫ 𝟙 _ =
      𝟙 _ ≫ evenHomEquiv C _ _ (eTensor (ofOldMonoidalStructureData C)
        ((ofOldSupercategoryData C).id Z) f)
    rw [Category.comp_id, Category.id_comp, evenHomEquiv_tensor,
      evenHomEquiv_id, id_tensorHom]
  associativity X Y Z := by
    change 𝟙 _ ▷ oldEvenObj C Z ≫ 𝟙 _ ≫
      evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).associatorHom X Y Z) =
      (α_ (oldEvenObj C X) (oldEvenObj C Y) (oldEvenObj C Z)).hom ≫
        oldEvenObj C X ◁ 𝟙 _ ≫ 𝟙 _
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    exact evenHomEquiv_associatorHom C X Y Z
  left_unitality X := by
    change (λ_ (oldEvenObj C X)).hom = 𝟙 _ ▷ oldEvenObj C X ≫ 𝟙 _ ≫
      evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).leftHom X)
    simp only [id_whiskerRight, Category.id_comp]
    exact (evenHomEquiv_leftHom C X).symm
  right_unitality X := by
    change (ρ_ (oldEvenObj C X)).hom = oldEvenObj C X ◁ 𝟙 _ ≫ 𝟙 _ ≫
      evenHomEquiv C _ _ ((ofOldMonoidalStructureData C).rightHom X)
    simp only [whiskerLeft_id, Category.id_comp]
    exact (evenHomEquiv_rightHom C X).symm

instance evenForget_monoidal : (evenForget C).Monoidal :=
  (evenForgetCoreMonoidal C).toMonoidal

@[implicit_reducible]
def ofOldExactPairing (X Y : C.data.Obj) (h : C.data.HasExactPairing X Y) :
    ExactPairing (evenObj (ofOldSupercategory C) X) (evenObj (ofOldSupercategory C) Y) := by
  let p := Classical.choice ((Classification.hasExactPairing_iff C X Y).mp h)
  letI : ExactPairing ((evenForget C).obj (evenObj (ofOldSupercategory C) X))
      ((evenForget C).obj (evenObj (ofOldSupercategory C) Y)) := p.toEvenPairing
  exact ExactPairing.ofFullyFaithful (evenForget C) _ _

@[implicit_reducible]
def ofOldRigidCategory : RigidCategory (Even (ofOldSupercategory C)) where
  rightDual X := {
    rightDual := (C.laws.has_right_dual X).choose
    exact := ofOldExactPairing C X _ (C.laws.has_right_dual X).choose_spec }
  leftDual X := {
    leftDual := (C.laws.has_left_dual X).choose
    exact := ofOldExactPairing C _ X (C.laws.has_left_dual X).choose_spec }

end RMod.Legacy.Hierarchy
