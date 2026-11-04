import RMod.BrundanEllis.StackingParityCover
import RMod.Classification.Proofs.ParityPowers
import Mathlib.CategoryTheory.Monoidal.Category

/-! The category and tensor data for the parity cover. The scalar on a
tensor of arrows is (-1)^(p deg(g)), with p the source parity of the first
arrow. This converts super-interchange into ordinary interchange. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace RMod.BrundanEllis.Stacking.ParityCover
open RMod.Classification CategoryTheory
variable (C : WeaklyPointedSuperfusion.{u, v})

/-- Two adjacent endpoint parities cancel in a composite. -/
theorem composeParity (p q r : ZMod 2) : (p + q) + (q + r) = p + r := by
  ring_nf
  simp [CharTwo.two_eq_zero]

instance category : Category.{v} (ParityCover C) where
  Hom := Hom C
  id X := ⟨C.data.id X.1, by
    change C.data.id X.1 ∈ C.data.grade X.1 X.1 (X.2 + X.2)
    rw [CharTwo.add_self_eq_zero]
    exact C.laws.id_even X.1⟩
  comp {X Y Z} f g := ⟨C.data.comp f.val g.val, by
    rw [← composeParity X.2 Y.2 Z.2]
    exact C.laws.comp_grade _ _ f.property g.property⟩
  id_comp f := Subtype.ext (C.laws.id_comp f.val)
  comp_id f := Subtype.ext (C.laws.comp_id f.val)
  assoc f g h := Subtype.ext (C.laws.comp_assoc f.val g.val h.val)

/-- Keep the original tensor object and add the auxiliary labels. -/
def tensorObj (X Y : ParityCover C) : ParityCover C := (C.data.tensorObj X.1 Y.1, X.2 + Y.2)

/-- Explicit ordinary tensor of arrows; the correction uses the first source label. -/
def tensorHom {X X' Y Y' : ParityCover C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj C X Y ⟶ tensorObj C X' Y' :=
  ⟨C.data.smul ((-1 : ℝ) ^ (X.2 * (Y.2 + Y'.2)).val) (C.data.tensorHom f.val g.val), by
    have he : (X.2 + X'.2) + (Y.2 + Y'.2) = (X.2 + Y.2) + (X'.2 + Y'.2) := by ring
    change C.data.IsHomogeneous ((X.2 + Y.2) + (X'.2 + Y'.2)) _
    rw [← he]
    exact C.laws.grade_smul _ _ (C.laws.tensor_grade _ _ f.property g.property)⟩

/-- Even arrows lift whenever the two auxiliary labels agree. -/
def evenHom {X Y : ParityCover C} (he : X.2 = Y.2)
    (f : C.data.Hom X.1 Y.1) (hf : C.data.IsHomogeneous 0 f) : X ⟶ Y :=
  ⟨f, by rw [he, CharTwo.add_self_eq_zero]; exact hf⟩

/-- All coherence maps are the original even maps, with their original inverses. -/
instance monoidalStruct : MonoidalCategoryStruct (ParityCover C) where
  tensorObj := tensorObj C
  tensorHom := tensorHom C
  whiskerLeft X _ _ f := tensorHom C (𝟙 X) f
  whiskerRight f Y := tensorHom C f (𝟙 Y)
  tensorUnit := (C.data.tensorUnit, 0)
  associator X Y Z :=
    { hom := evenHom C (add_assoc _ _ _) (C.data.associatorHom X.1 Y.1 Z.1)
        (C.laws.associator_hom_even _ _ _)
      inv := evenHom C (add_assoc _ _ _).symm (C.data.associatorInv X.1 Y.1 Z.1)
        (C.laws.associator_inv_even _ _ _)
      hom_inv_id := Subtype.ext (C.laws.associator_hom_inv _ _ _)
      inv_hom_id := Subtype.ext (C.laws.associator_inv_hom _ _ _) }
  leftUnitor X :=
    { hom := evenHom C (zero_add _) (C.data.leftUnitorHom X.1) (C.laws.left_unitor_hom_even _)
      inv := evenHom C (zero_add _).symm (C.data.leftUnitorInv X.1) (C.laws.left_unitor_inv_even _)
      hom_inv_id := Subtype.ext (C.laws.left_unitor_hom_inv _)
      inv_hom_id := Subtype.ext (C.laws.left_unitor_inv_hom _) }
  rightUnitor X :=
    { hom := evenHom C (add_zero _) (C.data.rightUnitorHom X.1) (C.laws.right_unitor_hom_even _)
      inv := evenHom C (add_zero _).symm (C.data.rightUnitorInv X.1) (C.laws.right_unitor_inv_even _)
      hom_inv_id := Subtype.ext (C.laws.right_unitor_hom_inv _)
      inv_hom_id := Subtype.ext (C.laws.right_unitor_inv_hom _) }

end RMod.BrundanEllis.Stacking.ParityCover
