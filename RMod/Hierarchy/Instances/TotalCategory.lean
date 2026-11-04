import RMod.Hierarchy.Instances.TotalComposition

/-!
# The total linear category

The categorical operations are the two-component convolution. The grading
submodule records morphisms supported in a single parity.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy

@[implicit_reducible] def TotalCategory (C : Supercategory) := C.data.Obj
def totalObj (C : Supercategory) (X : C.data.Obj) : TotalCategory C := X
instance totalCategoryCategory (C : Supercategory) : Category (TotalCategory C) where
  Hom := THom C.data
  id X := evenPoint (C.data.id X)
  comp := tComp C.data
  id_comp := fun {_ _} f => tComp_id_left C f
  comp_id := fun {_ _} f => tComp_id_right C f
  assoc := fun {_ _ _ _} f g h => tComp_assoc C f g h

instance totalCategoryPreadditive (C : Supercategory) : Preadditive (TotalCategory C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (THom C.data X Y))
  add_comp := fun _ _ _ f g h => tComp_add_left C.data f g h
  comp_add := fun _ _ _ f g h => tComp_add_right C.data f g h
instance totalCategoryLinear (C : Supercategory) : Linear ℝ (TotalCategory C) where
  homModule X Y := inferInstanceAs (Module ℝ (THom C.data X Y))
  smul_comp := fun _ _ _ r f g => tComp_smul_left C.data r f g
  comp_smul := fun _ _ _ f r g => tComp_smul_right C.data r f g

def grade (C : Supercategory) (X Y : TotalCategory C) (a : ZMod 2) :
    Submodule ℝ (X ⟶ Y) where
  carrier f := ∀ b, b ≠ a → f b = 0
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro f g hf hg b hb
    change f b + g b = 0
    rw [hf b hb, hg b hb, add_zero]
  smul_mem' := by
    intro r f hf b hb
    change r • f b = 0
    rw [hf b hb, smul_zero]

def SameParityOrbit (C : Supercategory) (X Y : TotalCategory C) : Prop :=
  ∃ (a : ZMod 2) (e : X ≅ Y), e.hom ∈ grade C X Y a ∧ e.inv ∈ grade C Y X a

end RMod.Legacy
