import RMod.Hierarchy.Instances.SuperVecLinear

/-!
# The Koszul interchange map

The graded tensor universal property assembles the ordinary module flip,
multiplied by the parity sign on each homogeneous summand. Applying the
map twice is the identity, with both maps specified explicitly.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
namespace RMod.Legacy

def koszulMap (X Y : SuperVec) : X ⊗ Y ⟶ Y ⊗ X := fun a =>
  GradedObject.Monoidal.tensorObjDesc fun i j hij =>
    ((-1 : ℝ) ^ (i * j).val) •
      ((β_ (X i) (Y j)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X j i a (by simpa only [add_comm j i] using hij))

@[reassoc]
theorem ι_koszulMap (X Y : SuperVec) (i j a : ZMod 2) (h : i + j = a) :
    ιTensorObj X Y i j a h ≫ koszulMap X Y a =
      ((-1 : ℝ) ^ (i * j).val) •
        ((β_ (X i) (Y j)).hom ≫ ιTensorObj Y X j i a (by simpa only [add_comm j i] using h)) :=
  ι_tensorObjDesc _ i j h

theorem koszulMap_comp (X Y : SuperVec) : koszulMap X Y ≫ koszulMap Y X = 𝟙 (X ⊗ Y) := by
  funext a
  apply tensorObj_ext
  intro i j h
  change ιTensorObj X Y i j a h ≫ (koszulMap X Y a ≫ koszulMap Y X a) =
    ιTensorObj X Y i j a h ≫ 𝟙 _
  erw [ι_koszulMap_assoc, Linear.smul_comp, assoc, ι_koszulMap,
    Linear.comp_smul, smul_smul, ← assoc, SymmetricCategory.symmetry,
    id_comp]
  have hs : (-1 : ℝ) ^ (i * j).val * (-1 : ℝ) ^ (j * i).val = 1 := by
    rw [mul_comm j i, ← pow_add, ← two_mul]
    simp [pow_mul]
  rw [hs, one_smul]

def koszulBraiding (X Y : SuperVec) : X ⊗ Y ≅ Y ⊗ X where
  hom := koszulMap X Y
  inv := koszulMap Y X
  hom_inv_id := koszulMap_comp X Y
  inv_hom_id := koszulMap_comp Y X

/-! The even and odd crossing signs are distinguished explicitly. -/
example (X Y : SuperVec) :
    ιTensorObj X Y 0 1 1 (zero_add 1) ≫ koszulMap X Y 1 =
      (β_ (X 0) (Y 1)).hom ≫ ιTensorObj Y X 1 0 1 (add_zero 1) := by
  simpa using ι_koszulMap X Y 0 1 1 (zero_add 1)

example (X Y : SuperVec) :
    ιTensorObj X Y 1 1 0 (CharTwo.add_self_eq_zero 1) ≫ koszulMap X Y 0 =
      -((β_ (X 1) (Y 1)).hom ≫ ιTensorObj Y X 1 1 0 (CharTwo.add_self_eq_zero 1)) := by
  simpa [ZMod.val_one] using ι_koszulMap X Y 1 1 0 (CharTwo.add_self_eq_zero 1)

end RMod.Legacy
