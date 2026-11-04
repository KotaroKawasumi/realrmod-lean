import RMod.Hierarchy.Instances.KoszulCoherence

/-!
# Koszul symmetry on real super vector spaces

The forward hexagon is checked on homogeneous tensor summands using
bimultiplicativity of the parity sign. Inverting that hexagon gives the
reverse hexagon, because the specified crossing is involutive.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
namespace RMod.Legacy

@[reassoc]
theorem ι₃_koszul_outer (X Y Z : SuperVec) (i j k a : ZMod 2) (h : i + j + k = a) :
    ιTensorObj₃ X Y Z i j k a h ≫ koszulMap X (Y ⊗ Z) a =
      (-1 : ℝ) ^ (i * (j + k)).val •
        ((β_ (X i) (Y j ⊗ Z k)).hom ≫
          ιTensorObj₃' Y Z X j k i a (by simpa only [add_assoc, add_comm, add_left_comm] using h)) := by
  erw [ιTensorObj₃_eq X Y Z i j k a h _ rfl, assoc, ι_koszulMap, Linear.comp_smul]
  congr 1
  erw [← MonoidalCategory.id_tensorHom, ← assoc, BraidedCategory.braiding_naturality,
    assoc, MonoidalCategory.tensorHom_id]

@[reassoc]
theorem ι₃'_koszul_left (X Y Z : SuperVec) (i j k a : ZMod 2) (h : i + j + k = a) :
    ιTensorObj₃' X Y Z i j k a h ≫ (koszulMap X Y ▷ Z) a =
      (-1 : ℝ) ^ (i * j).val •
        (((β_ (X i) (Y j)).hom ▷ Z k) ≫
          ιTensorObj₃' Y X Z j i k a (by simpa only [add_assoc, add_comm, add_left_comm] using h)) := by
  change ιTensorObj₃' X Y Z i j k a h ≫
    GradedObject.Monoidal.tensorHom (koszulMap X Y) (𝟙 Z) a = _
  erw [ιTensorObj₃'_eq X Y Z i j k a h _ rfl, assoc, ι_tensorHom]
  change (ιTensorObj X Y i j (i + j) rfl ▷ Z k) ≫
    ((koszulMap X Y (i + j) ▷ Z k) ≫ ιTensorObj (Y ⊗ X) Z (i + j) k a h) = _
  erw [← comp_whiskerRight_assoc, ι_koszulMap, MonoidalLinear.smul_whiskerRight,
    Linear.smul_comp]
  congr 1
  erw [comp_whiskerRight, assoc,
    ← ιTensorObj₃'_eq Y X Z j i k a
      (by simpa only [add_assoc, add_comm, add_left_comm] using h) (i + j) (add_comm j i)]

@[reassoc]
theorem ι₃_koszul_right (X Y Z : SuperVec) (i j k a : ZMod 2) (h : i + j + k = a) :
    ιTensorObj₃ X Y Z i j k a h ≫ (X ◁ koszulMap Y Z) a =
      (-1 : ℝ) ^ (j * k).val •
        ((X i ◁ (β_ (Y j) (Z k)).hom) ≫
          ιTensorObj₃ X Z Y i k j a (by simpa only [add_assoc, add_comm, add_left_comm] using h)) := by
  change ιTensorObj₃ X Y Z i j k a h ≫
    GradedObject.Monoidal.tensorHom (𝟙 X) (koszulMap Y Z) a = _
  erw [ιTensorObj₃_eq X Y Z i j k a h _ rfl, assoc, ι_tensorHom]
  change (X i ◁ ιTensorObj Y Z j k (j + k) rfl) ≫
    ((X i ◁ koszulMap Y Z (j + k)) ≫
      ιTensorObj X (Z ⊗ Y) i (j + k) a (by rw [← add_assoc, h])) = _
  erw [← whiskerLeft_comp_assoc, ι_koszulMap, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp]
  congr 1
  erw [whiskerLeft_comp, assoc,
    ← ιTensorObj₃_eq X Z Y i k j a
      (by simpa only [add_assoc, add_comm, add_left_comm] using h) (j + k) (add_comm k j)]

theorem koszul_hexagon_forward (X Y Z : SuperVec) :
    (α_ X Y Z).hom ≫ koszulMap X (Y ⊗ Z) ≫ (α_ Y Z X).hom =
      (koszulMap X Y ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ koszulMap X Z) := by
  funext a
  apply tensorObj₃'_ext
  intro i j k h
  change ιTensorObj₃' X Y Z i j k a h ≫
      ((GradedObject.Monoidal.associator X Y Z).hom a ≫
        koszulMap X (Y ⊗ Z) a ≫ (GradedObject.Monoidal.associator Y Z X).hom a) =
    ιTensorObj₃' X Y Z i j k a h ≫
      ((koszulMap X Y ▷ Z) a ≫ (GradedObject.Monoidal.associator Y X Z).hom a ≫
        (Y ◁ koszulMap X Z) a)
  erw [ιTensorObj₃'_associator_hom_assoc, ι₃_koszul_outer_assoc,
    Linear.smul_comp, Linear.comp_smul, assoc, ιTensorObj₃'_associator_hom,
    ι₃'_koszul_left_assoc, Linear.smul_comp, assoc,
    ιTensorObj₃'_associator_hom_assoc, assoc, ι₃_koszul_right,
    Linear.comp_smul, Linear.comp_smul, smul_smul, koszulSign_add_right]
  congr 1
  erw [BraidedCategory.hexagon_forward_assoc]
  all_goals simpa only [add_assoc, add_comm, add_left_comm] using h

theorem koszul_hexagon_reverse (X Y Z : SuperVec) :
    (α_ X Y Z).inv ≫ koszulMap (X ⊗ Y) Z ≫ (α_ Z X Y).inv =
      (X ◁ koszulMap Y Z) ≫ (α_ X Z Y).inv ≫ (koszulMap X Z ▷ Y) := by
  have h : (α_ Z X Y) ≪≫ koszulBraiding Z (X ⊗ Y) ≪≫ (α_ X Y Z) =
      whiskerRightIso (koszulBraiding Z X) Y ≪≫ (α_ X Z Y) ≪≫
        whiskerLeftIso X (koszulBraiding Z Y) := Iso.ext (koszul_hexagon_forward Z X Y)
  have hi := congrArg Iso.inv h
  simpa only [Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, koszulBraiding,
    Category.assoc] using hi

instance superVecSymmetric : SymmetricCategory SuperVec where
  braiding := koszulBraiding
  braiding_naturality_left := koszul_naturality_left
  braiding_naturality_right := koszul_naturality_right
  hexagon_forward := koszul_hexagon_forward
  hexagon_reverse := koszul_hexagon_reverse
  symmetry := koszulMap_comp

end RMod.Legacy
