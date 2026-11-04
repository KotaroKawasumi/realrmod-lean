import RMod.Hierarchy.Instances.GradedTensorPoints

/-!
# The middle crossing on homogeneous generators

Mathlib's tensor comparison swaps the second and third inputs. With the
Koszul braiding this contributes exactly their parity product sign.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace RMod.Legacy

theorem tensorμ_gradedTmul (A B C D : SuperVec) (i j k l a : ZMod 2)
    (h : i + j + k + l = a) (f : A i) (g : B j) (q : C k) (r : D l) :
    tensorμ A B C D a
      (gradedTmul (A ⊗ B) (C ⊗ D) (i + j) (k + l) a (by rw [← add_assoc, h])
        (gradedTmul A B i j (i + j) rfl f g) (gradedTmul C D k l (k + l) rfl q r)) =
    (-1 : ℝ) ^ (j * k).val •
      gradedTmul (A ⊗ C) (B ⊗ D) (i + k) (j + l) a (by linear_combination h)
        (gradedTmul A C i k (i + k) rfl f q) (gradedTmul B D j l (j + l) rfl g r) := by
  change (α_ A C (B ⊗ D)).inv a
    (((𝟙 A) ⊗ₘ (α_ C B D).hom) a
      (((𝟙 A) ⊗ₘ (koszulMap B C ⊗ₘ (𝟙 D))) a
        (((𝟙 A) ⊗ₘ (α_ B C D).inv) a
          ((α_ A B (C ⊗ D)).hom a
            (gradedTmul (A ⊗ B) (C ⊗ D) (i + j) (k + l) a _
              (gradedTmul A B i j (i + j) rfl f g)
              (gradedTmul C D k l (k + l) rfl q r)))))) = _
  erw [associator_hom_gradedTmul A B (C ⊗ D) i j (k + l) a (by rw [← add_assoc, h])]
  erw [tensorHom_gradedTmul (𝟙 A) (α_ B C D).inv]
  erw [associator_inv_gradedTmul B C D j k l (j + (k + l)) (add_assoc j k l)]
  erw [tensorHom_gradedTmul (𝟙 A) (koszulMap B C ⊗ₘ (𝟙 D))]
  erw [tensorHom_gradedTmul (koszulMap B C) (𝟙 D)]
  erw [koszulMap_gradedTmul B C j k (j + k) rfl]
  erw [gradedTmul_smul_left, gradedTmul_smul_right]
  erw [map_smul, tensorHom_gradedTmul (𝟙 A) (α_ C B D).hom]
  erw [associator_hom_gradedTmul_of_eq C B D k j l (j + k) (j + (k + l))
    (add_comm k j) (add_assoc j k l)]
  erw [map_smul, associator_inv_gradedTmul_of_eq A C (B ⊗ D) i k (j + l) (j + (k + l)) a
    (by abel) (by linear_combination h)]
  rfl

end RMod.Legacy
