import RMod.Hierarchy.Instances.SuperVecSymmetric

/-!
# Homogeneous tensor generators and coherence maps

These formulas evaluate Mathlib's graded associators and the Koszul braiding
on pure homogeneous tensors. They provide the sign bookkeeping needed to
transport tensor functors between the old and new presentations.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy

def gradedTmul (A B : SuperVec) (i j a : ZMod 2) (h : i + j = a)
    (f : A i) (g : B j) : (A ⊗ B) a := ιTensorObj A B i j a h (f ⊗ₜ[ℝ] g)

@[simp]
theorem gradedTmul_smul_left (A B : SuperVec) (i j a : ZMod 2) (h : i + j = a)
    (r : ℝ) (f : A i) (g : B j) :
    gradedTmul A B i j a h (r • f) g = r • gradedTmul A B i j a h f g := by
  simp [gradedTmul, ← TensorProduct.smul_tmul']

@[simp]
theorem gradedTmul_smul_right (A B : SuperVec) (i j a : ZMod 2) (h : i + j = a)
    (r : ℝ) (f : A i) (g : B j) :
    gradedTmul A B i j a h f (r • g) = r • gradedTmul A B i j a h f g := by
  simp [gradedTmul, TensorProduct.tmul_smul]

theorem tensorHom_gradedTmul {A B C D : SuperVec} (F : A ⟶ C) (G : B ⟶ D)
    (i j a : ZMod 2) (h : i + j = a) (f : A i) (g : B j) :
    (F ⊗ₘ G) a (gradedTmul A B i j a h f g) =
      gradedTmul C D i j a h (F i f) (G j g) := by
  have he := ι_tensorHom F G i j a h
  exact congrArg (fun m => m (f ⊗ₜ[ℝ] g)) he

theorem associator_hom_gradedTmul (A B C : SuperVec) (i j k a : ZMod 2)
    (h : i + j + k = a) (f : A i) (g : B j) (q : C k) :
    (α_ A B C).hom a (gradedTmul (A ⊗ B) C (i + j) k a h
      (gradedTmul A B i j (i + j) rfl f g) q) =
    gradedTmul A (B ⊗ C) i (j + k) a (by rw [← add_assoc, h]) f
      (gradedTmul B C j k (j + k) rfl g q) := by
  have he := ιTensorObj₃'_associator_hom A B C i j k a h
  have hx := congrArg (fun m => m ((f ⊗ₜ[ℝ] g) ⊗ₜ[ℝ] q)) he
  convert! hx

theorem associator_inv_gradedTmul (A B C : SuperVec) (i j k a : ZMod 2)
    (h : i + j + k = a) (f : A i) (g : B j) (q : C k) :
    (α_ A B C).inv a (gradedTmul A (B ⊗ C) i (j + k) a
      (by rw [← add_assoc, h]) f (gradedTmul B C j k (j + k) rfl g q)) =
    gradedTmul (A ⊗ B) C (i + j) k a h
      (gradedTmul A B i j (i + j) rfl f g) q := by
  have he := ιTensorObj₃_associator_inv A B C i j k a h
  have hx := congrArg (fun m => m (f ⊗ₜ[ℝ] (g ⊗ₜ[ℝ] q))) he
  convert! hx

theorem associator_hom_gradedTmul_of_eq (A B C : SuperVec) (i j k b a : ZMod 2)
    (hb : i + j = b) (ha : b + k = a) (f : A i) (g : B j) (q : C k) :
    (α_ A B C).hom a (gradedTmul (A ⊗ B) C b k a ha
      (gradedTmul A B i j b hb f g) q) =
    gradedTmul A (B ⊗ C) i (j + k) a (by rw [← add_assoc, hb, ha]) f
      (gradedTmul B C j k (j + k) rfl g q) := by
  subst b
  exact associator_hom_gradedTmul A B C i j k a ha f g q

theorem associator_inv_gradedTmul_of_eq (A B C : SuperVec) (i j k b a : ZMod 2)
    (hb : j + k = b) (ha : i + b = a) (f : A i) (g : B j) (q : C k) :
    (α_ A B C).inv a (gradedTmul A (B ⊗ C) i b a ha f
      (gradedTmul B C j k b hb g q)) =
    gradedTmul (A ⊗ B) C (i + j) k a (by rw [add_assoc, hb, ha])
      (gradedTmul A B i j (i + j) rfl f g) q := by
  subst b
  exact associator_inv_gradedTmul A B C i j k a (by rw [add_assoc, ha]) f g q

theorem koszulMap_gradedTmul (A B : SuperVec) (i j a : ZMod 2)
    (h : i + j = a) (f : A i) (g : B j) :
    koszulMap A B a (gradedTmul A B i j a h f g) =
      (-1 : ℝ) ^ (i * j).val • gradedTmul B A j i a (by rw [add_comm, h]) g f := by
  have he := ι_koszulMap A B i j a h
  have hx := congrArg (fun m => m (f ⊗ₜ[ℝ] g)) he
  convert! hx

/-- Four homogeneous inputs determine a map out of a paired graded tensor. -/
theorem gradedFour_ext (A B C D V : SuperVec) (F G : (A ⊗ B) ⊗ (C ⊗ D) ⟶ V)
    (h : ∀ (i j k l a : ZMod 2) (ha : i + j + k + l = a)
      (f : A i) (g : B j) (q : C k) (r : D l),
      F a (gradedTmul (A ⊗ B) (C ⊗ D) (i + j) (k + l) a (by rw [← add_assoc, ha])
        (gradedTmul A B i j (i + j) rfl f g) (gradedTmul C D k l (k + l) rfl q r)) =
      G a (gradedTmul (A ⊗ B) (C ⊗ D) (i + j) (k + l) a (by rw [← add_assoc, ha])
        (gradedTmul A B i j (i + j) rfl f g) (gradedTmul C D k l (k + l) rfl q r))) :
    F = G := by
  funext a
  apply (cancel_epi ((α_ A B (C ⊗ D)).inv a)).mp
  apply tensorObj₄_ext
  intro i j k l ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply TensorProduct.ext_threefold'
  intro g q r
  change F a ((α_ A B (C ⊗ D)).inv a
    (gradedTmul A (B ⊗ (C ⊗ D)) i (j + k + l) a _ f
      (gradedTmul B (C ⊗ D) j (k + l) (j + k + l) _ g
        (gradedTmul C D k l (k + l) rfl q r)))) =
    G a ((α_ A B (C ⊗ D)).inv a
    (gradedTmul A (B ⊗ (C ⊗ D)) i (j + k + l) a _ f
      (gradedTmul B (C ⊗ D) j (k + l) (j + k + l) _ g
        (gradedTmul C D k l (k + l) rfl q r))))
  erw [associator_inv_gradedTmul_of_eq A B (C ⊗ D) i j (k + l) (j + k + l) a
    (add_assoc j k l).symm (by rw [← add_assoc, ← add_assoc, ha])]
  exact h i j k l a ha f g q r

end RMod.Legacy
