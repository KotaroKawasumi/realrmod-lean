import RMod.Classification.Instances.HomogeneousHomMatrix

/-!
# Composition and grading of rectangular Hom coordinates

Matrix multiplication contracts the middle sum using its total identity.
The entry in row i and column j of a degree-a map has degree
`a + targetParity i + sourceParity j`. Both coordinate directions
respect these grades, including zero and empty presentations.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory CategoryTheory.Preadditive

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C : WeaklyPointedSuperfusion.{0, 0}} {S X Y Z : LinearCategory C} {n m l : ℕ}
  (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data S Y m)
  (h : HomogeneousSum C.data S Z l)

theorem toHomMatrix_id : toHomMatrix d d (𝟙 X) = 1 := toMatrix_one d

theorem toHomMatrix_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    toHomMatrix d h (f ≫ g) = toHomMatrix e h g * toHomMatrix d e f := by
  ext i j
  change d.data.inclusion j ≫ (f ≫ g) ≫ h.data.projection i = _
  rw [Matrix.mul_apply]
  change _ = ∑ k, (d.data.inclusion j ≫ f ≫ e.data.projection k) ≫
    (e.data.inclusion k ≫ g ≫ h.data.projection i)
  simp only [Category.assoc]
  have hterm (k) :
      d.data.inclusion j ≫ f ≫ e.data.projection k ≫ e.data.inclusion k ≫ g ≫ h.data.projection i =
        d.data.inclusion j ≫ f ≫ (e.data.projection k ≫ e.data.inclusion k) ≫ g ≫
          h.data.projection i := by simp only [Category.assoc]
  simp only [hterm, ← comp_sum (C := LinearCategory C), ← sum_comp (C := LinearCategory C),
    total, Category.id_comp]

theorem toHomMatrix_grade {a : ZMod 2} {f : X ⟶ Y}
    (hf : C.data.IsHomogeneous a f) (i j) :
    C.data.IsHomogeneous (a + e.data.parity i + d.data.parity j) (toHomMatrix d e f i j) := by
  have hg := C.laws.comp_grade _ _ (d.laws.inclusion_grade j)
    (C.laws.comp_grade _ _ hf (e.laws.projection_grade i))
  rw [add_comm (d.data.parity j)] at hg
  exact hg

theorem fromHomMatrix_grade {a : ZMod 2} {f : Matrix (Fin m) (Fin n) (End S)}
    (hf : ∀ i j, C.data.IsHomogeneous (a + e.data.parity i + d.data.parity j) (f i j)) :
    C.data.IsHomogeneous a (fromHomMatrix d e f) := by
  change fromHomMatrix d e f ∈ LinearCategory.grade C X Y a
  apply Submodule.sum_mem
  intro j _
  apply Submodule.sum_mem
  intro i _
  have hg := C.laws.comp_grade _ _ (d.laws.projection_grade j)
    (C.laws.comp_grade _ _ (hf i j) (e.laws.inclusion_grade i))
  have hp : d.data.parity j + ((a + e.data.parity i + d.data.parity j) + e.data.parity i) = a := by
    calc
      _ = a + (e.data.parity i + e.data.parity i) + (d.data.parity j + d.data.parity j) := by abel
      _ = a := by simp only [CharTwo.add_self_eq_zero, add_zero]
  rw [hp] at hg
  exact hg

end RMod.Classification.HomogeneousSum
