import RMod.Classification.Instances.HomogeneousMatrix

/-!
# Rectangular Hom matrices between homogeneous sums

Two sums of shifts of the same generator have an actual linear Hom
equivalence with rectangular matrices over its endomorphism algebra.
Inclusions and projections give both directions. These coordinates will
transport all morphisms in a component, not just endomorphisms of simples.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory CategoryTheory.Preadditive

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C : WeaklyPointedSuperfusion.{0, 0}} {S X Y : LinearCategory C} {n m : ℕ}
  (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data S Y m)

def toHomMatrix (f : X ⟶ Y) : Matrix (Fin m) (Fin n) (End S) :=
  fun i j => d.data.inclusion j ≫ f ≫ e.data.projection i

def fromHomMatrix (a : Matrix (Fin m) (Fin n) (End S)) : X ⟶ Y :=
  ∑ j, ∑ i, d.data.projection j ≫ a i j ≫ e.data.inclusion i

theorem toHomMatrix_fromHomMatrix (a : Matrix (Fin m) (Fin n) (End S)) :
    toHomMatrix d e (fromHomMatrix d e a) = a := by
  ext i j
  change d.data.inclusion j ≫
    (∑ k, ∑ l, d.data.projection k ≫ a l k ≫ e.data.inclusion l : X ⟶ Y) ≫
      e.data.projection i = a i j
  simp only [comp_sum, sum_comp]
  have hterm (k l) :
      d.data.inclusion j ≫ (d.data.projection k ≫ a l k ≫ e.data.inclusion l) ≫
          e.data.projection i =
        (d.data.inclusion j ≫ d.data.projection k) ≫ a l k ≫
          (e.data.inclusion l ≫ e.data.projection i) := by simp only [Category.assoc]
  conv_lhs =>
    arg 2
    ext k
    arg 2
    ext l
    rw [hterm k l, inclusion_projection, inclusion_projection]
  simp [ite_comp, comp_ite]

theorem fromHomMatrix_toHomMatrix (f : X ⟶ Y) :
    fromHomMatrix d e (toHomMatrix d e f) = f := by
  have hterm (j i) :
      d.data.projection j ≫ (d.data.inclusion j ≫ f ≫ e.data.projection i) ≫
          e.data.inclusion i =
        (d.data.projection j ≫ d.data.inclusion j) ≫ f ≫
          (e.data.projection i ≫ e.data.inclusion i) := by simp only [Category.assoc]
  change (∑ j, ∑ i, d.data.projection j ≫
    (d.data.inclusion j ≫ f ≫ e.data.projection i) ≫ e.data.inclusion i : X ⟶ Y) = f
  simp only [hterm]
  simp only [← comp_sum (C := LinearCategory C), total, Category.comp_id]
  rw [← sum_comp (C := LinearCategory C), total, Category.id_comp]

def homMatrixLinearEquiv : (X ⟶ Y) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) (End S) where
  toFun := toHomMatrix d e
  invFun := fromHomMatrix d e
  left_inv := fromHomMatrix_toHomMatrix d e
  right_inv := toHomMatrix_fromHomMatrix d e
  map_add' f g := by
    ext i j
    change C.data.comp (d.data.inclusion j) (C.data.comp (C.data.add f g)
      (e.data.projection i)) = C.data.add _ _
    rw [C.laws.add_comp, C.laws.comp_add]
    rfl
  map_smul' r f := by
    ext i j
    change C.data.comp (d.data.inclusion j) (C.data.comp (C.data.smul r f)
      (e.data.projection i)) = C.data.smul r _
    rw [C.laws.smul_comp, C.laws.comp_smul]
    rfl

end RMod.Classification.HomogeneousSum
