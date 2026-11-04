import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Data.ZMod.Basic
import Superfusion.Conventions

/-!
# Supercategories

A supercategory is modelled on top of a Mathlib linear category whose Hom
modules contain all morphisms.  Each Hom module is equipped with an internal
direct-sum decomposition indexed by ZMod 2, identities are even, and
composition adds parity.
-/

universe v v₂ u u₂

open CategoryTheory

namespace Superfusion.Category

/-- A K-linear category enriched in Z/2-graded vector spaces. -/
class Supercategory (K : Type*) [Field K] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear K C] where
  /-- The parity-a homogeneous part of the Hom module from X to Y. -/
  grade : ∀ X Y : C, ZMod 2 → Submodule K (X ⟶ Y)
  /-- The two homogeneous parts internally span each Hom module. -/
  isInternal_grade : ∀ X Y : C, DirectSum.IsInternal (grade X Y)
  /-- Identity morphisms are even. -/
  id_mem_even : ∀ X : C, 𝟙 X ∈ grade X X 0
  /-- Composition adds the parities of homogeneous morphisms. -/
  comp_mem : ∀ {X Y Z : C} {a b : ZMod 2} (f : X ⟶ Y) (g : Y ⟶ Z),
    f ∈ grade X Y a → g ∈ grade Y Z b → f ≫ g ∈ grade X Z (a + b)

variable (K : Type*) [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C]

/-- The parity-a part of the Hom module from X to Y. -/
def homGrade (X Y : C) (a : ZMod 2) : Submodule K (X ⟶ Y) :=
  Supercategory.grade X Y a

/-- A homogeneous morphism of parity zero. -/
def IsEven {X Y : C} (f : X ⟶ Y) : Prop :=
  f ∈ homGrade K X Y 0

/-- A homogeneous morphism of parity one. -/
def IsOdd {X Y : C} (f : X ⟶ Y) : Prop :=
  f ∈ homGrade K X Y 1

/-- A morphism is homogeneous when it belongs to one of the two graded
summands of its Hom superspace. -/
def IsHomogeneous {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ a : ZMod 2, f ∈ homGrade K X Y a

/-- The scalar introduced when homogeneous morphisms of parities `a` and `b`
cross. -/
def koszulSign (a b : ZMod 2) : K :=
  (-1 : K) ^ (a * b).val

/-- The field-valued Koszul sign agrees with the project's generic integer
sign acting by repeated addition. -/
theorem koszulSign_smul_eq_sgn_zsmul
    (a b : ZMod 2) {M : Type*} [AddCommGroup M] [Module K M] (x : M) :
    koszulSign K a b • x = ((sgn (a * b) : ℤˣ) : ℤ) • x := by
  rw [← Int.cast_smul_eq_zsmul K]
  congr 1
  rcases zmod2_cases a with ha | ha <;>
    rcases zmod2_cases b with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [koszulSign, sgn, ZMod.val_one]

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear K D]
  [Supercategory K D]

/-- An even linear functor between supercategories. -/
structure Superfunctor extends C ⥤ D where
  map_add : ∀ {X Y : C} (f g : X ⟶ Y), map (f + g) = map f + map g
  map_smul : ∀ {X Y : C} (c : K) (f : X ⟶ Y), map (c • f) = c • map f
  map_mem : ∀ {X Y : C} (a : ZMod 2) (f : X ⟶ Y),
    f ∈ homGrade K X Y a → map f ∈ homGrade K (obj X) (obj Y) a

instance (F : Superfunctor K (C := C) (D := D)) : F.toFunctor.Additive where
  map_add {X Y f g} := F.map_add (X := X) (Y := Y) f g

instance (F : Superfunctor K (C := C) (D := D)) : F.toFunctor.Linear K where
  map_smul {X Y} f c := F.map_smul (X := X) (Y := Y) c f

/-- The inverse of a homogeneous isomorphism has the same degree. -/
theorem inv_mem_homGrade_of_hom_mem
    {X Y : C} (e : X ≅ Y) (d : ZMod 2)
    (h : e.hom ∈ homGrade K X Y d) :
    e.inv ∈ homGrade K Y X d := by
  classical
  have huniv : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext i
    rcases zmod2_cases i with hi | hi <;> subst i <;> simp
  have hcomplYX :
      IsCompl (homGrade K Y X 0) (homGrade K Y X 1) :=
    DirectSum.IsInternal.isCompl zero_ne_one huniv
      (Supercategory.isInternal_grade Y X)
  have hcomplXX :
      IsCompl (homGrade K X X 0) (homGrade K X X 1) :=
    DirectSum.IsInternal.isCompl zero_ne_one huniv
      (Supercategory.isInternal_grade X X)
  obtain ⟨g₀, g₁, hg₀, hg₁, hdecomp⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hcomplYX.codisjoint e.inv
  have heq : e.hom ≫ g₀ + e.hom ≫ g₁ = 𝟙 X := by
    rw [← Preadditive.comp_add, hdecomp, e.hom_inv_id]
  rcases zmod2_cases d with hd | hd
  · subst d
    have hcomp₀ : e.hom ≫ g₀ ∈ homGrade K X X 0 := by
      simpa only [homGrade, zero_add] using
        Supercategory.comp_mem e.hom g₀ h hg₀
    have hcomp₁ : e.hom ≫ g₁ ∈ homGrade K X X 1 := by
      simpa only [homGrade, zero_add] using
        Supercategory.comp_mem e.hom g₁ h hg₁
    have hcomp₁_even : e.hom ≫ g₁ ∈ homGrade K X X 0 := by
      rw [show e.hom ≫ g₁ = 𝟙 X - e.hom ≫ g₀ by
        rw [eq_sub_iff_add_eq, add_comm]
        exact heq]
      exact Submodule.sub_mem _ (Supercategory.id_mem_even X) hcomp₀
    have hcomp₁_zero : e.hom ≫ g₁ = 0 := by
      have hboth :
          e.hom ≫ g₁ ∈
            homGrade K X X 0 ⊓ homGrade K X X 1 :=
        ⟨hcomp₁_even, hcomp₁⟩
      rw [hcomplXX.disjoint.eq_bot, Submodule.mem_bot] at hboth
      exact hboth
    have hg₁_zero : g₁ = 0 := by
      apply (cancel_epi e.hom).1
      simpa only [CategoryTheory.Limits.comp_zero] using hcomp₁_zero
    rw [← hdecomp, hg₁_zero, add_zero]
    exact hg₀
  · subst d
    have hcomp₀ : e.hom ≫ g₀ ∈ homGrade K X X 1 := by
      simpa only [homGrade, add_zero] using
        Supercategory.comp_mem e.hom g₀ h hg₀
    have hcomp₁ : e.hom ≫ g₁ ∈ homGrade K X X 0 := by
      simpa only [homGrade, show (1 : ZMod 2) + 1 = 0 by decide] using
        Supercategory.comp_mem e.hom g₁ h hg₁
    have hcomp₀_even : e.hom ≫ g₀ ∈ homGrade K X X 0 := by
      rw [show e.hom ≫ g₀ = 𝟙 X - e.hom ≫ g₁ by
        rw [eq_sub_iff_add_eq]
        exact heq]
      exact Submodule.sub_mem _ (Supercategory.id_mem_even X) hcomp₁
    have hcomp₀_zero : e.hom ≫ g₀ = 0 := by
      have hboth :
          e.hom ≫ g₀ ∈
            homGrade K X X 0 ⊓ homGrade K X X 1 :=
        ⟨hcomp₀_even, hcomp₀⟩
      rw [hcomplXX.disjoint.eq_bot, Submodule.mem_bot] at hboth
      exact hboth
    have hg₀_zero : g₀ = 0 := by
      apply (cancel_epi e.hom).1
      simpa only [CategoryTheory.Limits.comp_zero] using hcomp₀_zero
    rw [← hdecomp, hg₀_zero, zero_add]
    exact hg₁

/-- An isomorphism whose forward and inverse maps are homogeneous of the
specified parity.  In `ZMod 2` the inverse has the same parity. -/
structure HomogeneousIso (a : ZMod 2) (X Y : C) where
  iso : X ≅ Y
  hom_mem : iso.hom ∈ homGrade K X Y a
  inv_mem : iso.inv ∈ homGrade K Y X a

/-- An isomorphism with even forward and inverse maps. -/
abbrev EvenIso (X Y : C) := HomogeneousIso K 0 X Y

/-- An isomorphism with odd forward and inverse maps. -/
abbrev OddIso (X Y : C) := HomogeneousIso K 1 X Y

end Superfusion.Category
