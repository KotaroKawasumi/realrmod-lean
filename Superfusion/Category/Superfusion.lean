import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Superfusion.Category.Even

/-!
# Superfusion categories

This file gives a parity-aware interface for a superfusion category.  Ordinary
categorical simplicity and finite biproduct decompositions live in the even
subcategory.  The full Hom spaces retain their odd parts, so Schur's lemma and
the finiteness condition on simple objects are stated using homogeneous
morphisms and homogeneous isomorphisms.

The monoidal unit is required to be absolutely simple: scalar multiples of
its identity exhaust its *total* endomorphism space.  In particular, this
rules out an odd endomorphism of the unit.
-/

universe v u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Superfusion.Category

variable (K : Type*) [Field K]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C]

/-- A supercategory is semisimple when every object is an even finite
biproduct of super-simple objects.  The second field is the graded Schur
property: a nonzero homogeneous map between super-simple objects is an
isomorphism in the ambient category.

Finite biproducts are deliberately assumed in `EvenSubcategory K C`, rather
than merely in `C`, so that all inclusions and projections are even. -/
class SuperSemisimple [HasFiniteBiproducts (EvenSubcategory K C)] : Prop where
  /-- Every object admits an even finite-biproduct decomposition into
  super-simple objects. -/
  exists_simple_decomposition (X : C) :
    ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, IsSuperSimple K C (S i)) ∧
        Nonempty (evenObj K C X ≅ ⨁ fun i => evenObj K C (S i))
  /-- Graded Schur property for homogeneous maps. -/
  isIso_of_homogeneous_of_ne_zero {X Y : C}
      (hX : IsSuperSimple K C X) (hY : IsSuperSimple K C Y)
      {a : ZMod 2} (f : X ⟶ Y)
      (hf : f ∈ homGrade K X Y a) (h0 : f ≠ 0) :
    IsIso f

variable [MonoidalCategoryStruct C]

/-- The canonical linear map from scalars to endomorphisms of the monoidal
unit. -/
def unitEndLinearMap : K →ₗ[K] (𝟙_ C ⟶ 𝟙_ C) where
  toFun r := r • 𝟙 (𝟙_ C)
  map_add' r s := add_smul r s (𝟙 (𝟙_ C))
  map_smul' r s := mul_smul r s (𝟙 (𝟙_ C))

omit [Supercategory K C] in
@[simp] lemma unitEndLinearMap_apply (r : K) :
    unitEndLinearMap K C r = r • 𝟙 (𝟙_ C) := rfl

/-- A parity-aware superfusion category over `K`.

Semisimplicity is imposed in the even subcategory.  The list of simple
representatives is taken modulo homogeneous isomorphism, hence modulo parity
shift whenever an odd isomorphism exists. -/
class SuperfusionCategory
    [MonoidalSupercategory K C]
    [HasFiniteBiproducts (EvenSubcategory K C)] : Prop where
  /-- The even semisimplicity and graded Schur axioms. -/
  semisimple : SuperSemisimple K C
  /-- Every full Hom superspace is finite-dimensional. -/
  finiteDimensional_hom (X Y : C) : FiniteDimensional K (X ⟶ Y)
  /-- There are finitely many super-simple objects up to homogeneous
  isomorphism. -/
  finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, IsSuperSimple K C (S i)) ∧
        ∀ X : C, IsSuperSimple K C X →
          ∃ (i : Fin n) (a : ZMod 2), Nonempty (HomogeneousIso K a X (S i))
  /-- The monoidal unit is super-simple. -/
  simple_unit : IsSuperSimple K C (𝟙_ C)
  /-- Every endomorphism of the monoidal unit is a unique scalar multiple of
  its identity.  The codomain is the total Hom space, so this also excludes
  odd unit endomorphisms. -/
  unitEndLinearMap_bijective : Function.Bijective (unitEndLinearMap K C)
  /-- Every object has an even right-duality pairing. -/
  hasSuperRightDual (X : C) : HasSuperRightDual K X
  /-- Every object has an even left-duality pairing. -/
  hasSuperLeftDual (X : C) : HasSuperLeftDual K X

instance [MonoidalSupercategory K C]
    [HasFiniteBiproducts (EvenSubcategory K C)]
    [SuperfusionCategory K C] : SuperSemisimple K C :=
  SuperfusionCategory.semisimple (K := K) (C := C)

instance [MonoidalSupercategory K C]
    [HasFiniteBiproducts (EvenSubcategory K C)]
    [SuperfusionCategory K C] (X Y : C) : FiniteDimensional K (X ⟶ Y) :=
  SuperfusionCategory.finiteDimensional_hom (K := K) (C := C) X Y

/-- In a superfusion category, scalar multiplication identifies `K` with the
full endomorphism space of the monoidal unit. -/
noncomputable def unitEndLinearEquiv
    [MonoidalSupercategory K C]
    [HasFiniteBiproducts (EvenSubcategory K C)] [SuperfusionCategory K C] :
    K ≃ₗ[K] (𝟙_ C ⟶ 𝟙_ C) :=
  LinearEquiv.ofBijective (unitEndLinearMap K C)
    (SuperfusionCategory.unitEndLinearMap_bijective (K := K) (C := C))

end Superfusion.Category
