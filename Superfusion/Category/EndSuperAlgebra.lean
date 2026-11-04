import Superfusion.Category.Supercategory
import Superfusion.Super.DivisionTower

/-!
# Endomorphism superalgebras of supercategory objects

The endomorphisms of an object in a `K`-linear supercategory form a
`K`-algebra with Mathlib's categorical multiplication convention.  The Hom
grading is multiplicative and internally exhaustive, so it bundles as a
`SuperAlgebra K`.

This construction is independent of monoidal structure and is the intrinsic
endomorphism-superalgebra object used by the group-labelled weak-pointed API.
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Superfusion.Category

variable {K : Type*} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C]

/-- The Hom grading on the categorical endomorphism algebra of `X`. -/
def endGrading (X : C) :
    ZMod 2 → Submodule K (CategoryTheory.End X) :=
  fun i ↦ homGrade K X X i

instance endGradingGradedMonoid (X : C) :
    SetLike.GradedMonoid (endGrading (K := K) X) where
  one_mem := Supercategory.id_mem_even X
  mul_mem := by
    intro i j f g hf hg
    change g ≫ f ∈ homGrade K X X (i + j)
    simpa only [homGrade, add_comm] using
      Supercategory.comp_mem g f hg hf

/-- The categorical endomorphism algebra, with its intrinsic Hom grading. -/
noncomputable instance endGradingGradedAlgebra (X : C) :
    GradedAlgebra (endGrading (K := K) X) :=
  (Supercategory.isInternal_grade X X).gradedAlgebra

/-- Bundle the categorical endomorphism algebra of `X` as a superalgebra. -/
noncomputable def endSuperAlgebra (X : C) : SuperAlgebra K where
  carrier := CategoryTheory.End X
  grading := endGrading (K := K) X

@[simp]
theorem endSuperAlgebra_grading (X : C) (i : ZMod 2) :
    (endSuperAlgebra (K := K) X).grading i = homGrade K X X i :=
  rfl

end Superfusion.Category
