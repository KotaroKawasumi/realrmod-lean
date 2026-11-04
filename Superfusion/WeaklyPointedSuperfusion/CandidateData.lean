import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Raw data for a weakly pointed superfusion category

This module deliberately contains data only.  In particular, it does not
import any of the project's category-theory hierarchy, and none of the
fields below is a category, monoidal, linear, or isomorphism structure.

The scalar field is fixed to `ℝ`, matching the concrete real regular-module
example.  All algebraic, graded, monoidal, finiteness, rigidity, and
weak-pointedness assertions belong to `CandidateLaws`.
-/

set_option autoImplicit false

universe u v

namespace Superfusion

/-- Raw operations underlying a real weakly pointed superfusion category.

`grade X Y a` is only the chosen carrier set of degree-`a` morphisms.  Its
linear-subspace properties and the direct-sum condition are laws.  Likewise,
the two directions of each structural isomorphism are stored independently;
being inverse and satisfying coherence are laws. -/
structure CandidateData where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Raw identity morphisms. -/
  id : (X : Obj) → Hom X X
  /-- Raw composition, in diagrammatic order. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Raw zero morphisms. -/
  zero : {X Y : Obj} → Hom X Y
  /-- Raw addition of morphisms. -/
  add : {X Y : Obj} → Hom X Y → Hom X Y → Hom X Y
  /-- Raw additive inverse of a morphism. -/
  neg : {X Y : Obj} → Hom X Y → Hom X Y
  /-- Raw real scalar multiplication. -/
  smul : {X Y : Obj} → ℝ → Hom X Y → Hom X Y
  /-- Chosen carrier of homogeneous morphisms of each parity. -/
  grade : (X Y : Obj) → ZMod 2 → Set (Hom X Y)
  /-- Tensor product on objects. -/
  tensorObj : Obj → Obj → Obj
  /-- Tensor product on morphisms. -/
  tensorHom : {X₁ Y₁ X₂ Y₂ : Obj} →
    Hom X₁ Y₁ → Hom X₂ Y₂ → Hom (tensorObj X₁ X₂) (tensorObj Y₁ Y₂)
  /-- Tensor unit. -/
  tensorUnit : Obj
  /-- Forward associator morphism. -/
  associatorHom : (X Y Z : Obj) →
    Hom (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
  /-- Backward associator morphism. -/
  associatorInv : (X Y Z : Obj) →
    Hom (tensorObj X (tensorObj Y Z)) (tensorObj (tensorObj X Y) Z)
  /-- Forward left-unitor morphism. -/
  leftUnitorHom : (X : Obj) → Hom (tensorObj tensorUnit X) X
  /-- Backward left-unitor morphism. -/
  leftUnitorInv : (X : Obj) → Hom X (tensorObj tensorUnit X)
  /-- Forward right-unitor morphism. -/
  rightUnitorHom : (X : Obj) → Hom (tensorObj X tensorUnit) X
  /-- Backward right-unitor morphism. -/
  rightUnitorInv : (X : Obj) → Hom X (tensorObj X tensorUnit)

end Superfusion
