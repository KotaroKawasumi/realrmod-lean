import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Data underlying a weakly pointed superfusion category

This module is the dependency boundary of the public interface. It imports
only Mathlib and contains the operations needed for computation. Derived
propositions are defined in `WeaklyPointedSuperfusionPredicates`; algebraic,
graded, monoidal, finiteness, rigidity, and weak-pointedness assertions are
stated separately as laws.
-/

set_option autoImplicit false

universe u v

namespace RMod

/-! ## Computational data -/

/-- Operations underlying a real weakly pointed superfusion category.

The carrier of each homogeneous component is stored as data. Structural
isomorphisms are represented by their two executable directions; inverse and
coherence properties belong to `WeaklyPointedSuperfusionLaws`. -/
structure WeaklyPointedSuperfusionData where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Identity morphisms. -/
  id : (X : Obj) → Hom X X
  /-- Composition in diagrammatic order. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Zero morphisms. -/
  zero : {X Y : Obj} → Hom X Y
  /-- Addition of morphisms. -/
  add : {X Y : Obj} → Hom X Y → Hom X Y → Hom X Y
  /-- Additive inverse. -/
  neg : {X Y : Obj} → Hom X Y → Hom X Y
  /-- Real scalar multiplication. -/
  smul : {X Y : Obj} → ℝ → Hom X Y → Hom X Y
  /-- Carrier of the homogeneous morphisms of each parity. -/
  grade : (X Y : Obj) → ZMod 2 → Set (Hom X Y)
  /-- Tensor product on objects. -/
  tensorObj : Obj → Obj → Obj
  /-- Tensor product on morphisms. -/
  tensorHom : {X₁ Y₁ X₂ Y₂ : Obj} →
    Hom X₁ Y₁ → Hom X₂ Y₂ → Hom (tensorObj X₁ X₂) (tensorObj Y₁ Y₂)
  /-- Tensor unit. -/
  tensorUnit : Obj
  /-- Forward associator. -/
  associatorHom : (X Y Z : Obj) →
    Hom (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
  /-- Backward associator. -/
  associatorInv : (X Y Z : Obj) →
    Hom (tensorObj X (tensorObj Y Z)) (tensorObj (tensorObj X Y) Z)
  /-- Forward left unitor. -/
  leftUnitorHom : (X : Obj) → Hom (tensorObj tensorUnit X) X
  /-- Backward left unitor. -/
  leftUnitorInv : (X : Obj) → Hom X (tensorObj tensorUnit X)
  /-- Forward right unitor. -/
  rightUnitorHom : (X : Obj) → Hom (tensorObj X tensorUnit) X
  /-- Backward right unitor. -/
  rightUnitorInv : (X : Obj) → Hom X (tensorObj X tensorUnit)

namespace WeaklyPointedSuperfusionData

variable (D : WeaklyPointedSuperfusionData.{u, v})

/-! ## Derived computational operations -/

/-- Left whiskering derived from tensoring with an identity. -/
def whiskerLeft (X : D.Obj) {Y Z : D.Obj} (f : D.Hom Y Z) :
    D.Hom (D.tensorObj X Y) (D.tensorObj X Z) :=
  D.tensorHom (D.id X) f

/-- Right whiskering derived from tensoring with an identity. -/
def whiskerRight {X Y : D.Obj} (f : D.Hom X Y) (Z : D.Obj) :
    D.Hom (D.tensorObj X Z) (D.tensorObj Y Z) :=
  D.tensorHom f (D.id Z)

/-- A fixed-order finite sum using the stored zero and addition. -/
def finSum {X Y : D.Obj} :
    (n : ℕ) → (Fin n → D.Hom X Y) → D.Hom X Y
  | 0, _ => D.zero
  | n + 1, f =>
      D.add (finSum n (fun i => f i.castSucc)) (f (Fin.last n))

/-- Parity of an even or odd multiplicity coordinate. -/
def superIndexParity {p q : ℕ} : Fin p ⊕ Fin q → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Fixed-order sum over even and odd multiplicity coordinates. -/
def superFinSum {X Y : D.Obj} {p q : ℕ}
    (f : Fin p ⊕ Fin q → D.Hom X Y) : D.Hom X Y :=
  D.add (D.finSum p (fun i => f (Sum.inl i)))
    (D.finSum q (fun i => f (Sum.inr i)))

end WeaklyPointedSuperfusionData

end RMod
