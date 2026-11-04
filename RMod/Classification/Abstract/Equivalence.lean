import RMod.Classification.Abstract.Pi
import Mathlib.Combinatorics.Quiver.Prefunctor

/-!
# Real monoidal superequivalences of structured triples

Functor maps, inverse functor maps, tensorators, unit comparisons and both
directions of the unit/counit are executable data. Naturality includes odd
morphisms. In particular no strict equality of the chosen parity objects
is imposed. The forced parity comparison is derived from `ζ` and the unit
map, rather than supplied as an additional classification parameter.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

/-- The existing raw Hom operation supplies Mathlib's quiver interface. -/
instance dataQuiver (C : WeaklyPointedSuperfusionData.{u₁, v₁}) : Quiver C.Obj :=
  ⟨C.Hom⟩

variable (A : WeaklyPointedSuperfusionData.{u₁, v₁})
  (B : WeaklyPointedSuperfusionData.{u₂, v₂})

/-- Mathlib's object/map data on the underlying Hom quivers. The functor,
linear and grading laws are imposed separately below. -/
abbrev SuperfunctorData :=
  Prefunctor A.Obj B.Obj

structure SuperfunctorLaws (F : SuperfunctorData A B) : Prop where
  map_id : ∀ X, F.map (A.id X) = B.id (F.obj X)
  map_comp : ∀ {X Y Z} (f : A.Hom X Y) (g : A.Hom Y Z),
    F.map (A.comp f g) = B.comp (F.map f) (F.map g)
  map_zero : ∀ X Y, F.map (A.zero : A.Hom X Y) = B.zero
  map_add : ∀ {X Y} (f g : A.Hom X Y),
    F.map (A.add f g) = B.add (F.map f) (F.map g)
  map_smul : ∀ {X Y} (r : ℝ) (f : A.Hom X Y),
    F.map (A.smul r f) = B.smul r (F.map f)
  map_grade : ∀ {X Y a} (f : A.Hom X Y),
    A.IsHomogeneous a f → B.IsHomogeneous a (F.map f)

/-- A superfunctor between categories whose own laws are already supplied. -/
structure Superfunctor (C : WeaklyPointedSuperfusion.{u₁, v₁})
    (D : WeaklyPointedSuperfusion.{u₂, v₂}) where
  data : SuperfunctorData C.data D.data
  laws : SuperfunctorLaws C.data D.data data

/-! Strong monoidality uses the direction `FX ⊗ FY → F(X ⊗ Y)`. -/

structure MonoidalSuperfunctorData extends SuperfunctorData A B where
  tensorHom : (X Y : A.Obj) → B.Hom (B.tensorObj (obj X) (obj Y))
    (obj (A.tensorObj X Y))
  tensorInv : (X Y : A.Obj) → B.Hom (obj (A.tensorObj X Y))
    (B.tensorObj (obj X) (obj Y))
  unitHom : B.Hom B.tensorUnit (obj A.tensorUnit)
  unitInv : B.Hom (obj A.tensorUnit) B.tensorUnit

structure MonoidalSuperfunctorLaws (F : MonoidalSuperfunctorData A B) : Prop
    extends SuperfunctorLaws A B F.toPrefunctor where
  tensor_hom_even : ∀ X Y, B.IsHomogeneous 0 (F.tensorHom X Y)
  tensor_inv_even : ∀ X Y, B.IsHomogeneous 0 (F.tensorInv X Y)
  tensor_hom_inv : ∀ X Y,
    B.comp (F.tensorHom X Y) (F.tensorInv X Y) = B.id (B.tensorObj (F.obj X) (F.obj Y))
  tensor_inv_hom : ∀ X Y,
    B.comp (F.tensorInv X Y) (F.tensorHom X Y) = B.id (F.obj (A.tensorObj X Y))
  unit_hom_even : B.IsHomogeneous 0 F.unitHom
  unit_inv_even : B.IsHomogeneous 0 F.unitInv
  unit_hom_inv : B.comp F.unitHom F.unitInv = B.id B.tensorUnit
  unit_inv_hom : B.comp F.unitInv F.unitHom = B.id (F.obj A.tensorUnit)
  tensor_naturality : ∀ {X X' Y Y'} (f : A.Hom X X') (g : A.Hom Y Y'),
    B.comp (B.tensorHom (F.map f) (F.map g)) (F.tensorHom X' Y') =
      B.comp (F.tensorHom X Y) (F.map (A.tensorHom f g))
  associativity : ∀ X Y Z,
    B.comp (B.comp (B.tensorHom (F.tensorHom X Y) (B.id (F.obj Z)))
      (F.tensorHom (A.tensorObj X Y) Z)) (F.map (A.associatorHom X Y Z)) =
    B.comp (B.comp (B.associatorHom (F.obj X) (F.obj Y) (F.obj Z))
      (B.tensorHom (B.id (F.obj X)) (F.tensorHom Y Z)))
      (F.tensorHom X (A.tensorObj Y Z))
  left_unit : ∀ X,
    B.comp (B.comp (B.tensorHom F.unitHom (B.id (F.obj X)))
      (F.tensorHom A.tensorUnit X)) (F.map (A.leftUnitorHom X)) =
      B.leftUnitorHom (F.obj X)
  right_unit : ∀ X,
    B.comp (B.comp (B.tensorHom (B.id (F.obj X)) F.unitHom)
      (F.tensorHom X A.tensorUnit)) (F.map (A.rightUnitorHom X)) =
      B.rightUnitorHom (F.obj X)

structure MonoidalSuperfunctor (C : WeaklyPointedSuperfusion.{u₁, v₁})
    (D : WeaklyPointedSuperfusion.{u₂, v₂}) where
  data : MonoidalSuperfunctorData C.data D.data
  laws : MonoidalSuperfunctorLaws C.data D.data data

/-! An actual inverse functor and even unit/counit witness equivalence. -/

structure MonoidalSuperequivalenceData where
  forward : MonoidalSuperfunctorData A B
  backward : SuperfunctorData B A
  unitHom : (X : A.Obj) → A.Hom X (backward.obj (forward.obj X))
  unitInv : (X : A.Obj) → A.Hom (backward.obj (forward.obj X)) X
  counitHom : (Y : B.Obj) → B.Hom (forward.obj (backward.obj Y)) Y
  counitInv : (Y : B.Obj) → B.Hom Y (forward.obj (backward.obj Y))

structure MonoidalSuperequivalenceLaws (F : MonoidalSuperequivalenceData A B) : Prop where
  forward : MonoidalSuperfunctorLaws A B F.forward
  backward : SuperfunctorLaws B A F.backward
  unit_hom_even : ∀ X, A.IsHomogeneous 0 (F.unitHom X)
  unit_inv_even : ∀ X, A.IsHomogeneous 0 (F.unitInv X)
  unit_hom_inv : ∀ X, A.comp (F.unitHom X) (F.unitInv X) = A.id X
  unit_inv_hom : ∀ X,
    A.comp (F.unitInv X) (F.unitHom X) = A.id (F.backward.obj (F.forward.obj X))
  counit_hom_even : ∀ Y, B.IsHomogeneous 0 (F.counitHom Y)
  counit_inv_even : ∀ Y, B.IsHomogeneous 0 (F.counitInv Y)
  counit_hom_inv : ∀ Y,
    B.comp (F.counitHom Y) (F.counitInv Y) = B.id (F.forward.obj (F.backward.obj Y))
  counit_inv_hom : ∀ Y, B.comp (F.counitInv Y) (F.counitHom Y) = B.id Y
  unit_naturality : ∀ {X Y} (f : A.Hom X Y),
    A.comp f (F.unitHom Y) = A.comp (F.unitHom X) (F.backward.map (F.forward.map f))
  counit_naturality : ∀ {X Y} (f : B.Hom X Y),
    B.comp (F.forward.map (F.backward.map f)) (F.counitHom Y) =
      B.comp (F.counitHom X) f

structure MonoidalSuperequivalence (C : WeaklyPointedSuperfusion.{u₁, v₁})
    (D : WeaklyPointedSuperfusion.{u₂, v₂}) where
  data : MonoidalSuperequivalenceData C.data D.data
  laws : MonoidalSuperequivalenceLaws C.data D.data data

/-- Equivalence of triples permits the canonical even comparison of parity
objects; it does not require equality of objects. -/
def Equivalent (C : PiSuperfusion.{u₁, v₁})
    (D : PiSuperfusion.{u₂, v₂}) : Prop :=
  Nonempty (MonoidalSuperequivalence C.toWeaklyPointedSuperfusion
    D.toWeaklyPointedSuperfusion)

end RMod.Classification
