import RMod.Statement.Surface
import RMod.Hierarchy.Abstract.Superfunctor

/-!
# Changes of presentation for the enriched operations

The bundled Mathlib enrichment and the previous separated enrichment carry
identical objects, Hom spaces, identities, and compositions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.StatementLegacy.StatementBridge

abbrev fromSuper (C : Legacy.Supercategory) : Supercategory :=
  letI : EnrichedCategory SuperVec C.data.Obj :=
    { Hom := C.data.Hom, id := C.data.id, comp := C.data.comp,
      id_comp := C.laws.id_comp, comp_id := C.laws.comp_id, assoc := C.laws.assoc }
  EnrichedCat.of SuperVec C.data.Obj

abbrev toFunctor {C D : Supercategory} (F : Superfunctor C D) :
    Legacy.Superfunctor (toLegacySupercategory C) (toLegacySupercategory D) where
  data := { obj := F.obj, map := F.map }
  laws := { map_id := F.map_id, map_comp := F.map_comp }

abbrev fromFunctor {C D : Legacy.Supercategory} (F : Legacy.Superfunctor C D) :
    Superfunctor (fromSuper C) (fromSuper D) := F.enriched

/-- Transport of identities along equality of objects. -/
theorem id_transport {C : Supercategory} {X Y : C} (h : X = Y) :
    eId SuperVec X ≫ eqToHom (congrArg (fun Z => SHom C Z Z) h) = eId SuperVec Y := by
  subst Y
  simp

/-- Transport of composition along three object equalities. -/
theorem comp_transport {C : Supercategory} {X Y Z X' Y' Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (eqToHom (congrArg₂ (SHom C) hX hY) ⊗ₘ eqToHom (congrArg₂ (SHom C) hY hZ)) ≫
      eComp SuperVec X' Y' Z' =
    eComp SuperVec X Y Z ≫ eqToHom (congrArg₂ (SHom C) hX hZ) := by
  subst X'
  subst Y'
  subst Z'
  simp

/-- Change only the object presentation of an enriched functor. -/
def changeObj {C D : Supercategory} (F : Superfunctor C D) (obj : C → D)
    (h : ∀ X, F.obj X = obj X) : Superfunctor C D where
  obj := obj
  map X Y := F.map X Y ≫ eqToHom (congrArg₂ (SHom D) (h X) (h Y))
  map_id X := by
    rw [← Category.assoc, F.map_id]
    exact id_transport (h X)
  map_comp X Y Z := by
    rw [← Category.assoc, F.map_comp, Category.assoc,
      ← tensorHom_comp_tensorHom, Category.assoc, comp_transport (h X) (h Y) (h Z)]

/-- The former support predicate equals Mathlib's pointwise submodule. -/
theorem grade_mem_iff (C : Supercategory) (X Y : C) (a : ZMod 2) (f : THom C X Y) :
    f ∈ grade C X Y a ↔ ∀ b, b ≠ a → f b = 0 := by
  change (∀ b, b ≠ a → f b = 0) ↔ _
  rfl

end RMod.StatementLegacy.StatementBridge
