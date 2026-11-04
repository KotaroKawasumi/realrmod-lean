import RMod.BrundanEllis.Surface
import RMod.Enriched.FromStatement
import RMod.Enriched.ToStatement
import RMod.Enriched.FromEquivalence

/-! Compatibility with the established Mathlib-based enriched implementation.
The public structures are specialized to super vector spaces. The adapter reuses
Mathlib enriched functors, ordinary natural isomorphisms and CoreMonoidal data.
No extra coherence hypotheses are required in either direction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Bridge

/-- Rebundle the same carrier, Hom objects and enriched composition. -/
@[implicit_reducible] def bundled (C : Type) [SuperCategory C] :
    RMod.StatementLegacy.Supercategory := EnrichedCat.of SuperVec C

/-- All-degree coherence is exactly the established specialized super interface. -/
def toStatementMonoidal (C : Type) [SuperCategory C]
    [mc : MonoidalCategory (Even C)] [M : MonoidalSuperCategory C] :
    RMod.StatementLegacy.MonoidalSupercategory where
  toSupercategory := bundled C
  monoidalStructure := {
    even := mc
    tensor := M.tensor
    tensor_objects := M.tensor_objects
    tensor_even := M.tensor_even
    associator_naturality := M.associator_naturality
    left_naturality := M.left_naturality
    right_naturality := M.right_naturality }

/-- The Mathlib-based enriched implementation is available behind the specialized surface. -/
@[implicit_reducible] def toEnriched (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalSuperCategory C] :
    RMod.MonoidalEnrichedCategory SuperVec C :=
  RMod.EnrichedBridge.fromMonoidal (toStatementMonoidal C)

/-- Conversely, the existing enriched structure supplies every specialized law. -/
@[implicit_reducible] def fromEnriched (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [M : RMod.MonoidalEnrichedCategory SuperVec C] :
    MonoidalSuperCategory C where
  tensor := M.tensor
  tensor_objects := M.tensor_objects
  tensor_even := M.tensor_even
  associator_naturality := RMod.Regression.associator_natural (C := C)
  left_naturality := RMod.Regression.leftUnitor_natural (C := C)
  right_naturality := RMod.Regression.rightUnitor_natural (C := C)

/-- The compatibility conversion preserves the enriched tensor without transport. -/
theorem toEnriched_tensor (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [M : MonoidalSuperCategory C] :
    (toEnriched C).tensor = M.tensor := rfl

/-- Reverse conversion preserves the same tensor functor, including its Hom maps. -/
theorem fromEnriched_tensor (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [M : RMod.MonoidalEnrichedCategory SuperVec C] :
    (fromEnriched C).tensor = M.tensor := rfl

/-- Specializing and rebuilding changes no monoidal data; coherence is proof-irrelevant. -/
theorem monoidal_roundtrip (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [M : MonoidalSuperCategory C] :
    letI := toEnriched C
    fromEnriched C = M := by
  cases M
  rfl

/-! Equivalence comparisons retain the full odd as well as even naturality laws. -/
def toStatementEquivalence (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalSuperCategory C] [MonoidalSuperCategory D]
    (e : MonoidalSuperequivalence C D) :
    RMod.StatementLegacy.MonoidalSuperequivalence
      (toStatementMonoidal C) (toStatementMonoidal D) where
  forward := e.forward
  backward := e.backward
  monoidal := e.monoidal
  unit := e.unit
  counit := e.counit
  unit_natural := e.unit_natural
  counit_natural := e.counit_natural
  tensor_natural := e.tensor_natural

/-- No additional data are needed to reconstruct the public superequivalence. -/
def fromStatementEquivalence (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalSuperCategory C] [MonoidalSuperCategory D]
    (e : RMod.StatementLegacy.MonoidalSuperequivalence
      (toStatementMonoidal C) (toStatementMonoidal D)) :
    MonoidalSuperequivalence C D where
  forward := e.forward
  backward := e.backward
  monoidal := e.monoidal
  unit := e.unit
  counit := e.counit
  unit_natural := e.unit_natural
  counit_natural := e.counit_natural
  tensor_natural := e.tensor_natural

/-- Passing through the compatibility layer does not change an equivalence. -/
theorem equivalence_roundtrip (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalSuperCategory C] [MonoidalSuperCategory D]
    (e : MonoidalSuperequivalence C D) :
    fromStatementEquivalence C D (toStatementEquivalence C D e) = e := rfl

/-- The ordinary even equivalence is Mathlib's standard half-adjoint equivalence. -/
def forgetEquivalence (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalSuperCategory C] [MonoidalSuperCategory D]
    (e : MonoidalSuperequivalence C D) : Even C ≌ Even D :=
  CategoryTheory.Equivalence.mk e.forward.forget e.backward.forget e.unit e.counit

/-- Adjointification retains the given ordinary functor. -/
theorem forgetEquivalence_functor (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalSuperCategory C] [MonoidalSuperCategory D]
    (e : MonoidalSuperequivalence C D) :
    (forgetEquivalence C D e).functor = e.forward.forget := rfl

end RMod.BrundanEllis.Bridge
