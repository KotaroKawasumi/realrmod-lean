import RMod.Statement.ParityBridge
import RMod.Hierarchy.Abstract.Reference

/-! Fusion and reference properties are transported without adding assumptions. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.StatementLegacy.StatementBridge

theorem orbit_fromSuper (C : Legacy.Supercategory) (X Y : C.data.Obj) :
    SameParityOrbit (fromSuper C) X Y ↔ Legacy.SameParityOrbit C X Y := by
  simp only [SameParityOrbit, Legacy.SameParityOrbit, grade_mem_iff]
  rfl

theorem orbit_toSuper (C : Supercategory) (X Y : C) :
    Legacy.SameParityOrbit (toLegacySupercategory C) X Y ↔ SameParityOrbit C X Y := by
  simp only [SameParityOrbit, Legacy.SameParityOrbit, grade_mem_iff]
  rfl

/-- Existing fusion proofs apply to the same completed enriched structure. -/
def fromFusion (C : Legacy.FusionPiSupercategory) : FusionPiSupercategory where
  toMonoidalPiSupercategory := fromPiMonoidal C.toMonoidalPiSupercategory
  rigid := C.rigid
  biproducts := C.biproducts
  hom_finite := C.hom_finite
  semisimple := C.semisimple
  finite_simples := by
    obtain ⟨n, S, hS, h⟩ := C.finite_simples
    exact ⟨n, S, hS, fun X hX => by
      obtain ⟨i, hi⟩ := h X hX
      exact ⟨i, (orbit_fromSuper _ _ _).mpr hi⟩⟩
  graded_schur := by
    intro X Y hX hY a f hf hn
    exact C.graded_schur X Y hX hY a f ((grade_mem_iff _ _ _ _ _).mp hf) hn
  simple_unit := C.simple_unit

def fromWeak (C : Legacy.WeaklyPointedFusionPiSupercategory) :
    WeaklyPointedFusionPiSupercategory where
  toFusionPiSupercategory := fromFusion C.toFusionPiSupercategory
  splitUnit := C.splitUnit
  weaklyPointed := C.weaklyPointed

/-- Reconstructed even operations agree with the source's operations. -/
theorem rigid_toMonoidal (C : MonoidalSupercategory) :
    Legacy.IsRigid (toMonoidal C) ↔ IsRigid C := by
  change Nonempty (@RigidCategory (Even C.super) _
    (Legacy.evenCategoryMonoidal (toMonoidal C))) ↔ _
  rw [toMonoidal_even]
  rfl

def toFusion (C : FusionPiSupercategory) : Legacy.FusionPiSupercategory where
  toMonoidalPiSupercategory := toPiMonoidal C.toMonoidalPiSupercategory
  rigid := (rigid_toMonoidal _).mpr C.rigid
  biproducts := C.biproducts
  hom_finite := C.hom_finite
  semisimple := C.semisimple
  finite_simples := by
    obtain ⟨n, S, hS, h⟩ := C.finite_simples
    exact ⟨n, S, hS, fun X hX => by
      obtain ⟨i, hi⟩ := h X hX
      exact ⟨i, (orbit_toSuper _ _ _).mpr hi⟩⟩
  graded_schur := by
    intro X Y hX hY a f hf hn
    exact C.graded_schur X Y hX hY a f ((grade_mem_iff _ _ _ _ _).mpr hf) hn
  simple_unit := C.simple_unit

theorem weaklyInvertible_toPi (C : MonoidalPiSupercategory)
    [hB : HasFiniteBiproducts (Even C.monoidal.super)] (X : Even C.monoidal.super) :
    @Legacy.IsWeaklyInvertible (toPiMonoidal C) hB X ↔ IsWeaklyInvertible C X := by
  unfold Legacy.IsWeaklyInvertible IsWeaklyInvertible
  apply exists_congr
  intro Y
  apply and_congr
  · change Nonempty (@ExactPairing (Even C.monoidal.super) _
      (Legacy.evenCategoryMonoidal (toMonoidal C.monoidal)) X Y) ↔ _
    rw [toMonoidal_even]
  · rfl

def toWeak (C : WeaklyPointedFusionPiSupercategory) :
    Legacy.WeaklyPointedFusionPiSupercategory where
  toFusionPiSupercategory := toFusion C.toFusionPiSupercategory
  splitUnit := C.splitUnit
  weaklyPointed X hX := (weaklyInvertible_toPi _ X).mpr (C.weaklyPointed X hX)

end RMod.StatementLegacy.StatementBridge
