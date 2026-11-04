import RMod.Enriched.ToStatement
import RMod.Enriched.FromStatement
import RMod.Enriched.GradedSchur
import RMod.Enriched.StatementAbelian

/-! Fusion hypotheses are transported in both directions. The new interface
obtains graded Schur from abelianity, whereas the previously proved models
obtain abelianity from their finite semisimple decomposition and Schur proof. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.EnrichedBridge

/-- Kernel existence is independent of the unique zero-morphism structure. -/
theorem kernelsOfAbelian {C : Type*} [Category* C] [Abelian C] (z : HasZeroMorphisms C) :
    @HasKernels C _ z := by
  have hz : z = @Preadditive.preadditiveHasZeroMorphisms C _ Abelian.toPreadditive :=
    Subsingleton.elim _ _
  subst z
  infer_instance

/-- The new fusion hypotheses imply every former fusion property. -/
def toFusion (C : Type) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalEnrichedCategory SuperVec C]
    [RigidCategory (Even C)] [Abelian (Even C)] [FusionPiSuperCategory C] :
    StatementLegacy.FusionPiSupercategory where
  toMonoidalPiSupercategory := toPiMonoidal C
  rigid := ⟨inferInstanceAs (RigidCategory (Even C))⟩
  biproducts := inferInstanceAs (HasFiniteBiproducts (Even C))
  hom_finite := FusionPiSuperCategory.hom_finite (C := C)
  semisimple := FusionPiSuperCategory.semisimple (C := C)
  finite_simples := FusionPiSuperCategory.finite_simples (C := C)
  graded_schur := by
    let L := StatementLegacy.toLegacySupercategory (bundled C)
    letI : HasFiniteBiproducts (Legacy.Even L) := inferInstanceAs (HasFiniteBiproducts (Even C))
    letI : HasKernels (Legacy.Even L) := kernelsOfAbelian (C := Even C) _
    let p : Legacy.ParityShift L :=
      ⟨StatementLegacy.StatementBridge.toParityData (toParityShift C),
        StatementLegacy.StatementBridge.toParityLaws (toParityShift C)⟩
    intro X Y hX hY a f hf hn
    exact EnrichedSupport.graded_schur L (FusionPiSuperCategory.semisimple (C := C)) p X Y hX hY a f
      ((StatementLegacy.StatementBridge.grade_mem_iff _ _ _ _ _).mp hf) hn
  simple_unit := FusionPiSuperCategory.simple_unit (C := C)

/-- Rebundle a new classification input for the existing classification proof. -/
def toWeak (C : WeaklyPointedFusionPiSuperCat) : StatementLegacy.WeaklyPointedFusionPiSupercategory where
  toFusionPiSupercategory := toFusion C
  splitUnit := WeaklyPointedFusionPiSuperCategory.splitUnit (C := C)
  weaklyPointed := WeaklyPointedFusionPiSuperCategory.weaklyPointed (C := C)

/-- The previous parity data already have the new carrier-based interface. -/
@[implicit_reducible] def fromParity (C : StatementLegacy.PiSupercategory) : PiSuperCategory (C.toSupercategory : Type) where
  parityShift := {
    functor := C.parityShift.functor
    hom := C.parityShift.hom
    inv := C.parityShift.inv
    hom_inv := C.parityShift.hom_inv
    inv_hom := C.parityShift.inv_hom }

/-- Previously proved models supply the new completed classification bundle. -/
def fromWeak (C : StatementLegacy.WeaklyPointedFusionPiSupercategory) : WeaklyPointedFusionPiSuperCat := by
  let A := (C.toSupercategory : Type)
  letI : PiSuperCategory A := fromParity C.toPiSupercategory
  letI : MonoidalCategory (Even A) := C.monoidalStructure.even
  letI : MonoidalEnrichedCategory SuperVec A := fromMonoidal C.toMonoidalPiSupercategory.monoidal
  letI : RigidCategory (Even A) := C.rigid.some
  letI : Abelian (Even A) := statementAbelian C.toFusionPiSupercategory
  letI : FusionPiSuperCategory A := {
    hom_finite := C.hom_finite
    semisimple := C.semisimple
    finite_simples := C.finite_simples
    simple_unit := C.simple_unit }
  letI : WeaklyPointedFusionPiSuperCategory A := {
    splitUnit := C.splitUnit
    weaklyPointed := C.weaklyPointed }
  exact { carrier := A
          superCategory := inferInstance
          piSuperCategory := inferInstance
          monoidalCategory := inferInstance
          monoidalEnrichedCategory := inferInstance
          rigidCategory := inferInstance
          abelian := inferInstance
          fusion := inferInstance
          weaklyPointed := inferInstance }

/-- Brauer-Wall reference predicates describe exactly the same total algebras. -/
def toReference (C : WeaklyPointedFusionPiSuperCat) (h : IsBrauerWallReference C) :
    StatementLegacy.IsBrauerWallReference (toWeak C) where
  simple_type := h.simple_type
  realizes_type := h.realizes_type
  type_detects_orbit := h.type_detects_orbit

def fromReference (C : StatementLegacy.WeaklyPointedFusionPiSupercategory)
    (h : StatementLegacy.IsBrauerWallReference C) : IsBrauerWallReference (fromWeak C) where
  simple_type := h.simple_type
  realizes_type := h.realizes_type
  type_detects_orbit := h.type_detects_orbit

end RMod.EnrichedBridge
