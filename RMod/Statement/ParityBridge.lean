import RMod.Statement.MonoidalBridge

/-! Parity shifts retain the same enriched functor and the same odd inverse maps. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.StatementLegacy.StatementBridge

/-- Extract the computational fields of the completed parity shift. -/
def toParityData {C : Supercategory} (p : ParityShift C) :
    Legacy.ParityShiftData (toLegacySupercategory C).data where
  functor := (toFunctor p.functor).data
  hom := p.hom.app
  inv := p.inv

theorem toParityLaws {C : Supercategory} (p : ParityShift C) :
    Legacy.ParityShiftLaws (toLegacySupercategory C) (toParityData p) where
  functor := (toFunctor p.functor).laws
  naturality := ⟨p.hom, rfl⟩
  hom_inv := p.hom_inv
  inv_hom := p.inv_hom

/-- Repackage the witnessed graded naturality with its specified components. -/
def fromParity {C : Legacy.Supercategory} (p : Legacy.ParityShift C) : ParityShift (fromSuper C) where
  functor := fromFunctor ⟨p.data.functor, p.laws.functor⟩
  hom := {
    app := p.data.hom
    naturality := by
      obtain ⟨η, hη⟩ := p.laws.naturality
      rw [← hη]
      exact η.naturality }
  inv := p.data.inv
  hom_inv := p.laws.hom_inv
  inv_hom := p.laws.inv_hom

/-- The monoidal and parity operations share one unchanged base enrichment. -/
def toPiMonoidalData (C : MonoidalPiSupercategory) : Legacy.MonoidalPiSupercategoryData where
  toPiSupercategoryData := {
    toSupercategoryData := (toLegacySupercategory C.monoidal.super).data
    parityShift := toParityData C.parityShift }
  monoidal := (toMonoidalData C.monoidal).monoidal

theorem toPiMonoidalLaws (C : MonoidalPiSupercategory) :
    Legacy.MonoidalPiSupercategoryLaws (toPiMonoidalData C) where
  toSupercategoryLaws := (toLegacySupercategory C.monoidal.super).laws
  parityShift := toParityLaws C.parityShift
  monoidal := (toMonoidalLaws C.monoidal).monoidal

def toPiMonoidal (C : MonoidalPiSupercategory) : Legacy.MonoidalPiSupercategory :=
  ⟨toPiMonoidalData C, toPiMonoidalLaws C⟩

def fromPiMonoidal (C : Legacy.MonoidalPiSupercategory) : MonoidalPiSupercategory where
  toPiSupercategory := {
    toSupercategory := fromSuper C.monoidal.super
    parityShift := fromParity ⟨C.data.parityShift, C.laws.parityShift⟩ }
  monoidalStructure := (fromMonoidal C.monoidal).monoidalStructure

end RMod.StatementLegacy.StatementBridge
