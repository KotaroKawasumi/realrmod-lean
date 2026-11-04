import RMod.Hierarchy.Bridge.LegacyCoherence
import RMod.Classification.Abstract.Pi

/-!
# The specified parity object extracted from the parity shift

The image of the unit under the parity functor carries the two odd maps
already provided by the parity-shift data. Their inverse equations are
exactly the legacy parity laws.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (A : MonoidalPiSupercategory)

def toOldParityData : Classification.PiData (toOldData A.monoidal) where
  object := A.data.parityShift.functor.obj A.data.monoidal.unit
  hom := homogeneousPoint 1 (A.data.parityShift.inv A.data.monoidal.unit)
  inv := homogeneousPoint 1 (A.data.parityShift.hom A.data.monoidal.unit)

theorem toOldParityLaws : Classification.PiLaws (toOldData A.monoidal) (toOldParityData A) where
  hom_odd := by
    intro b hb
    simp [toOldParityData, homogeneousPoint, hb]
    rfl
  inv_odd := by
    intro b hb
    simp [toOldParityData, homogeneousPoint, hb]
    rfl
  hom_inv := A.laws.parityShift.inv_hom A.data.monoidal.unit
  inv_hom := A.laws.parityShift.hom_inv A.data.monoidal.unit

def legacyParityIso :
    totalObj A.monoidal.super A.data.monoidal.unit ≅
      totalObj A.monoidal.super (A.data.parityShift.functor.obj A.data.monoidal.unit) where
  hom := (toOldParityData A).inv
  inv := (toOldParityData A).hom
  hom_inv_id := (toOldParityLaws A).inv_hom
  inv_hom_id := (toOldParityLaws A).hom_inv

end RMod.Legacy.Hierarchy
