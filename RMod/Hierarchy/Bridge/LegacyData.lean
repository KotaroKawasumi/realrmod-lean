import RMod.Hierarchy.Abstract.FusionPiSupercategory
import RMod.Hierarchy.Instances.TotalTensor
import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Legacy operations extracted from an enriched monoidal category

Only the odd-odd tensor summand changes sign. This is the inverse of the
chronological convention correction in the old-to-new adapter. Objects,
composition, and all even coherence maps retain their specified values.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace RMod.Legacy.Hierarchy

def legacyTensor (C : MonoidalSupercategory) {X X' Y Y' : C.data.Obj}
    (f : THom C.super.data X X') (g : THom C.super.data Y Y') :
    THom C.super.data (C.data.monoidal.tensor.obj (X, Y))
      (C.data.monoidal.tensor.obj (X', Y')) :=
  tTensor C.data.monoidal f g -
    (2 : ℝ) • tTensor C.data.monoidal (homogeneousPart C.super 1 f) (homogeneousPart C.super 1 g)

def toOldData (C : MonoidalSupercategory) : WeaklyPointedSuperfusionData.{0, 0} where
  Obj := TotalCategory C.super
  Hom := fun X Y => X ⟶ Y
  id := fun X => 𝟙 X
  comp := fun f g => f ≫ g
  zero := 0
  add := fun f g => f + g
  neg := fun f => -f
  smul := fun r f => r • f
  grade := fun X Y a => (RMod.Legacy.grade C.super X Y a : Set (X ⟶ Y))
  tensorObj := fun X Y => C.data.monoidal.tensor.obj (X, Y)
  tensorHom := legacyTensor C
  tensorUnit := C.data.monoidal.unit
  associatorHom := fun X Y Z => evenPoint (C.data.monoidal.associatorHom X Y Z)
  associatorInv := fun X Y Z => evenPoint (C.data.monoidal.associatorInv X Y Z)
  leftUnitorHom := fun X => evenPoint (C.data.monoidal.leftHom X)
  leftUnitorInv := fun X => evenPoint (C.data.monoidal.leftInv X)
  rightUnitorHom := fun X => evenPoint (C.data.monoidal.rightHom X)
  rightUnitorInv := fun X => evenPoint (C.data.monoidal.rightInv X)

end RMod.Legacy.Hierarchy
