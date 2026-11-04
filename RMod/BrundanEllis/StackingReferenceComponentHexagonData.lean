import RMod.BrundanEllis.StackingReferenceShuffle
import RMod.Classification.Proofs.TensorTypes

/-! The reference hexagon paths on arbitrary objects in three specified
components. These are composites of the existing structural maps; no
coherence condition is assumed in their construction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "C" => reference.data.toWeaklyPointedSuperfusionData

/-- The short side moving the first object across the last two. -/
def referenceLeftHexagonShort (a b c : ZMod 8) (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    IsoData C (reference.data.tensorObj (reference.data.tensorObj X Y) Z) (reference.data.tensorObj Y (reference.data.tensorObj Z X)) :=
  (IsoData.assoc C X Y Z).trans C
    ((referenceExchangeData a (b + c) X (reference.data.tensorObj Y Z) hX
      (hY.tensor referenceProperty hZ)).trans C (IsoData.assoc C Y Z X))

/-- The long side moving the first object across each of the last two. -/
def referenceLeftHexagonLong (a b c : ZMod 8) (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    IsoData C (reference.data.tensorObj (reference.data.tensorObj X Y) Z) (reference.data.tensorObj Y (reference.data.tensorObj Z X)) :=
  ((referenceExchangeData a b X Y hX hY).tensor C (IsoData.refl C Z)).trans C
    ((IsoData.assoc C Y X Z).trans C
      ((IsoData.refl C Y).tensor C (referenceExchangeData a c X Z hX hZ)))

/-- The short side moving the last object across the first two. -/
def referenceRightHexagonShort (a b c : ZMod 8) (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    IsoData C (reference.data.tensorObj (reference.data.tensorObj X Y) Z) (reference.data.tensorObj Z (reference.data.tensorObj X Y)) :=
  referenceExchangeData (a + b) c (reference.data.tensorObj X Y) Z
    (hX.tensor referenceProperty hY) hZ

/-- The long side moving the last object across each of the first two. -/
def referenceRightHexagonLong (a b c : ZMod 8) (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    IsoData C (reference.data.tensorObj (reference.data.tensorObj X Y) Z) (reference.data.tensorObj Z (reference.data.tensorObj X Y)) :=
  (IsoData.assoc C X Y Z).trans C
    (((IsoData.refl C X).tensor C (referenceExchangeData b c Y Z hY hZ)).trans C
      (((IsoData.assoc C X Z Y).symm C).trans C
        (((referenceExchangeData a c X Z hX hZ).tensor C (IsoData.refl C Y)).trans C
          (IsoData.assoc C Z X Y))))

end RMod.BrundanEllis.Stacking
