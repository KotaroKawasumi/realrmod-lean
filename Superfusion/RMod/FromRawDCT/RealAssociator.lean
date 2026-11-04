import Superfusion.RMod.FromRawDCT.Associator
import Superfusion.RMod.RawDCT.RealComputableShift

/-!
# Endpoint-normalized associator data for the shifted real raw DCT

The abstract associator reads the stored connector coefficient without an
endpoint convention.  For shifted atoms, reassociating a left route also
moves the third endpoint past the inner `(X, Y)` fusion row.  Its Koszul
normalization is

`(-1)^(p * s_c)`,

where `p` is the parity of that inner left-route row and `s_c` is the shift
of the third atom.  This file inserts precisely that executable sign in both
directions.  It contains data only; inverse, naturality, and pentagon proofs
belong to the separate concrete laws layer.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace RealAssociator

/-! ## Concrete shifted input and endpoint sign -/

/-- The exact computably shifted real raw DCT used by the concrete
associator. -/
abbrev shiftedReal : RawDCTData :=
  realComputableShiftedRawDCT.data

/-- Parity of the inner `(X, Y)` row represented by a left-associated
ternary slot. -/
def leftInnerParity (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) : ZMod 2 :=
  let xy := (Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left
  shiftedReal.C.rowParity
    (X.atom xy.left).label (Y.atom xy.right).label xy.fusion

/-- Endpoint normalization for one left-associated ternary slot. -/
def endpointSign (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) : ℝ :=
  RawDCT.paritySign
    (leftInnerParity X Y Z qL * (Z.atom qL.right).shift)

/-! ## Endpoint-normalized matrix entries -/

/-- Forward connector entry with the left-route endpoint convention. -/
def homEntry (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL)
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR) :=
  AtomHom.smul (endpointSign X Y Z qL)
    (Associator.homEntry shiftedReal X Y Z qL qR)

/-- Backward connector entry with the same left-route endpoint convention.
The sign is indexed by the left-associated target slot `qL`, not by the
right-associated source slot. -/
def invEntry (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR)
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL) :=
  AtomHom.smul (endpointSign X Y Z qL)
    (Associator.invEntry shiftedReal X Y Z qR qL)

/-! ## Matrices and proof-free associator data -/

/-- Endpoint-normalized forward associator on finite coordinate objects. -/
def hom (X Y Z : Obj) :
    Hom shiftedReal.D
      (Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
      (Tensor.obj shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :=
  fun i j => homEntry X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get j)

/-- Endpoint-normalized backward associator on finite coordinate objects. -/
def inv (X Y Z : Obj) :
    Hom shiftedReal.D
      (Tensor.obj shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
      (Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :=
  fun i j => invEntry X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get j)

/-- Concrete executable associator data.  No law is bundled here. -/
def data : AssociatorData shiftedReal.D
    (Tensor.canonicalData shiftedReal.D shiftedReal.C) where
  associatorHom := hom
  associatorInv := inv

/-! ## Closed nontrivial endpoint evaluations -/

private def exampleX : Obj := Obj.singleton (1, 0)
private def exampleY : Obj := Obj.singleton (3, 0)
private def exampleZ : Obj := Obj.singleton (0, 1)

/-- The even row of the rank-two `(1,3)` kernel contributes no sign even
when the third endpoint is shifted. -/
example :
    endpointSign exampleX exampleY exampleZ
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C exampleX exampleY)
        exampleZ).get ⟨0, by decide⟩) = 1 :=
  rfl

/-- The odd row of the same kernel contributes the nontrivial sign when the
third endpoint has shift one. -/
example :
    endpointSign exampleX exampleY exampleZ
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C exampleX exampleY)
        exampleZ).get ⟨1, by decide⟩) = -1 :=
  rfl

end RealAssociator

/-- Public concrete associator data used by the real candidate. -/
def realAssociatorData : AssociatorData
    realComputableShiftedRawDCT.data.D
    (Tensor.canonicalData realComputableShiftedRawDCT.data.D
      realComputableShiftedRawDCT.data.C) :=
  RealAssociator.data

end Superfusion.RMod.FromRawDCT
