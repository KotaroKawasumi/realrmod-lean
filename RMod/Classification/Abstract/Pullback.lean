import RMod.Classification.Abstract.Reference
import RMod.Classification.Abstract.Parameters
import RMod.Classification.Abstract.ParityOperations

/-!
# The abstract pullback carrier and its tensor interface

Objects retain their group index even when `rho` is not injective. The Hom
carrier and all category operations are fixed componentwise in the reference
category. This file contains no concrete regular-module data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (t : TwistData)

/-! The subtype restricts the carrier to the intrinsic type component;
it does not store reconstruction data or an equivalence witness. -/

abbrev PullbackObj := (g : t.group) →
  {X : C.Obj // InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X}

abbrev PullbackHom (X Y : PullbackObj C t) := (g : t.group) → C.Hom (X g).val (Y g).val

/-! The monoidal operations are data on this fixed underlying category.
In particular implementations cannot substitute a category of U-modules. -/

structure PullbackTensorData where
  tensorObj : PullbackObj C t → PullbackObj C t → PullbackObj C t
  tensorHom : {X₁ Y₁ X₂ Y₂ : PullbackObj C t} →
    PullbackHom C t X₁ Y₁ → PullbackHom C t X₂ Y₂ →
      PullbackHom C t (tensorObj X₁ X₂) (tensorObj Y₁ Y₂)
  tensorUnit : PullbackObj C t
  associatorHom : (X Y Z : PullbackObj C t) →
    PullbackHom C t (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
  associatorInv : (X Y Z : PullbackObj C t) →
    PullbackHom C t (tensorObj X (tensorObj Y Z)) (tensorObj (tensorObj X Y) Z)
  leftUnitorHom : (X : PullbackObj C t) → PullbackHom C t (tensorObj tensorUnit X) X
  leftUnitorInv : (X : PullbackObj C t) → PullbackHom C t X (tensorObj tensorUnit X)
  rightUnitorHom : (X : PullbackObj C t) → PullbackHom C t (tensorObj X tensorUnit) X
  rightUnitorInv : (X : PullbackObj C t) → PullbackHom C t X (tensorObj X tensorUnit)
  piObj : PullbackObj C t
  piHom : PullbackHom C t piObj tensorUnit
  piInv : PullbackHom C t tensorUnit piObj

namespace PullbackTensorData

/-- Only the monoidal and specified parity operations can vary; the category
carrier, Hom, grading, composition and linear operations are fixed. -/
def toPiSuperfusionData (d : PullbackTensorData C t) : PiSuperfusionData.{0, 0} where
  Obj := PullbackObj C t
  Hom := PullbackHom C t
  id X g := C.id (X g).val
  comp f h g := C.comp (f g) (h g)
  zero _ := C.zero
  add f h g := C.add (f g) (h g)
  neg f g := C.neg (f g)
  smul r f g := C.smul r (f g)
  grade _ _ a := {f | ∀ g, C.IsHomogeneous a (f g)}
  tensorObj := d.tensorObj
  tensorHom := d.tensorHom
  tensorUnit := d.tensorUnit
  associatorHom := d.associatorHom
  associatorInv := d.associatorInv
  leftUnitorHom := d.leftUnitorHom
  leftUnitorInv := d.leftUnitorInv
  rightUnitorHom := d.rightUnitorHom
  rightUnitorInv := d.rightUnitorInv
  pi := ⟨d.piObj, d.piHom, d.piInv⟩

end PullbackTensorData

structure PullbackTensorLaws (d : PullbackTensorData C t) : Prop
    extends PiSuperfusionLaws (d.toPiSuperfusionData C t)

structure PullbackTensor where
  data : PullbackTensorData C t
  laws : PullbackTensorLaws C t data

/-! Convolution summands and their Hom maps, before taking finite sums. -/

def twistSummand (X Y : PullbackObj C t) (g h : t.group) : C.Obj :=
  C.tensorObj (C.tensorObj (X g).val (Y h).val) (C.pi.factor (t.nu g h))

def twistSummandHom {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (f' : PullbackHom C t Y Y') (g h : t.group) :
    C.Hom (twistSummand C t X Y g h) (twistSummand C t X' Y' g h) :=
  C.tensorHom (C.tensorHom (f g) (f' h)) (C.id (C.pi.factor (t.nu g h)))

end RMod.Classification
