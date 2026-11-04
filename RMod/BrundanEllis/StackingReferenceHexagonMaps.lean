import RMod.BrundanEllis.StackingReferenceTripleRows
import RMod.BrundanEllis.StackingReferenceUniformExchange

/-! The two reference hexagons as composites of the actual raw categorical
associators, tensor morphisms, and uniform exchanges. No coherence assertion
is included in these data definitions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Exchange the first two atoms while tensoring with the third identity. -/
def innerLeftMap (a b c : ZMod 8) :
    Hom realDData (leftAtomTensor a b c) (leftAtomTensor b a c) :=
  Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (uniformExchange a b (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (fun _ => rfl) (fun _ => rfl))
    (Hom.id realDData (Obj.singleton (c, 0)))

/-- Exchange the last two atoms while tensoring with the first identity. -/
def innerRightMap (a b c : ZMod 8) :
    Hom realDData (rightAtomTensor a b c) (rightAtomTensor a c b) :=
  Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (Hom.id realDData (Obj.singleton (a, 0)))
    (uniformExchange b c (Obj.singleton (b, 0)) (Obj.singleton (c, 0)) (fun _ => rfl) (fun _ => rfl))

/-- Exchange the first atom with the actual binary object formed by the last two. -/
def outerRightMap (a b c : ZMod 8) :
    Hom realDData (rightAtomTensor a b c) (leftAtomTensor b c a) :=
  uniformExchange a (b + c) (Obj.singleton (a, 0)) (atomTensor b c) (fun _ => rfl) (fun _ => rfl)

/-- Exchange the actual first binary object with the third atom. -/
def outerLeftMap (a b c : ZMod 8) :
    Hom realDData (leftAtomTensor a b c) (rightAtomTensor c a b) :=
  uniformExchange (a + b) c (atomTensor a b) (Obj.singleton (c, 0)) (fun _ => rfl) (fun _ => rfl)

/-- The three-arrow side of the first categorical reference hexagon. -/
def leftHexagonShortMap (a b c : ZMod 8) :
    Hom realDData (leftAtomTensor a b c) (rightAtomTensor b c a) :=
  Hom.comp (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0)))
    (Hom.comp (outerRightMap a b c)
      (RealAssociator.hom (Obj.singleton (b, 0)) (Obj.singleton (c, 0)) (Obj.singleton (a, 0))))

/-- The other three-arrow side of the first categorical hexagon. -/
def leftHexagonLongMap (a b c : ZMod 8) :
    Hom realDData (leftAtomTensor a b c) (rightAtomTensor b c a) :=
  Hom.comp (innerLeftMap a b c)
    (Hom.comp (RealAssociator.hom (Obj.singleton (b, 0)) (Obj.singleton (a, 0)) (Obj.singleton (c, 0)))
      (innerRightMap b a c))

/-- The five-arrow side of the second categorical hexagon. -/
def rightHexagonLongMap (a b c : ZMod 8) :
    Hom realDData (leftAtomTensor a b c) (rightAtomTensor c a b) :=
  Hom.comp (RealAssociator.hom (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0)))
    (Hom.comp (innerRightMap a b c)
      (Hom.comp (RealAssociator.inv (Obj.singleton (a, 0)) (Obj.singleton (c, 0)) (Obj.singleton (b, 0)))
        (Hom.comp (innerLeftMap a c b)
          (RealAssociator.hom (Obj.singleton (c, 0)) (Obj.singleton (a, 0)) (Obj.singleton (b, 0))))))

end RMod.BrundanEllis.Stacking.ReferenceCommutor
