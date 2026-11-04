import RMod.Hierarchy.Abstract.Superfunctor
import RMod.Hierarchy.Instances.TotalCategory
import RMod.Hierarchy.Instances.SuperVecSymmetric

/-! A parity shift is an odd enriched natural isomorphism. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

abbrev oddLine : SuperVec :=
  (GradedObject.single (1 : ZMod 2)).obj (ModuleCat.of ℝ ℝ)

structure ParityShiftData (C : SupercategoryData) where
  functor : SuperfunctorData C C
  hom : ∀ X, oddLine ⟶ C.Hom X (functor.obj X)
  inv : ∀ X, oddLine ⟶ C.Hom (functor.obj X) X
structure ParityShiftLaws (C : Supercategory) (d : ParityShiftData C.data) : Prop where
  functor : SuperfunctorLaws d.functor
  naturality : ∃ η : GradedNatTrans ((Center.ofBraided SuperVec).obj oddLine)
      (EnrichedFunctor.id SuperVec C.data.Obj) (Superfunctor.enriched ⟨d.functor, functor⟩),
    η.app = d.hom
  hom_inv : ∀ X, tComp C.data (homogeneousPoint 1 (d.hom X))
    (homogeneousPoint 1 (d.inv X)) = evenPoint (C.data.id X)
  inv_hom : ∀ X, tComp C.data (homogeneousPoint 1 (d.inv X))
    (homogeneousPoint 1 (d.hom X)) = evenPoint (C.data.id (d.functor.obj X))
structure ParityShift (C : Supercategory) where
  data : ParityShiftData C.data
  laws : ParityShiftLaws C data
structure PiSupercategoryData extends SupercategoryData where
  parityShift : ParityShiftData toSupercategoryData
structure PiSupercategoryLaws (d : PiSupercategoryData) : Prop
    extends SupercategoryLaws d.toSupercategoryData where
  parityShift : ParityShiftLaws ⟨d.toSupercategoryData, toSupercategoryLaws⟩ d.parityShift
structure PiSupercategory where
  data : PiSupercategoryData
  laws : PiSupercategoryLaws data

end RMod.Legacy
