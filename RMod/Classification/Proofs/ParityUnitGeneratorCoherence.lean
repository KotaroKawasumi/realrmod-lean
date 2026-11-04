import RMod.Classification.Proofs.ParityUnitTensorExtension
import RMod.Classification.Proofs.UnitGeneratorMaps
import RMod.Classification.Instances.UnitTensorComparisonExtension

/-!
# Unit coherence retains the equality of the selected generator with the unit

The normalized representative is identified with the unit by its actual
equality proof. Transporting the preceding component unit diagrams along
that equality gives exactly the specified comparisons and source maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (p : Pi C.data)
  (S T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj}
  (hi : EvenIsoLaws C.data i) (hS : S = unitSimple A)

theorem parityLeftUnitGenerator_coherence
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom i.hom (C.data.id (H.forwardFunctor.data.obj Y).obj))
        (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (leftUnitTensorComparison S T U V E H hi hS hA hC)).data.app
          (spanGenerator A S.data.object) Y).hom)
      (H.forwardFunctor.data.map (ObjectProperty.homMk (leftUnitGeneratorMap A S hS Y.obj).hom :
        leftUnitGeneratorSpan A S T hS Y ⟶ Y)).hom =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (H.forwardFunctor.data.obj Y).obj))
        (C.data.leftUnitorHom (H.forwardFunctor.data.obj Y).obj) := by
  subst S
  exact parityLeftUnitTensorExtension_coherence p T U V E H hi hA hC Y

theorem parityRightUnitGenerator_coherence
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T S).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (H.forwardFunctor.data.obj Y).obj) i.hom)
        (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (rightUnitTensorComparison S T U V E H hi hS hA hC)).data.app
          Y (spanGenerator A S.data.object)).hom)
      (H.forwardFunctor.data.map (ObjectProperty.homMk (rightUnitGeneratorMap A S hS Y.obj).hom :
        rightUnitGeneratorSpan A S T hS Y ⟶ Y)).hom =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (H.forwardFunctor.data.obj Y).obj C.data.tensorUnit))
        (C.data.rightUnitorHom (H.forwardFunctor.data.obj Y).obj) := by
  subst S
  exact parityRightUnitTensorExtension_coherence p T U V E H hi hA hC Y

end RMod.Classification
