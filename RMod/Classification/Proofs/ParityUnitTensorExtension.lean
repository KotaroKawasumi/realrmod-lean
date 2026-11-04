import RMod.Classification.Proofs.UnitTensorExtensionFormula
import RMod.Classification.Proofs.UnitTensoratorCoherence
import RMod.Classification.Instances.ParityTensorComparison

/-!
# Unit coherence of the actual parity-normalized component comparisons

At the unit generator the binary degree is zero. The specified parity
deletion is then the right unitor, and the proved extension formula
identifies the remaining inverse comparison. The resulting square is
the exact unit block of the convolution model on every component object.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (p : Pi C.data)
  (T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C A.data.tensorUnit U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

theorem parityLeftUnitTensorExtension_coherence
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom i.hom (C.data.id (H.forwardFunctor.data.obj Y).obj))
        (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (tensorComparisonExtension
        (leftUnitTensorIntertwiner T U V E H hi hA hC))).data.app
          (spanGenerator A A.data.tensorUnit) Y).hom)
      (H.forwardFunctor.data.map (ObjectProperty.homMk (A.data.leftUnitorHom Y.obj) :
        leftUnitSpanObj A T Y ⟶ Y)).hom =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit (H.forwardFunctor.data.obj Y).obj))
        (C.data.leftUnitorHom (H.forwardFunctor.data.obj Y).obj) := by
  have he := leftUnitTensorExtension_formula T U V E H hi hA hC Y
  have hm : ((parityTensorComparison p (tensorComparisonExtension
      (leftUnitTensorIntertwiner T U V E H hi hA hC))).data.app
      (spanGenerator A A.data.tensorUnit) Y).hom =
      C.data.comp (C.data.rightUnitorHom
        (C.data.tensorObj (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj
          (H.forwardFunctor.data.obj Y).obj))
        (leftUnitTensorComparisonAtData T E.forwardFunctor.data H.forwardFunctor.data i Y).inv :=
    congrArg (fun d : IsoData C.data _ _ => C.data.comp (C.data.rightUnitorHom _) d.inv) he
  rw [hm]
  exact leftUnitTensorator_zero_coherence C.laws i hi
    (SpanSuperfunctor.mapIsoData H.forwardFunctor.data (X := leftUnitSpanObj A T Y) (Y := Y)
      (IsoData.leftUnit A.data Y.obj))
    (H.forwardFunctor.mapIsoLaws (X := leftUnitSpanObj A T Y) (Y := Y)
      (EvenIsoLaws.leftUnit A.laws Y.obj).toIsoLaws)

theorem parityRightUnitTensorExtension_coherence
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T (unitSimple A)).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (H.forwardFunctor.data.obj Y).obj) i.hom)
        (C.data.id C.data.tensorUnit))
      ((parityTensorComparison p (tensorComparisonExtension
        (rightUnitTensorIntertwiner T U V E H hi hA hC))).data.app
          Y (spanGenerator A A.data.tensorUnit)).hom)
      (H.forwardFunctor.data.map (ObjectProperty.homMk (A.data.rightUnitorHom Y.obj) :
        rightUnitSpanObj A T Y ⟶ Y)).hom =
      C.data.comp (C.data.rightUnitorHom (C.data.tensorObj (H.forwardFunctor.data.obj Y).obj C.data.tensorUnit))
        (C.data.rightUnitorHom (H.forwardFunctor.data.obj Y).obj) := by
  have he := rightUnitTensorExtension_formula T U V E H hi hA hC Y
  have hm : ((parityTensorComparison p (tensorComparisonExtension
      (rightUnitTensorIntertwiner T U V E H hi hA hC))).data.app
      Y (spanGenerator A A.data.tensorUnit)).hom =
      C.data.comp (C.data.rightUnitorHom
        (C.data.tensorObj (H.forwardFunctor.data.obj Y).obj
          (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj))
        (rightUnitTensorComparisonAtData T H.forwardFunctor.data E.forwardFunctor.data i Y).inv :=
    congrArg (fun d : IsoData C.data _ _ => C.data.comp (C.data.rightUnitorHom _) d.inv) he
  rw [hm]
  exact rightUnitTensorator_zero_coherence C.laws i hi
    (SpanSuperfunctor.mapIsoData H.forwardFunctor.data (X := rightUnitSpanObj A T Y) (Y := Y)
      (IsoData.rightUnit A.data Y.obj))
    (H.forwardFunctor.mapIsoLaws (X := rightUnitSpanObj A T Y) (Y := Y)
      (EvenIsoLaws.rightUnit A.laws Y.obj).toIsoLaws)

end RMod.Classification
