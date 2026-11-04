import RMod.Classification.Proofs.UnitTensorComparisonAt
import RMod.Classification.Proofs.SpanTensorGeneratorExt
import RMod.Classification.Proofs.TensorComparisonExtensionEvaluation
import RMod.Classification.Instances.UnitTensorIntertwiner
import RMod.Classification.Proofs.IsoDataExt

/-!
# The normalized matrix extensions retain the unit formula everywhere

With the unit variable fixed at its generator, naturality on all
homogeneous inclusions determines the other variable. Thus the actual
matrix extension agrees with the canonical unitor composite, not just
with an unspecified scalar multiple of it.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (T : SimpleObject A) (U V : SimpleObject C)
  (E : SpanSuperequivalence A C A.data.tensorUnit U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  {i : IsoData C.data C.data.tensorUnit (E.forwardFunctor.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

theorem leftUnitTensorExtension_hom_formula
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    ((tensorComparisonExtension (leftUnitTensorIntertwiner T U V E H hi hA hC)).data.app
      (spanGenerator A A.data.tensorUnit) Y).hom =
      (leftUnitTensorComparisonAtData T E.forwardFunctor.data H.forwardFunctor.data i Y).hom := by
  let t := leftUnitTensorIntertwiner T U V E H hi hA hC
  let η := tensorComparisonExtension t
  let X := spanGenerator A A.data.tensorUnit
  let N := (tensorProductTransport (unitSimple A) T T U V V H hA hC).forwardFunctor
  let W := spanTensorObj C U V (E.forwardFunctor.data.obj X) (H.forwardFunctor.data.obj Y)
  let f : N.toFunctor.obj (spanTensorObj A (unitSimple A) T X Y) ⟶ W :=
    ObjectProperty.homMk (η.data.app X Y).hom
  let g : N.toFunctor.obj (spanTensorObj A (unitSimple A) T X Y) ⟶ W :=
    ObjectProperty.homMk (leftUnitTensorComparisonAtData T E.forwardFunctor.data H.forwardFunctor.data i Y).hom
  have hg : (η.data.app X (spanGenerator A T.data.object)).hom =
      (leftUnitTensorComparisonAtData T E.forwardFunctor.data H.forwardFunctor.data i
        (spanGenerator A T.data.object)).hom := tensorComparisonExtension_generator_hom t
  have he : f = g := by
    apply spanTensor_hom_ext_right (unitSimple A) T N X Y
    intro j
    apply ObjectProperty.hom_ext
    let q : spanGenerator A T.data.object ⟶ Y := ObjectProperty.homMk ((spanPresentation Y).data.inclusion j)
    have hη := η.laws.naturality (𝟙 X) q (A.laws.id_even _) ((spanPresentation Y).laws.inclusion_grade j)
    have hid : (E.forwardFunctor.data.map (𝟙 X)).hom = C.data.id (E.forwardFunctor.data.obj X).obj :=
      congrArg (fun m => m.hom) (E.forwardFunctor.laws.map_id X)
    rw [hid] at hη
    simp only [zero_mul, ZMod.val_zero, pow_zero, C.laws.one_smul] at hη
    exact hη.trans ((congrArg (fun z => C.data.comp z
      (C.data.tensorHom (C.data.id (E.forwardFunctor.data.obj X).obj) (H.forwardFunctor.data.map q).hom)) hg).trans
        (leftUnitTensorComparisonAt_naturality T E.forwardFunctor H.forwardFunctor hi q).symm)
  exact congrArg (fun m => m.hom) he

theorem rightUnitTensorExtension_hom_formula
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T (unitSimple A)).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    ((tensorComparisonExtension (rightUnitTensorIntertwiner T U V E H hi hA hC)).data.app
      Y (spanGenerator A A.data.tensorUnit)).hom =
      (rightUnitTensorComparisonAtData T H.forwardFunctor.data E.forwardFunctor.data i Y).hom := by
  let t := rightUnitTensorIntertwiner T U V E H hi hA hC
  let η := tensorComparisonExtension t
  let X := spanGenerator A A.data.tensorUnit
  let N := (tensorProductTransport T (unitSimple A) T V U V H hA hC).forwardFunctor
  let W := spanTensorObj C V U (H.forwardFunctor.data.obj Y) (E.forwardFunctor.data.obj X)
  let f : N.toFunctor.obj (spanTensorObj A T (unitSimple A) Y X) ⟶ W :=
    ObjectProperty.homMk (η.data.app Y X).hom
  let g : N.toFunctor.obj (spanTensorObj A T (unitSimple A) Y X) ⟶ W :=
    ObjectProperty.homMk (rightUnitTensorComparisonAtData T H.forwardFunctor.data E.forwardFunctor.data i Y).hom
  have hg : (η.data.app (spanGenerator A T.data.object) X).hom =
      (rightUnitTensorComparisonAtData T H.forwardFunctor.data E.forwardFunctor.data i
        (spanGenerator A T.data.object)).hom := tensorComparisonExtension_generator_hom t
  have he : f = g := by
    apply spanTensor_hom_ext_left T (unitSimple A) N Y X
    intro j
    apply ObjectProperty.hom_ext
    let q : spanGenerator A T.data.object ⟶ Y := ObjectProperty.homMk ((spanPresentation Y).data.inclusion j)
    have hη := η.laws.naturality q (𝟙 X) ((spanPresentation Y).laws.inclusion_grade j) (A.laws.id_even _)
    have hid : (E.forwardFunctor.data.map (𝟙 X)).hom = C.data.id (E.forwardFunctor.data.obj X).obj :=
      congrArg (fun m => m.hom) (E.forwardFunctor.laws.map_id X)
    rw [hid] at hη
    simp only [zero_mul, ZMod.val_zero, pow_zero, C.laws.one_smul] at hη
    exact hη.trans ((congrArg (fun z => C.data.comp z
      (C.data.tensorHom (H.forwardFunctor.data.map q).hom (C.data.id (E.forwardFunctor.data.obj X).obj))) hg).trans
        (rightUnitTensorComparisonAt_naturality T E.forwardFunctor H.forwardFunctor hi q).symm)
  exact congrArg (fun m => m.hom) he

/-! The inverse maps are also exactly the canonical maps: their uniqueness
follows from the inverse laws already proved for both constructions. -/

theorem leftUnitTensorExtension_formula
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A (unitSimple A) T).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    (tensorComparisonExtension (leftUnitTensorIntertwiner T U V E H hi hA hC)).data.app
      (spanGenerator A A.data.tensorUnit) Y =
      leftUnitTensorComparisonAtData T E.forwardFunctor.data H.forwardFunctor.data i Y :=
  isoData_ext_of_hom_eq C
    ((tensorComparisonExtension (leftUnitTensorIntertwiner T U V E H hi hA hC)).laws.iso _ _)
    (leftUnitTensorComparisonAt_even T E.forwardFunctor H.forwardFunctor hi Y).toIsoLaws
    (leftUnitTensorExtension_hom_formula T U V E H hi hA hC Y)

theorem rightUnitTensorExtension_formula
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A T (unitSimple A)).data.object T.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C V U).data.object V.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) :
    (tensorComparisonExtension (rightUnitTensorIntertwiner T U V E H hi hA hC)).data.app
      Y (spanGenerator A A.data.tensorUnit) =
      rightUnitTensorComparisonAtData T H.forwardFunctor.data E.forwardFunctor.data i Y :=
  isoData_ext_of_hom_eq C
    ((tensorComparisonExtension (rightUnitTensorIntertwiner T U V E H hi hA hC)).laws.iso _ _)
    (rightUnitTensorComparisonAt_even T E.forwardFunctor H.forwardFunctor hi Y).toIsoLaws
    (rightUnitTensorExtension_hom_formula T U V E H hi hA hC Y)

end RMod.Classification
