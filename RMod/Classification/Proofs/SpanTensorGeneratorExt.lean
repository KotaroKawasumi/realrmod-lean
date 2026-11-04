import RMod.Classification.Instances.SpanTensorFunctors
import RMod.Classification.Proofs.SpanGeneratorExt

/-!
# Generator detection in either variable of a tensor image

Tensoring with the identity of the fixed object is a superfunctor on all
maps. Compose it with the supplied component functor and reuse the
homogeneous generator detection theorem, including odd inclusions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (S T : SimpleObject A) {V : C.data.Obj}
  (N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object V)
  (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
  {Z : HomogeneousSpanCategory C V}

theorem spanTensor_hom_ext_right
    (f g : N.toFunctor.obj (spanTensorObj A S T X Y) ⟶ Z)
    (he : ∀ j, N.toFunctor.map (spanTensorHom A S T (𝟙 X)
      (ObjectProperty.homMk ((spanPresentation Y).data.inclusion j) : spanGenerator A T.data.object ⟶ Y)) ≫ f =
      N.toFunctor.map (spanTensorHom A S T (𝟙 X)
      (ObjectProperty.homMk ((spanPresentation Y).data.inclusion j) : spanGenerator A T.data.object ⟶ Y)) ≫ g) :
    f = g :=
  ((spanTensorLeft A S T X).comp N).hom_ext_generator f g he

theorem spanTensor_hom_ext_left
    (f g : N.toFunctor.obj (spanTensorObj A S T X Y) ⟶ Z)
    (he : ∀ j, N.toFunctor.map (spanTensorHom A S T
      (ObjectProperty.homMk ((spanPresentation X).data.inclusion j) : spanGenerator A S.data.object ⟶ X) (𝟙 Y)) ≫ f =
      N.toFunctor.map (spanTensorHom A S T
      (ObjectProperty.homMk ((spanPresentation X).data.inclusion j) : spanGenerator A S.data.object ⟶ X) (𝟙 Y)) ≫ g) :
    f = g :=
  ((spanTensorRight A S T Y).comp N).hom_ext_generator f g he

end RMod.Classification
