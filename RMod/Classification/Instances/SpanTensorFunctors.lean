import RMod.Classification.Instances.SpanTensor
import RMod.Classification.Instances.TensorFunctors
import RMod.Classification.Instances.SpanSuperfunctorComposition

/-!
# Tensoring homogeneous spans with one fixed object

Restrict the existing full-Hom tensor superfunctors to the proved product
spans. The object and map data are fixed first; their laws are the laws
of the ambient tensor superfunctors with the full-subcategory wrappers.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) (S T : SimpleObject C)

def spanTensorLeftData (X : HomogeneousSpanCategory C S.data.object) :
    SpanSuperfunctorData C C T.data.object (simpleTensorRepresentative C S T).data.object where
  obj Y := spanTensorObj C S T X Y
  map f := spanTensorHom C S T (𝟙 X) f

theorem spanTensorLeftLaws (X : HomogeneousSpanCategory C S.data.object) :
    SpanSuperfunctorLaws C C T.data.object (simpleTensorRepresentative C S T).data.object
      (spanTensorLeftData C S T X) where
  map_id Y := ObjectProperty.hom_ext _ ((tensorLeftLaws C X.obj).map_id Y.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((tensorLeftLaws C X.obj).map_comp f.hom g.hom)
  map_zero Y Z := ObjectProperty.hom_ext _ ((tensorLeftLaws C X.obj).map_zero Y.obj Z.obj)
  map_add f g := ObjectProperty.hom_ext _ ((tensorLeftLaws C X.obj).map_add f.hom g.hom)
  map_smul r f := ObjectProperty.hom_ext _ ((tensorLeftLaws C X.obj).map_smul r f.hom)
  map_grade f hf := (tensorLeftLaws C X.obj).map_grade f.hom hf

def spanTensorLeft (X : HomogeneousSpanCategory C S.data.object) :
    SpanSuperfunctor C C T.data.object (simpleTensorRepresentative C S T).data.object :=
  ⟨spanTensorLeftData C S T X, spanTensorLeftLaws C S T X⟩

def spanTensorRightData (Y : HomogeneousSpanCategory C T.data.object) :
    SpanSuperfunctorData C C S.data.object (simpleTensorRepresentative C S T).data.object where
  obj X := spanTensorObj C S T X Y
  map f := spanTensorHom C S T f (𝟙 Y)

theorem spanTensorRightLaws (Y : HomogeneousSpanCategory C T.data.object) :
    SpanSuperfunctorLaws C C S.data.object (simpleTensorRepresentative C S T).data.object
      (spanTensorRightData C S T Y) where
  map_id X := ObjectProperty.hom_ext _ ((tensorRightLaws C Y.obj).map_id X.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((tensorRightLaws C Y.obj).map_comp f.hom g.hom)
  map_zero X Z := ObjectProperty.hom_ext _ ((tensorRightLaws C Y.obj).map_zero X.obj Z.obj)
  map_add f g := ObjectProperty.hom_ext _ ((tensorRightLaws C Y.obj).map_add f.hom g.hom)
  map_smul r f := ObjectProperty.hom_ext _ ((tensorRightLaws C Y.obj).map_smul r f.hom)
  map_grade f hf := (tensorRightLaws C Y.obj).map_grade f.hom hf

def spanTensorRight (Y : HomogeneousSpanCategory C T.data.object) :
    SpanSuperfunctor C C S.data.object (simpleTensorRepresentative C S T).data.object :=
  ⟨spanTensorRightData C S T Y, spanTensorRightLaws C S T Y⟩

end RMod.Classification
