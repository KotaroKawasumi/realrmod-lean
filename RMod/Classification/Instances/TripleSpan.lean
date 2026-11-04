import RMod.Classification.Instances.SpanTensor
import RMod.Classification.Instances.SpanGenerator

/-! # Left-associated triple tensor objects in their intrinsic component -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : WeaklyPointedSuperfusion.{0, 0}) (S T R : SimpleObject A)

def tripleSpanObj (X : HomogeneousSpanCategory A S.data.object)
    (Y : HomogeneousSpanCategory A T.data.object) (Z : HomogeneousSpanCategory A R.data.object) :
    HomogeneousSpanCategory A (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object :=
  ⟨A.data.tensorObj (A.data.tensorObj X.obj Y.obj) Z.obj,
    (spanTensorObj A (simpleTensorRepresentative A S T) R (spanTensorObj A S T X Y) Z).property⟩

def tripleSpanHom
    {X X' : HomogeneousSpanCategory A S.data.object} {Y Y' : HomogeneousSpanCategory A T.data.object}
    {Z Z' : HomogeneousSpanCategory A R.data.object} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tripleSpanObj A S T R X Y Z ⟶ tripleSpanObj A S T R X' Y' Z' :=
  ObjectProperty.homMk (A.data.tensorHom (A.data.tensorHom f.hom g.hom) h.hom)

def tripleSpanGenerator :
    HomogeneousSpanCategory A (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object :=
  tripleSpanObj A S T R (spanGenerator A S.data.object) (spanGenerator A T.data.object) (spanGenerator A R.data.object)

end RMod.Classification
