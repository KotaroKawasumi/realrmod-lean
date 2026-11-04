import RMod.Classification.Instances.UnitTensorComparison

/-!
# Canonical unit comparisons at every object of a component

Map the source unitor, invert the target unitor, and insert the chosen
even comparison from the target unit. This is the generator formula
applied to an arbitrary object of its homogeneous span.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : WeaklyPointedSuperfusion.{0, 0}) (T : SimpleObject A)

def leftUnitSpanObj (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj A.data.tensorUnit Y.obj,
    inHomogeneousSpan_of_retract A T.laws.simple Y.property
      (A.data.leftUnitorHom Y.obj) (A.data.leftUnitorInv Y.obj)
      (A.laws.left_unitor_hom_inv _) (A.laws.left_unitor_hom_even _)⟩

def rightUnitSpanObj (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj Y.obj A.data.tensorUnit,
    inHomogeneousSpan_of_retract A T.laws.simple Y.property
      (A.data.rightUnitorHom Y.obj) (A.data.rightUnitorInv Y.obj)
      (A.laws.right_unitor_hom_inv _) (A.laws.right_unitor_hom_even _)⟩

variable {A} {C : WeaklyPointedSuperfusion.{0, 0}} {U V : C.data.Obj}

def leftUnitTensorComparisonAtData
    (E : SpanSuperfunctorData A C A.data.tensorUnit U)
    (H : SpanSuperfunctorData A C T.data.object V)
    (i : IsoData C.data C.data.tensorUnit (E.obj (spanGenerator A A.data.tensorUnit)).obj)
    (Y : HomogeneousSpanCategory A T.data.object) :
    IsoData C.data (H.obj (leftUnitSpanObj A T Y)).obj
      (C.data.tensorObj (E.obj (spanGenerator A A.data.tensorUnit)).obj (H.obj Y).obj) :=
  ((SpanSuperfunctor.mapIsoData H (X := leftUnitSpanObj A T Y) (Y := Y)
      (IsoData.leftUnit A.data Y.obj)).trans C.data
    ((IsoData.leftUnit C.data (H.obj Y).obj).symm C.data)).trans C.data
      (i.tensor C.data (IsoData.refl C.data (H.obj Y).obj))

def rightUnitTensorComparisonAtData
    (H : SpanSuperfunctorData A C T.data.object V)
    (E : SpanSuperfunctorData A C A.data.tensorUnit U)
    (i : IsoData C.data C.data.tensorUnit (E.obj (spanGenerator A A.data.tensorUnit)).obj)
    (Y : HomogeneousSpanCategory A T.data.object) :
    IsoData C.data (H.obj (rightUnitSpanObj A T Y)).obj
      (C.data.tensorObj (H.obj Y).obj (E.obj (spanGenerator A A.data.tensorUnit)).obj) :=
  ((SpanSuperfunctor.mapIsoData H (X := rightUnitSpanObj A T Y) (Y := Y)
      (IsoData.rightUnit A.data Y.obj)).trans C.data
    ((IsoData.rightUnit C.data (H.obj Y).obj).symm C.data)).trans C.data
      ((IsoData.refl C.data (H.obj Y).obj).tensor C.data i)

end RMod.Classification
