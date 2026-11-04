import RMod.Classification.Instances.SpanMapIso
import RMod.Classification.Abstract.SimpleObjects
import RMod.Classification.Instances.SpanGenerator
import RMod.Classification.Proofs.HomogeneousSpanMembership
import RMod.Classification.Proofs.IsoCalculus

/-!
# The canonical unit tensor comparisons

Map the source unitor through the component functor, invert the target
unitor, and insert the specified even unit comparison. The reverse
composite is retained in the data. These operations are already even
isomorphisms, so their separated laws follow by the iso calculus.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : WeaklyPointedSuperfusion.{0, 0}) (T : SimpleObject A)

def leftUnitSpanObject : HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj A.data.tensorUnit T.data.object,
    inHomogeneousSpan_of_retract A T.laws.simple (spanGenerator_mem A T.data.object)
      (A.data.leftUnitorHom T.data.object) (A.data.leftUnitorInv T.data.object)
      (A.laws.left_unitor_hom_inv _) (A.laws.left_unitor_hom_even _)⟩

def rightUnitSpanObject : HomogeneousSpanCategory A T.data.object :=
  ⟨A.data.tensorObj T.data.object A.data.tensorUnit,
    inHomogeneousSpan_of_retract A T.laws.simple (spanGenerator_mem A T.data.object)
      (A.data.rightUnitorHom T.data.object) (A.data.rightUnitorInv T.data.object)
      (A.laws.right_unitor_hom_inv _) (A.laws.right_unitor_hom_even _)⟩

variable {A} {C : WeaklyPointedSuperfusion.{0, 0}} {U V : C.data.Obj}

def leftUnitTensorComparisonData
    (E : SpanSuperfunctorData A C A.data.tensorUnit U)
    (H : SpanSuperfunctorData A C T.data.object V)
    (i : IsoData C.data C.data.tensorUnit (E.obj (spanGenerator A A.data.tensorUnit)).obj) :
    IsoData C.data (H.obj (leftUnitSpanObject A T)).obj
      (C.data.tensorObj (E.obj (spanGenerator A A.data.tensorUnit)).obj
        (H.obj (spanGenerator A T.data.object)).obj) :=
  ((SpanSuperfunctor.mapIsoData H (X := leftUnitSpanObject A T)
      (Y := spanGenerator A T.data.object) (IsoData.leftUnit A.data T.data.object)).trans C.data
    ((IsoData.leftUnit C.data (H.obj (spanGenerator A T.data.object)).obj).symm C.data)).trans C.data
      (i.tensor C.data (IsoData.refl C.data (H.obj (spanGenerator A T.data.object)).obj))

theorem leftUnitTensorComparison_evenIso
    (E : SpanSuperfunctor A C A.data.tensorUnit U)
    (H : SpanSuperfunctor A C T.data.object V)
    {i : IsoData C.data C.data.tensorUnit (E.data.obj (spanGenerator A A.data.tensorUnit)).obj}
    (hi : EvenIsoLaws C.data i) :
    EvenIsoLaws C.data (leftUnitTensorComparisonData T E.data H.data i) :=
  ((H.mapEvenIsoLaws (X := leftUnitSpanObject A T) (Y := spanGenerator A T.data.object)
    (EvenIsoLaws.leftUnit A.laws _)).trans C.laws (EvenIsoLaws.leftUnit C.laws _).symm).trans C.laws
      (hi.tensor C.laws (EvenIsoLaws.refl C.laws _))

def rightUnitTensorComparisonData
    (H : SpanSuperfunctorData A C T.data.object V)
    (E : SpanSuperfunctorData A C A.data.tensorUnit U)
    (i : IsoData C.data C.data.tensorUnit (E.obj (spanGenerator A A.data.tensorUnit)).obj) :
    IsoData C.data (H.obj (rightUnitSpanObject A T)).obj
      (C.data.tensorObj (H.obj (spanGenerator A T.data.object)).obj
        (E.obj (spanGenerator A A.data.tensorUnit)).obj) :=
  ((SpanSuperfunctor.mapIsoData H (X := rightUnitSpanObject A T)
      (Y := spanGenerator A T.data.object) (IsoData.rightUnit A.data T.data.object)).trans C.data
    ((IsoData.rightUnit C.data (H.obj (spanGenerator A T.data.object)).obj).symm C.data)).trans C.data
      ((IsoData.refl C.data (H.obj (spanGenerator A T.data.object)).obj).tensor C.data i)

theorem rightUnitTensorComparison_evenIso
    (H : SpanSuperfunctor A C T.data.object V)
    (E : SpanSuperfunctor A C A.data.tensorUnit U)
    {i : IsoData C.data C.data.tensorUnit (E.data.obj (spanGenerator A A.data.tensorUnit)).obj}
    (hi : EvenIsoLaws C.data i) :
    EvenIsoLaws C.data (rightUnitTensorComparisonData T H.data E.data i) :=
  ((H.mapEvenIsoLaws (X := rightUnitSpanObject A T) (Y := spanGenerator A T.data.object)
    (EvenIsoLaws.rightUnit A.laws _)).trans C.laws (EvenIsoLaws.rightUnit C.laws _).symm).trans C.laws
      ((EvenIsoLaws.refl C.laws _).tensor C.laws hi)

end RMod.Classification
