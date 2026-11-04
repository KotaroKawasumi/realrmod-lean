import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Abstract.HomogeneousIso
import RMod.Classification.Instances.SpanMapIso

/-! # The homogeneous isomorphism laws retained by comparison maps -/

set_option autoImplicit false

namespace RMod.Classification

theorem TensorComparison.homogeneousIsoLaws {A C : WeaklyPointedSuperfusion.{0, 0}}
    {S T : SimpleObject A} {U V : SimpleObject C}
    {E : SpanSuperfunctor A C S.data.object U.data.object}
    {H : SpanSuperfunctor A C T.data.object V.data.object}
    {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}
    (η : TensorComparison S T U V E H N a)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousIsoLaws C.data a (η.data.app X Y) :=
  ⟨η.laws.iso X Y, η.laws.hom_grade X Y, η.laws.inv_grade X Y⟩

theorem SpanSuperfunctor.mapHomogeneousIsoLaws {A C : WeaklyPointedSuperfusion.{0, 0}}
    {S : A.data.Obj} {T : C.data.Obj} (F : SpanSuperfunctor A C S T)
    {X Y : HomogeneousSpanCategory A S} {a : ZMod 2} {i : IsoData A.data X.obj Y.obj}
    (hi : HomogeneousIsoLaws A.data a i) :
    HomogeneousIsoLaws C.data a (SpanSuperfunctor.mapIsoData F.data i) :=
  ⟨F.mapIsoLaws hi.toIsoLaws, F.laws.map_grade _ hi.hom_grade, F.laws.map_grade _ hi.inv_grade⟩

end RMod.Classification
