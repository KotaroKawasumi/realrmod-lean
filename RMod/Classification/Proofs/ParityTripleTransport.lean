import RMod.Classification.Instances.ParityTripleTransportData
import RMod.Classification.Proofs.IsoNaturality

/-! # Transport of total parity preserves the actual even natural maps -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
  (e : a = b) (η : ParityTripleComparison S T R U V W p E H K N a)

theorem parityTripleTransportLaws : ParityTripleComparisonLaws S T R U V W
    (parityTripleTransportData e η.data) where
  iso X Y Z := (η.laws.iso X Y Z).trans C.laws (EvenIsoLaws.ofEq C.laws _)
  naturality f g h hf hg hh := iso_naturality_trans C.laws (η.laws.naturality f g h hf hg hh)
    (iso_naturality_tensor_ofEq C.laws (congrArg p.data.factor e)
      (C.data.tensorHom (E.data.map f).hom (C.data.tensorHom (H.data.map g).hom (K.data.map h).hom)))

end RMod.Classification
