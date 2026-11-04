import RMod.Classification.Instances.SpanReindexFunctor
import RMod.Classification.Instances.TensorProductTransport

/-!
# Identity span changes compose without altering a functor

Membership witnesses are propositions, so the identity inclusions compose
definitionally on every ambient object and map. Reindexing therefore
depends only on the specified functor and its final source and target
spans. In particular equal family indices give equal completed functors.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}

theorem spanReindexSuperfunctor_self (S : SimpleObject A) (T : SimpleObject C)
    (hS : SameParityOrbit A.data S.data.object S.data.object)
    (hT : SameParityOrbit C.data T.data.object T.data.object)
    (F : SpanSuperfunctor A C S.data.object T.data.object) :
    spanReindexSuperfunctor S T S T hS hT F = F := rfl

theorem spanReindexSuperfunctor_trans
    (S U R : SimpleObject A) (T V W : SimpleObject C)
    (hSU : SameParityOrbit A.data U.data.object S.data.object)
    (hTV : SameParityOrbit C.data V.data.object T.data.object)
    (hUR : SameParityOrbit A.data R.data.object U.data.object)
    (hVW : SameParityOrbit C.data W.data.object V.data.object)
    (F : SpanSuperfunctor A C S.data.object T.data.object) :
    spanReindexSuperfunctor U V R W hUR hVW (spanReindexSuperfunctor S T U V hSU hTV F) =
      spanReindexSuperfunctor S T R W (SameParityOrbit.trans A.laws hUR hSU)
        (SameParityOrbit.trans C.laws hVW hTV) F := rfl

theorem spanReindexSuperfunctor_index_eq {G : Type} (S : G → SimpleObject A) (T : G → SimpleObject C)
    (F : ∀ g, SpanSuperfunctor A C (S g).data.object (T g).data.object)
    (U : SimpleObject A) (V : SimpleObject C) (g h : G) (he : g = h)
    (hSg : SameParityOrbit A.data U.data.object (S g).data.object)
    (hTg : SameParityOrbit C.data V.data.object (T g).data.object)
    (hSh : SameParityOrbit A.data U.data.object (S h).data.object)
    (hTh : SameParityOrbit C.data V.data.object (T h).data.object) :
    spanReindexSuperfunctor (S g) (T g) U V hSg hTg (F g) =
      spanReindexSuperfunctor (S h) (T h) U V hSh hTh (F h) := by
  subst h
  rfl

theorem tensorProductTransport_forward (S T R : SimpleObject A) (U V W : SimpleObject C)
    (F : SpanSuperequivalence A C R.data.object W.data.object)
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S T).data.object R.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object W.data.object) :
    (tensorProductTransport S T R U V W F hA hC).forwardFunctor =
      spanReindexSuperfunctor R W (simpleTensorRepresentative A S T)
        (simpleTensorRepresentative C U V) hA hC F.forwardFunctor := rfl

end RMod.Classification
