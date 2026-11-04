import RMod.Classification.Instances.ComponentTripleFunctor
import RMod.Classification.Instances.TripleRightFunctor
import RMod.Classification.Proofs.SpanReindexFunctor

/-!
# Associativity identifies the two chosen triple product functors

All changes of component span are identities on ambient maps. Flatten
their reindexings, then use equality of the two group products in the
same selected family. This gives equality of completed functors, so no
additional parity or scalar comparison is introduced.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem componentTripleFunctor_assoc {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
    {S : G → SimpleObject A} {T : G → SimpleObject C}
    (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
    (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
      (S (g * h)).data.object)
    (hT : ∀ g h, SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
      (T (g * h)).data.object) (g h k : G) :
    tripleRightFunctor (S g) (S h) (S k) (T g) (T h) (T k) (componentTripleRightFunctor d hS hT g h k) =
      componentTripleLeftFunctor d hS hT g h k := by
  exact spanReindexSuperfunctor_index_eq S T (fun j => (d.component j).forwardFunctor)
    (simpleTensorRepresentative A (simpleTensorRepresentative A (S g) (S h)) (S k))
    (simpleTensorRepresentative C (simpleTensorRepresentative C (T g) (T h)) (T k))
    (g * (h * k)) ((g * h) * k) (mul_assoc g h k).symm
    (SameParityOrbit.trans A.laws (simpleTensorRepresentative_assoc A (S g) (S h) (S k))
      (componentTripleOrbit_right S hS g h k))
    (SameParityOrbit.trans C.laws (simpleTensorRepresentative_assoc C (T g) (T h) (T k))
      (componentTripleOrbit_right T hT g h k))
    (componentTripleOrbit_left S hS g h k) (componentTripleOrbit_left T hT g h k)

end RMod.Classification
