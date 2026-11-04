import RMod.Classification.Instances.ComponentParityTriples
import RMod.Classification.Instances.ParityTripleTransport
import RMod.Classification.Proofs.ComponentTripleParity

/-!
# Both actual component routes with the same normal form

The two-cocycle equality identifies the left total parity with the right
total parity. Its identity isomorphism is inserted after L, exactly as
in the pullback model's local associator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (p : Pi C.data)
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
  (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
    (S (g * h)).data.object)
  (hT : ∀ g h, SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
    (T (g * h)).data.object)
  (ν : G → G → ZMod 2)
  (t : ∀ g h, TensorComparison (S g) (S h) (T g) (T h)
    (d.component g).forwardFunctor (d.component h).forwardFunctor
    (componentProductEquivalence d g h (hS g h) (hT g h)).forwardFunctor (ν g h))

noncomputable def componentNormalizedLeft (g h k : G) :
    ParityTripleComparison (S g) (S h) (S k) (T g) (T h) (T k) p
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (componentTripleLeftFunctor d hS hT g h k) (ν h k + ν g (h * k)) :=
  parityTripleTransport (componentTripleParity d hS hT ν t g h k)
    (componentParityTripleLeft p d hS hT ν t g h k)

end RMod.Classification
