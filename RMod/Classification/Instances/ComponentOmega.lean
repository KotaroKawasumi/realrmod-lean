import RMod.Classification.Instances.ComponentNormalizedTriples
import RMod.Classification.Proofs.ParityTripleUniqueness

/-!
# Extracting the associator scalar from the actual normalizations

The right route is omega times the left route after identifying the two
total parities. The comparison theorem supplies a unique real unit on
all triples of objects. This definition therefore uses the specified
right-factor normalizers, including their crossing and contraction signs.
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

noncomputable def componentOmega (g h k : G) : ℝˣ :=
  (ParityTripleComparison.comparison_eq_unique_unit_smul (d.component g) (d.component h) (d.component k)
    (componentNormalizedLeft p d hS hT ν t g h k) (componentParityTripleRight p d hS hT ν t g h k)).choose

end RMod.Classification
