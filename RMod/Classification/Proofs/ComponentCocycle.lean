import RMod.Classification.Instances.ComponentTripleComparisons
import RMod.Classification.Proofs.TripleComparisonParity

/-!
# Binary comparison degrees satisfy the cocycle equation

The two actual associative routes compare the same triple product functor
with the same three component functors. The unique-parity theorem forces
their degrees to agree. Rearranging that equality in characteristic two
is precisely the normalized-cochain cocycle equation.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
  (hS : ∀ g h, SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S h)).data.object
    (S (g * h)).data.object)
  (hT : ∀ g h, SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T h)).data.object
    (T (g * h)).data.object)
  (ν : G → G → ZMod 2)
  (t : ∀ g h, TensorComparison (S g) (S h) (T g) (T h)
    (d.component g).forwardFunctor (d.component h).forwardFunctor
    (componentProductEquivalence d g h (hS g h) (hT g h)).forwardFunctor (ν g h))

include t

theorem componentNu_cocycle (g h k : G) : ν h k + ν (g * h) k + ν g (h * k) + ν g h = 0 := by
  have he := TripleComparison.parity_unique (d.component g) (d.component h) (d.component k)
    (componentTripleLeftComparison d hS hT ν t g h k) (componentTripleRightComparison d hS hT ν t g h k)
  calc
    _ = (ν g h + ν (g * h) k) + (ν h k + ν g (h * k)) := by ac_rfl
    _ = (ν h k + ν g (h * k)) + (ν h k + ν g (h * k)) := by rw [he]
    _ = 0 := CharTwo.add_self_eq_zero _

end RMod.Classification
