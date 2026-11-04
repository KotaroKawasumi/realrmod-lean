import RMod.Classification.Instances.ComponentProduct
import RMod.Classification.Instances.TensorComparisonReindex
import RMod.Classification.Instances.TripleLeftComparison
import RMod.Classification.Instances.TripleRightComparison
import RMod.Classification.Proofs.ComponentTripleFunctor

/-!
# Both triple routes of a component system

Reindex the outer binary comparisons from the selected group generators
to the tensor constituents used by the inner comparison. The identity
span changes retain every ambient map. Associativity of the group then
identifies the right product functor with the same selected functor used
by the left route. Their degrees are the two sums in the cocycle equation.
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

noncomputable def componentTripleLeftComparison (g h k : G) :
    TripleComparison (S g) (S h) (S k) (T g) (T h) (T k)
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (componentTripleLeftFunctor d hS hT g h k) (ν g h + ν (g * h) k) := by
  let θ := TensorComparison.reindex (simpleTensorRepresentative A (S g) (S h)) (S k)
    (simpleTensorRepresentative C (T g) (T h)) (T k)
    (hS g h) (SameParityOrbit.refl A.laws _) (hT g h) (SameParityOrbit.refl C.laws _) (t (g * h) k)
  exact tripleLeftComparison (t g h) θ

noncomputable def componentTripleRightComparison (g h k : G) :
    TripleComparison (S g) (S h) (S k) (T g) (T h) (T k)
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (componentTripleLeftFunctor d hS hT g h k) (ν h k + ν g (h * k)) := by
  let θ := TensorComparison.reindex (S g) (simpleTensorRepresentative A (S h) (S k))
    (T g) (simpleTensorRepresentative C (T h) (T k))
    (SameParityOrbit.refl A.laws _) (hS h k) (SameParityOrbit.refl C.laws _) (hT h k) (t g (h * k))
  have q : TripleComparison (S g) (S h) (S k) (T g) (T h) (T k)
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (tripleRightFunctor (S g) (S h) (S k) (T g) (T h) (T k) (componentTripleRightFunctor d hS hT g h k))
      (ν h k + ν g (h * k)) := tripleRightComparison (t h k) θ
  rw [componentTripleFunctor_assoc] at q
  exact q

end RMod.Classification
