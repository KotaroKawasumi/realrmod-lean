import RMod.Classification.Instances.ComponentProduct
import RMod.Classification.Instances.TensorComparisonReindex
import RMod.Classification.Instances.ParityTripleLeft
import RMod.Classification.Instances.ParityTripleRight
import RMod.Classification.Proofs.ComponentTripleFunctor
import RMod.Classification.Instances.ParityTensorComparison

/-!
# Component tensorators followed by the actual normalizers

Reindex the outer homogeneous comparisons and convert them to even
right-parity tensorators. The left and right constructions then retain
the exact L and R maps used in the manuscript's associator convention.
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

noncomputable def componentParityTripleLeft (g h k : G) :
    ParityTripleComparison (S g) (S h) (S k) (T g) (T h) (T k) p
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (componentTripleLeftFunctor d hS hT g h k) (ν g h + ν (g * h) k) := by
  let θ := TensorComparison.reindex (simpleTensorRepresentative A (S g) (S h)) (S k)
    (simpleTensorRepresentative C (T g) (T h)) (T k)
    (hS g h) (SameParityOrbit.refl A.laws _) (hT g h) (SameParityOrbit.refl C.laws _) (t (g * h) k)
  exact parityTripleLeft (parityTensorComparison p (t g h)) (parityTensorComparison p θ)

noncomputable def componentParityTripleRight (g h k : G) :
    ParityTripleComparison (S g) (S h) (S k) (T g) (T h) (T k) p
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (componentTripleLeftFunctor d hS hT g h k) (ν h k + ν g (h * k)) := by
  let θ := TensorComparison.reindex (S g) (simpleTensorRepresentative A (S h) (S k))
    (T g) (simpleTensorRepresentative C (T h) (T k))
    (SameParityOrbit.refl A.laws _) (hS h k) (SameParityOrbit.refl C.laws _) (hT h k) (t g (h * k))
  have q : ParityTripleComparison (S g) (S h) (S k) (T g) (T h) (T k) p
      (d.component g).forwardFunctor (d.component h).forwardFunctor (d.component k).forwardFunctor
      (tripleRightFunctor (S g) (S h) (S k) (T g) (T h) (T k) (componentTripleRightFunctor d hS hT g h k))
      (ν h k + ν g (h * k)) := parityTripleRight (parityTensorComparison p (t h k)) (parityTensorComparison p θ)
  rw [componentTripleFunctor_assoc] at q
  exact q

end RMod.Classification
