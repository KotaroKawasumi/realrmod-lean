import RMod.Classification.Instances.ComponentParityTriples
import RMod.Classification.Instances.MappedTripleAssociator

/-!
# The two component tensorators and their mapped source associator

These are the actual maps before the normalizers used to define omega.
Their intermediate component functors are identified by intrinsic group
associativity, with the corresponding equality isomorphism retained.
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

noncomputable def componentTripleLeftTensorator (g h k : G)
    (X : HomogeneousSpanCategory A (S g).data.object)
    (Y : HomogeneousSpanCategory A (S h).data.object)
    (Z : HomogeneousSpanCategory A (S k).data.object) :=
  let θ := TensorComparison.reindex (simpleTensorRepresentative A (S g) (S h)) (S k)
    (simpleTensorRepresentative C (T g) (T h)) (T k)
    (hS g h) (SameParityOrbit.refl A.laws _) (hT g h) (SameParityOrbit.refl C.laws _) (t (g * h) k)
  parityTripleLeftTensorator (S g) (S h) (S k) (T g) (T h) (T k)
    (parityTensorComparison p (t g h)).data (parityTensorComparison p θ).data X Y Z

noncomputable def componentTripleRightTensorator (g h k : G)
    (X : HomogeneousSpanCategory A (S g).data.object)
    (Y : HomogeneousSpanCategory A (S h).data.object)
    (Z : HomogeneousSpanCategory A (S k).data.object) :=
  let θ := TensorComparison.reindex (S g) (simpleTensorRepresentative A (S h) (S k))
    (T g) (simpleTensorRepresentative C (T h) (T k))
    (SameParityOrbit.refl A.laws _) (hS h k) (SameParityOrbit.refl C.laws _) (hT h k) (t g (h * k))
  parityTripleRightTensorator (S g) (S h) (S k) (T g) (T h) (T k)
    (parityTensorComparison p (t h k)).data (parityTensorComparison p θ).data X Y Z

noncomputable def componentMappedTripleAssociator (g h k : G)
    (X : HomogeneousSpanCategory A (S g).data.object)
    (Y : HomogeneousSpanCategory A (S h).data.object)
    (Z : HomogeneousSpanCategory A (S k).data.object) :=
  mappedTripleAssociatorData (S g) (S h) (S k) (T g) (T h) (T k)
    (componentTripleRightFunctor d hS hT g h k) (componentTripleLeftFunctor d hS hT g h k)
    (componentTripleFunctor_assoc d hS hT g h k) X Y Z

end RMod.Classification
