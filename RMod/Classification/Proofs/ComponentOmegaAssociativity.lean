import RMod.Classification.Instances.ComponentTripleTensorators
import RMod.Classification.Proofs.ComponentOmega
import RMod.Classification.Proofs.ParityTensoratorFunctorEquality

/-!
# The extracted component omega satisfies the tensorator associativity diagram

Apply normal-form cancellation after identifying the two product functors.
This is the precise local diagram used on each edge of the transported
pentagon; both tensorators and the mapped source associator are retained.
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

theorem componentOmega_associativity (g h k : G)
    (X : HomogeneousSpanCategory A (S g).data.object)
    (Y : HomogeneousSpanCategory A (S h).data.object)
    (Z : HomogeneousSpanCategory A (S k).data.object) :
    C.data.comp (componentTripleLeftTensorator p d hS hT ν t g h k X Y Z).hom
      (componentMappedTripleAssociator d hS hT g h k X Y Z).hom =
      C.data.comp (p.data.localAssociator
        ((d.component g).forwardFunctor.data.obj X).obj
        ((d.component h).forwardFunctor.data.obj Y).obj
        ((d.component k).forwardFunctor.data.obj Z).obj
        (ν g h) (ν (g * h) k) (ν h k) (ν g (h * k))
        (componentTripleParity d hS hT ν t g h k) (componentOmega p d hS hT ν t g h k)).hom
        (componentTripleRightTensorator p d hS hT ν t g h k X Y Z).hom := by
  let θL := TensorComparison.reindex (simpleTensorRepresentative A (S g) (S h)) (S k)
    (simpleTensorRepresentative C (T g) (T h)) (T k)
    (hS g h) (SameParityOrbit.refl A.laws _) (hT g h) (SameParityOrbit.refl C.laws _) (t (g * h) k)
  let θR := TensorComparison.reindex (S g) (simpleTensorRepresentative A (S h) (S k))
    (T g) (simpleTensorRepresentative C (T h) (T k))
    (SameParityOrbit.refl A.laws _) (hS h k) (SameParityOrbit.refl C.laws _) (hT h k) (t g (h * k))
  exact parityTensorator_associativity_of_functor_eq
    (parityTensorComparison p (t g h)) (parityTensorComparison p θL)
    (parityTensorComparison p (t h k)) (parityTensorComparison p θR)
    (componentTripleFunctor_assoc d hS hT g h k) (componentTripleParity d hS hT ν t g h k)
    (componentOmega p d hS hT ν t g h k) X Y Z (componentOmega_spec p d hS hT ν t g h k X Y Z)

end RMod.Classification
