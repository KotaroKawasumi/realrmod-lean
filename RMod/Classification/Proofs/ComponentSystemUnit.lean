import RMod.Classification.Instances.ComponentProduct
import RMod.Classification.Proofs.UnitTensorIntertwiner

/-!
# Even multiplication comparisons at the identity of a component system

The product component at one is the other component itself. Its unit
comparison and the actual unit generator therefore give an even tensor
comparison on either side, without imposing any condition on a selected
binary comparison's degree.
-/

set_option autoImplicit false

namespace RMod.Classification.ComponentSystem

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

theorem exists_leftUnitComparison (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object) :
    Nonempty (TensorComparison (S 1) (S g) (T 1) (T g)
      (d.component 1).forwardFunctor (d.component g).forwardFunctor
      (componentProductEquivalence d 1 g hS hT).forwardFunctor 0) := by
  unfold componentProductEquivalence
  revert hS hT
  rw [one_mul]
  intro hS hT
  exact exists_leftUnitTensorComparison (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) d.laws.unit_even (SimpleObject.ext d.laws.source_unit) _ _

theorem exists_rightUnitComparison (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object) :
    Nonempty (TensorComparison (S g) (S 1) (T g) (T 1)
      (d.component g).forwardFunctor (d.component 1).forwardFunctor
      (componentProductEquivalence d g 1 hS hT).forwardFunctor 0) := by
  unfold componentProductEquivalence
  revert hS hT
  rw [mul_one]
  intro hS hT
  exact exists_rightUnitTensorComparison (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) d.laws.unit_even (SimpleObject.ext d.laws.source_unit) _ _

end RMod.Classification.ComponentSystem
