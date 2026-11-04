import RMod.Classification.Instances.ComponentProduct
import RMod.Classification.Instances.UnitTensorComparisonExtension
import RMod.Classification.Proofs.SimpleObjectExt

/-!
# Canonical unit comparisons of a component system

Reindex the product component by the group unit equations and use the
actual even unit comparison retained by the component system. The
result is the specified unitor extension, with no additional choice.
-/

set_option autoImplicit false

namespace RMod.Classification.ComponentSystem

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → SimpleObject A} {T : G → SimpleObject C}
  (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))

noncomputable def leftUnitComparison (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S g)).data.object
      (S (1 * g)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T g)).data.object
      (T (1 * g)).data.object) :
    TensorComparison (S 1) (S g) (T 1) (T g)
      (d.component 1).forwardFunctor (d.component g).forwardFunctor
      (componentProductEquivalence d 1 g hS hT).forwardFunctor 0 := by
  unfold componentProductEquivalence
  revert hS hT
  rw [one_mul]
  intro hS hT
  exact leftUnitTensorComparison (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) d.laws.unit_even (SimpleObject.ext d.laws.source_unit) hS hT

noncomputable def rightUnitComparison (g : G)
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S g) (S 1)).data.object
      (S (g * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T g) (T 1)).data.object
      (T (g * 1)).data.object) :
    TensorComparison (S g) (S 1) (T g) (T 1)
      (d.component g).forwardFunctor (d.component 1).forwardFunctor
      (componentProductEquivalence d g 1 hS hT).forwardFunctor 0 := by
  unfold componentProductEquivalence
  revert hS hT
  rw [mul_one]
  intro hS hT
  exact rightUnitTensorComparison (S 1) (S g) (T 1) (T g)
    (d.component 1) (d.component g) d.laws.unit_even (SimpleObject.ext d.laws.source_unit) hS hT

end RMod.Classification.ComponentSystem
