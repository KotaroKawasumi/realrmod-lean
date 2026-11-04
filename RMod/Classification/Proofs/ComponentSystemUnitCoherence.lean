import RMod.Classification.Instances.ComponentSystemUnit
import RMod.Classification.Proofs.UnitTensorComparisonExtension

/-! # The canonical component-system unit comparisons agree at one -/

set_option autoImplicit false

namespace RMod.Classification.ComponentSystem

theorem unitComparisons_equal {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
    {S : G → SimpleObject A} {T : G → SimpleObject C}
    (d : ComponentSystem A C G (fun g => (S g).data.object) (fun g => (T g).data.object))
    (hS : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S 1)).data.object
      (S (1 * 1)).data.object)
    (hT : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T 1)).data.object
      (T (1 * 1)).data.object) :
    d.leftUnitComparison 1 hS hT = d.rightUnitComparison 1 hS hT := by
  have he :
      (fun (hA : SameParityOrbit A.data (simpleTensorRepresentative A (S 1) (S 1)).data.object (S 1).data.object)
        (hC : SameParityOrbit C.data (simpleTensorRepresentative C (T 1) (T 1)).data.object (T 1).data.object) =>
        leftUnitTensorComparison (S 1) (S 1) (T 1) (T 1) (d.component 1) (d.component 1)
          d.laws.unit_even (SimpleObject.ext d.laws.source_unit) hA hC) =
      (fun hA hC => rightUnitTensorComparison (S 1) (S 1) (T 1) (T 1) (d.component 1) (d.component 1)
        d.laws.unit_even (SimpleObject.ext d.laws.source_unit) hA hC) := by
    funext hA hC
    exact unitTensorComparisons_ofEq_equal (S 1) (T 1) (d.component 1) d.laws.unit_even
      (SimpleObject.ext d.laws.source_unit) hA hC
  unfold leftUnitComparison rightUnitComparison
  rw [he]

end RMod.Classification.ComponentSystem
