import RMod.Classification.Instances.SimpleRetractRefl
import RMod.Classification.Instances.SimpleOrbits
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanEquivalenceComposition
import RMod.Classification.Proofs.SpanComparisonRealization
import RMod.Classification.Proofs.SpanTargetOrbit
import RMod.Classification.Proofs.IsoCalculus
import RMod.Classification.Proofs.Endomorphisms

/-!
# A unit-component equivalence with an even unit comparison

Identify the two split unit endomorphism algebras through the real
scalars. Realize this algebra equivalence at the actual tensor units,
using their identity retracts. The resulting even object comparison
places the target in the unit span; changing that span preserves every
ambient map and retains the specified even unit isomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem unitEndComparison_grade_iff (C D : WeaklyPointedSuperfusion.{0, 0})
    {a : ZMod 2} (f : @End (LinearCategory C) _ C.data.tensorUnit) :
    D.data.IsHomogeneous a (((unitEndEquiv C).symm.trans (unitEndEquiv D)) f) ↔
      C.data.IsHomogeneous a f := by
  rcases parity_cases a with rfl | rfl
  · exact ⟨fun _ => unit_end_even C f, fun _ => unit_end_even D _⟩
  · rw [unit_end_odd_iff D, unit_end_odd_iff C]
    exact map_eq_zero_iff _ ((unitEndEquiv C).symm.trans (unitEndEquiv D)).injective

theorem exists_unitComponentComparison (C D : PiSuperfusion.{0, 0}) :
    ∃ (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      C.data.tensorUnit D.data.tensorUnit)
      (i : IsoData D.data.toWeaklyPointedSuperfusionData D.data.tensorUnit
        (E.forwardFunctor.data.obj (spanGenerator C.toWeaklyPointedSuperfusion C.data.tensorUnit)).obj),
      EvenIsoLaws D.data.toWeaklyPointedSuperfusionData i := by
  let φ := (unitEndEquiv C.toWeaklyPointedSuperfusion).symm.trans (unitEndEquiv D.toWeaklyPointedSuperfusion)
  let X := spanGenerator C.toWeaklyPointedSuperfusion C.data.tensorUnit
  let Y := spanGenerator D.toWeaklyPointedSuperfusion D.data.tensorUnit
  obtain ⟨R, M, e, he, _⟩ := exists_spanComparison_realizing_algebra C D
    C.data.tensorUnit D.data.tensorUnit (simpleRetractRefl (unitSimple C.toWeaklyPointedSuperfusion))
    X.property φ (fun f => unitEndComparison_grade_iff C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion f)
  have hMX := inHomogeneousSpan_of_retract D.toWeaklyPointedSuperfusion D.laws.simple_unit Y.property
    e.hom e.inv he.hom_inv he.hom_even
  have hR := span_target_orbit_of_retract C.laws.simple_unit R.laws.simple D.laws.simple_unit
    M X (𝟙 X) (𝟙 X) (Category.id_comp _) (C.laws.id_even _) hMX
  let J := spanChangeSuperequivalence D.toWeaklyPointedSuperfusion
    (inHomogeneousSpan_congr_generator D.toWeaklyPointedSuperfusion R.laws.simple D.laws.simple_unit hR)
  exact ⟨M.trans J, e.symm D.data.toWeaklyPointedSuperfusionData, he.symm⟩

end RMod.Classification
