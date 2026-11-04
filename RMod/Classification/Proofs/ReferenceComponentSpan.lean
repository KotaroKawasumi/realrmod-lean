import RMod.Classification.Proofs.HomogeneousSpanMembership
import RMod.Classification.Proofs.Components
import RMod.Classification.Instances.ReferenceSimpleRepresentatives

/-!
# Reference type components are the chosen simple homogeneous spans

The reference property identifies the type of each simple summand with
its parity orbit. Apply this to an actual even simple decomposition to
identify the pullback carrier with the domains of the chosen component
equivalences, including the zero object and arbitrary finite sums.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

include hC

theorem inComponent_iff_homogeneousSpan {S X : C.data.Obj} {r : ZMod 8}
    (hS : C.data.IsSimple S) (hr : HasBWType C.toWeaklyPointedSuperfusion.data S r) :
    InComponent C.toWeaklyPointedSuperfusion.data r X ↔
      InHomogeneousSpan C.toWeaklyPointedSuperfusion S X := by
  constructor
  · rintro ⟨n, V, hV, hD⟩
    obtain ⟨d⟩ := (hasDecomposition_iff C.toWeaklyPointedSuperfusion X V).mp hD
    apply (inHomogeneousSpan_iff_simple_decomposition C.toWeaklyPointedSuperfusion hS d
      (fun i => (hV i).1)).mpr
    intro i
    exact (hC.type_detects_orbit S (V i) r hS (hV i).1 hr).mp (hV i).2
  · intro hX
    let d := simpleDecomposition C.toWeaklyPointedSuperfusion X
    have ho := (inHomogeneousSpan_iff_simple_decomposition C.toWeaklyPointedSuperfusion hS
      d.toDecomposition d.laws.simple).mp hX
    refine ⟨d.data.size, d.data.summand, ?_, d.hasDecomposition⟩
    intro i
    exact ⟨d.laws.simple i,
      (hC.type_detects_orbit S (d.data.summand i) r hS (d.laws.simple i) hr).mpr (ho i)⟩

theorem reference_component_iff_span (r : ZMod 8) (X : C.data.Obj) :
    InComponent C.toWeaklyPointedSuperfusion.data r X ↔
      InHomogeneousSpan C.toWeaklyPointedSuperfusion (referenceSimpleRepresentative C hC r).data.object X :=
  inComponent_iff_homogeneousSpan C hC (referenceSimpleRepresentative C hC r).laws.simple
    (referenceSimpleRepresentative_type C hC r)

end RMod.Classification
