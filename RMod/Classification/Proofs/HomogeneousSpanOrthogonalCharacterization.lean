import RMod.Classification.Proofs.HomogeneousSpanOrthogonality
import RMod.Classification.Proofs.HomogeneousSpanMembership
import RMod.Classification.Instances.SpanGenerator

/-!
# Orthogonality characterizes a homogeneous simple component

If a simple summand outside the generator's parity orbit occurred, its
nonzero inclusion would contradict orthogonality. This characterization
allows component closure to be proved without choosing new presentations.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem inHomogeneousSpan_iff_orthogonal {S X : C.data.Obj} (hS : C.data.IsSimple S) :
    InHomogeneousSpan C S X ↔ ∀ T, C.data.IsSimple T → ¬ SameParityOrbit C.data S T →
      ∀ f : C.data.Hom T X, f = C.data.zero := by
  constructor
  · intro hX T hT hST f
    exact hom_zero_of_distinct_spans C hT hS (fun h => hST h.symm) (spanGenerator_mem C T) hX f
  · intro h
    let d := simpleDecomposition C X
    apply (inHomogeneousSpan_iff_simple_decomposition C hS d.toDecomposition d.laws.simple).mpr
    intro i
    by_contra hn
    have hz := h (d.data.summand i) (d.laws.simple i) hn (d.data.decomposition.inclusion i)
    apply simple_id_ne_zero C.laws (d.laws.simple i)
    rw [← d.laws.decomposition.diagonal i, hz, raw_zero_comp C.laws]

end RMod.Classification
