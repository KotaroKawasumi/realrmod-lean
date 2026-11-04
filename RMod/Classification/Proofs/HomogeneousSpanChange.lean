import RMod.Classification.Proofs.HomogeneousSpanMembership

/-!
# Changing the simple generator does not change its component

The simple-decomposition characterization of membership shows that two
simple generators in the same parity orbit define the same full span.
This is equality of the actual object properties, not just a new
equivalence chosen from their Brauer--Wall types.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem inHomogeneousSpan_congr_generator (C : WeaklyPointedSuperfusion.{0, 0})
    {S T : C.data.Obj} (hS : C.data.IsSimple S) (hT : C.data.IsSimple T)
    (hST : SameParityOrbit C.data S T) (X : C.data.Obj) :
    InHomogeneousSpan C S X ↔ InHomogeneousSpan C T X := by
  let d := simpleDecomposition C X
  rw [inHomogeneousSpan_iff_simple_decomposition C hS d.toDecomposition d.laws.simple,
    inHomogeneousSpan_iff_simple_decomposition C hT d.toDecomposition d.laws.simple]
  exact ⟨fun h i => SameParityOrbit.trans C.laws hST.symm (h i),
    fun h i => SameParityOrbit.trans C.laws hST (h i)⟩

end RMod.Classification
