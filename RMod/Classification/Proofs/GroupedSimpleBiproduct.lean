import RMod.Classification.Instances.GroupedSimpleBiproduct
import RMod.Classification.Proofs.HomogeneousSpanBiproduct
import RMod.Classification.Proofs.HomogeneousSpanChange

/-! # Each grouped summand lies in its assigned simple component -/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : C.data.Obj}
  (d : SimpleDecomposition C X) {I : Type} [Fintype I] (S : I → C.data.Obj)
  (hS : ∀ i, C.data.IsSimple (S i)) (label : Fin d.data.size → I)
  (hlabel : ∀ j, SameParityOrbit C.data (S (label j)) (d.data.summand j))

include hS hlabel

omit [Fintype I] in
theorem groupedSimpleObject_mem (i : I) : InHomogeneousSpan C (S i) (groupedSimpleObject d label i).obj := by
  classical
  apply inHomogeneousSpan_even_biproduct C (hS i)
  intro j
  have hj := hlabel j.val
  rw [j.property] at hj
  exact (inHomogeneousSpan_congr_generator C (hS i) (d.laws.simple j.val) hj _).mpr
    (spanGenerator_mem C (d.data.summand j.val))

end RMod.Classification
