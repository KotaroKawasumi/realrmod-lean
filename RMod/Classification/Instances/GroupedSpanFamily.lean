import RMod.Classification.Proofs.GroupedSimpleBiproduct
import RMod.Classification.Abstract.SpanFamily

/-! # The completed family of grouped simple components -/

set_option autoImplicit false

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : C.data.Obj}
  (d : SimpleDecomposition C X) {I : Type} [Fintype I] (S : I → C.data.Obj)
  (hS : ∀ i, C.data.IsSimple (S i)) (label : Fin d.data.size → I)
  (hlabel : ∀ j, SameParityOrbit C.data (S (label j)) (d.data.summand j))

noncomputable def groupedSpanFamily : SpanFamilyCategory C S := fun i =>
  ⟨(groupedSimpleObject d label i).obj, groupedSimpleObject_mem d S hS label hlabel i⟩

end RMod.Classification
