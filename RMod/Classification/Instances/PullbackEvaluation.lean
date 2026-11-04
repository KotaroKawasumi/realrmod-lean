import RMod.Classification.Instances.TwistedPullback
import RMod.Classification.Abstract.Equivalence

/-!
# Evaluation of a pullback object at a fixed group coordinate

The underlying category is a product of full reference components.
Evaluation therefore preserves identities, composition, all real-linear
operations and every homogeneous degree by their specified pointwise
formulas. It need not preserve tensor products.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist) (g : t.data.group)

def pullbackEvaluationData : SuperfunctorData
    (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData C.toWeaklyPointedSuperfusionData where
  obj X := (X g).val
  map f := f g

theorem pullbackEvaluationLaws : SuperfunctorLaws
    (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData C.toWeaklyPointedSuperfusionData
    (pullbackEvaluationData C hC t g) where
  map_id _ := rfl
  map_comp _ _ := rfl
  map_zero _ _ := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_grade _ hf := hf g

def pullbackEvaluation : Superfunctor (twistedPullback C hC t).toWeaklyPointedSuperfusion
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ :=
  ⟨pullbackEvaluationData C hC t g, pullbackEvaluationLaws C hC t g⟩

end RMod.Classification
