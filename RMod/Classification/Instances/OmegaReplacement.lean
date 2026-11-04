import RMod.Classification.Instances.TwistedPullback
import RMod.Classification.Abstract.Equivalence
import RMod.Classification.Instances.TwistOmegaReplacement

/-!
# Changing only the associator cochain

Keep the finite group, type homomorphism and binary parity cochain. The
completed replacement receives its laws separately. Its underlying real
supercategory is definitionally the same, so both directions of the
underlying comparison preserve objects and full Hom maps literally.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (omega : t.data.group → t.data.group → t.data.group → ℝˣ)
  (h : TwistLaws (omegaReplacementData t.data omega))

def omegaReplacementForwardData :
    SuperfunctorData (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData where
  obj X k := ⟨(X k).val, (X k).property⟩
  map f k := f k

def omegaReplacementBackwardData :
    SuperfunctorData (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData where
  obj X k := ⟨(X k).val, (X k).property⟩
  map f k := f k


theorem omegaReplacementForwardLaws :
    SuperfunctorLaws (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData
      (omegaReplacementForwardData C hC t omega h) where
  map_id _ := funext fun _ => rfl
  map_comp _ _ := funext fun _ => rfl
  map_zero _ _ := funext fun _ => rfl
  map_add _ _ := funext fun _ => rfl
  map_smul _ _ := funext fun _ => rfl
  map_grade _ hf := fun k => hf k

theorem omegaReplacementBackwardLaws :
    SuperfunctorLaws (twistedPullback C hC (omegaReplacement t omega h)).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (omegaReplacementBackwardData C hC t omega h) where
  map_id _ := funext fun _ => rfl
  map_comp _ _ := funext fun _ => rfl
  map_zero _ _ := funext fun _ => rfl
  map_add _ _ := funext fun _ => rfl
  map_smul _ _ := funext fun _ => rfl
  map_grade _ hf := fun k => hf k

def omegaReplacementForward :
    Superfunctor (twistedPullback C hC t).toWeaklyPointedSuperfusion
      (twistedPullback C hC (omegaReplacement t omega h)).toWeaklyPointedSuperfusion where
  data := omegaReplacementForwardData C hC t omega h
  laws := omegaReplacementForwardLaws C hC t omega h

def omegaReplacementBackward :
    Superfunctor (twistedPullback C hC (omegaReplacement t omega h)).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion where
  data := omegaReplacementBackwardData C hC t omega h
  laws := omegaReplacementBackwardLaws C hC t omega h

end RMod.Classification
