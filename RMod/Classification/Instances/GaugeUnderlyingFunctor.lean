import RMod.Classification.Instances.TwistedPullback
import RMod.Classification.Proofs.TensorCalculus

/-!
# The actual underlying functor of a reindexed parity gauge

At target degree k, take the source coordinate phi inverse(k) and tensor
its object and every morphism on the right with the prescribed parity
factor. Only rho compatibility is needed for this superlinear functor;
the tensorator and its coherence use the remaining gauge equations.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (φ : s.data.group ≃* t.data.group) (lam : s.data.group → ZMod 2)
  (hρ : ∀ g, t.data.rho (φ g) = s.data.rho g)

noncomputable def gaugeUnderlyingFunctorData :
    SuperfunctorData (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData where
  obj X k := ⟨C.tensorObj (X (φ.symm k)).val (C.pi.factor (lam (φ.symm k))), by
    have hm := InComponent.tensor hC (X (φ.symm k)).property
      (InComponent.parity_factor hC (lam (φ.symm k)))
    rw [add_zero] at hm
    have hr := congrArg Multiplicative.toAdd (hρ (φ.symm k))
    rw [φ.apply_symm_apply] at hr
    exact Eq.mp (congrArg (fun r => InComponent C.toWeaklyPointedSuperfusionData r
      (C.tensorObj (X (φ.symm k)).val (C.pi.factor (lam (φ.symm k))))) hr.symm) hm⟩
  map f k := C.tensorHom (f (φ.symm k)) (C.id (C.pi.factor (lam (φ.symm k))))

theorem gaugeUnderlyingFunctorLaws :
    SuperfunctorLaws (twistedPullback C hC s).data.toWeaklyPointedSuperfusionData
      (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
      (gaugeUnderlyingFunctorData C hC s t φ lam hρ) where
  map_id X := by
    funext k
    exact hC.tensor_id _ _
  map_comp f g := by
    funext k
    change C.tensorHom (C.comp (f (φ.symm k)) (g (φ.symm k))) (C.id _) =
      C.comp (C.tensorHom (f (φ.symm k)) (C.id _)) (C.tensorHom (g (φ.symm k)) (C.id _))
    rw [interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _), hC.id_comp]
  map_zero X Y := by
    funext k
    exact tensor_zero_left hC.toWeaklyPointedSuperfusionLaws _
  map_add f g := by
    funext k
    exact hC.tensor_add_left _ _ _
  map_smul r f := by
    funext k
    exact hC.tensor_smul_left r _ _
  map_grade f hf := by
    intro k
    have h := hC.tensor_grade _ _ (hf (φ.symm k)) (hC.id_even (C.pi.factor (lam (φ.symm k))))
    rw [add_zero] at h
    exact h

noncomputable def gaugeUnderlyingFunctor :
    Superfunctor (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion :=
  ⟨gaugeUnderlyingFunctorData C hC s t φ lam hρ, gaugeUnderlyingFunctorLaws C hC s t φ lam hρ⟩

end RMod.Classification
