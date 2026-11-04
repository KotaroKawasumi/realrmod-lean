import RMod.Classification.Instances.ComponentPlacement
import RMod.Classification.Proofs.PullbackObjects

/-!
# Laws of placement in a group component

The only nonzero coordinate carries the original map, transported through
the defining object equality. Away from that coordinate the empty-sum
identity is zero. This proves the linear and graded functorial equations
and the specified component inclusion/projection identities.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (g : t.group)

theorem placedObj_at (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X) :
    (placedObj C hC t g X hX g).val = X := by
  simp [placedObj]

theorem placedObj_away (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
    (k : t.group) (hk : k ≠ g) : placedObj C hC t g X hX k = pullbackZeroObj C hC t k := by
  apply Subtype.ext
  simp [placedObj, hk]

variable {X Y Z : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
  (hY : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) Y)
  (hZ : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) Z)

theorem placedHom_id (k : t.group) :
    placedHom C hC t g hX hX (C.id X) k = C.id (placedObj C hC t g X hX k).val := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.id C.toWeaklyPointedSuperfusionData (by simp) _
  · simp only [placedHom, dif_neg hk]
    rw [placedObj_away C hC t g X hX k hk]
    exact (pullbackZero_id C hC t k).symm

theorem placedHom_comp (f : C.Hom X Y) (h : C.Hom Y Z) (k : t.group) :
    C.comp (placedHom C hC t g hX hY f k) (placedHom C hC t g hY hZ h k) =
      placedHom C hC t g hX hZ (C.comp f h) k := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.comp C.toWeaklyPointedSuperfusionData
      (by simp) (by simp) (by simp) _ _ _ f h
  · simp only [placedHom, dif_neg hk]
    exact raw_zero_comp hC.toWeaklyPointedSuperfusionLaws _

theorem placedHom_zero (k : t.group) : placedHom C hC t g hX hY C.zero k = C.zero := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.zero C.toWeaklyPointedSuperfusionData (by simp) (by simp) _
  · simp [placedHom, hk]

theorem placedHom_add (f h : C.Hom X Y) (k : t.group) :
    placedHom C hC t g hX hY (C.add f h) k =
      C.add (placedHom C hC t g hX hY f k) (placedHom C hC t g hX hY h k) := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.add C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ f h
  · simp only [placedHom, dif_neg hk, hC.zero_add]

theorem placedHom_smul (r : ℝ) (f : C.Hom X Y) (k : t.group) :
    placedHom C hC t g hX hY (C.smul r f) k = C.smul r (placedHom C hC t g hX hY f k) := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.smul C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ r f
  · simp only [placedHom, dif_neg hk, hC.smul_zero]

theorem placedHom_grade {a : ZMod 2} (f : C.Hom X Y) (hf : C.IsHomogeneous a f) (k : t.group) :
    C.IsHomogeneous a (placedHom C hC t g hX hY f k) := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [placedHom, placedObj]
    simp
    exact HomTransport.grade C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ f hf
  · simp only [placedHom, dif_neg hk]
    exact hC.grade_zero _ _ _

theorem componentInclusion_even (A : PullbackObj C t) (k : t.group) :
    C.IsHomogeneous 0 (componentInclusion C hC t g A k) := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [componentInclusion, placedObj]
    simp
    exact HomTransport.grade C.toWeaklyPointedSuperfusionData (by simp) rfl _
      (C.id (A g).val) (hC.id_even (A g).val)
  · simp only [componentInclusion, dif_neg hk]
    exact hC.grade_zero _ _ _

theorem componentProjection_even (A : PullbackObj C t) (k : t.group) :
    C.IsHomogeneous 0 (componentProjection C hC t g A k) := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [componentProjection, placedObj]
    simp
    exact HomTransport.grade C.toWeaklyPointedSuperfusionData rfl (by simp) _
      (C.id (A g).val) (hC.id_even (A g).val)
  · simp only [componentProjection, dif_neg hk]
    exact hC.grade_zero _ _ _

theorem component_inclusion_projection (A : PullbackObj C t) (k : t.group) :
    C.comp (componentInclusion C hC t g A k) (componentProjection C hC t g A k) =
      C.id (placedObj C hC t g (A g).val (A g).property k).val := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [componentInclusion, componentProjection, placedObj]
    simp
    have e : (A g).val = (if g = g then (A g).val else (pullbackZeroObj C hC t g).val) := by simp
    rw [HomTransport.comp C.toWeaklyPointedSuperfusionData e rfl e _ _
      (congrArg (fun T => C.Hom T T) e), hC.id_comp]
    exact HomTransport.id C.toWeaklyPointedSuperfusionData e _
  · simp only [componentInclusion, componentProjection, dif_neg hk, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]
    rw [placedObj_away C hC t g _ _ k hk]
    exact (pullbackZero_id C hC t k).symm

theorem component_projection_inclusion (A : PullbackObj C t) (k : t.group) :
    letI := Classical.decEq t.group
    C.comp (componentProjection C hC t g A k) (componentInclusion C hC t g A k) =
      if k = g then C.id (A k).val else C.zero := by
  classical
  by_cases hk : k = g
  · subst k
    dsimp only [componentInclusion, componentProjection, placedObj]
    simp
    have e : (A g).val = (if g = g then (A g).val else (pullbackZeroObj C hC t g).val) := by simp
    rw [HomTransport.comp C.toWeaklyPointedSuperfusionData rfl e rfl _ _ rfl, hC.id_comp]
    rfl
  · simp only [componentInclusion, componentProjection, dif_neg hk, if_neg hk,
      raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

theorem component_inclusion_projection_ne (A : PullbackObj C t) (h : t.group) (hgh : g ≠ h)
    (k : t.group) :
    C.comp (componentInclusion C hC t g A k) (componentProjection C hC t h A k) = C.zero := by
  classical
  by_cases hk : k = g
  · have hkh : k ≠ h := by simpa only [hk] using hgh
    have hz : componentProjection C hC t h A k = C.zero := by
      simp only [componentProjection, dif_neg hkh]
    rw [hz, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws]
  · have hz : componentInclusion C hC t g A k = C.zero := by
      simp only [componentInclusion, dif_neg hk]
    rw [hz, raw_zero_comp hC.toWeaklyPointedSuperfusionLaws]

end RMod.Classification
