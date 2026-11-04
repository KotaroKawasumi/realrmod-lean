import RMod.Classification.Instances.PullbackObjects
import RMod.Classification.Proofs.Transport

/-!
# Laws for the supported pullback objects and morphisms

Extension by zero preserves identities, composition, real linear operations
and grading. The zero-coordinate identity is proved from the empty-sum law;
it is essential for the inverse equations outside the group identity.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem pullbackZero_id (g : t.group) :
    C.id (pullbackZeroObj C hC t g).val = C.zero :=
  ((finiteSumsLaws C hC.toWeaklyPointedSuperfusionLaws).sum
    (Fin.elim0 : Fin 0 → C.Obj)).total.symm

theorem supportedObj_one (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData 0 X) :
    (supportedObj C hC t X hX 1).val = X := by
  simp [supportedObj]

theorem supportedObj_ne_one (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData 0 X)
    (g : t.group) (hg : g ≠ 1) :
    supportedObj C hC t X hX g = pullbackZeroObj C hC t g := by
  apply Subtype.ext
  simp [supportedObj, hg]

variable {X Y Z : C.Obj}
  (hX : InComponent C.toWeaklyPointedSuperfusionData 0 X)
  (hY : InComponent C.toWeaklyPointedSuperfusionData 0 Y)
  (hZ : InComponent C.toWeaklyPointedSuperfusionData 0 Z)

theorem supportedHom_id (g : t.group) :
    supportedHom C hC t hX hX (C.id X) g = C.id (supportedObj C hC t X hX g).val := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.id C.toWeaklyPointedSuperfusionData (by simp) _
  · simp only [supportedHom, dif_neg hg]
    rw [supportedObj_ne_one C hC t X hX g hg]
    exact (pullbackZero_id C hC t g).symm

theorem supportedHom_comp (f : C.Hom X Y) (k : C.Hom Y Z) (g : t.group) :
    C.comp (supportedHom C hC t hX hY f g) (supportedHom C hC t hY hZ k g) =
      supportedHom C hC t hX hZ (C.comp f k) g := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.comp C.toWeaklyPointedSuperfusionData
      (by simp) (by simp) (by simp) _ _ _ f k
  · simp only [supportedHom, dif_neg hg]
    exact raw_zero_comp hC.toWeaklyPointedSuperfusionLaws _

theorem supportedHom_zero (g : t.group) :
    supportedHom C hC t hX hY C.zero g = C.zero := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.zero C.toWeaklyPointedSuperfusionData (by simp) (by simp) _
  · simp [supportedHom, hg]

theorem supportedHom_add (f k : C.Hom X Y) (g : t.group) :
    supportedHom C hC t hX hY (C.add f k) g =
      C.add (supportedHom C hC t hX hY f g) (supportedHom C hC t hX hY k g) := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.add C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ f k
  · simp only [supportedHom, dif_neg hg, hC.zero_add]

theorem supportedHom_smul (r : ℝ) (f : C.Hom X Y) (g : t.group) :
    supportedHom C hC t hX hY (C.smul r f) g =
      C.smul r (supportedHom C hC t hX hY f g) := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.smul C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ r f
  · simp only [supportedHom, dif_neg hg, hC.smul_zero]

theorem supportedHom_grade {a : ZMod 2} (f : C.Hom X Y)
    (hf : C.IsHomogeneous a f) (g : t.group) :
    C.IsHomogeneous a (supportedHom C hC t hX hY f g) := by
  classical
  by_cases hg : g = 1
  · subst g
    dsimp only [supportedHom, supportedObj]
    simp
    exact HomTransport.grade C.toWeaklyPointedSuperfusionData (by simp) (by simp) _ f hf
  · simp only [supportedHom, dif_neg hg]
    exact hC.grade_zero _ _ _

/-! The actual parity pair on the supported objects satisfies both inverse
equations and is odd in every coordinate. -/

theorem pullbackPi_hom_inv (g : t.group) :
    C.comp (pullbackPiHom C hC t g) (pullbackPiInv C hC t g) =
      C.id (pullbackPiObj C hC t g).val := by
  dsimp only [pullbackPiHom, pullbackPiInv, pullbackPiObj, pullbackUnitObj]
  rw [supportedHom_comp, hC.pi.hom_inv, supportedHom_id]

theorem pullbackPi_inv_hom (g : t.group) :
    C.comp (pullbackPiInv C hC t g) (pullbackPiHom C hC t g) =
      C.id (pullbackUnitObj C hC t g).val := by
  dsimp only [pullbackPiHom, pullbackPiInv, pullbackPiObj, pullbackUnitObj]
  rw [supportedHom_comp, hC.pi.inv_hom, supportedHom_id]

theorem pullbackPi_hom_odd (g : t.group) : C.IsHomogeneous 1 (pullbackPiHom C hC t g) :=
  supportedHom_grade C hC t _ _ C.pi.hom hC.pi.hom_odd g

theorem pullbackPi_inv_odd (g : t.group) : C.IsHomogeneous 1 (pullbackPiInv C hC t g) :=
  supportedHom_grade C hC t _ _ C.pi.inv hC.pi.inv_odd g

/-! Two nontrivial checks of the construction: the unit has nonzero identity
at the group identity, and the odd comparison there is nonzero. -/

example : C.id (pullbackUnitObj C hC t 1).val ≠ C.zero := by
  rw [pullbackUnitObj, supportedObj_one]
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hC.simple_unit

example : pullbackPiHom C hC t 1 ≠ C.zero := by
  intro hzero
  have h := pullbackPi_inv_hom C hC t 1
  rw [hzero, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws,
    pullbackUnitObj, supportedObj_one] at h
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hC.simple_unit h.symm

end RMod.Classification
