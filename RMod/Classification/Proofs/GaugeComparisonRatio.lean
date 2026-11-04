import RMod.Classification.Proofs.GaugeParityDeletion
import RMod.Classification.Proofs.WeightedPentagon

/-!
# The homogeneous comparison ratio of the prescribed gauge tensorator

Changing the three component functors by right-factor deletion compares
the inverse tensorator with the original tensor deletion. Its coefficient
is the inverse beta times a specific Koszul sign. This identifies the
convention needed when recovering beta from an arbitrary equivalence.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem gaugeLocalTensorator_comparison_ratio (X Y : C.Obj) (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (beta : ℝˣ) :
    C.comp (p.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) (p.factor n)) c).inv
      (C.comp (p.gaugeLocalTensorator X Y a b n' n c e beta).inv
        (C.comp (p.rightFactorDeletion
          (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))) n').hom
          (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom))) =
      C.smul ((beta⁻¹).val * (-1 : ℝ) ^ (a * b + (a + b) * n' + c * n).val)
        (p.rightFactorDeletion (C.tensorObj X Y) n).hom := by
  have hg := hp.gaugeLocalTensorator_deletion_tensor hC X Y a b n' n c e beta
  rw [hp.rightFactorDeletion_naturality hC c _
    (hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X Y) n).hom_grade,
    hC.comp_smul] at hg
  have he := congrArg (fun f =>
    C.comp (p.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) (p.factor n)) c).inv
      (C.comp (p.gaugeLocalTensorator X Y a b n' n c e beta).inv f)) hg
  simp only [hC.comp_smul, ← hC.comp_assoc,
    (hp.gaugeLocalTensorator_evenIso hC X Y a b n' n c e beta).inv_hom,
    (hp.rightFactorDeletion_homogeneousIso hC
      (C.tensorObj (C.tensorObj X Y) (p.factor n)) c).inv_hom,
    hC.id_comp] at he
  let q := a * b + (a + b) * n'
  have hc : ((beta⁻¹).val * (-1 : ℝ) ^ q.val) *
      (beta.val * (-1 : ℝ) ^ q.val) = 1 := by
    calc
      _ = ((beta⁻¹).val * beta.val) *
          ((-1 : ℝ) ^ q.val * (-1 : ℝ) ^ q.val) := by ring
      _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one,
        parity_power_mul_self, mul_one]
  have hh := congrArg (C.smul ((beta⁻¹).val * (-1 : ℝ) ^ q.val)) he
  rw [← hC.mul_smul, ← hC.mul_smul, hc, hC.one_smul] at hh
  simpa only [q, parity_power_add, hC.comp_assoc, mul_assoc] using hh.symm

end RMod.Classification.PiLaws
