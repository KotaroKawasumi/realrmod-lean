import RMod.Classification.Proofs.GaugeParityDeletion

/-!
# The crossing sign in a triple gauge comparison

After the inner tensorator, deletion of its source tensor factor can
cross the third component deletion. The left route records precisely
that sign; the corresponding right route has an identity on the first
crossing factor. These are equalities of the specified raw maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem gaugeLocalTensorator_deletion_right_tensor (X Y Z : C.Obj) (a b c n' n d : ZMod 2)
    (e : (a + b) + n' = n + d) (beta : ℝˣ) :
    C.comp (C.comp
      (C.tensorHom (p.gaugeLocalTensorator X Y a b n' n d e beta).hom (C.id (C.tensorObj Z (p.factor c))))
      (C.tensorHom (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id (p.factor d)))
        (C.id (C.tensorObj Z (p.factor c)))))
      (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) d).hom (p.rightFactorDeletion Z c).hom) =
      C.smul (beta.val * (-1 : ℝ) ^ (a * b + c * n).val)
        (C.tensorHom
          (C.comp (C.tensorHom
            (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)
            (C.id (p.factor n'))) (p.rightFactorDeletion (C.tensorObj X Y) n').hom)
          (p.rightFactorDeletion Z c).hom) := by
  have hn : C.IsHomogeneous n
      (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id (p.factor d))) :=
    ((hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X Y) n).whiskerRight hC (p.factor d)).hom_grade
  rw [hC.comp_assoc,
    hC.super_interchange _ _ _ _ (hp.rightFactorDeletion_homogeneousIso hC Z c).hom_grade hn,
    hC.id_comp, hC.comp_smul,
    interchange_first_even hC _ _ _ _ (hp.gaugeLocalTensorator_evenIso hC X Y a b n' n d e beta).hom_even,
    hC.id_comp, hp.gaugeLocalTensorator_deletion_inputs hC, hC.tensor_smul_left, ← hC.mul_smul]
  congr 1
  rw [parity_power_add]
  ring

theorem gaugeLocalTensorator_deletion_left_tensor (X Y Z : C.Obj) (a b c n' n d : ZMod 2)
    (e : (b + c) + n' = n + d) (beta : ℝˣ) :
    C.comp (C.comp
      (C.tensorHom (C.id (C.tensorObj X (p.factor a))) (p.gaugeLocalTensorator Y Z b c n' n d e beta).hom)
      (C.tensorHom (C.id (C.tensorObj X (p.factor a)))
        (C.tensorHom (p.rightFactorDeletion (C.tensorObj Y Z) n).hom (C.id (p.factor d)))))
      (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion (C.tensorObj Y Z) d).hom) =
      C.smul (beta.val * (-1 : ℝ) ^ (b * c).val)
        (C.tensorHom (p.rightFactorDeletion X a).hom
          (C.comp (C.tensorHom
            (C.tensorHom (p.rightFactorDeletion Y b).hom (p.rightFactorDeletion Z c).hom)
            (C.id (p.factor n'))) (p.rightFactorDeletion (C.tensorObj Y Z) n').hom)) := by
  rw [hC.comp_assoc, interchange_first_even hC _ _ _ _ (hC.id_even _), hC.id_comp,
    interchange_first_even hC _ _ _ _ (hC.id_even _), hC.id_comp,
    hp.gaugeLocalTensorator_deletion_inputs hC, hC.tensor_smul_right]

end RMod.Classification.PiLaws
