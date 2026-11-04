import RMod.Classification.Proofs.OrderedParityDeletion
import RMod.Classification.Proofs.GaugeTensorDeletion
import RMod.Classification.Proofs.GaugeLocalNaturality

/-!
# The right triple gauge route after ordered deletion

The right route has no crossing in the inner gauge comparison. When
the target inner parity deletion is separated from the first component
deletion, signed interchange contributes their product. The resulting
formula uses the original ordered right triple deletion.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem gaugeTripleRight_deletion (X Y Z : C.Obj) (a b c e f r s r' s' : ZMod 2)
    (e₁ : (b + c) + r' = r + e) (e₂ : (a + e) + s' = s + f) (beta₁ beta₂ : ℝˣ) :
    C.comp (C.comp
      (C.tensorHom (C.tensorHom (C.id (C.tensorObj X (p.factor a)))
        (p.gaugeLocalTensorator Y Z b c r' r e e₁ beta₁).hom) (C.id (p.factor s')))
      (p.gaugeLocalTensorator X (C.tensorObj (C.tensorObj Y Z) (p.factor r)) a e s' s f e₂ beta₂).hom)
      (p.orderedOutputDeletion X Y Z r s f).hom =
      C.smul (beta₁.val * beta₂.val * (-1 : ℝ) ^ (b * c + a * e + a * r').val)
        (C.comp (C.tensorHom (C.tensorHom (p.rightFactorDeletion X a).hom
          (C.tensorHom (C.tensorHom (p.rightFactorDeletion Y b).hom (p.rightFactorDeletion Z c).hom)
            (C.id (p.factor r')))) (C.id (p.factor s')))
          (p.orderedRightDeletion X Y Z r' s').hom) := by
  let W := C.tensorObj Y Z
  let Q := C.tensorObj X W
  let Dr := (p.rightFactorDeletion W r).hom
  let Da := (p.rightFactorDeletion X a).hom
  let De := (p.rightFactorDeletion W e).hom
  let Ds := (p.rightFactorDeletion Q s).hom
  let Df := (p.rightFactorDeletion Q f).hom
  let q₁ := (p.gaugeLocalTensorator Y Z b c r' r e e₁ beta₁).hom
  let q₂ := (p.gaugeLocalTensorator X (C.tensorObj W (p.factor r)) a e s' s f e₂ beta₂).hom
  let q₂' := (p.gaugeLocalTensorator X W a e s' s f e₂ beta₂).hom
  let A := C.tensorHom (C.tensorHom (C.id (C.tensorObj X (p.factor a))) q₁) (C.id (p.factor s'))
  let B := C.tensorHom (C.tensorHom (C.id (C.tensorObj X (p.factor a)))
    (C.tensorHom Dr (C.id (p.factor e)))) (C.id (p.factor s'))
  let T := C.tensorHom (C.tensorHom (C.tensorHom (C.id X) Dr) (C.id (p.factor s))) (C.id (p.factor f))
  let K := C.comp (C.tensorHom Ds (C.id (p.factor f))) Df
  let J := C.tensorHom (C.tensorHom Da De) (C.id (p.factor s'))
  let H := C.tensorHom (C.tensorHom (p.rightFactorDeletion Y b).hom
    (p.rightFactorDeletion Z c).hom) (C.id (p.factor r'))
  let I := C.tensorHom (C.tensorHom Da H) (C.id (p.factor s'))
  let Dr' := (p.rightFactorDeletion W r').hom
  let Ds' := (p.rightFactorDeletion Q s').hom
  let P := C.tensorHom (C.tensorHom Da (C.comp H Dr')) (C.id (p.factor s'))
  let k₁ := beta₁.val * (-1 : ℝ) ^ (b * c).val
  let k₂ := beta₂.val * (-1 : ℝ) ^ (a * e).val
  have ht (U : C.Obj) {R S T : C.Obj} (x : C.Hom R S) (y : C.Hom S T) :
      C.tensorHom (C.comp x y) (C.id U) =
        C.comp (C.tensorHom x (C.id U)) (C.tensorHom y (C.id U)) :=
    (tensorRightLaws ⟨C, hC⟩ U).map_comp x y
  have hO : (p.orderedOutputDeletion X Y Z r s f).hom = C.comp T K := by
    dsimp only [PiData.orderedOutputDeletion, PiData.orderedRightDeletion,
      IsoData.trans, IsoData.tensor, IsoData.refl]
    rw [ht, hC.comp_assoc]
  have hN : C.comp B q₂' = C.comp q₂ T := by
    have hn := hp.gaugeLocalTensorator_naturality hC (C.id X) Dr a e s' s f e₂ beta₂
    simpa only [hC.tensor_id, B, q₂, q₂', T, Dr, W] using hn
  have hQ : C.comp q₂' K = C.smul k₂ (C.comp J Ds') :=
    hp.gaugeLocalTensorator_deletion_inputs hC X W a e s' s f e₂ beta₂
  have hInner : C.comp (C.comp A B) J = C.smul k₁ P := by
    change C.comp (C.comp (C.tensorHom _ (C.id (p.factor s'))) (C.tensorHom _ (C.id (p.factor s'))))
      (C.tensorHom _ (C.id (p.factor s'))) = _
    rw [← ht, ← ht, hp.gaugeLocalTensorator_deletion_left_tensor hC, hC.tensor_smul_left]
  have hCommon : C.comp P Ds' = C.smul ((-1 : ℝ) ^ (a * r').val)
      (C.comp I (p.orderedRightDeletion X Y Z r' s').hom) := by
    have hJ : C.tensorHom Da (C.comp H Dr') = C.smul ((-1 : ℝ) ^ (a * r').val)
        (C.comp (C.tensorHom Da H) (C.tensorHom (C.id X) Dr')) := by
      rw [hC.super_interchange _ _ _ _ (hp.rightFactorDeletion_homogeneousIso hC W r').hom_grade
        (hp.rightFactorDeletion_homogeneousIso hC X a).hom_grade,
        hC.comp_id, ← hC.mul_smul, mul_comm r' a, parity_power_mul_self, hC.one_smul]
    change C.comp (C.tensorHom (C.tensorHom Da (C.comp H Dr')) (C.id (p.factor s'))) Ds' = _
    rw [hJ, hC.tensor_smul_left, hC.smul_comp, ht, hC.comp_assoc]
    rfl
  change C.comp (C.comp A q₂) _ = C.smul _ (C.comp I (p.orderedRightDeletion X Y Z r' s').hom)
  rw [hO, hC.comp_assoc, ← hC.comp_assoc q₂ T, ← hN, hC.comp_assoc B q₂', hQ,
    hC.comp_smul, hC.comp_smul, ← hC.comp_assoc A B, ← hC.comp_assoc (C.comp A B) J,
    hInner, hC.smul_comp, hCommon, ← hC.mul_smul, ← hC.mul_smul]
  congr 1
  dsimp only [k₁, k₂]
  simp only [parity_power_add]
  ring

end RMod.Classification.PiLaws
