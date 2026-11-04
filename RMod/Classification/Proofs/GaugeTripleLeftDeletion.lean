import RMod.Classification.Proofs.OrderedParityDeletion
import RMod.Classification.Proofs.GaugeTensorDeletion
import RMod.Classification.Proofs.GaugeLocalNaturality

/-!
# The left triple gauge route after ordered deletion

The two local gauge comparisons contribute their prescribed beta scalars.
Deleting the source binary parity crosses the third component deletion
once. Naturality moves the remaining structural maps to the common
target triple deletion. All associators and tensor factors are retained.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem gaugeTripleLeft_deletion (X Y Z : C.Obj) (a b c d f n m n' m' : ZMod 2)
    (e₁ : (a + b) + n' = n + d) (e₂ : (d + c) + m' = m + f) (beta₁ beta₂ : ℝˣ) :
    C.comp (C.comp
      (C.tensorHom (C.tensorHom (p.gaugeLocalTensorator X Y a b n' n d e₁ beta₁).hom
        (C.id (C.tensorObj Z (p.factor c)))) (C.id (p.factor m')))
      (p.gaugeLocalTensorator (C.tensorObj (C.tensorObj X Y) (p.factor n)) Z d c m' m f e₂ beta₂).hom)
      (C.comp (C.tensorHom (p.orderedLeftDeletion X Y Z n m).hom (C.id (p.factor f)))
        (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) f).hom) =
      C.smul (beta₁.val * beta₂.val * (-1 : ℝ) ^ (a * b + d * c + c * n).val)
        (C.comp (C.tensorHom (C.tensorHom
          (C.tensorHom (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)
            (C.id (p.factor n'))) (p.rightFactorDeletion Z c).hom) (C.id (p.factor m')))
          (p.orderedLeftDeletion X Y Z n' m').hom) := by
  let W := C.tensorObj X Y
  let V := C.tensorObj W Z
  let Q := C.tensorObj X (C.tensorObj Y Z)
  let Dn := (p.rightFactorDeletion W n).hom
  let Dd := (p.rightFactorDeletion W d).hom
  let Dc := (p.rightFactorDeletion Z c).hom
  let Dm := (p.rightFactorDeletion V m).hom
  let Df := (p.rightFactorDeletion V f).hom
  let q₁ := (p.gaugeLocalTensorator X Y a b n' n d e₁ beta₁).hom
  let q₂ := (p.gaugeLocalTensorator (C.tensorObj W (p.factor n)) Z d c m' m f e₂ beta₂).hom
  let q₂' := (p.gaugeLocalTensorator W Z d c m' m f e₂ beta₂).hom
  let A := C.tensorHom (C.tensorHom q₁ (C.id (C.tensorObj Z (p.factor c)))) (C.id (p.factor m'))
  let B := C.tensorHom (C.tensorHom (C.tensorHom Dn (C.id (p.factor d)))
    (C.id (C.tensorObj Z (p.factor c)))) (C.id (p.factor m'))
  let T := C.tensorHom (C.tensorHom (C.tensorHom Dn (C.id Z)) (C.id (p.factor m))) (C.id (p.factor f))
  let K := C.comp (C.tensorHom Dm (C.id (p.factor f))) Df
  let J := C.tensorHom (C.tensorHom Dd Dc) (C.id (p.factor m'))
  let H := C.tensorHom (C.tensorHom (p.rightFactorDeletion X a).hom
    (p.rightFactorDeletion Y b).hom) (C.id (p.factor n'))
  let I := C.tensorHom (C.tensorHom H Dc) (C.id (p.factor m'))
  let Dn' := (p.rightFactorDeletion W n').hom
  let Dm' := (p.rightFactorDeletion V m').hom
  let P := C.tensorHom (C.tensorHom (C.comp H Dn') Dc) (C.id (p.factor m'))
  let k₁ := beta₁.val * (-1 : ℝ) ^ (a * b + c * n).val
  let k₂ := beta₂.val * (-1 : ℝ) ^ (d * c).val
  have ht (U : C.Obj) {R S T : C.Obj} (x : C.Hom R S) (y : C.Hom S T) :
      C.tensorHom (C.comp x y) (C.id U) =
        C.comp (C.tensorHom x (C.id U)) (C.tensorHom y (C.id U)) :=
    (tensorRightLaws ⟨C, hC⟩ U).map_comp x y
  have hO : C.comp (C.tensorHom (p.orderedLeftDeletion X Y Z n m).hom (C.id (p.factor f)))
      (p.rightFactorDeletion Q f).hom = C.comp T (C.comp K (C.associatorHom X Y Z)) := by
    have hn := hp.rightFactorDeletion_naturality hC f (C.associatorHom X Y Z)
      (hC.associator_hom_even X Y Z)
    simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
    dsimp only [PiData.orderedLeftDeletion, IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.assoc]
    rw [ht, ht]
    simpa only [hC.comp_assoc, T, K, Dn, Dm, Df, Q, V, W] using
      congrArg (fun z => C.comp T (C.comp (C.tensorHom Dm (C.id (p.factor f))) z)) hn
  have hN : C.comp B q₂' = C.comp q₂ T := by
    have hn := hp.gaugeLocalTensorator_naturality hC Dn (C.id Z) d c m' m f e₂ beta₂
    simpa only [hC.tensor_id, B, q₂, q₂', T, Dn, W] using hn
  have hQ : C.comp q₂' K = C.smul k₂ (C.comp J Dm') :=
    hp.gaugeLocalTensorator_deletion_inputs hC W Z d c m' m f e₂ beta₂
  have hInner : C.comp (C.comp A B) J = C.smul k₁ P := by
    change C.comp (C.comp (C.tensorHom _ (C.id (p.factor m'))) (C.tensorHom _ (C.id (p.factor m'))))
      (C.tensorHom _ (C.id (p.factor m'))) = _
    rw [← ht, ← ht, hp.gaugeLocalTensorator_deletion_right_tensor hC, hC.tensor_smul_left]
  have hCommon : C.comp P (C.comp Dm' (C.associatorHom X Y Z)) =
      C.comp I (p.orderedLeftDeletion X Y Z n' m').hom := by
    have hJ : C.tensorHom (C.comp H Dn') Dc =
        C.comp (C.tensorHom H Dc) (C.tensorHom Dn' (C.id Z)) := by
      rw [interchange_second_even hC _ _ _ _ (hC.id_even Z), hC.comp_id]
    dsimp only [P, PiData.orderedLeftDeletion, IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.assoc]
    rw [hJ, ht]
    simp only [hC.comp_assoc, I, Dm', Dn', V, W]
  change C.comp (C.comp A q₂) _ = C.smul _ (C.comp I (p.orderedLeftDeletion X Y Z n' m').hom)
  rw [hC.comp_assoc, hO, ← hC.comp_assoc q₂ T, ← hN, hC.comp_assoc B q₂',
    ← hC.comp_assoc q₂' K, hQ, hC.smul_comp, hC.comp_smul, hC.comp_smul,
    hC.comp_assoc J Dm', ← hC.comp_assoc A B, ← hC.comp_assoc (C.comp A B) J,
    hInner, hC.smul_comp, ← hC.mul_smul, hCommon]
  congr 1
  dsimp only [k₁, k₂]
  simp only [parity_power_add]
  ring

end RMod.Classification.PiLaws
