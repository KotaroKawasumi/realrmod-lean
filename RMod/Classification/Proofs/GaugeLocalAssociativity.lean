import RMod.Classification.Proofs.GaugeTripleLeftDeletion
import RMod.Classification.Proofs.GaugeTripleRightDeletion
import RMod.Classification.Proofs.GaugeAssociativityScalars

/-!
# Associativity of the specified local gauge tensorator

Postcompose both routes with the same homogeneous invertible deletion.
The checked left and right formulas reduce them to one actual triple
map. The gauge omega equation identifies its two scalar coefficients.
Cancelling the supplied inverse proves equality of the original routes.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem gaugeLocalTensorator_associativity (X Y Z : C.Obj)
    (a b c d e f n m r s n' m' r' s' : ZMod 2)
    (hs : n + m = r + s) (ht : n' + m' = r' + s')
    (h₁ : (a + b) + n' = n + d) (h₂ : (d + c) + m' = m + f)
    (h₃ : (b + c) + r' = r + e) (h₄ : (a + e) + s' = s + f)
    (beta₁ beta₂ beta₃ beta₄ omega omega' : ℝˣ)
    (hw : omega' = omega * (beta₂ * beta₁) * (beta₃ * beta₄)⁻¹ * realSign (n' * c + a * r)) :
    C.comp (C.comp
      (C.tensorHom (C.tensorHom (p.gaugeLocalTensorator X Y a b n' n d h₁ beta₁).hom
        (C.id (C.tensorObj Z (p.factor c)))) (C.id (p.factor m')))
      (p.gaugeLocalTensorator (C.tensorObj (C.tensorObj X Y) (p.factor n)) Z d c m' m f h₂ beta₂).hom)
      (C.tensorHom (p.localAssociator X Y Z n m r s hs omega).hom (C.id (p.factor f))) =
      C.comp (p.localAssociator (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))
        (C.tensorObj Z (p.factor c)) n' m' r' s' ht omega').hom
        (C.comp (C.tensorHom (C.tensorHom (C.id (C.tensorObj X (p.factor a)))
          (p.gaugeLocalTensorator Y Z b c r' r e h₃ beta₃).hom) (C.id (p.factor s')))
          (p.gaugeLocalTensorator X (C.tensorObj (C.tensorObj Y Z) (p.factor r)) a e s' s f h₄ beta₄).hom) := by
  let L := C.comp
    (C.tensorHom (C.tensorHom (p.gaugeLocalTensorator X Y a b n' n d h₁ beta₁).hom
      (C.id (C.tensorObj Z (p.factor c)))) (C.id (p.factor m')))
    (p.gaugeLocalTensorator (C.tensorObj (C.tensorObj X Y) (p.factor n)) Z d c m' m f h₂ beta₂).hom
  let R := C.comp
    (C.tensorHom (C.tensorHom (C.id (C.tensorObj X (p.factor a)))
      (p.gaugeLocalTensorator Y Z b c r' r e h₃ beta₃).hom) (C.id (p.factor s')))
    (p.gaugeLocalTensorator X (C.tensorObj (C.tensorObj Y Z) (p.factor r)) a e s' s f h₄ beta₄).hom
  let As := C.tensorHom (p.localAssociator X Y Z n m r s hs omega).hom (C.id (p.factor f))
  let At := (p.localAssociator (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))
    (C.tensorObj Z (p.factor c)) n' m' r' s' ht omega').hom
  let D := p.orderedOutputDeletion X Y Z r s f
  let DL := C.comp (C.tensorHom (p.orderedLeftDeletion X Y Z n m).hom (C.id (p.factor f)))
    (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) f).hom
  let IL := C.tensorHom (C.tensorHom
    (C.tensorHom (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)
      (C.id (p.factor n'))) (p.rightFactorDeletion Z c).hom) (C.id (p.factor m'))
  let IR := C.tensorHom (C.tensorHom (p.rightFactorDeletion X a).hom
    (C.tensorHom (C.tensorHom (p.rightFactorDeletion Y b).hom (p.rightFactorDeletion Z c).hom)
      (C.id (p.factor r')))) (C.id (p.factor s'))
  let CL := C.comp IL (p.orderedLeftDeletion X Y Z n' m').hom
  let CR := C.comp IR (p.orderedRightDeletion X Y Z r' s').hom
  let kL := beta₁.val * beta₂.val * (-1 : ℝ) ^ (a * b + d * c + c * n).val
  let kR := beta₃.val * beta₄.val * (-1 : ℝ) ^ (b * c + a * e + a * r').val
  have hL : C.comp L DL = C.smul kL CL :=
    hp.gaugeTripleLeft_deletion hC X Y Z a b c d f n m n' m' h₁ h₂ beta₁ beta₂
  have hR : C.comp R D.hom = C.smul kR CR :=
    hp.gaugeTripleRight_deletion hC X Y Z a b c e f r s r' s' h₃ h₄ beta₃ beta₄
  have hAs : C.comp As D.hom = C.smul omega.val DL := by
    have hmap (U V W : C.Obj) (x : C.Hom U V) (y : C.Hom V W) :
        C.tensorHom (C.comp x y) (C.id (p.factor f)) =
          C.comp (C.tensorHom x (C.id (p.factor f))) (C.tensorHom y (C.id (p.factor f))) :=
      (tensorRightLaws ⟨C, hC⟩ (p.factor f)).map_comp x y
    change C.comp (C.tensorHom _ (C.id (p.factor f)))
      (C.comp (C.tensorHom _ (C.id (p.factor f))) _) = _
    rw [← hC.comp_assoc, ← hmap, hp.localAssociator_orderedDeletion hC,
      hC.tensor_smul_left, hC.smul_comp]
  have hAt : C.comp At CR = C.smul omega'.val CL := by
    have hn := hp.localAssociator_naturality hC
      (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom (p.rightFactorDeletion Z c).hom
      n' m' r' s' ht omega'
    change C.comp At (C.comp IR _) = _
    rw [← hC.comp_assoc, ← hn, hC.comp_assoc, hp.localAssociator_orderedDeletion hC, hC.comp_smul]
  have hcoef : omega.val * kL = kR * omega'.val :=
    gaugeTriple_scalar a b c d e n r n' r' h₁ h₃ beta₁ beta₂ beta₃ beta₄ omega omega' hw
  have he : C.comp (C.comp L As) D.hom = C.comp (C.comp At R) D.hom := by
    rw [hC.comp_assoc L As, hAs, hC.comp_smul, hL,
      hC.comp_assoc At R, hR, hC.comp_smul, hAt, ← hC.mul_smul, ← hC.mul_smul, hcoef]
  have he' := congrArg (fun z => C.comp z D.inv) he
  have hD : C.comp D.hom D.inv = C.id _ :=
    (hp.orderedOutputDeletion_homogeneousIso hC X Y Z r s f).hom_inv
  change C.comp L As = C.comp At R
  simpa only [hC.comp_assoc, hD, hC.comp_id] using he'

end RMod.Classification.PiLaws
