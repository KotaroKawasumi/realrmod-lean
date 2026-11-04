/-
Superfusion / GaugeChi / QuintExtractPCD

Spectator extraction for the `PCD` face.  The spectator is the explicit
column `F_{c,d}` and the residual quadruple is `(a,b,c+d,e)`.
-/
import Superfusion.GaugeChi.QuintFacesPBC

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d e : G)

attribute [local instance 500] leftModule rightModule

/-! The right-hand vertices differ from their shifted pentagon
presentations only by the parenthesization of `b+c+d`.  Since the module
instances depend on that index, the transport is packaged as an honest
balanced-tensor equivalence rather than a brittle tactic-level rewrite. -/

theorem pcdHeq : b + c + d + e = b + (c + d) + e :=
  pbcHeq b c d e

private theorem pcdFusionColumnCast_xslot (p : G) {x y : G} (h : x = y)
    (τ : (Γ.D x).carrier) (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p h (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv τ • fusionColumnCast K Γ p h w := by
  subst h
  rfl

private theorem pcdFusionColumnCast_symm_xslot (p : G) {x y : G} (h : x = y)
    (τ : (Γ.D y).carrier) (w : FusionColumn (Γ.fuse p y)) :
    (fusionColumnCast K Γ p h).symm (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (fusionColumnCast K Γ p h).symm w := by
  subst h
  rfl

/-- Successive second-index column transports compose. -/
theorem pcdFusionColumnCast_trans (p : G) {x y z : G} (hxy : x = y)
    (hyz : y = z) (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p hyz (fusionColumnCast K Γ p hxy w)
      = fusionColumnCast K Γ p (hxy.trans hyz) w := by
  subst hxy
  subst hyz
  rfl

theorem pcdFusionColumnCast_symm_eq (p : G) {x y : G} (h : x = y) :
    fusionColumnCast K Γ p h.symm = (fusionColumnCast K Γ p h).symm := by
  subst h
  rfl

/-! ### The `V13` inner transport -/

private noncomputable def pcdV13CastFwdBilin :
    GQ3Inner K Γ b c d e →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + d + e)) →ₗ[K]
        RelTensor K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
          (FusionColumn (Γ.fuse a (b + (c + d) + e))) :=
  (RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
    (FusionColumn (Γ.fuse a (b + (c + d) + e)))).compl₂
    (fusionColumnCast K Γ a (pcdHeq b c d e)).toLinearMap

private theorem pcdV13CastFwdBilin_apply (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV13CastFwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
          (FusionColumn (Γ.fuse a (b + (c + d) + e))) m
          (fusionColumnCast K Γ a (pcdHeq b c d e) w) :=
  rfl

private theorem pcdV13CastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d + e)).carrier
      (pcdV13CastFwdBilin K Γ a b c d e) := by
  intro t m w
  rw [pcdV13CastFwdBilin_apply, pcdV13CastFwdBilin_apply,
    pcdFusionColumnCast_xslot]
  show RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
      (FusionColumn (Γ.fuse a (b + (c + d) + e)))
      (rightActionEnd K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e))) (MulOpposite.op t) m)
      (fusionColumnCast K Γ a (pcdHeq b c d e) w)
    = RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
        (FusionColumn (Γ.fuse a (b + (c + d) + e))) m
        ((Γ.gaugeCast (pcdHeq b c d e)).toAlgEquiv t •
          fusionColumnCast K Γ a (pcdHeq b c d e) w)
  rw [gq3v4RecastFull]
  exact RelTensor.mk_op_smul K (Γ.D (b + (c + d) + e)).carrier
    (GBR Γ b (c + d) e) (FusionColumn (Γ.fuse a (b + (c + d) + e)))
    ((Γ.gaugeCast (pcdHeq b c d e)).toAlgEquiv t) m
    (fusionColumnCast K Γ a (pcdHeq b c d e) w)

private noncomputable def pcdV13CastFwd :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) →ₗ[K]
      RelTensor K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
        (FusionColumn (Γ.fuse a (b + (c + d) + e))) :=
  RelTensor.lift (pcdV13CastFwdBilin K Γ a b c d e)
    (pcdV13CastFwd_balanced K Γ a b c d e)

private theorem pcdV13CastFwd_mk (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV13CastFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
      = RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
          (FusionColumn (Γ.fuse a (b + (c + d) + e))) m
          (fusionColumnCast K Γ a (pcdHeq b c d e) w) := by
  rw [pcdV13CastFwd, RelTensor.lift_mk, pcdV13CastFwdBilin_apply]

private noncomputable def pcdV13CastBwdBilin :
    GBR Γ b (c + d) e →ₗ[K]
      FusionColumn (Γ.fuse a (b + (c + d) + e)) →ₗ[K]
        RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e)))).compl₂
      (fusionColumnCast K Γ a (pcdHeq b c d e)).symm.toLinearMap

private theorem pcdV13CastBwdBilin_apply (m : GBR Γ b (c + d) e)
    (w : FusionColumn (Γ.fuse a (b + (c + d) + e))) :
    pcdV13CastBwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m
          ((fusionColumnCast K Γ a (pcdHeq b c d e)).symm w) :=
  rfl

private theorem pcdV13CastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d) + e)).carrier
      (pcdV13CastBwdBilin K Γ a b c d e) := by
  intro s m w
  rw [pcdV13CastBwdBilin_apply, pcdV13CastBwdBilin_apply,
    pcdFusionColumnCast_symm_xslot]
  have hbridge := gq3v4RecastFull K Γ b c d e
    ((Γ.gaugeCast (pcdHeq b c d e)).toAlgEquiv.symm s) m
  rw [AlgEquiv.apply_symm_apply] at hbridge
  show RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))
      (rightActionEnd K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e)))
        (MulOpposite.op ((Γ.gaugeCast (add_assoc b (c + d) e)).toAlgEquiv s)) m)
      ((fusionColumnCast K Γ a (pcdHeq b c d e)).symm w)
    = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m
        ((Γ.gaugeCast (pcdHeq b c d e)).toAlgEquiv.symm s •
          (fusionColumnCast K Γ a (pcdHeq b c d e)).symm w)
  rw [← hbridge]
  exact RelTensor.mk_op_smul K (Γ.D (b + c + d + e)).carrier
    (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
    ((Γ.gaugeCast (pcdHeq b c d e)).toAlgEquiv.symm s) m
    ((fusionColumnCast K Γ a (pcdHeq b c d e)).symm w)

private noncomputable def pcdV13CastBwd :
    RelTensor K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
        (FusionColumn (Γ.fuse a (b + (c + d) + e))) →ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  RelTensor.lift (pcdV13CastBwdBilin K Γ a b c d e)
    (pcdV13CastBwd_balanced K Γ a b c d e)

private theorem pcdV13CastBwd_mk (m : GBR Γ b (c + d) e)
    (w : FusionColumn (Γ.fuse a (b + (c + d) + e))) :
    pcdV13CastBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
          (FusionColumn (Γ.fuse a (b + (c + d) + e))) m w)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m
          ((fusionColumnCast K Γ a (pcdHeq b c d e)).symm w) := by
  rw [pcdV13CastBwd, RelTensor.lift_mk, pcdV13CastBwdBilin_apply]

private theorem pcdV13CastFwd_bwd :
    (pcdV13CastFwd K Γ a b c d e).comp (pcdV13CastBwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show pcdV13CastFwd K Γ a b c d e
      (pcdV13CastBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
          (FusionColumn (Γ.fuse a (b + (c + d) + e))) m w))
    = RelTensor.mk K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
        (FusionColumn (Γ.fuse a (b + (c + d) + e))) m w
  rw [pcdV13CastBwd_mk, pcdV13CastFwd_mk, LinearEquiv.apply_symm_apply]

private theorem pcdV13CastBwd_fwd :
    (pcdV13CastBwd K Γ a b c d e).comp (pcdV13CastFwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show pcdV13CastBwd K Γ a b c d e
      (pcdV13CastFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m w))
    = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) m w
  rw [pcdV13CastFwd_mk, pcdV13CastBwd_mk, LinearEquiv.symm_apply_apply]

private noncomputable def pcdV13RawCast :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
      ≃ₗ[K] RelTensor K (Γ.D (b + (c + d) + e)).carrier (GBR Γ b (c + d) e)
        (FusionColumn (Γ.fuse a (b + (c + d) + e))) :=
  LinearEquiv.ofLinear (pcdV13CastFwd K Γ a b c d e)
    (pcdV13CastBwd K Γ a b c d e)
    (pcdV13CastFwd_bwd K Γ a b c d e)
    (pcdV13CastBwd_fwd K Γ a b c d e)

noncomputable def pcdV13InnerCast :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
      ≃ₗ[K] GQ4 K Γ a b (c + d) e :=
  pcdV13RawCast K Γ a b c d e

theorem pcdV13InnerCast_mk (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV13InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
      = GQ4.mk K Γ a b (c + d) e m
          (fusionColumnCast K Γ a (pcdHeq b c d e) w) :=
  pcdV13CastFwd_mk K Γ a b c d e m w

theorem pcdV13InnerCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    pcdV13InnerCast K Γ a b c d e (τ • n)
      = τ • pcdV13InnerCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m w =>
      rw [show (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e))) m w
            : RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e))))
          = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
              (τ • m) w from
        leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier
          (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e))) τ m w,
        pcdV13InnerCast_mk, pcdV13InnerCast_mk, GQ4.cslot_smul_mk]
      rfl

noncomputable def omegaPcdV13 : V13 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ4 K Γ a b (c + d) e) :=
  (gV13StepB K Γ a b c d e).symm.trans
    (RelTensor.mapEquivRight K (pcdV13InnerCast K Γ a b c d e)
      (pcdV13InnerCast_cdSlot K Γ a b c d e))

private theorem pcdV13Peel_mk
    (u : FusionColumn (Γ.fuse c d))
    (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    (gV13StepB K Γ a b c d e).symm
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ3.mk K Γ b c d e u m) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (GQ3Inner K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (GQ3Inner K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) m w) :=
  RelTensor.assoc_mk K (Γ.D (c + d)).carrier
    (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse c d)) (GQ3Inner K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) u m w

private theorem pcdV13Map_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (RelTensor.mapEquivRight K (pcdV13InnerCast K Γ a b c d e)
        (pcdV13InnerCast_cdSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (GQ3Inner K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) u
          (pcdV13InnerCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K]
      FusionColumn (Γ.fuse c d))
    (pcdV13InnerCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (pcdV13InnerCast_cdSlot K Γ a b c d e) u n

theorem omegaPcdV13_core_mk
    (u : FusionColumn (Γ.fuse c d))
    (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV13 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ3.mk K Γ b c d e u m) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) u
          (pcdV13InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GQ3Inner K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e))) m w)) := by
  rw [omegaPcdV13, LinearEquiv.trans_apply, pcdV13Peel_mk,
    pcdV13Map_mk]

/-- Extraction after a value already presented through `gV13StepB`.
This form keeps the residual factor opaque and is tailored to edge 19. -/
theorem omegaPcdV13_gV13StepB_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (GQ3Inner K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    omegaPcdV13 K Γ a b c d e
        (gV13StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d))
            (RelTensor K (Γ.D (b + c + d + e)).carrier
              (GQ3Inner K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e)))) u n))
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) u
          (pcdV13InnerCast K Γ a b c d e n) := by
  rw [omegaPcdV13, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, pcdV13Map_mk]

theorem omegaPcdV13_mk
    (u : FusionColumn (Γ.fuse c d))
    (m : GQ3Inner K Γ b c d e)
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV13 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ3 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ3.mk K Γ b c d e u m) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ4 K Γ a b (c + d) e) u
          (GQ4.mk K Γ a b (c + d) e m
            (fusionColumnCast K Γ a (pcdHeq b c d e) w)) := by
  rw [omegaPcdV13, LinearEquiv.trans_apply, pcdV13Peel_mk,
    pcdV13Map_mk,
    pcdV13InnerCast_mk]

/-! ### The `V11` inner transport -/

/-- Change the middle argument of `GBR`; equality induction transports
the complete bimodule structure, including its signed outer actions. -/
noncomputable def pcdGbrCastSnd (p r : G) {q q' : G} (h : q = q') :
    GBR Γ p q r ≃ₗ[K] GBR Γ p q' r := by
  subst h
  exact LinearEquiv.refl K _

theorem pcdGbrCastSnd_bslot (p r : G) {q q' : G} (h : q = q')
    (t : (Γ.D q).carrier) (n : GBR Γ p q r) :
    pcdGbrCastSnd K Γ p r h (t • n)
      = (Γ.gaugeCast h).toAlgEquiv t • pcdGbrCastSnd K Γ p r h n := by
  subst h
  rfl

theorem pcdGbrCastSnd_symm_bslot (p r : G) {q q' : G} (h : q = q')
    (t : (Γ.D q').carrier) (n : GBR Γ p q' r) :
    (pcdGbrCastSnd K Γ p r h).symm (t • n)
      = (Γ.gaugeCast h).toAlgEquiv.symm t •
          (pcdGbrCastSnd K Γ p r h).symm n := by
  subst h
  rfl

theorem pcdGbrCastSnd_mk (p r : G) {q q' : G} (h : q = q')
    (u : FusionColumn (Γ.fuse q r)) (v : FusionColumn (Γ.fuse p (q + r))) :
    pcdGbrCastSnd K Γ p r h (GBR.mk Γ p q r u v)
      = GBR.mk Γ p q' r (gColumnCastFst K Γ r h u)
          (fusionColumnCast K Γ p (congrArg (· + r) h) v) := by
  subst h
  rfl

private noncomputable def pcdV11CastFwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      GBR Γ a (b + c + d) e →ₗ[K]
        RelTensor K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) :=
  (RelTensor.mk K (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e)).compl₂
      (pcdGbrCastSnd K Γ a e (add_assoc b c d)).toLinearMap

private theorem pcdV11CastFwdBilin_apply
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBR Γ a (b + c + d) e) :
    pcdV11CastFwdBilin K Γ a b c d e m n
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) m
          (pcdGbrCastSnd K Γ a e (add_assoc b c d) n) :=
  rfl

private theorem pcdV11CastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d)).carrier
      (pcdV11CastFwdBilin K Γ a b c d e) := by
  intro t m n
  rw [pcdV11CastFwdBilin_apply, pcdV11CastFwdBilin_apply,
    fusionColumn_recast_op_smul_def, pcdGbrCastSnd_bslot]
  exact RelTensor.mk_op_smul K (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e)
    ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv t) m
    (pcdGbrCastSnd K Γ a e (add_assoc b c d) n)

private noncomputable def pcdV11CastFwd :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBR Γ a (b + c + d) e) →ₗ[K]
      RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) :=
  RelTensor.lift (pcdV11CastFwdBilin K Γ a b c d e)
    (pcdV11CastFwd_balanced K Γ a b c d e)

private theorem pcdV11CastFwd_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBR Γ a (b + c + d) e) :
    pcdV11CastFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m n)
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) m
          (pcdGbrCastSnd K Γ a e (add_assoc b c d) n) := by
  rw [pcdV11CastFwd, RelTensor.lift_mk, pcdV11CastFwdBilin_apply]

private noncomputable def pcdV11CastBwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      GBR Γ a (b + (c + d)) e →ₗ[K]
        RelTensor K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) :=
  (RelTensor.mk K (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)).compl₂
      (pcdGbrCastSnd K Γ a e (add_assoc b c d)).symm.toLinearMap

private theorem pcdV11CastBwdBilin_apply
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBR Γ a (b + (c + d)) e) :
    pcdV11CastBwdBilin K Γ a b c d e m n
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m
          ((pcdGbrCastSnd K Γ a e (add_assoc b c d)).symm n) :=
  rfl

private theorem pcdV11CastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d))).carrier
      (pcdV11CastBwdBilin K Γ a b c d e) := by
  intro s m n
  rw [pcdV11CastBwdBilin_apply, pcdV11CastBwdBilin_apply,
    pcdGbrCastSnd_symm_bslot]
  have hm :
      (MulOpposite.op s • m : FusionColumn (Γ.fuse b (c + d)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm s) • m := by
    rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply]
  rw [hm]
  exact RelTensor.mk_op_smul K (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)
    ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm s) m
    ((pcdGbrCastSnd K Γ a e (add_assoc b c d)).symm n)

private noncomputable def pcdV11CastBwd :
    RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) →ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBR Γ a (b + c + d) e) :=
  RelTensor.lift (pcdV11CastBwdBilin K Γ a b c d e)
    (pcdV11CastBwd_balanced K Γ a b c d e)

private theorem pcdV11CastBwd_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBR Γ a (b + (c + d)) e) :
    pcdV11CastBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) m n)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m
          ((pcdGbrCastSnd K Γ a e (add_assoc b c d)).symm n) := by
  rw [pcdV11CastBwd, RelTensor.lift_mk, pcdV11CastBwdBilin_apply]

private theorem pcdV11CastFwd_bwd :
    (pcdV11CastFwd K Γ a b c d e).comp (pcdV11CastBwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show pcdV11CastFwd K Γ a b c d e
      (pcdV11CastBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) m n))
    = RelTensor.mk K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) m n
  rw [pcdV11CastBwd_mk, pcdV11CastFwd_mk, LinearEquiv.apply_symm_apply]

private theorem pcdV11CastBwd_fwd :
    (pcdV11CastBwd K Γ a b c d e).comp (pcdV11CastFwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show pcdV11CastBwd K Γ a b c d e
      (pcdV11CastFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m n))
    = RelTensor.mk K (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m n
  rw [pcdV11CastFwd_mk, pcdV11CastBwd_mk, LinearEquiv.symm_apply_apply]

private noncomputable def pcdV11RawCast :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBR Γ a (b + c + d) e)
      ≃ₗ[K] RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + (c + d)) e) :=
  LinearEquiv.ofLinear (pcdV11CastFwd K Γ a b c d e)
    (pcdV11CastBwd K Γ a b c d e)
    (pcdV11CastFwd_bwd K Γ a b c d e)
    (pcdV11CastBwd_fwd K Γ a b c d e)

noncomputable def pcdV11InnerCast :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBR Γ a (b + c + d) e)
      ≃ₗ[K] GQ3 K Γ a b (c + d) e :=
  pcdV11RawCast K Γ a b c d e

theorem pcdV11InnerCast_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBR Γ a (b + c + d) e) :
    pcdV11InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m n)
      = GQ3.mk K Γ a b (c + d) e m
          (pcdGbrCastSnd K Γ a e (add_assoc b c d) n) :=
  pcdV11CastFwd_mk K Γ a b c d e m n

theorem pcdV11InnerCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) :
    pcdV11InnerCast K Γ a b c d e (τ • n)
      = τ • pcdV11InnerCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m q =>
      rw [show (τ • RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) m q
            : RelTensor K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e))
          = RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)
              (τ • m) q from
        leftActionEnd_mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) τ m q,
        pcdV11InnerCast_mk, pcdV11InnerCast_mk, GQ3.cslot_smul_mk]

noncomputable def pcdV11Peel : V11 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (RelTensor K (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) :=
  (gV11Assoc K Γ a b c d e).trans
    (RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
      (GBR Γ a (b + c + d) e))

noncomputable def omegaPcdV11 : V11 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ3 K Γ a b (c + d) e) :=
  (pcdV11Peel K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (pcdV11InnerCast K Γ a b c d e)
      (pcdV11InnerCast_cdSlot K Γ a b c d e))

private theorem pcdV11Assoc_mk
    (m : GBR Γ b c d)
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV11Assoc K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e m w) x)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBR Γ a (b + c + d) e) m
          (GBR.mk Γ a (b + c + d) e w x) :=
  RelTensor.assoc_mk K (Γ.D (b + c + d)).carrier
    (Γ.D (b + c + d + e)).carrier
    (GBR Γ b c d) (FusionColumn (Γ.fuse (b + c + d) e))
    (FusionColumn (Γ.fuse a (b + c + d + e))) m w x

private theorem pcdV11Peel_assoc_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (n : GBR Γ a (b + c + d) e) :
    (RelTensor.assoc K (Γ.D (c + d)).carrier
        (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
        (GBR Γ a (b + c + d) e))
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBR Γ a (b + c + d) e)
          (GBR.mk Γ b c d u v) n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v n) :=
  RelTensor.assoc_mk K (Γ.D (c + d)).carrier
    (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
    (GBR Γ a (b + c + d) e) u v n

private theorem pcdV11Peel_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pcdV11Peel K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v
            (GBR.mk Γ a (b + c + d) e w x)) := by
  rw [pcdV11Peel, LinearEquiv.trans_apply, pcdV11Assoc_mk]
  exact pcdV11Peel_assoc_mk K Γ a b c d e u v
    (GBR.mk Γ a (b + c + d) e w x)

private theorem pcdV11Map_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) :
    (RelTensor.mapEquivRight K (pcdV11InnerCast K Γ a b c d e)
        (pcdV11InnerCast_cdSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) u n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ3 K Γ a b (c + d) e) u
          (pcdV11InnerCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K]
      FusionColumn (Γ.fuse c d))
    (pcdV11InnerCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (pcdV11InnerCast_cdSlot K Γ a b c d e) u n

theorem omegaPcdV11_core_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV11 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ3 K Γ a b (c + d) e) u
          (pcdV11InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v
              (GBR.mk Γ a (b + c + d) e w x))) := by
  rw [omegaPcdV11, LinearEquiv.trans_apply, pcdV11Peel_mk,
    pcdV11Map_mk]

theorem omegaPcdV11_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPcdV11 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ2 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ2.mk K Γ b c d e (GBR.mk Γ b c d u v) w) x)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ3 K Γ a b (c + d) e) u
          (GQ3.mk K Γ a b (c + d) e v
            (pcdGbrCastSnd K Γ a e (add_assoc b c d)
              (GBR.mk Γ a (b + c + d) e w x))) := by
  rw [omegaPcdV11, LinearEquiv.trans_apply, pcdV11Peel_mk,
    pcdV11Map_mk, pcdV11InnerCast_mk]

/-! ### The `V5` inner transport -/

/-- Change the middle argument of `GBL`.  As for `pcdGbrCastSnd`,
equality induction transports the whole signed bimodule structure. -/
noncomputable def pcdGblCastSnd (p r : G) {q q' : G} (h : q = q') :
    GBL Γ p q r ≃ₗ[K] GBL Γ p q' r := by
  subst h
  exact LinearEquiv.refl K _

theorem pcdGblCastSnd_bslot (p r : G) {q q' : G} (h : q = q')
    (t : (Γ.D q).carrier) (n : GBL Γ p q r) :
    pcdGblCastSnd K Γ p r h (t • n)
      = (Γ.gaugeCast h).toAlgEquiv t • pcdGblCastSnd K Γ p r h n := by
  subst h
  rfl

theorem pcdGblCastSnd_symm_bslot (p r : G) {q q' : G} (h : q = q')
    (t : (Γ.D q').carrier) (n : GBL Γ p q' r) :
    (pcdGblCastSnd K Γ p r h).symm (t • n)
      = (Γ.gaugeCast h).toAlgEquiv.symm t •
          (pcdGblCastSnd K Γ p r h).symm n := by
  subst h
  rfl

theorem pcdGblCastSnd_mk (p r : G) {q q' : G} (h : q = q')
    (u : FusionColumn (Γ.fuse p q)) (v : FusionColumn (Γ.fuse (p + q) r)) :
    pcdGblCastSnd K Γ p r h (GBL.mk Γ p q r u v)
      = GBL.mk Γ p q' r (fusionColumnCast K Γ p h u)
          (gColumnCastFst K Γ r (congrArg (p + ·) h) v) := by
  subst h
  rfl

/-- Naturality of the chosen canonical triple map under a propositional
change of its middle index.  This is pure transport: after equality
induction both sides are the same map applied to the same vector. -/
theorem pcdGCanonCastSnd (p r : G) {q q' : G} (h : q = q')
    (n : GBL Γ p q r) :
    pcdGbrCastSnd K Γ p r h (gTCanon K Γ p q r n)
      = gTCanon K Γ p q' r (pcdGblCastSnd K Γ p r h n) := by
  subst h
  rfl

private noncomputable def pcdV5MiddleFwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      GBL Γ a (b + c + d) e →ₗ[K]
        RelTensor K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) :=
  (RelTensor.mk K (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e)).compl₂
      (pcdGblCastSnd K Γ a e (add_assoc b c d)).toLinearMap

private theorem pcdV5MiddleFwdBilin_apply
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBL Γ a (b + c + d) e) :
    pcdV5MiddleFwdBilin K Γ a b c d e m n
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m
          (pcdGblCastSnd K Γ a e (add_assoc b c d) n) :=
  rfl

private theorem pcdV5MiddleFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d)).carrier
      (pcdV5MiddleFwdBilin K Γ a b c d e) := by
  intro t m n
  rw [pcdV5MiddleFwdBilin_apply, pcdV5MiddleFwdBilin_apply,
    fusionColumn_recast_op_smul_def, pcdGblCastSnd_bslot]
  exact RelTensor.mk_op_smul K (Γ.D (b + (c + d))).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e)
    ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv t) m
    (pcdGblCastSnd K Γ a e (add_assoc b c d) n)

private noncomputable def pcdV5MiddleFwd :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBL Γ a (b + c + d) e) →ₗ[K]
      RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) :=
  RelTensor.lift (pcdV5MiddleFwdBilin K Γ a b c d e)
    (pcdV5MiddleFwd_balanced K Γ a b c d e)

private theorem pcdV5MiddleFwd_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBL Γ a (b + c + d) e) :
    pcdV5MiddleFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m n)
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m
          (pcdGblCastSnd K Γ a e (add_assoc b c d) n) := by
  rw [pcdV5MiddleFwd, RelTensor.lift_mk, pcdV5MiddleFwdBilin_apply]

private noncomputable def pcdV5MiddleBwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      GBL Γ a (b + (c + d)) e →ₗ[K]
        RelTensor K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) :=
  (RelTensor.mk K (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)).compl₂
      (pcdGblCastSnd K Γ a e (add_assoc b c d)).symm.toLinearMap

private theorem pcdV5MiddleBwdBilin_apply
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBL Γ a (b + (c + d)) e) :
    pcdV5MiddleBwdBilin K Γ a b c d e m n
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m
          ((pcdGblCastSnd K Γ a e (add_assoc b c d)).symm n) :=
  rfl

private theorem pcdV5MiddleBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d))).carrier
      (pcdV5MiddleBwdBilin K Γ a b c d e) := by
  intro s m n
  rw [pcdV5MiddleBwdBilin_apply, pcdV5MiddleBwdBilin_apply,
    pcdGblCastSnd_symm_bslot]
  have hm :
      (MulOpposite.op s • m : FusionColumn (Γ.fuse b (c + d)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm s) • m := by
    rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply]
  rw [hm]
  exact RelTensor.mk_op_smul K (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)
    ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm s) m
    ((pcdGblCastSnd K Γ a e (add_assoc b c d)).symm n)

private noncomputable def pcdV5MiddleBwd :
    RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) →ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBL Γ a (b + c + d) e) :=
  RelTensor.lift (pcdV5MiddleBwdBilin K Γ a b c d e)
    (pcdV5MiddleBwd_balanced K Γ a b c d e)

private theorem pcdV5MiddleBwd_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBL Γ a (b + (c + d)) e) :
    pcdV5MiddleBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m n)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m
          ((pcdGblCastSnd K Γ a e (add_assoc b c d)).symm n) := by
  rw [pcdV5MiddleBwd, RelTensor.lift_mk, pcdV5MiddleBwdBilin_apply]

private theorem pcdV5MiddleFwd_bwd :
    (pcdV5MiddleFwd K Γ a b c d e).comp (pcdV5MiddleBwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show pcdV5MiddleFwd K Γ a b c d e
      (pcdV5MiddleBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m n))
    = RelTensor.mk K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m n
  rw [pcdV5MiddleBwd_mk, pcdV5MiddleFwd_mk, LinearEquiv.apply_symm_apply]

private theorem pcdV5MiddleBwd_fwd :
    (pcdV5MiddleBwd K Γ a b c d e).comp (pcdV5MiddleFwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show pcdV5MiddleBwd K Γ a b c d e
      (pcdV5MiddleFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m n))
    = RelTensor.mk K (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m n
  rw [pcdV5MiddleFwd_mk, pcdV5MiddleBwd_mk, LinearEquiv.symm_apply_apply]

/-- The `b+c+d` parenthesization change after the explicit
`F_{c,d}` spectator has been peeled from `V5`. -/
noncomputable def pcdV5MiddleCast :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBL Γ a (b + c + d) e)
      ≃ₗ[K] RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) :=
  LinearEquiv.ofLinear (pcdV5MiddleFwd K Γ a b c d e)
    (pcdV5MiddleBwd K Γ a b c d e)
    (pcdV5MiddleFwd_bwd K Γ a b c d e)
    (pcdV5MiddleBwd_fwd K Γ a b c d e)

theorem pcdV5MiddleCast_mk
    (m : FusionColumn (Γ.fuse b (c + d))) (n : GBL Γ a (b + c + d) e) :
    pcdV5MiddleCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m n)
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m
          (pcdGblCastSnd K Γ a e (add_assoc b c d) n) :=
  pcdV5MiddleFwd_mk K Γ a b c d e m n

/-! The second half of the `V5` transport changes the total coefficient
from the natural right-route frame `a+(b+(c+d))` to the left-associated
frame `(a+b)+(c+d)` used by `GQ2`. -/

theorem pcdV5TotalHeq : a + (b + (c + d)) = a + b + (c + d) :=
  (add_assoc a b (c + d)).symm

private noncomputable def pcdV5TotalFwdBilin :
    GBR Γ a b (c + d) →ₗ[K]
      FusionColumn (Γ.fuse (a + (b + (c + d))) e) →ₗ[K]
        GQ2 K Γ a b (c + d) e :=
  (GQ2.mk K Γ a b (c + d) e).compl₂
    (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)).toLinearMap

private theorem pcdV5TotalFwdBilin_apply (m : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :
    pcdV5TotalFwdBilin K Γ a b c d e m w
      = GQ2.mk K Γ a b (c + d) e m
          (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d) w) :=
  rfl

private theorem pcdV5TotalFwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + (b + (c + d)))).carrier
      (pcdV5TotalFwdBilin K Γ a b c d e) := by
  intro t m w
  rw [pcdV5TotalFwdBilin_apply, pcdV5TotalFwdBilin_apply,
    gColumnCastFst_xslot]
  have hm :
      (MulOpposite.op t • m : GBR Γ a b (c + d))
        = MulOpposite.op
            ((Γ.gaugeCast (pcdV5TotalHeq a b c d)).toAlgEquiv t) • m := by
    rw [GBR.recast_op_smul_def,
      ← gaugeCast_symm_apply' K Γ (add_assoc a b (c + d)),
      AlgEquiv.apply_symm_apply]
  rw [hm]
  exact RelTensor.mk_op_smul K (Γ.D (a + b + (c + d))).carrier
    (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + b + (c + d)) e))
    ((Γ.gaugeCast (pcdV5TotalHeq a b c d)).toAlgEquiv t) m
    (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d) w)

private noncomputable def pcdV5TotalFwd :
    RelTensor K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) →ₗ[K]
      GQ2 K Γ a b (c + d) e :=
  RelTensor.lift (pcdV5TotalFwdBilin K Γ a b c d e)
    (pcdV5TotalFwd_balanced K Γ a b c d e)

private theorem pcdV5TotalFwd_mk (m : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :
    pcdV5TotalFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier
          (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m w)
      = GQ2.mk K Γ a b (c + d) e m
          (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d) w) := by
  rw [pcdV5TotalFwd, RelTensor.lift_mk, pcdV5TotalFwdBilin_apply]

private noncomputable def pcdV5TotalBwdBilin :
    GBR Γ a b (c + d) →ₗ[K]
      FusionColumn (Γ.fuse (a + b + (c + d)) e) →ₗ[K]
        RelTensor K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
          (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :=
  (RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
    (FusionColumn (Γ.fuse (a + (b + (c + d))) e))).compl₂
      (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)).symm.toLinearMap

private theorem pcdV5TotalBwdBilin_apply (m : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    pcdV5TotalBwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
          (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m
          ((gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)).symm w) :=
  rfl

private theorem pcdV5TotalBwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + b + (c + d))).carrier
      (pcdV5TotalBwdBilin K Γ a b c d e) := by
  intro s m w
  rw [pcdV5TotalBwdBilin_apply, pcdV5TotalBwdBilin_apply,
    GBR.recast_op_smul_def, gColumnCastFst_symm_xslot,
    gaugeCast_symm_apply' K Γ (pcdV5TotalHeq a b c d)]
  exact RelTensor.mk_op_smul K (Γ.D (a + (b + (c + d)))).carrier
    (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e))
    ((Γ.gaugeCast (add_assoc a b (c + d))).toAlgEquiv s) m
    ((gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)).symm w)

private noncomputable def pcdV5TotalBwd :
    GQ2 K Γ a b (c + d) e →ₗ[K]
      RelTensor K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :=
  RelTensor.lift (pcdV5TotalBwdBilin K Γ a b c d e)
    (pcdV5TotalBwd_balanced K Γ a b c d e)

private theorem pcdV5TotalBwd_mk (m : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    pcdV5TotalBwd K Γ a b c d e (GQ2.mk K Γ a b (c + d) e m w)
      = RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
          (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m
          ((gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)).symm w) := by
  show RelTensor.lift (pcdV5TotalBwdBilin K Γ a b c d e)
      (pcdV5TotalBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier (GBR Γ a b (c + d))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)) m w) = _
  rw [RelTensor.lift_mk, pcdV5TotalBwdBilin_apply]

private theorem pcdV5TotalFwd_bwd :
    (pcdV5TotalFwd K Γ a b c d e).comp (pcdV5TotalBwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show pcdV5TotalFwd K Γ a b c d e
      (pcdV5TotalBwd K Γ a b c d e (GQ2.mk K Γ a b (c + d) e m w))
    = GQ2.mk K Γ a b (c + d) e m w
  rw [pcdV5TotalBwd_mk, pcdV5TotalFwd_mk, LinearEquiv.apply_symm_apply]

private theorem pcdV5TotalBwd_fwd :
    (pcdV5TotalBwd K Γ a b c d e).comp (pcdV5TotalFwd K Γ a b c d e)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show pcdV5TotalBwd K Γ a b c d e
      (pcdV5TotalFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
          (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m w))
    = RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m w
  rw [pcdV5TotalFwd_mk, pcdV5TotalBwd_mk, LinearEquiv.symm_apply_apply]

noncomputable def pcdV5TotalCast :
    RelTensor K (Γ.D (a + (b + (c + d)))).carrier (GBR Γ a b (c + d))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e))
      ≃ₗ[K] GQ2 K Γ a b (c + d) e :=
  LinearEquiv.ofLinear (pcdV5TotalFwd K Γ a b c d e)
    (pcdV5TotalBwd K Γ a b c d e)
    (pcdV5TotalFwd_bwd K Γ a b c d e)
    (pcdV5TotalBwd_fwd K Γ a b c d e)

theorem pcdV5TotalCast_mk (m : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :
    pcdV5TotalCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier
          (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m w)
      = GQ2.mk K Γ a b (c + d) e m
          (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d) w) :=
  pcdV5TotalFwd_mk K Γ a b c d e m w

/-- Reassociate the transported middle tensor into the right-route
factor expected by `GQ2`. -/
noncomputable def pcdV5MiddleAssoc :
    RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e)
      ≃ₗ[K] RelTensor K (Γ.D (a + (b + (c + d)))).carrier
        (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :=
  (RelTensor.assoc K (Γ.D (b + (c + d))).carrier
    (Γ.D (a + (b + (c + d)))).carrier
    (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + (c + d))))
    (FusionColumn (Γ.fuse (a + (b + (c + d))) e))).symm

theorem pcdV5MiddleAssoc_mk
    (m : FusionColumn (Γ.fuse b (c + d)))
    (u : FusionColumn (Γ.fuse a (b + (c + d))))
    (v : FusionColumn (Γ.fuse (a + (b + (c + d))) e)) :
    pcdV5MiddleAssoc K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e) m
          (GBL.mk Γ a (b + (c + d)) e u v))
      = RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier
          (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e))
          (GBR.mk Γ a b (c + d) m u) v :=
  RelTensor.assoc_symm_mk K (Γ.D (b + (c + d))).carrier
    (Γ.D (a + (b + (c + d)))).carrier
    (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + (c + d))))
    (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m u v

/-- The complete residual transport at `V5`, after the explicit
`F_{c,d}` factor has been peeled. -/
noncomputable def pcdV5InnerCast :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (GBL Γ a (b + c + d) e)
      ≃ₗ[K] GQ2 K Γ a b (c + d) e :=
  ((pcdV5MiddleCast K Γ a b c d e).trans
    (pcdV5MiddleAssoc K Γ a b c d e)).trans
      (pcdV5TotalCast K Γ a b c d e)

theorem pcdV5InnerCast_mk
    (m : FusionColumn (Γ.fuse b (c + d)))
    (u : FusionColumn (Γ.fuse a (b + c + d)))
    (v : FusionColumn (Γ.fuse (a + (b + c + d)) e)) :
    pcdV5InnerCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m
          (GBL.mk Γ a (b + c + d) e u v))
      = GQ2.mk K Γ a b (c + d) e
          (GBR.mk Γ a b (c + d) m
            (fusionColumnCast K Γ a (add_assoc b c d) u))
          (gColumnCastFst K Γ e (pcdV5TotalHeq a b c d)
            (gColumnCastFst K Γ e (congrArg (a + ·) (add_assoc b c d)) v)) := by
  rw [pcdV5InnerCast, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    pcdV5MiddleCast_mk, pcdGblCastSnd_mk, pcdV5MiddleAssoc_mk,
    pcdV5TotalCast_mk]

theorem pcdV5MiddleCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) :
    pcdV5MiddleCast K Γ a b c d e (τ • n)
      = τ • pcdV5MiddleCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m q =>
      rw [show (τ • RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) m q
            : RelTensor K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e))
          = RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)
              (τ • m) q from
        leftActionEnd_mk K (Γ.D (b + c + d)).carrier
          (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) τ m q]
      rw [pcdV5MiddleCast_mk, pcdV5MiddleCast_mk]
      exact (leftActionEnd_mk K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e)
        τ m (pcdGblCastSnd K Γ a e (add_assoc b c d) q)).symm

/-- Raw associator naturality for the untouched first slot.  Keeping the
three tensor factors explicit prevents named-type unfolding from changing
the inferred module instances during the nested induction. -/
private noncomputable instance pcdV5RawGbrCdModule :
    Module (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d))))) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier (GBR Γ a b (c + d)))

private instance pcdV5RawGbrCdTower :
    IsScalarTower K (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d))))) :=
  inferInstanceAs (IsScalarTower K (Γ.D (c + d)).carrier (GBR Γ a b (c + d)))

private instance pcdV5RawGbrCdComm :
    SMulCommClass (Γ.D (c + d)).carrier
      ((Γ.D (a + (b + (c + d)))).carrier)ᵐᵒᵖ
      (RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d))))) :=
  inferInstanceAs (SMulCommClass (Γ.D (c + d)).carrier
    ((Γ.D (a + (b + (c + d)))).carrier)ᵐᵒᵖ (GBR Γ a b (c + d)))

set_option maxHeartbeats 1000000 in
private theorem pcdV5MiddleAssoc_cdSlotCore (τ : (Γ.D (c + d)).carrier)
    (X : RelTensor K (Γ.D (b + (c + d))).carrier
      (FusionColumn (Γ.fuse b (c + d)))
      (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
        (FusionColumn (Γ.fuse a (b + (c + d))))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e)))) :
    (RelTensor.assoc K (Γ.D (b + (c + d))).carrier
        (Γ.D (a + (b + (c + d)))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d))))
        (FusionColumn (Γ.fuse (a + (b + (c + d))) e))).symm (τ • X)
      = τ •
        (RelTensor.assoc K (Γ.D (b + (c + d))).carrier
          (Γ.D (a + (b + (c + d)))).carrier
          (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d))))
          (FusionColumn (Γ.fuse (a + (b + (c + d))) e))).symm X := by
  induction X using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | mk m Y =>
      have hτm :
          (τ • RelTensor.mk K (Γ.D (b + (c + d))).carrier
              (FusionColumn (Γ.fuse b (c + d)))
              (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                (FusionColumn (Γ.fuse a (b + (c + d))))
                (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) m Y
            : RelTensor K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))))
            = RelTensor.mk K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) (τ • m) Y :=
        leftActionEnd_mk K (Γ.D (b + (c + d))).carrier
          (FusionColumn (Γ.fuse b (c + d)))
          (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
            (FusionColumn (Γ.fuse a (b + (c + d))))
            (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) τ m Y
      rw [hτm]
      clear hτm
      induction Y using RelTensor.induction_on with
      | zero =>
          rw [show RelTensor.mk K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) m 0 = 0 from by
              simp only [map_zero],
            show RelTensor.mk K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) (τ • m) 0 = 0 from by
              simp only [map_zero], map_zero, smul_zero]
      | mk u v =>
          rw [RelTensor.assoc_symm_mk, RelTensor.assoc_symm_mk]
          exact (leftActionEnd_mk K (Γ.D (a + (b + (c + d)))).carrier
            (RelTensor K (Γ.D (b + (c + d))).carrier
              (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + (c + d)))))
            (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) τ
            (RelTensor.mk K (Γ.D (b + (c + d))).carrier
              (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + (c + d)))) m u) v).symm
      | add x y hx hy =>
          have e1 : RelTensor.mk K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) m (x + y)
              = RelTensor.mk K (Γ.D (b + (c + d))).carrier
                  (FusionColumn (Γ.fuse b (c + d)))
                  (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                    (FusionColumn (Γ.fuse a (b + (c + d))))
                    (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) m x
                + RelTensor.mk K (Γ.D (b + (c + d))).carrier
                    (FusionColumn (Γ.fuse b (c + d)))
                    (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                      (FusionColumn (Γ.fuse a (b + (c + d))))
                      (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) m y :=
            map_add _ _ _
          have e2 : RelTensor.mk K (Γ.D (b + (c + d))).carrier
                (FusionColumn (Γ.fuse b (c + d)))
                (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                  (FusionColumn (Γ.fuse a (b + (c + d))))
                  (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) (τ • m) (x + y)
              = RelTensor.mk K (Γ.D (b + (c + d))).carrier
                  (FusionColumn (Γ.fuse b (c + d)))
                  (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                    (FusionColumn (Γ.fuse a (b + (c + d))))
                    (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) (τ • m) x
                + RelTensor.mk K (Γ.D (b + (c + d))).carrier
                    (FusionColumn (Γ.fuse b (c + d)))
                    (RelTensor K (Γ.D (a + (b + (c + d)))).carrier
                      (FusionColumn (Γ.fuse a (b + (c + d))))
                      (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) (τ • m) y :=
            map_add _ _ _
          rw [e1, e2, map_add, map_add, hx, hy, smul_add]

theorem pcdV5MiddleAssoc_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (b + (c + d))).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + (c + d)) e)) :
    pcdV5MiddleAssoc K Γ a b c d e (τ • n)
      = τ • pcdV5MiddleAssoc K Γ a b c d e n :=
  pcdV5MiddleAssoc_cdSlotCore K Γ a b c d e τ n

theorem pcdV5TotalCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (a + (b + (c + d)))).carrier
      (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e))) :
    pcdV5TotalCast K Γ a b c d e (τ • n)
      = τ • pcdV5TotalCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m w =>
      rw [show (τ • RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier
            (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) m w
            : RelTensor K (Γ.D (a + (b + (c + d)))).carrier
              (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)))
          = RelTensor.mk K (Γ.D (a + (b + (c + d)))).carrier
              (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e))
              (τ • m) w from
        leftActionEnd_mk K (Γ.D (a + (b + (c + d)))).carrier
          (GBR Γ a b (c + d)) (FusionColumn (Γ.fuse (a + (b + (c + d))) e)) τ m w,
        pcdV5TotalCast_mk, pcdV5TotalCast_mk, GQ2.cslot_smul_mk]

theorem pcdV5InnerCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) :
    pcdV5InnerCast K Γ a b c d e (τ • n)
      = τ • pcdV5InnerCast K Γ a b c d e n := by
  change pcdV5TotalCast K Γ a b c d e
      (pcdV5MiddleAssoc K Γ a b c d e
        (pcdV5MiddleCast K Γ a b c d e (τ • n)))
    = τ • pcdV5TotalCast K Γ a b c d e
        (pcdV5MiddleAssoc K Γ a b c d e
          (pcdV5MiddleCast K Γ a b c d e n))
  rw [pcdV5MiddleCast_cdSlot, pcdV5MiddleAssoc_cdSlot,
    pcdV5TotalCast_cdSlot]

/-- Peel the explicit `F_{c,d}` spectator from `V5`. -/
noncomputable def pcdV5Peel : V5 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (RelTensor K (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) :=
  (gV5Assoc K Γ a b c d e).trans
    (RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
      (GBL Γ a (b + c + d) e))

noncomputable def omegaPcdV5 : V5 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2 K Γ a b (c + d) e) :=
  (pcdV5Peel K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (pcdV5InnerCast K Γ a b c d e)
      (pcdV5InnerCast_cdSlot K Γ a b c d e))

private noncomputable def pcdV5AssocA : V5 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
      (RelTensor K (Γ.D (a + b + c + d)).carrier
        (FusionColumn (Γ.fuse a (b + c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
  RelTensor.assoc K (Γ.D (b + c + d)).carrier
    (Γ.D (a + b + c + d)).carrier
    (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))
    (FusionColumn (Γ.fuse (a + b + c + d) e))

private noncomputable def pcdV5AssocB :
    RelTensor K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
        (RelTensor K (Γ.D (a + b + c + d)).carrier
          (FusionColumn (Γ.fuse a (b + c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)))
      ≃ₗ[K] RelTensor K (Γ.D (b + c + d)).carrier
        (GBR Γ b c d) (GBL Γ a (b + c + d) e) :=
  RelTensor.mapEquivRight K (gFourCast K Γ a b c d e)
    (gFourCast_midSlot K Γ a b c d e)

private theorem pcdV5OuterAssoc_mk
    (m : GBR Γ b c d)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5AssocA K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d m x) w)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d)
          (RelTensor K (Γ.D (a + b + c + d)).carrier
            (FusionColumn (Γ.fuse a (b + c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e))) m
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (FusionColumn (Γ.fuse a (b + c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) x w) :=
  RelTensor.assoc_mk K (Γ.D (b + c + d)).carrier
    (Γ.D (a + b + c + d)).carrier
    (GBR Γ b c d) (FusionColumn (Γ.fuse a (b + c + d)))
    (FusionColumn (Γ.fuse (a + b + c + d) e)) m x w

private theorem pcdV5FourMap_mk
    (m : GBR Γ b c d)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse a (b + c + d)))
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    pcdV5AssocB K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d)
          (RelTensor K (Γ.D (a + b + c + d)).carrier
            (FusionColumn (Γ.fuse a (b + c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e))) m n)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBL Γ a (b + c + d) e) m
          (gFourCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : GBR Γ b c d →ₗ[K] GBR Γ b c d)
    (gFourCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (gFourCast_midSlot K Γ a b c d e) m n

private theorem pcdV5Assoc_mk
    (m : GBR Γ b c d)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gV5Assoc K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d m x) w)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBL Γ a (b + c + d) e) m
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) w)) := by
  change pcdV5AssocB K Γ a b c d e
      (pcdV5AssocA K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d m x) w)) = _
  rw [pcdV5OuterAssoc_mk,
    pcdV5FourMap_mk, gFourCast_mk]

private theorem pcdV5PeelAssoc_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (n : GBL Γ a (b + c + d) e) :
    (RelTensor.assoc K (Γ.D (c + d)).carrier
        (Γ.D (b + c + d)).carrier
        (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
        (GBL Γ a (b + c + d) e))
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBL Γ a (b + c + d) e)
          (GBR.mk Γ b c d u v) n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) v n) :=
  RelTensor.assoc_mk K (Γ.D (c + d)).carrier
    (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
    (GBL Γ a (b + c + d) e) u v n

private theorem pcdV5Peel_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5Peel K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) v
            (GBL.mk Γ a (b + c + d) e x
              (gColumnCastFst K Γ e (add_assoc_four a b c d) w))) := by
  rw [pcdV5Peel, LinearEquiv.trans_apply, pcdV5Assoc_mk]
  exact pcdV5PeelAssoc_mk K Γ a b c d e u v
    (GBL.mk Γ a (b + c + d) e x
      (gColumnCastFst K Γ e (add_assoc_four a b c d) w))

private theorem pcdV5Map_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) :
    (RelTensor.mapEquivRight K (pcdV5InnerCast K Γ a b c d e)
        (pcdV5InnerCast_cdSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e)) u n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u
          (pcdV5InnerCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K]
      FusionColumn (Γ.fuse c d))
    (pcdV5InnerCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (pcdV5InnerCast_cdSlot K Γ a b c d e) u n

theorem omegaPcdV5_core_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV5 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u
          (pcdV5InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) v
              (GBL.mk Γ a (b + c + d) e x
                (gColumnCastFst K Γ e (add_assoc_four a b c d) w)))) := by
  rw [omegaPcdV5, LinearEquiv.trans_apply, pcdV5Peel_mk, pcdV5Map_mk]

/-- Typed packing of a `GQ4` value into `V5`.  This small wrapper keeps
the named `V5` module instance stable in edge-recognition proofs. -/
noncomputable def pcdV5Pack
    (m : GQ4 K Γ a b c d)
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    V5 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b + c + d)).carrier
    (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) m w

private noncomputable def pcdV5CloseMap
    (u : FusionColumn (Γ.fuse c d)) :
    GBR Γ a b (c + d) →ₗ[K] GQ4 K Γ a b c d :=
  (gq4Close K Γ a b c d).toLinearMap.comp
    (RelTensor.mk K (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) u)

private noncomputable def pcdV5OuterMap
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    GQ4 K Γ a b c d →ₗ[K] V5 K Γ a b c d e :=
  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
    (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))).flip w

private noncomputable def pcdV5ClosedExtract
    (u : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    GBR Γ a b (c + d) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2 K Γ a b (c + d) e) :=
  (omegaPcdV5 K Γ a b c d e).toLinearMap.comp
    ((pcdV5OuterMap K Γ a b c d e w).comp
      (pcdV5CloseMap K Γ a b c d u))

private noncomputable def pcdV5ResidualExtract
    (u : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    GBR Γ a b (c + d) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2 K Γ a b (c + d) e) :=
  (RelTensor.mk K (Γ.D (c + d)).carrier
    (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u).comp
      ((GQ2.mk K Γ a b (c + d) e).flip
        (gColumnCastFst K Γ e (add_assoc (a + b) c d) w))

private theorem pcdV5ClosedExtract_apply
    (u : FusionColumn (Γ.fuse c d))
    (n : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5ClosedExtract K Γ a b c d e u w n
      = omegaPcdV5 K Γ a b c d e
          (pcdV5Pack K Γ a b c d e
            (gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d u n)) w) :=
  rfl

private theorem pcdV5ResidualExtract_apply
    (u : FusionColumn (Γ.fuse c d))
    (n : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5ResidualExtract K Γ a b c d e u w n
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u
          (GQ2.mk K Γ a b (c + d) e n
            (gColumnCastFst K Γ e (add_assoc (a + b) c d) w)) :=
  rfl

private theorem pcdV5Pack_close_gen
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (x : FusionColumn (Γ.fuse a (b + (c + d))))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5Pack K Γ a b c d e
        (gq4Close K Γ a b c d
          (GQ4r.mk K Γ a b c d u (GBR.mk Γ a b (c + d) v x))) w
      = pcdV5Pack K Γ a b c d e
          (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v)
            (fusionColumnCast K Γ a (add_assoc b c d).symm x)) w :=
  congrArg (fun z => pcdV5Pack K Γ a b c d e z w)
    (gq4Close_mk K Γ a b c d u v x)

private theorem omegaPcdV5_pack_core
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV5 K Γ a b c d e
        (pcdV5Pack K Γ a b c d e
          (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u
          (pcdV5InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBL Γ a (b + c + d) e) v
              (GBL.mk Γ a (b + c + d) e x
                (gColumnCastFst K Γ e (add_assoc_four a b c d) w)))) :=
  omegaPcdV5_core_mk K Γ a b c d e u v x w

private theorem pcdV5ClosedExtract_gen
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (x : FusionColumn (Γ.fuse a (b + (c + d))))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5ClosedExtract K Γ a b c d e u w (GBR.mk Γ a b (c + d) v x)
      = pcdV5ResidualExtract K Γ a b c d e u w
          (GBR.mk Γ a b (c + d) v x) := by
  rw [pcdV5ClosedExtract_apply, pcdV5ResidualExtract_apply,
    pcdV5Pack_close_gen, omegaPcdV5_pack_core, pcdV5InnerCast_mk,
    pcdFusionColumnCast_symm_eq K Γ a (add_assoc b c d),
    LinearEquiv.apply_symm_apply,
    gColumnCastFst_trans, gColumnCastFst_trans]

private noncomputable def pcdV5ClosedExtractRaw
    (u : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d)))) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2 K Γ a b (c + d) e) where
  toFun := fun n => pcdV5ClosedExtract K Γ a b c d e u w n
  map_add' := (pcdV5ClosedExtract K Γ a b c d e u w).map_add
  map_smul' := (pcdV5ClosedExtract K Γ a b c d e u w).map_smul

private noncomputable def pcdV5ResidualExtractRaw
    (u : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    RelTensor K (Γ.D (b + (c + d))).carrier
        (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d)))) →ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2 K Γ a b (c + d) e) where
  toFun := fun n => pcdV5ResidualExtract K Γ a b c d e u w n
  map_add' := (pcdV5ResidualExtract K Γ a b c d e u w).map_add
  map_smul' := (pcdV5ResidualExtract K Γ a b c d e u w).map_smul

private theorem pcdV5Extract_maps_eq
    (u : FusionColumn (Γ.fuse c d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV5ClosedExtractRaw K Γ a b c d e u w
      = pcdV5ResidualExtractRaw K Γ a b c d e u w := by
  refine RelTensor.hom_ext fun v x => ?_
  exact pcdV5ClosedExtract_gen K Γ a b c d e u v x w

/-- The `V5` extraction cancels the closing presentation used by edge 5.
The residual `GBR(a,b,c+d)` element is deliberately kept opaque. -/
theorem omegaPcdV5_gq4Close_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : GBR Γ a b (c + d))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV5 K Γ a b c d e
        (pcdV5Pack K Γ a b c d e
          (gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d u n)) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2 K Γ a b (c + d) e) u
          (GQ2.mk K Γ a b (c + d) e n
            (gColumnCastFst K Γ e (add_assoc (a + b) c d) w)) := by
  change pcdV5ClosedExtract K Γ a b c d e u w n
    = pcdV5ResidualExtract K Γ a b c d e u w n
  exact LinearMap.congr_fun (pcdV5Extract_maps_eq K Γ a b c d e u w) n

theorem E18M_leaf_pcd {i j : ZMod 2}
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    {v : FusionColumn (Γ.fuse b (c + d))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E18M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w)
      = ((sgn (gParity K Γ a (b + c + d) e * (i + j)) : ℤˣ) : ℤ) •
          (gV11Assoc K Γ a b c d e).symm
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (GBR Γ b c d) (GBR Γ a (b + c + d) e)
              (GBR.mk Γ b c d u v)
              (gTCanon K Γ a (b + c + d) e
                (GBL.mk Γ a (b + c + d) e x
                  (gColumnCastFst K Γ e (add_assoc_four a b c d) w)))) := by
  have hm : GBR.mk Γ b c d u v ∈ GBR.grading Γ b c d (i + j) :=
    GBR.mk_mem_grading Γ b c d hu hv
  show (gV11Assoc K Γ a b c d e).symm
      (gE18Step K Γ a b c d e
        (gV5Assoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ4 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ4.mk K Γ a b c d (GBR.mk Γ b c d u v) x) w))) = _
  rw [pcdV5Assoc_mk]
  change (gV11Assoc K Γ a b c d e).symm
      (smap (Γ.D (b + c + d)).grading (GBR.grading Γ b c d)
        (gTCanon K Γ a (b + c + d) e).toLinearMap
        (gParity K Γ a (b + c + d) e)
        (gCanonMidSlot K Γ a (b + c + d) e)
        (RelTensor.mk K (Γ.D (b + c + d)).carrier
          (GBR Γ b c d) (GBL Γ a (b + c + d) e)
          (GBR.mk Γ b c d u v)
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) w)))) = _
  rw [smap_mk_of_mem (Γ.D (b + c + d)).grading (GBR.grading Γ b c d)
      (gTCanon K Γ a (b + c + d) e).toLinearMap
      (gParity K Γ a (b + c + d) e)
      (gCanonMidSlot K Γ a (b + c + d) e) hm,
    map_zsmul]
  rfl

private theorem pcdV11Peel_gV11Assoc_symm_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (n : GBR Γ a (b + c + d) e) :
    pcdV11Peel K Γ a b c d e
        ((gV11Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (GBR Γ b c d) (GBR Γ a (b + c + d) e)
            (GBR.mk Γ b c d u v) n))
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e)) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v n) := by
  change (RelTensor.assoc K (Γ.D (c + d)).carrier
      (Γ.D (b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse b (c + d)))
      (GBR Γ a (b + c + d) e))
      (gV11Assoc K Γ a b c d e
        ((gV11Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (GBR Γ b c d) (GBR Γ a (b + c + d) e)
            (GBR.mk Γ b c d u v) n))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact pcdV11Peel_assoc_mk K Γ a b c d e u v n

theorem omegaPcdV11_gV11Assoc_symm_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse b (c + d)))
    (n : GBR Γ a (b + c + d) e) :
    omegaPcdV11 K Γ a b c d e
        ((gV11Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c + d)).carrier
            (GBR Γ b c d) (GBR Γ a (b + c + d) e)
            (GBR.mk Γ b c d u v) n))
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ3 K Γ a b (c + d) e) u
          (pcdV11InnerCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d)).carrier
              (FusionColumn (Γ.fuse b (c + d))) (GBR Γ a (b + c + d) e) v n)) := by
  rw [omegaPcdV11, LinearEquiv.trans_apply,
    pcdV11Peel_gV11Assoc_symm_mk, pcdV11Map_mk]

/-! ### The `V8` extraction -/

/-- Undo the final associator in `V8Inner`, exposing `F_{c,d}` while
leaving the outer `F_{a,b}` in place. -/
noncomputable def pcdV8Split : V8 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GBR Γ (a + b) (c + d) e)) :=
  RelTensor.mapEquivRight K (gE11GBRAssoc K Γ a b c d e).symm
    (leftEquivariant_symm K (gE11GBRAssoc K Γ a b c d e)
      (gE11GBRAssoc_aSlot_general K Γ a b c d e))

private theorem pcdGE11Symm_mk
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse (c + d) e))
    (x : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    (gE11GBRAssoc K Γ a b c d e).symm
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e)))
          (GBL.mk Γ c d e u v) x)
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ (a + b) (c + d) e) u
          (GBR.mk Γ (a + b) (c + d) e v x) := by
  have h := RelTensor.assoc_symm_mk K (Γ.D (c + d)).carrier
    (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c d))
    (FusionColumn (Γ.fuse (c + d) e))
    (FusionColumn (Γ.fuse (a + b) (c + d + e))) u v x
  calc
    (gE11GBRAssoc K Γ a b c d e).symm
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e)))
          (GBL.mk Γ c d e u v) x)
      = (gE11GBRAssoc K Γ a b c d e).symm
          (gE11GBRAssoc K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ (a + b) (c + d) e) u
              (GBR.mk Γ (a + b) (c + d) e v x))) := congrArg _ h.symm
    _ = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ (a + b) (c + d) e) u
          (GBR.mk Γ (a + b) (c + d) e v x) :=
      (gE11GBRAssoc K Γ a b c d e).symm_apply_apply _

private theorem pcdV8Split_outer_mk (t : FusionColumn (Γ.fuse a b))
    (n : V8Inner K Γ a b c d e) :
    pcdV8Split K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V8Inner K Γ a b c d e) t n)
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e)) t
          ((gE11GBRAssoc K Γ a b c d e).symm n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K]
      FusionColumn (Γ.fuse a b))
    (gE11GBRAssoc K Γ a b c d e).symm.toLinearMap (fun _ _ => rfl)
    (leftEquivariant_symm K (gE11GBRAssoc K Γ a b c d e)
      (gE11GBRAssoc_aSlot_general K Γ a b c d e)) t n

theorem pcdV8Split_mk
    (t : FusionColumn (Γ.fuse a b))
    (u : FusionColumn (Γ.fuse c d))
    (v : FusionColumn (Γ.fuse (c + d) e))
    (x : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    pcdV8Split K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e)))
            (GBL.mk Γ c d e u v) x))
      = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e)) t
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) u
            (GBR.mk Γ (a + b) (c + d) e v x)) := by
  rw [pcdV8Split_outer_mk, pcdGE11Symm_mk]

private theorem pcdV8LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
      (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse c d)) := by
  intro l i x hx n hn p
  show midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) x
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GBR Γ (a + b) (c + d) e) n p)
    = ((sgn (l * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ (a + b) (c + d) e) n (x • p)
  exact midEnd_mk_of_mem (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
    (gbrBslotAslotSuperComm K Γ a b c d e) hn hx p

private noncomputable instance pcdV8RawGQ5CdModule :
    Module (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (GBR Γ (a + b) (c + d) e)) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier (GQ5 K Γ a b (c + d) e))

private theorem pcdV8LawB :
    MidSignLaw K (Γ.D (c + d)).carrier (Γ.D (a + b)).carrier
      (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) (c + d) e)
      (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  exact GQ5.cslot_smul_mk_of_mem (K := K) (Γ := Γ)
    (a := a) (b := b) (c := c + d) (d := e) hz hm p

/-- Spectator extraction at `V8`.  The only nontrivial move after
`pcdV8Split` is the universal Koszul middle interchange. -/
noncomputable def omegaPcdV8 : V8 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ5 K Γ a b (c + d) e) :=
  (pcdV8Split K Γ a b c d e).trans
    (midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse c d))
      (GBR Γ (a + b) (c + d) e)
      (Γ.D (a + b)).grading (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
      (pcdV8LawA K Γ a b c d e) (pcdV8LawB K Γ a b c d e))

theorem omegaPcdV8_mk_of_mem {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)} (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (v : FusionColumn (Γ.fuse (c + d) e))
    (x : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaPcdV8 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e)))
            (GBL.mk Γ c d e u v) x))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ5 K Γ a b (c + d) e) u
            (GQ5.mk K Γ a b (c + d) e t
              (GBR.mk Γ (a + b) (c + d) e v x)) := by
  rw [omegaPcdV8, LinearEquiv.trans_apply, pcdV8Split_mk]
  exact midSwap_mk_of_mem K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse c d))
    (GBR Γ (a + b) (c + d) e)
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
    (pcdV8LawA K Γ a b c d e) (pcdV8LawB K Γ a b c d e) hu ht
    (GBR.mk Γ (a + b) (c + d) e v x)

/-- A form of the `V8` extraction adapted to the output of `E11M`.
The closing `gE11GBRAssoc` cancels before the middle interchange. -/
theorem omegaPcdV8_gE11Assoc_mk_of_mem {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (n : GBR Γ (a + b) (c + d) e) :
    omegaPcdV8 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V8Inner K Γ a b c d e) t
          (gE11GBRAssoc K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier
              (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e) u n)))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GQ5 K Γ a b (c + d) e) u
            (GQ5.mk K Γ a b (c + d) e t n) := by
  rw [omegaPcdV8, LinearEquiv.trans_apply, pcdV8Split_outer_mk,
    LinearEquiv.symm_apply_apply]
  exact midSwap_mk_of_mem K (Γ.D (a + b)).carrier
    (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse c d))
    (pcdV8LawA K Γ a b c d e) (pcdV8LawB K Γ a b c d e) hu ht n

/-! ### The `V3` extraction -/

/-- The residual `D_{c+d}` action on the right-associated
`F_{a,b} ⊗ GBL(a+b,c+d,e)` factor.  It is the universal signed middle
action; this raw instance is the codomain-side action for `gq1Assoc`. -/
private noncomputable instance pcdV3RightCdModule :
    Module (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (GBL Γ (a + b) (c + d) e)) :=
  Module.compHom _
    ((midAlgHom (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)).toRingHom)

private theorem pcdV3LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)
      (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse c d)) := by
  intro l i x hx n hn p
  show midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gblSuperComm K Γ a b c d e)) x
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GBL Γ (a + b) (c + d) e) n p)
    = ((sgn (l * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBL Γ (a + b) (c + d) e) n (x • p)
  exact midEnd_mk_of_mem (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
    (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
      (gblSuperComm K Γ a b c d e)) hn hx p

private theorem pcdV3LawB :
    MidSignLaw K (Γ.D (c + d)).carrier (Γ.D (a + b)).carrier
      (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e)
      (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  show midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e) z
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (GBL Γ (a + b) (c + d) e) m p)
    = ((sgn (l * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GBL Γ (a + b) (c + d) e) m (z • p)
  exact midEnd_mk_of_mem (Γ.D (a + b)).grading
    (FusionColumn.grading (Γ.fuse a b)) (Γ.D (c + d)).grading
    (gblSuperComm K Γ a b c d e) hm hz p

/-- Expose `F_{c,d}` at `V3` and interchange it with `F_{a,b}`. -/
noncomputable def pcdV3Swap : V3 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (GBL Γ (a + b) (c + d) e)) :=
  (gV3AssocABC K Γ a b c d e).trans
    (midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse c d))
      (GBL Γ (a + b) (c + d) e)
      (Γ.D (a + b)).grading (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse a b)) (FusionColumn.grading (Γ.fuse c d))
      (pcdV3LawA K Γ a b c d e) (pcdV3LawB K Γ a b c d e))

private noncomputable instance pcdV3RawHeadCdModule :
    Module (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) (c + d)))) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier (GBL Γ a b (c + d)))

private instance pcdV3RawHeadCdTower :
    IsScalarTower K (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) (c + d)))) :=
  inferInstanceAs (IsScalarTower K (Γ.D (c + d)).carrier (GBL Γ a b (c + d)))

private instance pcdV3RawHeadCdTotalComm :
    SMulCommClass (Γ.D (c + d)).carrier
      ((Γ.D (a + b + (c + d))).carrier)ᵐᵒᵖ
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) (c + d)))) :=
  inferInstanceAs (SMulCommClass (Γ.D (c + d)).carrier
    ((Γ.D (a + b + (c + d))).carrier)ᵐᵒᵖ (GBL Γ a b (c + d)))

private noncomputable instance pcdV3RawTailAbModule :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))) :=
  inferInstanceAs (Module (Γ.D (a + b)).carrier (GBL Γ (a + b) (c + d) e))

private noncomputable instance pcdV3RawTailCdModule :
    Module (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier (GBL Γ (a + b) (c + d) e))

private instance pcdV3RawTailCdTower :
    IsScalarTower K (Γ.D (c + d)).carrier
      (RelTensor K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))) :=
  inferInstanceAs (IsScalarTower K (Γ.D (c + d)).carrier
    (GBL Γ (a + b) (c + d) e))

private theorem pcdV3RawTailSuperComm :
    SuperCommSMul (Γ.D (a + b)).grading (Γ.D (c + d)).grading
      (RelTensor K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))) :=
  gblSuperComm K Γ a b c d e

set_option maxHeartbeats 1000000 in
private theorem pcdGq1Assoc_cdSlot_leaf (τ : (Γ.D (c + d)).carrier)
    (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    (RelTensor.assoc K (Γ.D (a + b)).carrier
        (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)))
      (leftActionEnd K (Γ.D (a + b + (c + d))).carrier
        (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d))))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)) τ
        (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
          (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d))))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e))
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d))) u v) w))
    = midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (Γ.D (c + d)).grading (pcdV3RawTailSuperComm K Γ a b c d e) τ
        ((RelTensor.assoc K (Γ.D (a + b)).carrier
          (Γ.D (a + b + (c + d))).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e)))
          (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
            (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d))))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d))) u v) w)) := by
  rw [leftActionEnd_mk]
  change (RelTensor.assoc K (Γ.D (a + b)).carrier
        (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)))
      (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
        (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d))))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))
        (midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
          (Γ.D (c + d)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d))) τ
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d))) u v)) w)
    = midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (Γ.D (c + d)).grading (pcdV3RawTailSuperComm K Γ a b c d e) τ
        ((RelTensor.assoc K (Γ.D (a + b)).carrier
          (Γ.D (a + b + (c + d))).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e)))
          (RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
            (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d))))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d))) u v) w))
  rw [midEnd_mk, midBilin_apply]
  rw [map_sub, map_zsmul]
  rw [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [map_sub (RelTensor.assoc K (Γ.D (a + b)).carrier
    (Γ.D (a + b + (c + d))).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
    (FusionColumn (Γ.fuse (a + b + (c + d)) e))), map_zsmul]
  rw [RelTensor.assoc_mk, RelTensor.assoc_mk, RelTensor.assoc_mk,
    midEnd_mk, midBilin_apply,
    show τ • RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
          (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e)) v w
        = RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
            (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e)) (τ • v) w from
      leftActionEnd_mk K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)) τ v w,
    show (oddPart (Γ.D (c + d)).grading τ) •
          RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
            (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e)) v w
        = RelTensor.mk K (Γ.D (a + b + (c + d))).carrier
            (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e))
            ((oddPart (Γ.D (c + d)).grading τ) • v) w from
      leftActionEnd_mk K (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e))
        (oddPart (Γ.D (c + d)).grading τ) v w]

private theorem pcdGq1Assoc_cdSlot_core (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (a + b + (c + d))).carrier
      (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (FusionColumn (Γ.fuse (a + b) (c + d))))
      (FusionColumn (Γ.fuse (a + b + (c + d)) e))) :
    (RelTensor.assoc K (Γ.D (a + b)).carrier
        (Γ.D (a + b + (c + d))).carrier
        (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)))
      (leftActionEnd K (Γ.D (a + b + (c + d))).carrier
        (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d))))
        (FusionColumn (Γ.fuse (a + b + (c + d)) e)) τ n)
      = midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
          (Γ.D (c + d)).grading (pcdV3RawTailSuperComm K Γ a b c d e) τ
          ((RelTensor.assoc K (Γ.D (a + b)).carrier
            (Γ.D (a + b + (c + d))).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e))) n) := by
  have h :
      (RelTensor.assoc K (Γ.D (a + b)).carrier
          (Γ.D (a + b + (c + d))).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e))).toLinearMap.comp
        (leftActionEnd K (Γ.D (a + b + (c + d))).carrier
          (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d))))
          (FusionColumn (Γ.fuse (a + b + (c + d)) e)) τ)
        = (midEnd (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
            (Γ.D (c + d)).grading (pcdV3RawTailSuperComm K Γ a b c d e) τ).comp
          (RelTensor.assoc K (Γ.D (a + b)).carrier
            (Γ.D (a + b + (c + d))).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + (c + d)) e))).toLinearMap :=
    gHomExtAssoc K fun u v w => pcdGq1Assoc_cdSlot_leaf K Γ a b c d e τ u v w
  exact LinearMap.congr_fun h n

theorem pcdGq1Assoc_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : GQ1 K Γ a b (c + d) e) :
    gq1Assoc K Γ a b (c + d) e (τ • n)
      = τ • gq1Assoc K Γ a b (c + d) e n :=
  pcdGq1Assoc_cdSlot_core K Γ a b c d e τ n

theorem pcdGq1Assoc_symm_cdSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (GBL Γ (a + b) (c + d) e)) :
    (gq1Assoc K Γ a b (c + d) e).symm (τ • n)
      = τ • (gq1Assoc K Γ a b (c + d) e).symm n :=
  leftEquivariant_symm K (gq1Assoc K Γ a b (c + d) e)
    (pcdGq1Assoc_cdSlot K Γ a b c d e) τ n

private noncomputable def pcdV3FinalMap :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (GBL Γ (a + b) (c + d) e))
      ≃ₗ[K] RelTensor K (Γ.D (c + d)).carrier
        (FusionColumn (Γ.fuse c d)) (GQ1 K Γ a b (c + d) e) :=
  RelTensor.mapEquivRight K (gq1Assoc K Γ a b (c + d) e).symm
    (pcdGq1Assoc_symm_cdSlot K Γ a b c d e)

noncomputable def omegaPcdV3 : V3 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ1 K Γ a b (c + d) e) :=
  (pcdV3Swap K Γ a b c d e).trans
    (pcdV3FinalMap K Γ a b c d e)

private noncomputable def pcdV3StepB :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
      ≃ₗ[K] RelTensor K (Γ.D (c + d)).carrier
        (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) :=
  gV3StepB K Γ a b c d e

private noncomputable def pcdV3StepC :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2rInner K Γ (a + b) c d e)
      ≃ₗ[K] RelTensor K (Γ.D (c + d)).carrier
        (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) :=
  gV3StepC K Γ a b c d e

private theorem pcdV3StepB_mk
    (u : FusionColumn (Γ.fuse c d))
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV3StepB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GBR.mk Γ (a + b) c d u q) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) u
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) q w) :=
  RelTensor.assoc_mk K (Γ.D (c + d)).carrier
    (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse c d))
    (FusionColumn (Γ.fuse (a + b) (c + d)))
    (FusionColumn (Γ.fuse (a + b + c + d) e)) u q w

private theorem pcdV3StepC_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : GQ2rInner K Γ (a + b) c d e) :
    pcdV3StepC K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) u n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) u
          (gq2rCast K Γ (a + b) c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K]
      FusionColumn (Γ.fuse c d))
    (gq2rCast K Γ (a + b) c d e).toLinearMap (fun _ _ => rfl)
    (gq2rCast_bcSlot K Γ (a + b) c d e) u n

private noncomputable def pcdV3AssocA : V3 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
  gV3AssocA K Γ a b c d e

private noncomputable def pcdV3AssocB :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)))
      ≃ₗ[K] RelTensor K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) :=
  RelTensor.mapEquivRight K (gV3AssocBC K Γ a b c d e)
    (gV3AssocBC_aSlot_general K Γ a b c d e)

private theorem pcdV3AssocA_mk
    (t : FusionColumn (Γ.fuse a b))
    (n : GBR Γ (a + b) c d)
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV3AssocA K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t n) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (a + b + c + d)).carrier
            (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))) t
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) n w) :=
  RelTensor.assoc_mk K (Γ.D (a + b)).carrier
    (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse a b))
    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) t n w

private theorem pcdV3AssocB_mk
    (t : FusionColumn (Γ.fuse a b))
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier
      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    pcdV3AssocB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (a + b + c + d)).carrier
            (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))) t n)
      = RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
          (gV3AssocBC K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K]
      FusionColumn (Γ.fuse a b))
    (gV3AssocBC K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (gV3AssocBC_aSlot_general K Γ a b c d e) t n

private theorem pcdV3AssocBC_mk
    (u : FusionColumn (Γ.fuse c d))
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gV3AssocBC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GBR.mk Γ (a + b) c d u q) w)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) u
          (GBL.mk Γ (a + b) (c + d) e q
            (gColumnCastFst K Γ e (add_assoc (a + b) c d) w)) := by
  change pcdV3StepC K Γ a b c d e
      (pcdV3StepB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GBR.mk Γ (a + b) c d u q) w)) = _
  rw [pcdV3StepB_mk, pcdV3StepC_mk, gq2rCast_mk]

private theorem pcdV3AssocABC_mk
    (t : FusionColumn (Γ.fuse a b))
    (u : FusionColumn (Γ.fuse c d))
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gV3AssocABC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)
      = RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) t
          (RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) u
            (GBL.mk Γ (a + b) (c + d) e q
              (gColumnCastFst K Γ e (add_assoc (a + b) c d) w))) := by
  change pcdV3AssocB K Γ a b c d e
      (pcdV3AssocA K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)) = _
  rw [pcdV3AssocA_mk, pcdV3AssocB_mk, pcdV3AssocBC_mk]

private theorem pcdV3Swap_mk_of_mem {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    pcdV3Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d))
            (RelTensor K (Γ.D (a + b)).carrier
              (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e)) u
            (RelTensor.mk K (Γ.D (a + b)).carrier
              (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e) t
              (GBL.mk Γ (a + b) (c + d) e q
                (gColumnCastFst K Γ e (add_assoc (a + b) c d) w))) := by
  change (midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d)).carrier
      (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse c d))
      (GBL Γ (a + b) (c + d) e)
      (Γ.D (a + b)).grading (Γ.D (c + d)).grading
      (FusionColumn.grading (Γ.fuse a b))
      (FusionColumn.grading (Γ.fuse c d))
      (pcdV3LawA K Γ a b c d e) (pcdV3LawB K Γ a b c d e))
      (gV3AssocABC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)) = _
  rw [pcdV3AssocABC_mk]
  exact midSwap_mk_of_mem K (Γ.D (a + b)).carrier
    (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse a b))
    (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading
    (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse c d))
    (pcdV3LawA K Γ a b c d e) (pcdV3LawB K Γ a b c d e) hu ht
    (GBL.mk Γ (a + b) (c + d) e q
      (gColumnCastFst K Γ e (add_assoc (a + b) c d) w))

private theorem pcdGq1Assoc_symm_mk
    (t : FusionColumn (Γ.fuse a b))
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + (c + d)) e)) :
    (gq1Assoc K Γ a b (c + d) e).symm
        (RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e) t
          (GBL.mk Γ (a + b) (c + d) e q w))
      = GQ1.mk K Γ a b (c + d) e (GBL.mk Γ a b (c + d) t q) w := by
  rw [show RelTensor.mk K (Γ.D (a + b)).carrier
        (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e) t
        (GBL.mk Γ (a + b) (c + d) e q w)
      = gq1Assoc K Γ a b (c + d) e
          (GQ1.mk K Γ a b (c + d) e (GBL.mk Γ a b (c + d) t q) w) from
        (gq1Assoc_mk K Γ a b (c + d) e t q w).symm,
    LinearEquiv.symm_apply_apply]

private theorem pcdV3FinalMap_mk
    (u : FusionColumn (Γ.fuse c d))
    (n : RelTensor K (Γ.D (a + b)).carrier
      (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e)) :
    pcdV3FinalMap K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (GBL Γ (a + b) (c + d) e)) u n)
      = RelTensor.mk K (Γ.D (c + d)).carrier
          (FusionColumn (Γ.fuse c d)) (GQ1 K Γ a b (c + d) e) u
          ((gq1Assoc K Γ a b (c + d) e).symm n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K]
      FusionColumn (Γ.fuse c d))
    (gq1Assoc K Γ a b (c + d) e).symm.toLinearMap (fun _ _ => rfl)
    (pcdGq1Assoc_symm_cdSlot K Γ a b c d e) u n

/-- Generator formula for the `V3` extraction.  Its sole sign is the
Koszul interchange of `F_{a,b}` and the spectator `F_{c,d}`. -/
theorem omegaPcdV3_mk_of_mem {i j : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    {u : FusionColumn (Γ.fuse c d)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse c d) i)
    (q : FusionColumn (Γ.fuse (a + b) (c + d)))
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    omegaPcdV3 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GQ1 K Γ a b (c + d) e) u
            (GQ1.mk K Γ a b (c + d) e
              (GBL.mk Γ a b (c + d) t q)
              (gColumnCastFst K Γ e (add_assoc (a + b) c d) w)) := by
  change pcdV3FinalMap K Γ a b c d e
      (pcdV3Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ5 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ5.mk K Γ a b c d t (GBR.mk Γ (a + b) c d u q)) w)) = _
  rw [
    pcdV3Swap_mk_of_mem K Γ a b c d e ht hu,
    map_zsmul, pcdV3FinalMap_mk, pcdGq1Assoc_symm_mk]

end GaugeChi

end Superfusion
