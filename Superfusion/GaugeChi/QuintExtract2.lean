/-
Superfusion / GaugeChi / QuintExtract2

Milestone M13-R2 of the `(p, χ)` arc's CLUSTER-FACE phase, executing
round R2 of `docs/m13-cluster-route.md`: the deferred `omegaV14`
(R1's own deferral, gate (β)), `smap_congr_deg`, the five `hg`
super-equivariance bridges `hg₁`..`hg₅`, and the two easy recognitions
`recog_E20M`/`recog_E14M`.

## `omegaV14`: the new recast device

`QuintExtract.lean`'s own finding (module docstring, gate (β)) is that
`ω14`'s naive codomain, after peeling `V14`'s own native `GQ4 K Γ b c d e`
via `gq4Close K Γ b c d e).symm` and one `RelTensor.assoc`, lands on
`RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
(FusionColumn (Γ.fuse a (b + c + d + e)))` — the SAME two raw factors as
`GQ4 K Γ a b c (d + e)`, but balanced over the LEFT-associated algebra
`Γ.D (b + c + d + e)` rather than `GQ4`'s own `Γ.D (b + c + (d + e))`.
**`gq4TotalCast`** (deliverable, `gq2rCast`/`gq3rCast`/`gFourCast`-genre:
two `RelTensor.lift` legs glued by `LinearEquiv.ofLinear`, identity on the
shared OPAQUE first factor `GBR Γ b c (d + e)`, `fusionColumnCast` on the
second) closes this gap. Its one slot-compatibility law
(`gq4TotalCast_dSlot`, the `D_{d+e}`-slot commutation needed to wrap it
under the outer `F_{d,e}` spectator via `RelTensor.mapEquivRight`) is
UNCONDITIONAL/sign-free, exactly as `gq3rCast_bSlot`/`gFourCast_midSlot`:
the `D_{d+e}`-slot only ever touches the untouched shared first factor
(`GQ4.dslot_smul_mk` on the codomain side, the raw `leftActionEnd_mk` on
the domain side).

The one new algebraic fact `gq4TotalCast`'s balancedness needs —
`GBR Γ b c (d+e)`'s `Total4` action (`QuintEdges2.lean`'s
`instModuleGBRTotal4`, the ONE registered at `Γ.D (b+c+d+e)`, matching
`V14`'s own native algebra) and its NATURAL `GBR.recast` action
(`RouteBimod.lean`, the ONE registered at `Γ.D (b+c+(d+e))`, matching
`GQ4`'s own algebra) agree along the SINGLE `Γ.gaugeCast (add_assoc (b+c)
d e)` — is `gbrTotal4_recast_smul_eq`, a two-line corollary of the
ALREADY-PUBLIC `GBR.recast_op_smul_def` (`RouteBimod.lean`) and
`GBR_abcd_natural_recast_eq` (`QuintEdges2.lean`), both landed in R1's
dependency closure. `gq4TotalCast` is wrapped under the outer `F_{d,e}`
spectator via `RelTensor.mapEquivRight` (`gq4TotalCastWrapped`), mirroring
`omegaV12`'s `gV12AssocC`-style closing stage.

`omegaV14` itself is three UNSIGNED stages (`PentagonB.RelTensor.
mapEquivLeft` of `(gq4Close K Γ b c d e).symm`, then `RelTensor.assoc`,
then `gq4TotalCastWrapped`) — no `midSwap` anywhere, hence
`omegaV14_mk_of_mem` (on fully split generators) carries NO sign
coefficient, unlike `omegaV6`/`omegaV7`/`omegaV9`/`omegaV12`'s leaves.
The `(gq4Close K Γ b c d e).symm`-stage's own `D_{b+c+d+e}`-equivariance
(`gq4Close_symm_rightTotal`) is derived from the ALREADY-PUBLIC
`gq4Close_rightTotal` (`QuintEdges2.lean`) via `PentagonB.
rightEquivariant_symm`, through a fresh `Total`-instance on `GQ4r` itself
(`instModuleGQ4rTotal`, mirroring `Quint.lean`'s `instModuleGQ1Total`
recipe one level deeper — needed so `PentagonB.RelTensor.mapEquivLeft`'s
implicit `[Module Aᵐᵒᵖ M']` instance search succeeds on `GQ4r`).

## `smap_congr_deg`, the `hg` bridges, and the two recognitions

`smap_congr_deg` is `subst`-trivial (Prop-irrelevance of the equivariance
witness, mirroring `Bimod.PentagonB`'s private `smap_congr` one level
up, now public in the DEGREE argument alone). `hg₁` (`GE1` has no
`PentagonRouteEquiv` suite) is a fresh nested `RelTensor.induction_on` +
`DirectSum.Decomposition.inductionOn` descent from `GQ1.dslot_smul_mk_of_mem`/
`GQ2.dslot_smul_mk_of_mem` plus `gTCanon_mem_grading`'s degree-shift;
`hg₂`..`hg₅` are direct instantiations of `PentagonRouteEquiv`'s
`GE2`/`GE3`/`GE4`/`GE5`/`GQ4Close.comp_dslot_univ` suites at the
canonical data, closed off with the underlying edge-map's own bare
`d`-slot equivariance (unconditional for `GE3`/`GQ4Close`, signed via
`gCanonHphi5`/`gt2Canon`'s own `dSlot` law for `GE2`/`GE4`/`GE5`).
`recog_E20M`/`recog_E14M` chain the ω-leaves against `E20M_mk`/`E14M_leaf`
by `hom_ext` + nested induction, per the sign ledger verified in the
route doc's §2 (both match: `(-1)^{jw(jm+p)}` split into
`(-1)^{jw·jm}·(-1)^{p·jw}` on the recognition's `smap`-side).
-/
import Superfusion.GaugeChi.QuintExtract
import Superfusion.GaugeChi.PentagonRouteEquiv
import Superfusion.GaugeChi.QuintFaces4

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

/-! ### `omegaV14 : V14 ≃ₗ F_{d,e} ⊗ GQ4(a,b,c,d+e)` -/

section OmegaV14

/-! #### The new recast device: `gq4TotalCast` -/

/-- The `D_{d+e}`-slot commutation of `fusionColumnCast`, unconditionally
(the local mirror of `QuintEdges8.lean`'s private `fusionColumnCast_xslot`
— re-proved here since `private` names do not cross files). -/
private theorem fusionColumnCast_xslot' (p : G) {x y : G} (h : x = y) (τ : (Γ.D x).carrier)
    (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p h (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv τ • fusionColumnCast K Γ p h w := by
  subst h
  rfl

private theorem fusionColumnCast_symm_xslot' (p : G) {x y : G} (h : x = y) (τ : (Γ.D y).carrier)
    (w : FusionColumn (Γ.fuse p y)) :
    (fusionColumnCast K Γ p h).symm (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (fusionColumnCast K Γ p h).symm w := by
  subst h
  rfl

/-- **The coefficient commutation `gq4TotalCast` needs**: `GBR Γ b c (d+e)`'s
`Total4` action (`Γ.D (b+c+d+e)`, `QuintEdges2.lean`'s
`instModuleGBRTotal4`) and its NATURAL `GBR.recast` action (`Γ.D
(b+c+(d+e))`, `RouteBimod.lean`) agree along the single `Γ.gaugeCast
(add_assoc (b+c) d e)` — a two-line corollary of `GBR.recast_op_smul_def`
and `GBR_abcd_natural_recast_eq`. -/
private theorem gbrTotal4_recast_smul_eq (τ : (Γ.D (b + c + d + e)).carrier)
    (n : GBR Γ b c (d + e)) :
    MulOpposite.op ((Γ.gaugeCast (add_assoc (b + c) d e)).toAlgEquiv τ) • n
      = MulOpposite.op τ • n := by
  rw [GBR.recast_op_smul_def]
  exact GBR_abcd_natural_recast_eq K Γ b c d e τ n

private theorem GQ4_mk_eq (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + (d + e)))) :
    GQ4.mk K Γ a b c (d + e) m w
      = RelTensor.mk K (Γ.D (b + c + (d + e))).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + (d + e)))) m w :=
  rfl

private noncomputable def gq4TotalCastFwdBilin :
    GBR Γ b c (d + e) →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + d + e)) →ₗ[K] GQ4 K Γ a b c (d + e) :=
  (GQ4.mk K Γ a b c (d + e)).compl₂
    (fusionColumnCast K Γ a (add_assoc (b + c) d e)).toLinearMap

private theorem gq4TotalCastFwdBilin_apply (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq4TotalCastFwdBilin K Γ a b c d e m w
      = GQ4.mk K Γ a b c (d + e) m (fusionColumnCast K Γ a (add_assoc (b + c) d e) w) := rfl

private theorem gq4TotalCastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d + e)).carrier (gq4TotalCastFwdBilin K Γ a b c d e) := by
  intro τ m w
  rw [gq4TotalCastFwdBilin_apply, gq4TotalCastFwdBilin_apply,
    ← gbrTotal4_recast_smul_eq K Γ b c d e τ m, GQ4_mk_eq, GQ4_mk_eq,
    RelTensor.mk_op_smul, fusionColumnCast_xslot']

private noncomputable def gq4TotalCastFwd :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) →ₗ[K]
      GQ4 K Γ a b c (d + e) :=
  RelTensor.lift (gq4TotalCastFwdBilin K Γ a b c d e) (gq4TotalCastFwd_balanced K Γ a b c d e)

private theorem gq4TotalCastFwd_mk (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq4TotalCastFwd K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
        (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
      = GQ4.mk K Γ a b c (d + e) m (fusionColumnCast K Γ a (add_assoc (b + c) d e) w) := by
  show RelTensor.lift (gq4TotalCastFwdBilin K Γ a b c d e) (gq4TotalCastFwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) m w) = _
  rw [RelTensor.lift_mk, gq4TotalCastFwdBilin_apply]

private noncomputable def gq4TotalCastBwdBilin :
    GBR Γ b c (d + e) →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + (d + e))) →ₗ[K]
        RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
      (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e)))).compl₂
    (fusionColumnCast K Γ a (add_assoc (b + c) d e)).symm.toLinearMap

private theorem gq4TotalCastBwdBilin_apply (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + (d + e)))) :
    gq4TotalCastBwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) m
          ((fusionColumnCast K Γ a (add_assoc (b + c) d e)).symm w) := rfl

private theorem gq4TotalCastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + (d + e))).carrier (gq4TotalCastBwdBilin K Γ a b c d e) := by
  intro t m w
  rw [gq4TotalCastBwdBilin_apply, gq4TotalCastBwdBilin_apply, fusionColumnCast_symm_xslot',
    ← RelTensor.mk_op_smul,
    ← gbrTotal4_recast_smul_eq K Γ b c d e ((Γ.gaugeCast (add_assoc (b + c) d e)).toAlgEquiv.symm t)
      m,
    AlgEquiv.apply_symm_apply]

private noncomputable def gq4TotalCastBwd :
    GQ4 K Γ a b c (d + e) →ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  RelTensor.lift (gq4TotalCastBwdBilin K Γ a b c d e) (gq4TotalCastBwd_balanced K Γ a b c d e)

private theorem gq4TotalCastBwd_mk (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + (d + e)))) :
    gq4TotalCastBwd K Γ a b c d e (GQ4.mk K Γ a b c (d + e) m w)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) m
          ((fusionColumnCast K Γ a (add_assoc (b + c) d e)).symm w) := by
  show RelTensor.lift (gq4TotalCastBwdBilin K Γ a b c d e) (gq4TotalCastBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c + (d + e))).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + (d + e)))) m w) = _
  rw [RelTensor.lift_mk, gq4TotalCastBwdBilin_apply]

private theorem gq4TotalCastFwd_bwd :
    (gq4TotalCastFwd K Γ a b c d e).comp (gq4TotalCastBwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show gq4TotalCastFwd K Γ a b c d e (gq4TotalCastBwd K Γ a b c d e (GQ4.mk K Γ a b c (d + e) m w))
    = GQ4.mk K Γ a b c (d + e) m w
  rw [gq4TotalCastBwd_mk, gq4TotalCastFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq4TotalCastBwd_fwd :
    (gq4TotalCastBwd K Γ a b c d e).comp (gq4TotalCastFwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show gq4TotalCastBwd K Γ a b c d e (gq4TotalCastFwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) m w))
    = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) m w
  rw [gq4TotalCastFwd_mk, gq4TotalCastBwd_mk, LinearEquiv.symm_apply_apply]

/-- **`gq4TotalCast`**: the R1-flagged recast device (gate (β)), closing
`GBR Γ b c (d+e) ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e}` (`V14`'s own native
bracketing) against `GQ4 K Γ a b c (d+e)` (`GQ4`'s own bracketing) — the
`gq2rCast`/`gq3rCast`/`gFourCast` family, one level deeper. -/
noncomputable def gq4TotalCast :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) ≃ₗ[K]
      GQ4 K Γ a b c (d + e) :=
  LinearEquiv.ofLinear (gq4TotalCastFwd K Γ a b c d e) (gq4TotalCastBwd K Γ a b c d e)
    (gq4TotalCastFwd_bwd K Γ a b c d e) (gq4TotalCastBwd_fwd K Γ a b c d e)

theorem gq4TotalCast_mk (m : GBR Γ b c (d + e))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq4TotalCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
        (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
      = GQ4.mk K Γ a b c (d + e) m (fusionColumnCast K Γ a (add_assoc (b + c) d e) w) :=
  gq4TotalCastFwd_mk K Γ a b c d e m w

/-- **`gq4TotalCast`'s `D_{d+e}`-slot commutation, unconditionally**: the
shared first factor `GBR Γ b c (d+e)` is untouched by the cast, and its
own `D_{d+e}`-slot (`GBR.cslot`) matches `GQ4`'s own `D_{d+e}`-slot
(`GQ4.dslot_smul_mk`, at the shifted 4th argument) on the OTHER side —
both `leftActionEnd`-built, sign-free (mirrors `gq3rCast_bSlot`/
`gFourCast_midSlot`). -/
theorem gq4TotalCast_dSlot (τ : (Γ.D (d + e)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    gq4TotalCast K Γ a b c d e (τ • n) = τ • gq4TotalCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk m w =>
      have hR : τ • gq4TotalCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
        = GQ4.mk K Γ a b c (d + e) (τ • m) (fusionColumnCast K Γ a (add_assoc (b + c) d e) w) := by
        rw [gq4TotalCast_mk, GQ4.dslot_smul_mk]
      have hL : gq4TotalCast K Γ a b c d e (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
        = GQ4.mk K Γ a b c (d + e) (τ • m) (fusionColumnCast K Γ a (add_assoc (b + c) d e) w) := by
        rw [show (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) m w
              : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
                  (FusionColumn (Γ.fuse a (b + c + d + e))))
            = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
                (FusionColumn (Γ.fuse a (b + c + d + e))) (τ • m) w from
          leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) τ m w,
          gq4TotalCast_mk]
      rw [hL, hR]
  | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]

/-- `gq4TotalCast`, wrapped by the outer `F_{d,e}` spectator
(`RelTensor.mapEquivRight`, via `gq4TotalCast_dSlot`). -/
noncomputable def gq4TotalCastWrapped :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) :=
  RelTensor.mapEquivRight K (gq4TotalCast K Γ a b c d e) (gq4TotalCast_dSlot K Γ a b c d e)

/-- `gq4TotalCastWrapped`'s generator formula (the `omegaV9_mapEquivRight_mk`
discipline: a direct term-mode application of `RelTensor.map_mk`, valid by
the `LinearEquiv.ofLinear`/`RelTensor.mapEquivRight` defeq-unfold). -/
private theorem gq4TotalCastWrapped_mk (w : FusionColumn (Γ.fuse d e))
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (gq4TotalCastWrapped K Γ a b c d e)
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w n)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
          (gq4TotalCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K] FusionColumn (Γ.fuse d e))
    (gq4TotalCast K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gq4TotalCast_dSlot K Γ a b c d e) w n

/-! #### Stage A: peeling `V14`'s own `GQ4 K Γ b c d e` via `gq4Close.symm` -/

/-- **`GQ4r K Γ a b c d`'s `Total` instance**, mirroring `Quint.lean`'s
`instModuleGQ1Total` recipe one level deeper — needed so
`PentagonB.RelTensor.mapEquivLeft`'s implicit `[Module Aᵐᵒᵖ M']` instance
search succeeds on `GQ4r` (which, unlike `GQ4`, carries no registered
`Total` instance in `Pentagon.lean`). -/
noncomputable instance instModuleGQ4rTotal (p q r s : G) :
    Module ((Γ.D (p + q + r + s)).carrier)ᵐᵒᵖ (GQ4r K Γ p q r s) :=
  Module.compHom
    (RelTensor K (Γ.D (r + s)).carrier (FusionColumn (Γ.fuse r s)) (GBR Γ p q (r + s)))
    ((rightActionEnd K (Γ.D (r + s)).carrier (FusionColumn (Γ.fuse r s)) (GBR Γ p q (r + s))
      (C := (Γ.D (p + q + r + s)).carrier)).toRingHom)

theorem GQ4rTotal_op_smul_def (p q r s : G) (t : (Γ.D (p + q + r + s)).carrier)
    (n : GQ4r K Γ p q r s) :
    MulOpposite.op t • n
      = rightActionEnd K (Γ.D (r + s)).carrier (FusionColumn (Γ.fuse r s)) (GBR Γ p q (r + s))
          (MulOpposite.op t) n := rfl

/-- **`gq4Close`'s `Total`-naturality, restated via `instModuleGQ4rTotal`**:
a `rfl`-unfold of `QuintEdges2.lean`'s `gq4Close_rightTotal`. -/
theorem gq4Close_rightTotal' (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ4r K Γ p q r s) :
    gq4Close K Γ p q r s (MulOpposite.op τ • m) = MulOpposite.op τ • gq4Close K Γ p q r s m := by
  rw [GQ4rTotal_op_smul_def]
  exact gq4Close_rightTotal K Γ p q r s τ m

/-- **`(gq4Close K Γ p q r s).symm`'s `Total`-naturality**, via
`PentagonB.rightEquivariant_symm`. -/
theorem gq4Close_symm_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (n : GQ4 K Γ p q r s) :
    (gq4Close K Γ p q r s).symm (MulOpposite.op τ • n)
      = MulOpposite.op τ • (gq4Close K Γ p q r s).symm n :=
  PentagonB.rightEquivariant_symm K (gq4Close K Γ p q r s) (gq4Close_rightTotal' K Γ p q r s) τ n

/-- **Stage A**: `V14`'s own `GQ4 K Γ b c d e` factor, peeled to `GQ4r K Γ
b c d e` via `(gq4Close K Γ b c d e).symm` (`PentagonB.RelTensor.
mapEquivLeft`). -/
noncomputable def omegaV14StageA : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d + e)).carrier (GQ4r K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  PentagonB.RelTensor.mapEquivLeft K (gq4Close K Γ b c d e).symm
    (gq4Close_symm_rightTotal K Γ b c d e)

/-! #### Stage B: the plain associator exposing `F_{d,e}` at the outer-left -/

/-- **Stage B**: the plain `RelTensor.assoc`, exposing `F_{d,e}` at the
outer-left position (`GQ4r K Γ b c d e`'s own definition IS `F_{d,e}
⊗_{D_{d+e}} GBR Γ b c (d+e)`, so this is cast-free). -/
noncomputable def omegaV14StageB :
    RelTensor K (Γ.D (b + c + d + e)).carrier (GQ4r K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.assoc K (Γ.D (d + e)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e)))

/-! #### `omegaV14` itself -/

/-- **`omegaV14`**: `omegaV14StageA` (peeling `GQ4 K Γ b c d e`) then
`omegaV14StageB` (the plain assoc exposing `F_{d,e}`) then
`gq4TotalCastWrapped` (the new device, closing the recast gap), landing
the literal `GQ4 K Γ a b c (d+e)`. All three stages are UNSIGNED. -/
noncomputable def omegaV14 : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) :=
  (omegaV14StageA K Γ a b c d e).trans
    ((omegaV14StageB K Γ a b c d e).trans (gq4TotalCastWrapped K Γ a b c d e))

/-- `omegaV14StageA`'s generator formula, GENERIC in the (already
`V14`-typed) second slot `n` — avoids re-elaborating a fresh
`gq4Close`-shaped term at `V14`'s type (the `omegaV9`/`omegaV12`
discipline: keep `n` an abstract bound variable throughout). -/
private theorem omegaV14StageA_mk (x : FusionColumn (Γ.fuse a (b + c + d + e)))
    (n : GQ4 K Γ b c d e) :
    (omegaV14StageA K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) n x)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4r K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) ((gq4Close K Γ b c d e).symm n) x :=
  RelTensor.map_mk ((gq4Close K Γ b c d e).symm.toLinearMap)
    (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d + e))
      →ₗ[K] FusionColumn (Γ.fuse a (b + c + d + e)))
    (gq4Close_symm_rightTotal K Γ b c d e) (fun _ _ => rfl) n x

/-- The raw `GQ4 K Γ b c d e`-value produced by `gq4Close`, respelled ONCE
at `V14`'s own (defeq) type as a top-level `def` — the `QuintFaces3`
"auxiliary raw-domain relocation" discipline. -/
private noncomputable def omegaV14Gen (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ b c (d + e)) : GQ4 K Γ b c d e :=
  (gq4Close K Γ b c d e) (GQ4r.mk K Γ b c d e w p)

private theorem omegaV14Gen_eq (w : FusionColumn (Γ.fuse d e)) (p : GBR Γ b c (d + e)) :
    omegaV14Gen K Γ b c d e w p = (gq4Close K Γ b c d e) (GQ4r.mk K Γ b c d e w p) :=
  rfl

/-- **The (sign-free) formula of `omegaV14` on fully split generators.**
Named `_mk_of_mem` for continuity with the `ω`-family (`omegaV6`..
`omegaV12`), even though NO degree hypothesis is needed — `omegaV14` is
built entirely from unsigned devices (`mapEquivLeft`, `RelTensor.assoc`,
`mapEquivRight`), so no Koszul sign ever arises. -/
theorem omegaV14_mk_of_mem (w : FusionColumn (Γ.fuse d e)) (p : GBR Γ b c (d + e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) (omegaV14Gen K Γ b c d e w p) x)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
          (GQ4.mk K Γ a b c (d + e) p (fusionColumnCast K Γ a (add_assoc (b + c) d e) x)) := by
  have step1 :
      (omegaV14StageA K Γ a b c d e)
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) (omegaV14Gen K Γ b c d e w p) x)
        = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4r K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) (GQ4r.mk K Γ b c d e w p) x := by
    rw [omegaV14StageA_mk, omegaV14Gen_eq, LinearEquiv.symm_apply_apply]
  show (omegaV14StageB K Γ a b c d e).trans (gq4TotalCastWrapped K Γ a b c d e)
      ((omegaV14StageA K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) (omegaV14Gen K Γ b c d e w p) x)) = _
  rw [step1]
  show (gq4TotalCastWrapped K Γ a b c d e)
      ((omegaV14StageB K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4r K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) (GQ4r.mk K Γ b c d e w p) x)) = _
  show (gq4TotalCastWrapped K Γ a b c d e)
      ((omegaV14StageB K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)) w p)
          x)) = _
  rw [show (omegaV14StageB K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)) w p)
          x)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) p x) from
    RelTensor.assoc_mk K (Γ.D (d + e)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse d e)) (GBR Γ b c (d + e)) (FusionColumn (Γ.fuse a (b + c + d + e))) w p x]
  rw [gq4TotalCastWrapped_mk, gq4TotalCast_mk]

end OmegaV14

/-! ### `smap_congr_deg` -/

section SmapCongrDeg

variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ] [GradedRightSMul 𝒜 ℳ]
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']

omit [Invertible (2 : K)] in
/-- **`smap`-congruence in the degree argument**: `smap` depends on its
degree only up to equality — the equivariance witness `hg`/`hg'` is
Prop-irrelevant, so `subst` collapses both sides to the same term. -/
theorem smap_congr_deg (g : N →ₗ[K] N') {e e' : ZMod 2} (he : e = e')
    {hg : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      g (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • g n)}
    {hg' : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      g (x • n) = ((sgn (e' * i) : ℤˣ) : ℤ) • (x • g n)} :
    smap 𝒜 ℳ g e hg = smap 𝒜 ℳ g e' hg' := by
  subst he
  rfl

end SmapCongrDeg

/-! ### The five `hg` bridges

The `D_{d+e}`-slot super-equivariance, at the canonical data, of each of
the five `GE`-role maps `GQ1 K Γ a b c (d+e) →ₗ[K] _` reached at
`(a,b,c,d+e)`. `hg₁` (`GE1` has no `PentagonRouteEquiv` suite) is a fresh
nested induction from `GQ1.dslot_smul_mk_of_mem`/`GQ2.dslot_smul_mk_of_mem`
plus `gTCanon_mem_grading`'s degree-shift. `hg₄` is a direct instantiation
of `PentagonRouteEquiv`'s `GE4.comp_dslot_univ` suite, closed off with
`gTCanon`'s own bare `(d+e)`-slot law `gCanonHphi5`. -/

section HgBridges

/-- `GE1_mk`, restated with the source/target `mk`'s spelled via the
vertex-level `GQ1.mk`/`GQ2.mk` (`PentagonActions.lean`) rather than the
raw `RelTensor.mk` — needed since `rw` does not see through the
`GQ1`/`GQ2` `def`-wrappers to match `GE1_mk`'s literal `RelTensor.mk`
pattern. -/
theorem GE1_mk' (u : GBL Γ a b c) (v : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c)
        (GQ1.mk K Γ a b c (d + e) u v)
      = GQ2.mk K Γ a b c (d + e) (gTCanon K Γ a b c u) v :=
  GE1_mk K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c) u v

/-- **`hg₁`**: the `D_{d+e}`-slot super-equivariance of `GE1 K Γ a b c
(d+e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c)`, at parity
`gParity K Γ a b c`. `GE1` carries no `PentagonRouteEquiv` suite, so this
is built directly: `GQ1.dslot_smul_mk_of_mem` splits `τ • GQ1.mk m w` on
the source; `gTCanon_mem_grading` supplies `gTCanon m`'s shifted degree
`jm + gParity K Γ a b c`, feeding `GQ2.dslot_smul_mk_of_mem` on the
target; the two resulting signs combine to `sgn(i·jm)` via the `ZMod 2`
identity `p·i + i·(jm+p) = i·jm`. -/
theorem hg1 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄, τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ1 K Γ a b c (d + e),
        GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c) (τ • n)
          = ((sgn (gParity K Γ a b c * i) : ℤˣ) : ℤ) •
              (τ • GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap
                (gCanonRight K Γ a b c) n) := by
  intro i τ hτ n
  induction n using GQ1.induction_on K Γ a b c (d + e) with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m w =>
      induction m using DirectSum.Decomposition.inductionOn (GBL.grading Γ a b c) with
      | zero =>
          rw [show GQ1.mk K Γ a b c (d + e) (0 : GBL Γ a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          simp only [smul_zero, map_zero]
      | add m m' hm hm' =>
          rw [show GQ1.mk K Γ a b c (d + e) (m + m') w
              = GQ1.mk K Γ a b c (d + e) m w + GQ1.mk K Γ a b c (d + e) m' w from by
            simp only [map_add, LinearMap.add_apply]]
          simp only [smul_add, map_add, hm, hm']
      | homogeneous xm =>
          have sign_id : ∀ p i j : ZMod 2, p * i + i * (j + p) = i * j := by decide
          rw [GQ1.dslot_smul_mk_of_mem K Γ a b c (d + e) hτ xm.2, map_zsmul,
            GE1_mk' K Γ a b c d e, GE1_mk' K Γ a b c d e,
            GQ2.dslot_smul_mk_of_mem K Γ a b c (d + e) hτ (gTCanon_mem_grading K Γ a b c xm.2),
            smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

/-- **`hg₂`**: the `D_{d+e}`-slot super-equivariance of `GE2 K Γ a b c
(d+e)` at the canonical second-edge intertwiner `gt2Canon K Γ a b c (d+e)
(gTCanon K Γ a (b+c) (d+e))`, at parity `gParity K Γ a (b+c) (d+e)` — a
direct instantiation of `PentagonRouteEquiv`'s `GE2.comp_dslot_univ`,
closed off with `gt2Canon`'s own bare `(d+e)`-slot law `gt2Canon_dSlot`
(`ChiCanon.lean`), fed by `gTCanon_mem_gInterSpace`. -/
theorem hg2 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄, τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ2 K Γ a b c (d + e),
        GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
            (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
              (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)))
            (τ • n)
          = ((sgn (gParity K Γ a (b + c) (d + e) * i) : ℤˣ) : ℤ) •
              (τ • GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
                (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
                (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
                  (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)))
                n) :=
  fun _i _τ hτ n =>
    GE2.comp_dslot_univ K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
      (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
        (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)))
      hτ
      (gt2Canon_dSlot K Γ (gTCanon K Γ a (b + c) (d + e))
        (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)) hτ)
      n

/-- **`hg₄`**: the `D_{d+e}`-slot super-equivariance of `GE4 K Γ a b c
(d+e) (gParity K Γ (a+b) c (d+e)) (gTCanon K Γ (a+b) c (d+e)).toLinearMap
(gCanonHphi4 K Γ a b c (d+e))`, at parity `gParity K Γ (a+b) c (d+e)` —
a direct instantiation of `PentagonRouteEquiv`'s `GE4.comp_dslot_univ`,
closed off with `gTCanon`'s own bare `(d+e)`-slot law `gCanonHphi5`. -/
theorem hg4 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄, τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ1 K Γ a b c (d + e),
        GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
            (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)) (τ • n)
          = ((sgn (gParity K Γ (a + b) c (d + e) * i) : ℤˣ) : ℤ) •
              (τ • GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
                (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)) n) :=
  fun _i _τ hτ n =>
    GE4.comp_dslot_univ K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
      (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)) hτ
      (gCanonHphi5 K Γ (a + b) c d e hτ) n

/-- **`hg₃`**: the `D_{d+e}`-slot super-equivariance of `GE3 K Γ a b c
(d+e) (gTCanon K Γ b c (d+e)).toLinearMap (gCanonRight K Γ b c (d+e))`,
at parity `gParity K Γ b c (d+e)` — a direct instantiation of
`PentagonRouteEquiv`'s `GE3.comp_dslot_univ`, closed off with `gTCanon`'s
own bare `(d+e)`-slot law `gCanonHphi5`. -/
theorem hg3 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄, τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ3 K Γ a b c (d + e),
        GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
            (gCanonRight K Γ b c (d + e)) (τ • n)
          = ((sgn (gParity K Γ b c (d + e) * i) : ℤˣ) : ℤ) •
              (τ • GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
                (gCanonRight K Γ b c (d + e)) n) :=
  fun _i _τ hτ n =>
    GE3.comp_dslot_univ K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
      (gCanonRight K Γ b c (d + e)) hτ (gCanonHphi5 K Γ b c d e hτ) n

/-- **`hg₅`**: the `D_{d+e}`-slot super-equivariance of `GE5 K Γ a b c
(d+e) (gParity K Γ a b (c+(d+e))) (gTCanon K Γ a b (c+(d+e))).toLinearMap
(gCanonHphi5 K Γ a b c (d+e))`, at parity `gParity K Γ a b (c+(d+e))` —
`GE5`'s own `d`-slot is the *spectator* slot (`PentagonRouteEquiv`'s
`GE5.comp_dslot_univ` is UNCONDITIONAL there, no extra hypothesis on
`t₅` needed). -/
theorem hg5 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄, τ ∈ (Γ.D (d + e)).grading i →
      ∀ n : GQ5 K Γ a b c (d + e),
        GE5 K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
            (gTCanon K Γ a b (c + (d + e))).toLinearMap (gCanonHphi5 K Γ a b c (d + e)) (τ • n)
          = ((sgn (gParity K Γ a b (c + (d + e)) * i) : ℤˣ) : ℤ) •
              (τ • GE5 K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
                (gTCanon K Γ a b (c + (d + e))).toLinearMap (gCanonHphi5 K Γ a b c (d + e)) n) :=
  fun _i _τ hτ n =>
    GE5.comp_dslot_univ K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
      (gTCanon K Γ a b (c + (d + e))).toLinearMap (gCanonHphi5 K Γ a b c (d + e)) hτ n

end HgBridges

/-! ### `recog_E20M` -/

section RecogE20M

/-- **`recog_E20M`**: the `PDE`-face recognition at edge 20 —
`omegaV7 ∘ₗ E20M = smap(GE1 …) ∘ₗ omegaV6`. Proved by `hom_ext` +
nested induction (`n : GBR Γ (a+b+c) d e` peeled to `GBR.mk w p`, `m`
split by `GBL.grading`, `w` split by `FusionColumn.grading (Γ.fuse d
e)`), landing on `omegaV6_mk_of_mem`/`omegaV7_mk_of_mem`/`GE1_mk'` —
the sign ledger `(-1)^{jw(jm+p₁)}` (LHS) vs `(-1)^{jw·jm}·(-1)^{p₁·jw}`
(RHS) match by `jw·(jm+p₁) = jw·jm + p₁·jw` (`ring`, `ZMod 2` a
`CommRing`). -/
theorem recog_E20M :
    (omegaV7 K Γ a b c d e).toLinearMap ∘ₗ E20M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
          (gParity K Γ a b c) (hg1 K Γ a b c d e) ∘ₗ (omegaV6 K Γ a b c d e).toLinearMap := by
  have sign_id : ∀ p i j : ZMod 2, i * (j + p) = i * j + p * i := by decide
  refine RelTensor.hom_ext fun m n => ?_
  induction n using GBR.induction_on_left_homog K Γ (a + b + c) d e with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | homog jw w p hw =>
      induction m using DirectSum.Decomposition.inductionOn (GBL.grading Γ a b c) with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
      | homogeneous xm =>
          show (omegaV7 K Γ a b c d e)
              (E20M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                (GBR Γ (a + b + c) d e) (xm : GBL Γ a b c) (GBR.mk Γ (a + b + c) d e w p)))
            = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
                (gParity K Γ a b c) (hg1 K Γ a b c d e)
                ((omegaV6 K Γ a b c d e) (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                  (GBR Γ (a + b + c) d e) (xm : GBL Γ a b c) (GBR.mk Γ (a + b + c) d e w p)))
          rw [E20M_mk, omegaV6_mk_of_mem K Γ a b c d e xm.2 hw, map_zsmul,
            omegaV7_mk_of_mem K Γ a b c d e (gTCanon_mem_grading K Γ a b c xm.2) hw,
            smap_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
              (GE1 K Γ a b c (d + e) (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
              (gParity K Γ a b c) (hg1 K Γ a b c d e) hw, GE1_mk' K Γ a b c d e,
            smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

end RecogE20M

/-! ### `recog_E14M` -/

section RecogE14M

/-- **The `QuintFaces3` "coercion-relocation" discipline**: the raw
`GQ4 K Γ (a+b) c d e`-value produced by `gq4Close`, respelled ONCE at
`V9Inner`'s own (defeq) type as a top-level `def` — mirrors
`QuintExtract.lean`'s `private omegaV9Gen` verbatim (that name is
`private`, so does not cross the file boundary; this is the SAME
underlying term under a fresh name), avoiding the `have`-wrapped
coercion artifact a bare inline `gq4Close (…)` produces (which defeats
`rw`'s pattern matching against `E14M_leaf`'s/`omegaV9_mk_of_mem`'s own
`V9Inner`-typed statements). -/
private noncomputable def e14mGen (w : FusionColumn (Γ.fuse d e)) (p : GBR Γ (a + b) c (d + e)) :
    V9Inner K Γ a b c d e :=
  gq4Close K Γ (a + b) c d e (GQ4r.mk K Γ (a + b) c d e w p)

private theorem e14mGen_eq (w : FusionColumn (Γ.fuse d e)) (p : GBR Γ (a + b) c (d + e)) :
    e14mGen K Γ a b c d e w p = gq4Close K Γ (a + b) c d e (GQ4r.mk K Γ (a + b) c d e w p) :=
  rfl

/-- The `gTCanon`-image respelled ONCE at `GBR Γ (a+b) c (d+e)` as a
top-level `def`, the SAME "coercion-relocation" discipline as
`e14mGen`. -/
private noncomputable def e14mCanon (v : FusionColumn (Γ.fuse (a + b) c))
    (x : FusionColumn (Γ.fuse (a + b + c) (d + e))) : GBR Γ (a + b) c (d + e) :=
  gTCanon K Γ (a + b) c (d + e)
    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)

private theorem e14mCanon_eq (v : FusionColumn (Γ.fuse (a + b) c))
    (x : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    e14mCanon K Γ a b c d e v x
      = gTCanon K Γ (a + b) c (d + e)
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x) :=
  rfl

/-- `E14M_leaf`, restated through `e14mGen`/`e14mCanon`. -/
theorem E14M_leaf' {ju jv jw : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (x : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    E14M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
          (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x))
      = ((sgn (jw * jv + gParity K Γ (a + b) c (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
            u (e14mGen K Γ a b c d e w (e14mCanon K Γ a b c d e v x)) :=
  E14M_leaf K Γ a b c d e hu hv hw x

/-- `GE4_mk_of_mem`, specialized to the canonical `t₄ := (gTCanon K Γ
(a+b) c (d+e)).toLinearMap`/`ht₄ := gCanonHphi4 K Γ a b c (d+e)` data and
restated through `GQ1.mk`/`GQ5.mk`/`e14mCanon` (the same reason as
`GE1_mk'`/`e14mGen`). -/
theorem GE4_mk_of_mem_canon {j : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j) (v : FusionColumn (Γ.fuse (a + b) c))
    (x : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
        (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e))
        (GQ1.mk K Γ a b c (d + e) (GBL.mk Γ a b c u v) x)
      = ((sgn (gParity K Γ (a + b) c (d + e) * j) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b c (d + e) u (e14mCanon K Γ a b c d e v x) :=
  GE4_mk_of_mem K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
    (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)) hu v x

/-- `omegaV9_mk_of_mem`, restated through `e14mGen`. -/
theorem omegaV9_mk_of_mem' {ju jw : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw) (p : GBR Γ (a + b) c (d + e)) :
    omegaV9 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
          (e14mGen K Γ a b c d e w p))
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ5 K Γ a b c (d + e)) w
            (GQ5.mk K Γ a b c (d + e) u p) :=
  omegaV9_mk_of_mem K Γ a b c d e hu hw p

/-- **`recog_E14M`**: the `PAB`/`PDE`-face recognition at edge 14 —
`omegaV9 ∘ₗ E14M = smap(GE4 …) ∘ₗ omegaV6`, at `GE4`'s own parity
`p₄ := gParity K Γ (a+b) c (d+e)`. Proved by `hom_ext` + nested induction
(`n : GBR Γ (a+b+c) d e` peeled to `GBR.mk w x`; `m : GBL Γ a b c` peeled
to `GBL.mk u v`, both `u,v` split by degree via `GBL.induction_on_gen2`),
landing on `E14M_leaf`/`omegaV9_mk_of_mem'`/`omegaV6_mk_of_mem`/
`smap_mk_of_mem`/`GE4_mk_of_mem` — the sign ledger `jw·jv + p₄·(ju+jw) +
jw·ju` (LHS) vs `jw·(ju+jv) + p₄·jw + p₄·ju` (RHS) match termwise
(`decide`, `ZMod 2`). -/
theorem recog_E14M :
    (omegaV9 K Γ a b c d e).toLinearMap ∘ₗ E14M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
            (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)))
          (gParity K Γ (a + b) c (d + e)) (hg4 K Γ a b c d e)
          ∘ₗ (omegaV6 K Γ a b c d e).toLinearMap := by
  have sign_id : ∀ p ju jv jw : ZMod 2,
      jw * jv + p * (ju + jw) + jw * ju = jw * (ju + jv) + p * jw + p * ju := by decide
  refine RelTensor.hom_ext fun m n => ?_
  induction n using GBR.induction_on_left_homog K Γ (a + b + c) d e with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | homog jw w x hw =>
      induction m using GBL.induction_on_gen2 K Γ a b c with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
      | @homog j jv u v hu hv =>
          show (omegaV9 K Γ a b c d e)
              (E14M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                (GBR Γ (a + b + c) d e) (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x)))
            = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)))
                (gParity K Γ (a + b) c (d + e)) (hg4 K Γ a b c d e)
                ((omegaV6 K Γ a b c d e) (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                  (GBR Γ (a + b + c) d e) (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x)))
          have hLHS : (omegaV9 K Γ a b c d e)
              (E14M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                (GBR Γ (a + b + c) d e) (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x)))
              = ((sgn (jw * jv + gParity K Γ (a + b) c (d + e) * (j + jw)) * sgn (jw * j) : ℤˣ)
                  : ℤ) •
                RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ5 K Γ a b c (d + e)) w
                  (GQ5.mk K Γ a b c (d + e) u (e14mCanon K Γ a b c d e v x)) := by
            rw [E14M_leaf' K Γ a b c d e hu hv hw x]
            refine (map_zsmul (omegaV9 K Γ a b c d e) _ _).trans ?_
            rw [omegaV9_mk_of_mem' K Γ a b c d e hu hw, smul_smul, ← Units.val_mul]
          have hRHS : smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)))
                (gParity K Γ (a + b) c (d + e)) (hg4 K Γ a b c d e)
                ((omegaV6 K Γ a b c d e) (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                  (GBR Γ (a + b + c) d e) (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x)))
              = ((sgn (jw * (j + jv)) * sgn (gParity K Γ (a + b) c (d + e) * jw)
                  * sgn (gParity K Γ (a + b) c (d + e) * j) : ℤˣ) : ℤ) •
                RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ5 K Γ a b c (d + e)) w
                  (GQ5.mk K Γ a b c (d + e) u (e14mCanon K Γ a b c d e v x)) := by
            rw [omegaV6_mk_of_mem K Γ a b c d e (GBL.mk_mem_grading Γ a b c hu hv) hw]
            refine (map_zsmul _ _ _).trans ?_
            rw [smap_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE4 K Γ a b c (d + e) (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi4 K Γ a b c (d + e)))
                (gParity K Γ (a + b) c (d + e)) (hg4 K Γ a b c d e) hw,
              GE4_mk_of_mem_canon K Γ a b c d e hu v x, map_zsmul, smul_smul, smul_smul,
              ← Units.val_mul, ← Units.val_mul]
          rw [hLHS, hRHS]
          congr 2
          rw [← sgn_add, ← sgn_add, ← sgn_add, sign_id]

end RecogE14M

end GaugeChi

end Superfusion
