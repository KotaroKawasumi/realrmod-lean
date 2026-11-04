/-
Superfusion / GaugeChi / QuintExtract4

The order-of-operations repair for the `PDE` spectator extraction at
`V14`.  The original `omegaV14` first opens a `GQ4` by `gq4Close.symm`;
that is convenient for edge 10, but it cannot simplify directly after
`E21M`'s final associator when the inner tensor is opaque.

This file builds the complementary presentation.  It first cancels
`gV14StepFinal`, then exposes the `F_{d,e}` spectator, and only then
performs the coefficient recasts.  The only new recast is the elementary
three-letter map

  F_{b,c+d} tensor_[D_{b+c+d}] F_{a,b+c+d}
    ~= GBR(a,b,c+d),

obtained from `fusionColumnCast` along `add_assoc b c d`.  In particular,
no arbitrary-map associator naturality principle is assumed: the two
compatibility laws below concern only the total coefficient and the
untouched `(c+d)` slot.
Milestone M13-R3b of the `(p, χ)` arc's CLUSTER-FACE phase: **`omegaV14'`**,
the re-ordered ("peel-before-regroup") spelling of the `PDE`-face
spectator-extraction equivalence `V14 ≃ F_{d,e} ⊗ GQ4 K Γ a b c (d+e)`,
targeting `recog_E21M`'s known blocker (`QuintExtract3.lean`'s module
docstring: `E21M_leaf`'s closing move `gV14StepFinal` lands on `mk n Y`
with `Y` an OPAQUE `gTCanon`-image, and the ORIGINAL `omegaV14`
(`QuintExtract2.lean`, `gq4Close`-peel AFTER the `assoc`-regroup) has no
`mk`-shaped reduction for such input).

## Option chosen: (i), the reordering — and why

Both options from the round brief were investigated. **Option (i)**
(reorder `omegaV14`'s own construction so the `gq4Close`-style peel
happens BEFORE the `assoc`-regroup, mirroring `omegaV12`'s successful
`gV12Assoc`-then-`mapEquivRight` ordering) is the one landed here.
**Option (ii)** (a general naturality lemma commuting `RelTensor.map`
past `RelTensor.assoc` over an opaque inner argument) was examined and
found to need EXACTLY the same missing ingredient as option (i) — see
the finding below — so no separate device was built for it.

**The construction**: instead of `omegaV14`'s own `mapEquivLeft(gq4Close
K Γ b c d e).symm` (which needs `V14`'s argument `mk`-shaped at `V14`'s
OWN top level, immediately blocked on `E21M_leaf`'s opaque-`Y` output),
`omegaV14'` STARTS by directly CANCELLING `gV14StepFinal` (`E21M`'s own
closing move, itself a plain `RelTensor.assoc.symm`) via
`(gV14StepFinal).symm`, a GENERAL, unconditional cancellation valid for
ANY argument (not requiring any `mk`-shape at all — `LinearEquiv.
symm_apply_apply`). This exposes `V14`'s native `GBR Γ c d e` factor
`n` UNPEELED, landing on `RelTensor(D_{c+d+e}, GBR Γ c d e, Y-type)`
(`Y-type := RelTensor(D_{bcde}, F_{b,c+d+e}, F_{a,bcde})`, `E21M_leaf`'s
own domain-side `Y`'s type). From there:

* `gV14Split` (`(gV14StepFinal).symm` then a plain `RelTensor.assoc`
  splitting `GBR Γ c d e`'s own two raw columns): lands
  `F_{d,e} ⊗_{D_{de}} (F_{c,d+e} ⊗_{D_{cde}} Y-type)` — this stage needs
  `n` split (`GBR.mk w u`, tractable, since `n` is under OUR OWN control
  in `recog_E21M`'s domain induction — matches `QuintExtract3`'s own
  "domain side alone is tractable" finding) but is GENERAL in `Y`
  (`assoc_mk`'s formula never touches its own `P`-slot).
* `gV14SplitC` (a further plain `RelTensor.assoc.symm`, regrouping
  `F_{c,d+e}` with `Y`'s own first factor `F_{b,c+d+e}`): lands
  `F_{d,e} ⊗ ((F_{c,d+e} ⊗_{D_{cde}} F_{b,c+d+e}) ⊗_{D_{bcde}} F_{a,bcde})`
  — GENERAL in `Y` too (`assoc_symm_mk`'s own formula never touches its
  `M`-slot `F_{c,d+e}`, the ONLY thing this stage moves).
* **`gThreeCast`, THE NEW DEVICE** (deliverable): identity on the shared
  first factor `F_{c,d+e}`, `fusionColumnCast` on the second — the
  `gq4TotalCast`-mirror ONE LEVEL SHALLOWER, closing
  `F_{c,d+e} ⊗_{D_{cde}} F_{b,c+d+e} ≃ GBR Γ b c (d+e)` (built exactly
  like `gq4TotalCast`/`gq3rCast`/`gq2rCast`: two `RelTensor.lift` legs
  glued by `LinearEquiv.ofLinear`; balancedness via a fresh Module
  instance `instModuleGV14ColumnRecast : Module (D_{cde})ᵐᵒᵖ F_{c,d+e}`
  — the 3-letter mirror of `Quint.lean`'s `instModuleFusionColumnRecast4`
  — plus `RelTensor.mk_op_smul`). Its `D_{bcde}`-slot right-equivariance
  `gThreeCast_rightTotal` (needed to wrap it via `mapEquivLeft`) closes
  via the ALREADY-PUBLIC bridge `fusionColumnCast_bcd_recast`
  (`QuintEdges2.lean`) between the two `D_{bcde}`-flavoured recast
  instances `instModuleFusionColumnRecast4`/`instModuleFusionColumnRecastABR`
  (`fusionColumnCast_cde_recast`, a two-line round-trip corollary).
* `gq4TotalCast` (ALREADY LANDED, `QuintExtract2.lean`): closes the
  remaining outer-bracket mismatch, landing the literal
  `GQ4 K Γ a b c (d+e)`.

Each stage is wrapped under the outer `F_{d,e}` spectator via
`RelTensor.mapEquivRight`/`PentagonB.RelTensor.mapEquivLeft`, each
needing its own `D_{d+e}`-slot equivariance law (`gV14SplitC_leftEquiv`,
`gThreeCast_leftEquivDe` + `mapEquivLeftGThreeCast_leftEquiv`,
`gq4TotalCast_dSlot` — already landed) — all UNSIGNED, mirroring
`omegaV14`'s own "no Koszul sign anywhere" property. The composite
**`omegaV14'`** lands `V14 K Γ a b c d e ≃ₗ[K] F_{d,e} ⊗ GQ4 K Γ a b c (d+e)`.

Three fresh instance triples (`Module`/`SMulCommClass`/`IsScalarTower`)
were needed to let `RelTensor.assoc`/`RelTensor.mapEquivRight`/
`PentagonB.RelTensor.mapEquivLeft` typecheck at each new intermediate
type (`instModuleGV14ColumnRecast` on `F_{c,d+e}`, `instModuleInnerDe`
on the compound `F_{c,d+e} ⊗ F_{b,c+d+e}`, `instModuleGBRcde` on
`GBR Γ b c (d+e)`) — mirroring `Pentagon.lean`'s own `gq2Assoc`-adjacent
"column-level recast" pattern (verified, this session, to coexist
diamond-free with `RouteBimod.lean`'s own `GBR`-level "coefficient
recast" instance, exactly as `gq2Assoc` itself already relies on).

## What did NOT land this round, and the precise finding

**`recog_E21M` itself is NOT landed.** Tracing `omegaV14'`'s own
generator formula against `E21M_leaf`'s domain shape (`mk n Y`, `n`
split-able, `Y` opaque) surfaces a finding ONE STAGE DEEPER than the
original blocker, not an elimination of it: `gV14SplitC`'s own generator
formula (`RelTensor.assoc_symm_mk`) needs its OWN second argument (here,
`Y`) `mk`-shaped to reduce — the SAME kind of obstruction as the
original `omegaV14`'s `mapEquivLeft(gq4Close.symm)`, just relocated from
`omegaV14`'s FIRST stage to `omegaV14'`'s SECOND stage. Since `Y` is
never split in `E21M_leaf`'s own statement (per the established "leave
the canonical image unexpanded" convention, `QuintRecog5.lean`), a leaf
firing on `E21M_leaf`'s literal opaque-`Y` output is NOT achievable via
`omegaV14'`'s current staging alone. **Recommended next step** (for
whichever round schedules `recog_E21M`): build the `gV14SplitC`+
`gThreeCast`+`gq4TotalCast` composite as ONE combined bilinear-lift
device DIRECTLY over `(u : F_{c,d+e}, Y : Y_{-}type)` — a genuinely NEW
device, since `Y` would then be consumed via `RelTensor.lift`'s OWN
universal property (valid on ALL of `Y`, opaque or not) rather than via
`gV14SplitC`'s own `assoc_symm_mk`-based generator formula — and relate
its value on `E21M_leaf`'s specific `Y = (gq3rCast).symm(gTCanon(mk t p))`
to `GE5`'s own `gq5Swap`-built output through a FRESH naturality lemma
(the `gq3rCast`-compatibility of this new combined device), rather than
attempting a "closed GQ4-value" reduction independent of `Y`. A fully
split-generator leaf for `omegaV14'` (mirroring `omegaV14_mk_of_mem`'s
own shape with `Y` ALSO split) is mechanically routine given the pieces
here, but was not the requested shape and was not pursued this round.

## Instance ledger (new)

`instModuleGV14ColumnRecast`/`instSMulCommClassGV14ColumnRecast`/
`instIsScalarTowerGV14ColumnRecast` (on `F_{c,d+e}`, recast to
`D_{c+d+e}` via `Γ.gaugeCast (add_assoc c d e)`); `instModuleInnerDe`/
`instSMulCommClassInnerDe`/`instIsScalarTowerInnerDe` (on the compound
`F_{c,d+e} ⊗ F_{b,c+d+e}`, `D_{d+e}`-slot, via `leftModule` propagated
from `F_{c,d+e}`'s own `SlotRight`, `SMulCommClass` via
`leftActionEnd_comm_rightActionEnd`, `IsScalarTower` via `leftActionEnd`'s
own `K`-linearity); `instModuleGBRcde`/`instSMulCommClassGBRcde`/
`instIsScalarTowerGBRcde` (on `GBR Γ b c (d+e)`, `D_{d+e}`-slot — its own
`cslot`, found already registered via `infer_instance`).
-/
import Superfusion.GaugeChi.QuintExtract3

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

/-! ### The three-letter right-route recast -/

section GbrAssocCast

private noncomputable def gbrAssocCastFwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + d)) →ₗ[K] GBR Γ a b (c + d) :=
  (GBR.mk Γ a b (c + d)).compl₂
    (fusionColumnCast K Γ a (add_assoc b c d).symm).symm.toLinearMap

private theorem gbrAssocCastFwdBilin_apply (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + c + d))) :
    gbrAssocCastFwdBilin K Γ a b c d m n
      = GBR.mk Γ a b (c + d) m
          ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm n) :=
  rfl

private theorem gbrAssocCastGBRMkEq (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + (c + d)))) :
    GBR.mk Γ a b (c + d) m n
      = RelTensor.mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + (c + d)))) m n :=
  rfl

private theorem gbrAssocCastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d)).carrier
      (gbrAssocCastFwdBilin K Γ a b c d) := by
  intro t m n
  rw [gbrAssocCastFwdBilin_apply, gbrAssocCastFwdBilin_apply,
    fusionColumnCast_symm_symm_rslot, gbrAssocCastGBRMkEq, gbrAssocCastGBRMkEq,
    fusionColumn_recast_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gbrAssocCastFwd :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + c + d))) →ₗ[K]
      GBR Γ a b (c + d) :=
  RelTensor.lift (gbrAssocCastFwdBilin K Γ a b c d)
    (gbrAssocCastFwd_balanced K Γ a b c d)

private theorem gbrAssocCastFwd_mk (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + c + d))) :
    gbrAssocCastFwd K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) m n)
      = GBR.mk Γ a b (c + d) m
          ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm n) := by
  rw [gbrAssocCastFwd, RelTensor.lift_mk, gbrAssocCastFwdBilin_apply]

private noncomputable def gbrAssocCastBwdBilin :
    FusionColumn (Γ.fuse b (c + d)) →ₗ[K]
      FusionColumn (Γ.fuse a (b + (c + d))) →ₗ[K]
        RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) :=
  (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
    (FusionColumn (Γ.fuse a (b + c + d)))).compl₂
      (fusionColumnCast K Γ a (add_assoc b c d).symm).toLinearMap

private theorem gbrAssocCastBwdBilin_apply (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gbrAssocCastBwdBilin K Γ a b c d m n
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm n) :=
  rfl

private theorem gbrAssocCastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d))).carrier
      (gbrAssocCastBwdBilin K Γ a b c d) := by
  intro t m n
  rw [gbrAssocCastBwdBilin_apply, gbrAssocCastBwdBilin_apply,
    fusionColumnCast_symm_rslot,
    show (MulOpposite.op t • m : FusionColumn (Γ.fuse b (c + d)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc b c d)).toAlgEquiv.symm t) • m from by
      rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gbrAssocCastBwd :
    GBR Γ a b (c + d) →ₗ[K]
      RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + c + d))) :=
  RelTensor.lift (gbrAssocCastBwdBilin K Γ a b c d)
    (gbrAssocCastBwd_balanced K Γ a b c d)

private theorem gbrAssocCastBwd_mk (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gbrAssocCastBwd K Γ a b c d (GBR.mk Γ a b (c + d) m n)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) m
          (fusionColumnCast K Γ a (add_assoc b c d).symm n) := by
  show RelTensor.lift (gbrAssocCastBwdBilin K Γ a b c d)
      (gbrAssocCastBwd_balanced K Γ a b c d)
      (RelTensor.mk K (Γ.D (b + (c + d))).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + (c + d)))) m n) = _
  rw [RelTensor.lift_mk, gbrAssocCastBwdBilin_apply]

private theorem gbrAssocCastFwd_bwd :
    (gbrAssocCastFwd K Γ a b c d).comp (gbrAssocCastBwd K Γ a b c d)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show gbrAssocCastFwd K Γ a b c d
      (gbrAssocCastBwd K Γ a b c d (GBR.mk Γ a b (c + d) m n))
    = GBR.mk Γ a b (c + d) m n
  rw [gbrAssocCastBwd_mk, gbrAssocCastFwd_mk,
    LinearEquiv.symm_apply_apply]

private theorem gbrAssocCastBwd_fwd :
    (gbrAssocCastBwd K Γ a b c d).comp (gbrAssocCastFwd K Γ a b c d)
      = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show gbrAssocCastBwd K Γ a b c d
      (gbrAssocCastFwd K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) m n))
    = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + c + d))) m n
  rw [gbrAssocCastFwd_mk, gbrAssocCastBwd_mk,
    LinearEquiv.apply_symm_apply]

/-- Reassociate the coefficient of a raw right-route pair. -/
noncomputable def gbrAssocCast :
    RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
        (FusionColumn (Γ.fuse a (b + c + d))) ≃ₗ[K]
      GBR Γ a b (c + d) :=
  LinearEquiv.ofLinear (gbrAssocCastFwd K Γ a b c d)
    (gbrAssocCastBwd K Γ a b c d)
    (gbrAssocCastFwd_bwd K Γ a b c d) (gbrAssocCastBwd_fwd K Γ a b c d)

theorem gbrAssocCast_mk (m : FusionColumn (Γ.fuse b (c + d)))
    (n : FusionColumn (Γ.fuse a (b + c + d))) :
    gbrAssocCast K Γ a b c d
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) m n)
      = GBR.mk Γ a b (c + d) m
          ((fusionColumnCast K Γ a (add_assoc b c d).symm).symm n) :=
  gbrAssocCastFwd_mk K Γ a b c d m n

private theorem fusionColumnCast_assoc_total (τ : (Γ.D (a + b + c + d)).carrier)
    (n : FusionColumn (Γ.fuse a (b + c + d))) :
    (fusionColumnCast K Γ a (add_assoc b c d).symm).symm (MulOpposite.op τ • n)
      = MulOpposite.op τ •
          (fusionColumnCast K Γ a (add_assoc b c d).symm).symm n :=
  PentagonB.rightEquivariant_symm K
    (fusionColumnCast K Γ a (add_assoc b c d).symm)
    (fusionColumnCast_bcd_recast K Γ a b c d) τ n

/-- `gbrAssocCast` commutes with the left-associated total coefficient. -/
theorem gbrAssocCast_totalSlot (τ : (Γ.D (a + b + c + d)).carrier)
    (z : RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
      (FusionColumn (Γ.fuse a (b + c + d)))) :
    gbrAssocCast K Γ a b c d (MulOpposite.op τ • z)
      = MulOpposite.op τ • gbrAssocCast K Γ a b c d z := by
  induction z using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m n =>
      rw [show (MulOpposite.op τ • RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (FusionColumn (Γ.fuse a (b + c + d))) m n
            : RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + c + d))))
          = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + c + d))) m (MulOpposite.op τ • n) from
        rightActionEnd_mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) (MulOpposite.op τ) m n,
        gbrAssocCast_mk, gbrAssocCast_mk, GBRTotal4_smul_mk,
        fusionColumnCast_assoc_total]

/-- `gbrAssocCast` leaves the `(c+d)` slot untouched. -/
theorem gbrAssocCast_cdSlot (τ : (Γ.D (c + d)).carrier)
    (z : RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
      (FusionColumn (Γ.fuse a (b + c + d)))) :
    gbrAssocCast K Γ a b c d (τ • z) = τ • gbrAssocCast K Γ a b c d z := by
  induction z using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m n =>
      rw [show (τ • RelTensor.mk K (Γ.D (b + c + d)).carrier
            (FusionColumn (Γ.fuse b (c + d))) (FusionColumn (Γ.fuse a (b + c + d))) m n
            : RelTensor K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + c + d))))
          = RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
              (FusionColumn (Γ.fuse a (b + c + d))) (τ • m) n from
        leftActionEnd_mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse b (c + d)))
          (FusionColumn (Γ.fuse a (b + c + d))) τ m n,
        gbrAssocCast_mk, gbrAssocCast_mk, GBR.cslot_smul_mk]

end GbrAssocCast

/-! ### An order-compatible extraction at `V14` -/

section OmegaV14Alt

/-- Equality transport in the third group argument of `GBR`.  Unlike a
cast of the whole balanced tensor, this family has uniform `K`-module
instances, so equality elimination is cheap and robust. -/
noncomputable def gbrIndexCast {x y : G} (h : x = y) :
    GBR Γ a b x ≃ₗ[K] GBR Γ a b y :=
  LinearEquiv.cast h

theorem gbrIndexCast_cslot {x y : G} (h : x = y) (τ : (Γ.D x).carrier)
    (n : GBR Γ a b x) :
    gbrIndexCast K Γ a b h (τ • n)
      = (Γ.gaugeCast h).toAlgEquiv τ • gbrIndexCast K Γ a b h n := by
  subst y
  rfl

theorem gbrIndexCast_symm_cslot {x y : G} (h : x = y) (τ : (Γ.D y).carrier)
    (n : GBR Γ a b y) :
    (gbrIndexCast K Γ a b h).symm (τ • n)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (gbrIndexCast K Γ a b h).symm n := by
  subst y
  rfl

private noncomputable def gq4rClusterCastFwdBilin
    (h : c + d + e = c + (d + e)) :
    FusionColumn (Γ.fuse c (d + e)) →ₗ[K]
      GBR Γ a b (c + d + e) →ₗ[K] GQ4r K Γ a b c (d + e) :=
  (GQ4r.mk K Γ a b c (d + e)).compl₂ (gbrIndexCast K Γ a b h).toLinearMap

private theorem gq4rClusterCastFwdBilin_apply
    (h : c + d + e = c + (d + e)) (m : FusionColumn (Γ.fuse c (d + e)))
    (n : GBR Γ a b (c + d + e)) :
    gq4rClusterCastFwdBilin K Γ a b c d e h m n
      = GQ4r.mk K Γ a b c (d + e) m (gbrIndexCast K Γ a b h n) :=
  rfl

private theorem gq4rClusterCastMkEq (m : FusionColumn (Γ.fuse c (d + e)))
    (n : GBR Γ a b (c + (d + e))) :
    GQ4r.mk K Γ a b c (d + e) m n
      = RelTensor.mk K (Γ.D (c + (d + e))).carrier
          (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + (d + e))) m n :=
  rfl

private theorem gq4rClusterCastFwd_balanced
    (h : c + d + e = c + (d + e)) :
    RelTensor.IsBalanced (Γ.D (c + d + e)).carrier
      (gq4rClusterCastFwdBilin K Γ a b c d e h) := by
  intro t m n
  rw [gq4rClusterCastFwdBilin_apply, gq4rClusterCastFwdBilin_apply,
    fusionColumn_recast_op_smul_def, gq4rClusterCastMkEq, gq4rClusterCastMkEq,
    RelTensor.mk_op_smul, gbrIndexCast_cslot]

private noncomputable def gq4rClusterCastFwd
    (h : c + d + e = c + (d + e)) :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (GBR Γ a b (c + d + e)) →ₗ[K]
      GQ4r K Γ a b c (d + e) :=
  RelTensor.lift (gq4rClusterCastFwdBilin K Γ a b c d e h)
    (gq4rClusterCastFwd_balanced K Γ a b c d e h)

private theorem gq4rClusterCastFwd_mk
    (h : c + d + e = c + (d + e)) (m : FusionColumn (Γ.fuse c (d + e)))
    (n : GBR Γ a b (c + d + e)) :
    gq4rClusterCastFwd K Γ a b c d e h
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) m n)
      = GQ4r.mk K Γ a b c (d + e) m (gbrIndexCast K Γ a b h n) := by
  rw [gq4rClusterCastFwd, RelTensor.lift_mk, gq4rClusterCastFwdBilin_apply]

private noncomputable def gq4rClusterCastBwdBilin
    (h : c + d + e = c + (d + e)) :
    FusionColumn (Γ.fuse c (d + e)) →ₗ[K]
      GBR Γ a b (c + (d + e)) →ₗ[K]
        RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) :=
  (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
    (GBR Γ a b (c + d + e))).compl₂ (gbrIndexCast K Γ a b h).symm.toLinearMap

private theorem gq4rClusterCastBwdBilin_apply
    (h : c + d + e = c + (d + e)) (m : FusionColumn (Γ.fuse c (d + e)))
    (n : GBR Γ a b (c + (d + e))) :
    gq4rClusterCastBwdBilin K Γ a b c d e h m n
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) m ((gbrIndexCast K Γ a b h).symm n) :=
  rfl

private theorem gq4rClusterCastBwd_balanced
    (h : c + d + e = c + (d + e)) :
    RelTensor.IsBalanced (Γ.D (c + (d + e))).carrier
      (gq4rClusterCastBwdBilin K Γ a b c d e h) := by
  intro t m n
  rw [gq4rClusterCastBwdBilin_apply, gq4rClusterCastBwdBilin_apply,
    gbrIndexCast_symm_cslot,
    show (MulOpposite.op t • m : FusionColumn (Γ.fuse c (d + e)))
        = MulOpposite.op ((Γ.gaugeCast h).toAlgEquiv.symm t) • m from by
      rw [fusionColumn_recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gq4rClusterCastBwd
    (h : c + d + e = c + (d + e)) :
    GQ4r K Γ a b c (d + e) →ₗ[K]
      RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (GBR Γ a b (c + d + e)) :=
  RelTensor.lift (gq4rClusterCastBwdBilin K Γ a b c d e h)
    (gq4rClusterCastBwd_balanced K Γ a b c d e h)

private theorem gq4rClusterCastBwd_mk
    (h : c + d + e = c + (d + e)) (m : FusionColumn (Γ.fuse c (d + e)))
    (n : GBR Γ a b (c + (d + e))) :
    gq4rClusterCastBwd K Γ a b c d e h (GQ4r.mk K Γ a b c (d + e) m n)
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) m ((gbrIndexCast K Γ a b h).symm n) := by
  show RelTensor.lift (gq4rClusterCastBwdBilin K Γ a b c d e h)
      (gq4rClusterCastBwd_balanced K Γ a b c d e h)
      (RelTensor.mk K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
        (GBR Γ a b (c + (d + e))) m n) = _
  rw [RelTensor.lift_mk, gq4rClusterCastBwdBilin_apply]

private theorem gq4rClusterCastFwd_bwd
    (h : c + d + e = c + (d + e)) :
    (gq4rClusterCastFwd K Γ a b c d e h).comp
        (gq4rClusterCastBwd K Γ a b c d e h) = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show gq4rClusterCastFwd K Γ a b c d e h
      (gq4rClusterCastBwd K Γ a b c d e h (GQ4r.mk K Γ a b c (d + e) m n))
    = GQ4r.mk K Γ a b c (d + e) m n
  rw [gq4rClusterCastBwd_mk, gq4rClusterCastFwd_mk,
    LinearEquiv.apply_symm_apply]

private theorem gq4rClusterCastBwd_fwd
    (h : c + d + e = c + (d + e)) :
    (gq4rClusterCastBwd K Γ a b c d e h).comp
        (gq4rClusterCastFwd K Γ a b c d e h) = LinearMap.id := by
  refine RelTensor.hom_ext fun m n => ?_
  show gq4rClusterCastBwd K Γ a b c d e h
      (gq4rClusterCastFwd K Γ a b c d e h
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) m n))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (GBR Γ a b (c + d + e)) m n
  rw [gq4rClusterCastFwd_mk, gq4rClusterCastBwd_mk,
    LinearEquiv.symm_apply_apply]

/-- Recast the raw exposed inner tensor to the literal shifted `GQ4r`. -/
noncomputable def gq4rClusterCast (h : c + d + e = c + (d + e)) :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (GBR Γ a b (c + d + e)) ≃ₗ[K]
      GQ4r K Γ a b c (d + e) :=
  LinearEquiv.ofLinear (gq4rClusterCastFwd K Γ a b c d e h)
    (gq4rClusterCastBwd K Γ a b c d e h)
    (gq4rClusterCastFwd_bwd K Γ a b c d e h)
    (gq4rClusterCastBwd_fwd K Γ a b c d e h)

theorem gq4rClusterCast_mk (h : c + d + e = c + (d + e))
    (m : FusionColumn (Γ.fuse c (d + e))) (n : GBR Γ a b (c + d + e)) :
    gq4rClusterCast K Γ a b c d e h
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) m n)
      = GQ4r.mk K Γ a b c (d + e) m (gbrIndexCast K Γ a b h n) :=
  gq4rClusterCastFwd_mk K Γ a b c d e h m n

theorem gq4rClusterCast_deSlot (h : c + d + e = c + (d + e))
    (τ : (Γ.D (d + e)).carrier)
    (z : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (GBR Γ a b (c + d + e))) :
    gq4rClusterCast K Γ a b c d e h (τ • z)
      = τ • gq4rClusterCast K Γ a b c d e h z := by
  induction z using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | mk m n =>
      rw [show (τ • RelTensor.mk K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e)) m n
            : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (GBR Γ a b (c + d + e)))
          = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (GBR Γ a b (c + d + e)) (τ • m) n from
        leftActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (GBR Γ a b (c + d + e)) τ m n,
        gq4rClusterCast_mk, gq4rClusterCast_mk, GQ4r.dslot_smul_mk]

/-- First cancel the associator which closes edge 21. -/
noncomputable def omegaV14AltStageA : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
      (RelTensor K (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  (gV14StepFinal K Γ a b c d e).symm

/-- Undo `gq3rCast.symm` before any reassociation.  This is the decisive
ordering change: an opaque canonical `GBR` value remains an opaque
top-level tensor factor. -/
noncomputable def omegaV14AltStageB :
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) ≃ₗ[K]
      RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (GBR Γ a b (c + d + e)) :=
  RelTensor.mapEquivRight K (gq3rCast K Γ a b c d e)
    (gq3rCast_bSlot K Γ a b c d e)

/-- Expose `F_{d,e}` after the opaque inner value has been restored. -/
noncomputable def omegaV14AltStageC :
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (GBR Γ a b (c + d + e)) ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e))) :=
  RelTensor.assoc K (Γ.D (d + e)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse c (d + e)))
    (GBR Γ a b (c + d + e))

/-- Re-index the exposed inner tensor to the literal shifted `GQ4r`. -/
noncomputable def omegaV14AltStageD :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e))) ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ4r K Γ a b c (d + e)) :=
  RelTensor.mapEquivRight K
    (gq4rClusterCast K Γ a b c d e (add_assoc c d e))
    (gq4rClusterCast_deSlot K Γ a b c d e (add_assoc c d e))

/-- Close the literal shifted `GQ4r`, still under the untouched
`F_{d,e}` spectator. -/
noncomputable def omegaV14AltStageE :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ4r K Γ a b c (d + e)) ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ4 K Γ a b c (d + e)) :=
  RelTensor.mapEquivRight K (gq4Close K Γ a b c (d + e))
    (GQ4Close.comp_dslot_univ K Γ a b c (d + e))

/-- The `V14` spectator extraction ordered for edge 21. -/
noncomputable def omegaV14Alt : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GQ4 K Γ a b c (d + e)) :=
  (omegaV14AltStageA K Γ a b c d e).trans
    ((omegaV14AltStageB K Γ a b c d e).trans
      ((omegaV14AltStageC K Γ a b c d e).trans
        ((omegaV14AltStageD K Γ a b c d e).trans
          (omegaV14AltStageE K Γ a b c d e))))

private theorem omegaV14AltStageB_mk (m : GBR Γ c d e)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    omegaV14AltStageB K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) m n)
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (GBR Γ a b (c + d + e)) m (gq3rCast K Γ a b c d e n) :=
  RelTensor.map_mk (LinearMap.id : GBR Γ c d e →ₗ[K] GBR Γ c d e)
    (gq3rCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (gq3rCast_bSlot K Γ a b c d e) m n

private theorem omegaV14AltStageD_mk (w : FusionColumn (Γ.fuse d e))
    (n : RelTensor K (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e))) :
    omegaV14AltStageD K Γ a b c d e
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e))) w n)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4r K Γ a b c (d + e)) w
          (gq4rClusterCast K Γ a b c d e (add_assoc c d e) n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K]
      FusionColumn (Γ.fuse d e))
    (gq4rClusterCast K Γ a b c d e (add_assoc c d e)).toLinearMap
    (fun _ _ => rfl) (gq4rClusterCast_deSlot K Γ a b c d e (add_assoc c d e)) w n

private theorem omegaV14AltStageE_mk (w : FusionColumn (Γ.fuse d e))
    (n : GQ4r K Γ a b c (d + e)) :
    omegaV14AltStageE K Γ a b c d e
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4r K Γ a b c (d + e)) w n)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4 K Γ a b c (d + e)) w (gq4Close K Γ a b c (d + e) n) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K]
      FusionColumn (Γ.fuse d e))
    (gq4Close K Γ a b c (d + e)).toLinearMap (fun _ _ => rfl)
    (GQ4Close.comp_dslot_univ K Γ a b c (d + e)) w n

/-- The cancellation formula needed by `recog_E21M`.  Its inner value
`n` is completely opaque: `gq3rCast.symm` is cancelled before the only
associator that inspects the outer `GBR(c,d,e)` generator. -/
theorem omegaV14Alt_after_final (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e))) (n : GBR Γ a b (c + d + e)) :
    omegaV14Alt K Γ a b c d e
        (gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (GBR.mk Γ c d e w s) ((gq3rCast K Γ a b c d e).symm n)))
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4 K Γ a b c (d + e)) w
          (gq4Close K Γ a b c (d + e)
            (GQ4r.mk K Γ a b c (d + e) s
              (gbrIndexCast K Γ a b (add_assoc c d e) n))) := by
  have hA : omegaV14AltStageA K Γ a b c d e
      (gV14StepFinal K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))
          (GBR.mk Γ c d e w s) ((gq3rCast K Γ a b c d e).symm n)))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        (GBR.mk Γ c d e w s) ((gq3rCast K Γ a b c d e).symm n) :=
    (gV14StepFinal K Γ a b c d e).symm_apply_apply _
  change omegaV14AltStageE K Γ a b c d e
      (omegaV14AltStageD K Γ a b c d e
        (omegaV14AltStageC K Γ a b c d e
          (omegaV14AltStageB K Γ a b c d e
            (omegaV14AltStageA K Γ a b c d e
              (gV14StepFinal K Γ a b c d e
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                  (RelTensor K (Γ.D (b + c + d + e)).carrier
                    (FusionColumn (Γ.fuse b (c + d + e)))
                    (FusionColumn (Γ.fuse a (b + c + d + e))))
                  (GBR.mk Γ c d e w s) ((gq3rCast K Γ a b c d e).symm n))))))) = _
  rw [hA, omegaV14AltStageB_mk, LinearEquiv.apply_symm_apply]
  rw [show omegaV14AltStageC K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (GBR Γ a b (c + d + e)) (GBR.mk Γ c d e w s) n)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e))) w
          (RelTensor.mk K (Γ.D (c + d + e)).carrier
            (FusionColumn (Γ.fuse c (d + e))) (GBR Γ a b (c + d + e)) s n) from
    RelTensor.assoc_mk K (Γ.D (d + e)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse c (d + e)))
      (GBR Γ a b (c + d + e)) w s n]
  rw [omegaV14AltStageD_mk, gq4rClusterCast_mk, omegaV14AltStageE_mk]

end OmegaV14Alt

/-! ### Comparison with the original `V14` extraction -/

section OmegaV14Comparison

private theorem fusionColumnCast_trans_apply {x y z : G}
    (hxy : x = y) (hyz : y = z) (m : FusionColumn (Γ.fuse a x)) :
    fusionColumnCast K Γ a hyz (fusionColumnCast K Γ a hxy m)
      = fusionColumnCast K Γ a (hxy.trans hyz) m := by
  subst y
  subst z
  rfl

private theorem fusionColumnCast_symm_eq {x y : G} (h : x = y) :
    fusionColumnCast K Γ a h.symm = (fusionColumnCast K Γ a h).symm := by
  subst y
  rfl

private theorem gbrIndexCast_mk {x y : G} (h : x = y)
    (m : FusionColumn (Γ.fuse b x))
    (n : FusionColumn (Γ.fuse a (b + x))) :
    gbrIndexCast K Γ a b h (GBR.mk Γ a b x m n)
      = GBR.mk Γ a b y (fusionColumnCast K Γ b h m)
          (fusionColumnCast K Γ a (congrArg (b + ·) h) n) := by
  subst y
  rfl

private noncomputable def omegaV14ShiftB
    (x : FusionColumn (Γ.fuse b (c + d + e))) :
    FusionColumn (Γ.fuse b (c + (d + e))) :=
  fusionColumnCast K Γ b (add_assoc c d e) x

private noncomputable def omegaV14CompareGen (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ b c (d + e)) : GQ4 K Γ b c d e :=
  gq4Close K Γ b c d e (GQ4r.mk K Γ b c d e w p)

private theorem omegaV14Gen_raw (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (x : FusionColumn (Γ.fuse b (c + d + e))) :
    omegaV14CompareGen K Γ b c d e w
        (GBR.mk Γ b c (d + e) s (omegaV14ShiftB K Γ b c d e x))
      = GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s) x := by
  unfold omegaV14CompareGen omegaV14ShiftB
  have hClose : gq4Close K Γ b c d e
        (GQ4r.mk K Γ b c d e w
          (GBR.mk Γ b c (d + e) s
            (fusionColumnCast K Γ b (add_assoc c d e) x)))
      = GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s)
          (fusionColumnCast K Γ b (add_assoc c d e).symm
            (fusionColumnCast K Γ b (add_assoc c d e) x)) :=
    gq4Close_mk K Γ b c d e w s
      (fusionColumnCast K Γ b (add_assoc c d e) x)
  rw [hClose, fusionColumnCast_symm_eq K Γ b (add_assoc c d e),
    LinearEquiv.symm_apply_apply]

/-- The original extraction on an ordinary fully split `V14` generator. -/
private theorem omegaV14_split (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (x : FusionColumn (Γ.fuse b (c + d + e)))
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s) x) y)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4 K Γ a b c (d + e)) w
          (GQ4.mk K Γ a b c (d + e)
            (GBR.mk Γ b c (d + e) s (omegaV14ShiftB K Γ b c d e x))
            (fusionColumnCast K Γ a (add_assoc (b + c) d e) y)) := by
  rw [← omegaV14Gen_raw K Γ b c d e w s x,
    show omegaV14 K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (omegaV14CompareGen K Γ b c d e w
              (GBR.mk Γ b c (d + e) s (omegaV14ShiftB K Γ b c d e x))) y)
        = _ from omegaV14_mk_of_mem K Γ a b c d e w
          (GBR.mk Γ b c (d + e) s (omegaV14ShiftB K Γ b c d e x)) y]

private theorem gV14StepFinal_split (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (x : FusionColumn (Γ.fuse b (c + d + e)))
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV14StepFinal K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))
          (GBR.mk Γ c d e w s)
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) x y))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s) x) y :=
  RelTensor.assoc_symm_mk K (Γ.D (c + d + e)).carrier
    (Γ.D (b + c + d + e)).carrier (GBR Γ c d e)
    (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e)))
    (GBR.mk Γ c d e w s) x y

/-- The reordered extraction has the same split-generator formula as
the original extraction. -/
private theorem omegaV14Alt_split (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (x : FusionColumn (Γ.fuse b (c + d + e)))
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14Alt K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s) x) y)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4 K Γ a b c (d + e)) w
          (GQ4.mk K Γ a b c (d + e)
            (GBR.mk Γ b c (d + e) s (omegaV14ShiftB K Γ b c d e x))
            (fusionColumnCast K Γ a (add_assoc (b + c) d e) y)) := by
  let q := RelTensor.mk K (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e))) x y
  let n := gq3rCast K Γ a b c d e q
  have hInput : gV14StepFinal K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))
          (GBR.mk Γ c d e w s) ((gq3rCast K Γ a b c d e).symm n))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ4.mk K Γ b c d e (GBR.mk Γ c d e w s) x) y := by
    dsimp [n]
    rw [LinearEquiv.symm_apply_apply]
    exact gV14StepFinal_split K Γ a b c d e w s x y
  rw [← hInput, omegaV14Alt_after_final]
  dsimp [n, q]
  rw [gq3rCast_mk, gbrIndexCast_mk]
  have hClose : gq4Close K Γ a b c (d + e)
        (GQ4r.mk K Γ a b c (d + e) s
          (GBR.mk Γ a b (c + (d + e))
            (fusionColumnCast K Γ b (add_assoc c d e) x)
            (fusionColumnCast K Γ a (congrArg (b + ·) (add_assoc c d e))
              (fusionColumnCast K Γ a (add_assoc_four b c d e) y))))
      = GQ4.mk K Γ a b c (d + e)
          (GBR.mk Γ b c (d + e) s
            (fusionColumnCast K Γ b (add_assoc c d e) x))
          (fusionColumnCast K Γ a (add_assoc b c (d + e)).symm
            (fusionColumnCast K Γ a (congrArg (b + ·) (add_assoc c d e))
              (fusionColumnCast K Γ a (add_assoc_four b c d e) y))) :=
    gq4Close_mk K Γ a b c (d + e) s
      (fusionColumnCast K Γ b (add_assoc c d e) x)
      (fusionColumnCast K Γ a (congrArg (b + ·) (add_assoc c d e))
        (fusionColumnCast K Γ a (add_assoc_four b c d e) y))
  rw [hClose]
  unfold omegaV14ShiftB
  congr 2
  rw [fusionColumnCast_trans_apply, fusionColumnCast_trans_apply]

private noncomputable def omegaV14GQ4Gen (n : GBR Γ c d e)
    (x : FusionColumn (Γ.fuse b (c + d + e))) : GQ4 K Γ b c d e :=
  GQ4.mk K Γ b c d e n x

@[simp] private theorem omegaV14GQ4Gen_zero
    (x : FusionColumn (Γ.fuse b (c + d + e))) :
    omegaV14GQ4Gen K Γ b c d e 0 x = 0 := by
  unfold omegaV14GQ4Gen GQ4.mk
  rw [map_zero, LinearMap.zero_apply]

@[simp] private theorem omegaV14GQ4Gen_add (n n' : GBR Γ c d e)
    (x : FusionColumn (Γ.fuse b (c + d + e))) :
    omegaV14GQ4Gen K Γ b c d e (n + n') x
      = omegaV14GQ4Gen K Γ b c d e n x
        + omegaV14GQ4Gen K Γ b c d e n' x := by
  unfold omegaV14GQ4Gen GQ4.mk
  rw [map_add, LinearMap.add_apply]

private noncomputable def omegaV14V14Gen (m : GQ4 K Γ b c d e)
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) : V14 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) m y

@[simp] private theorem omegaV14V14Gen_zero
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14V14Gen K Γ a b c d e 0 y = 0 := by
  unfold omegaV14V14Gen
  rw [map_zero, LinearMap.zero_apply]
  rfl

@[simp] private theorem omegaV14V14Gen_add (m m' : GQ4 K Γ b c d e)
    (y : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14V14Gen K Γ a b c d e (m + m') y
      = omegaV14V14Gen K Γ a b c d e m y
        + omegaV14V14Gen K Γ a b c d e m' y := by
  unfold omegaV14V14Gen
  rw [map_add, LinearMap.add_apply]
  rfl

@[elab_as_elim]
private theorem omegaV14GQ4_induction_on
    {motive : GQ4 K Γ b c d e → Prop} (m : GQ4 K Γ b c d e)
    (zero : motive 0)
    (mk : ∀ (n : GBR Γ c d e) (x : FusionColumn (Γ.fuse b (c + d + e))),
      motive (omegaV14GQ4Gen K Γ b c d e n x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m :=
  RelTensor.induction_on K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
    (FusionColumn (Γ.fuse b (c + d + e))) m zero mk add

@[elab_as_elim]
private theorem omegaV14V14_induction_on
    {motive : V14 K Γ a b c d e → Prop} (m : V14 K Γ a b c d e)
    (zero : motive 0)
    (mk : ∀ (n : GQ4 K Γ b c d e)
      (y : FusionColumn (Γ.fuse a (b + c + d + e))),
      motive (omegaV14V14Gen K Γ a b c d e n y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m :=
  RelTensor.induction_on K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) m zero mk add

/-- The two orderings are extensionally the same spectator extraction.
The reordered definition is only a proof-engineering presentation that
cancels edge 21 before inspecting its opaque canonical value. -/
theorem omegaV14Alt_eq_omegaV14 :
    omegaV14Alt K Γ a b c d e = omegaV14 K Γ a b c d e := by
  apply LinearEquiv.ext
  intro z
  induction z using omegaV14V14_induction_on K Γ a b c d e with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk m y =>
      induction m using omegaV14GQ4_induction_on K Γ b c d e with
      | zero => simp only [omegaV14V14Gen_zero, map_zero]
      | add m m' hm hm' =>
          simp only [omegaV14V14Gen_add, map_add, hm, hm']
      | mk n x =>
          induction n using GBR.induction_on K Γ c d e with
          | zero =>
              simp only [omegaV14GQ4Gen_zero, omegaV14V14Gen_zero, map_zero]
          | add n n' hn hn' =>
              simp only [omegaV14GQ4Gen_add, omegaV14V14Gen_add, map_add, hn, hn']
          | mk w s =>
              exact (omegaV14Alt_split K Γ a b c d e w s x y).trans
                (omegaV14_split K Γ a b c d e w s x y).symm

end OmegaV14Comparison

/-! ### Recognition of edge 21 through the alternate extraction -/

section RecogE21MAlt

/-- Equality transport in the third argument of `GBL`, parallel to
`gbrIndexCast`. -/
noncomputable def gblIndexCast {x y : G} (h : x = y) :
    GBL Γ a b x ≃ₗ[K] GBL Γ a b y :=
  LinearEquiv.cast h

theorem gblIndexCast_mk {x y : G} (h : x = y)
    (t : FusionColumn (Γ.fuse a b)) (p : FusionColumn (Γ.fuse (a + b) x)) :
    gblIndexCast K Γ a b h (GBL.mk Γ a b x t p)
      = GBL.mk Γ a b y t ((fusionColumnCast K Γ (a + b) h.symm).symm p) := by
  subst y
  rfl

/-- `gTCanon` is definitionally natural under equality transport of its
third group argument. -/
theorem gTCanon_indexCast {x y : G} (h : x = y) (n : GBL Γ a b x) :
    gbrIndexCast K Γ a b h (gTCanon K Γ a b x n)
      = gTCanon K Γ a b y (gblIndexCast K Γ a b h n) := by
  subst y
  rfl

theorem gTCanon_indexCast_mk {x y : G} (h : x = y)
    (t : FusionColumn (Γ.fuse a b)) (p : FusionColumn (Γ.fuse (a + b) x)) :
    gbrIndexCast K Γ a b h
        (gTCanon K Γ a b x
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) x)) t p))
      = gTCanon K Γ a b y
          (GBL.mk Γ a b y t ((fusionColumnCast K Γ (a + b) h.symm).symm p)) := by
  change gbrIndexCast K Γ a b h (gTCanon K Γ a b x (GBL.mk Γ a b x t p)) = _
  rw [gTCanon_indexCast, gblIndexCast_mk]

private noncomputable def e21ShiftedColumn
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    FusionColumn (Γ.fuse (a + b) (c + (d + e))) :=
  (fusionColumnCast K Γ (a + b) (add_assoc c d e).symm).symm p

private theorem e21ShiftedColumn_eq
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    e21ShiftedColumn K Γ a b c d e p
      = (fusionColumnCast K Γ (a + b) (add_assoc c d e).symm).symm p :=
  rfl

/-- The `V9Inner` generator in the exact inverse-close spelling consumed
by `omegaV9`. -/
private noncomputable def e21V9Gen (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    V9Inner K Γ a b c d e :=
  gq4Close K Γ (a + b) c d e
    (GQ4r.mk K Γ (a + b) c d e w
      (GBR.mk Γ (a + b) c (d + e) s (e21ShiftedColumn K Γ a b c d e p)))

private theorem e21V9Gen_raw (w : FusionColumn (Γ.fuse d e))
    (s : FusionColumn (Γ.fuse c (d + e)))
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    e21V9Gen K Γ a b c d e w s p
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e)))
          (GBR.mk Γ c d e w s) p := by
  change gq4Close K Γ (a + b) c d e
      (GQ4r.mk K Γ (a + b) c d e w
        (GBR.mk Γ (a + b) c (d + e) s (e21ShiftedColumn K Γ a b c d e p)))
    = GQ4.mk K Γ (a + b) c d e (GBR.mk Γ c d e w s) p
  show gq4Close K Γ (a + b) c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ (a + b) c (d + e)) w
        (RelTensor.mk K (Γ.D (c + (d + e))).carrier
          (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse (a + b) (c + (d + e)))) s
          (e21ShiftedColumn K Γ a b c d e p)))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBR.mk Γ c d e w s) p
  rw [gq4Close_mk, e21ShiftedColumn_eq,
    LinearEquiv.apply_symm_apply]

/-- `omegaV9` on the raw edge-21 domain generator, with the sole
coefficient cast made explicit in the shifted `GBR` value. -/
theorem omegaV9_e21_mk_of_mem {ju jw : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (s : FusionColumn (Γ.fuse c (d + e)))
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaV9 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (V9Inner K Γ a b c d e) t (e21V9Gen K Γ a b c d e w s p))
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ5 K Γ a b c (d + e)) w
            (GQ5.mk K Γ a b c (d + e) t
              (GBR.mk Γ (a + b) c (d + e) s (e21ShiftedColumn K Γ a b c d e p))) :=
  omegaV9_mk_of_mem K Γ a b c d e ht hw
    (GBR.mk Γ (a + b) c (d + e) s (e21ShiftedColumn K Γ a b c d e p))

/-- The alternate extraction after `E21M`, on fully split homogeneous
domain generators.  The canonical image itself remains opaque. -/
theorem omegaV14Alt_E21M_leaf {ju jw js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    {s : FusionColumn (Γ.fuse c (d + e))}
    (hs : s ∈ FusionColumn.grading (Γ.fuse c (d + e)) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaV14Alt K Γ a b c d e
        (E21M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (V9Inner K Γ a b c d e) t
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
              (FusionColumn (Γ.fuse (a + b) (c + d + e)))
              (GBR.mk Γ c d e w s) p)))
      = ((sgn ((jw + js) *
          (ju + gParity K Γ a b (c + (d + e)))) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ4 K Γ a b c (d + e)) w
            (gq4Close K Γ a b c (d + e)
              (GQ4r.mk K Γ a b c (d + e) s
                (gTCanon K Γ a b (c + (d + e))
                  (GBL.mk Γ a b (c + (d + e)) t
                    (e21ShiftedColumn K Γ a b c d e p))))) := by
  rw [E21M_leaf K Γ a b c d e ht (GBR.mk_mem_grading Γ c d e hw hs) p,
    map_zsmul, omegaV14Alt_after_final]
  rw [gTCanon_indexCast_mk K Γ a b (add_assoc c d e),
    e21ShiftedColumn_eq]
  congr 2
  rw [show gParity K Γ a b (c + d + e) = gParity K Γ a b (c + (d + e)) from
    congrArg (gParity K Γ a b) (add_assoc c d e)]

/-- The shifted bottom-route fifth edge, including its closing map. -/
noncomputable def pdeE21Map : GQ5 K Γ a b c (d + e) →ₗ[K]
    GQ4 K Γ a b c (d + e) :=
  (gq4Close K Γ a b c (d + e)).toLinearMap.comp
    (GE5 K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
      (gTCanon K Γ a b (c + (d + e))).toLinearMap
      (gCanonHphi5 K Γ a b c (d + e)))

/-- The spectator-slot super-equivariance of `pdeE21Map`: `hg5` followed
by the unsigned `d`-slot naturality of `gq4Close`. -/
theorem pdeE21Map_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (d + e)).carrier⦄,
      τ ∈ (Γ.D (d + e)).grading i → ∀ n : GQ5 K Γ a b c (d + e),
        pdeE21Map K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a b (c + (d + e)) * i) : ℤˣ) : ℤ) •
              (τ • pdeE21Map K Γ a b c d e n) := by
  intro i τ hτ n
  show gq4Close K Γ a b c (d + e)
      (GE5 K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
        (gTCanon K Γ a b (c + (d + e))).toLinearMap
        (gCanonHphi5 K Γ a b c (d + e)) (τ • n)) = _
  rw [hg5 K Γ a b c d e hτ n, map_zsmul,
    GQ4Close.comp_dslot_univ]
  rfl

theorem pdeE21Map_mk_of_mem {ju js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {s : FusionColumn (Γ.fuse c (d + e))}
    (hs : s ∈ FusionColumn.grading (Γ.fuse c (d + e)) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + (d + e)))) :
    pdeE21Map K Γ a b c d e
        (GQ5.mk K Γ a b c (d + e) t
          (GBR.mk Γ (a + b) c (d + e) s p))
      = ((sgn (js * (gParity K Γ a b (c + (d + e)) + ju)) : ℤˣ) : ℤ) •
          gq4Close K Γ a b c (d + e)
            (GQ4r.mk K Γ a b c (d + e) s
              (gTCanon K Γ a b (c + (d + e))
                (GBL.mk Γ a b (c + (d + e)) t p))) := by
  show gq4Close K Γ a b c (d + e)
      (GE5 K Γ a b c (d + e) (gParity K Γ a b (c + (d + e)))
        (gTCanon K Γ a b (c + (d + e))).toLinearMap
        (gCanonHphi5 K Γ a b c (d + e))
        (GQ5.mk K Γ a b c (d + e) t
          (GBR.mk Γ (a + b) c (d + e) s p))) = _
  have hGE : GE5 K Γ a b c (d + e)
      (gParity K Γ a b (c + (d + e)))
      (gTCanon K Γ a b (c + (d + e))).toLinearMap
      (gCanonHphi5 K Γ a b c (d + e))
      (GQ5.mk K Γ a b c (d + e) t
        (GBR.mk Γ (a + b) c (d + e) s p))
    = ((sgn (js * (gParity K Γ a b (c + (d + e)) + ju)) : ℤˣ) : ℤ) •
        (GQ4r.mk K Γ a b c (d + e) s
          (gTCanon K Γ a b (c + (d + e))
            (GBL.mk Γ a b (c + (d + e)) t p)) : GQ4r K Γ a b c (d + e)) :=
    GE5_mk_of_mem K Γ a b c (d + e)
      (gParity K Γ a b (c + (d + e)))
      (gTCanon K Γ a b (c + (d + e))).toLinearMap
      (gCanonHphi5 K Γ a b c (d + e)) hs ht p
  rw [hGE]
  exact map_zsmul (gq4Close K Γ a b c (d + e)) _ _

private noncomputable def v9InnerGen (n : GBR Γ c d e)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    V9Inner K Γ a b c d e :=
  RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
    (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p

@[simp] private theorem v9InnerGen_zero (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    v9InnerGen K Γ a b c d e 0 p = 0 := by
  unfold v9InnerGen
  rw [map_zero, LinearMap.zero_apply]
  rfl

@[simp] private theorem v9InnerGen_add (n n' : GBR Γ c d e)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    v9InnerGen K Γ a b c d e (n + n') p
      = v9InnerGen K Γ a b c d e n p + v9InnerGen K Γ a b c d e n' p := by
  unfold v9InnerGen
  rw [map_add, LinearMap.add_apply]
  rfl

private noncomputable def v9Gen (t : FusionColumn (Γ.fuse a b))
    (n : V9Inner K Γ a b c d e) : V9 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (a + b)).carrier
    (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t n

@[simp] private theorem v9Gen_zero_right (t : FusionColumn (Γ.fuse a b)) :
    v9Gen K Γ a b c d e t 0 = 0 := by
  unfold v9Gen
  rw [map_zero]
  rfl

@[simp] private theorem v9Gen_add_right (t : FusionColumn (Γ.fuse a b))
    (n n' : V9Inner K Γ a b c d e) :
    v9Gen K Γ a b c d e t (n + n')
      = v9Gen K Γ a b c d e t n + v9Gen K Γ a b c d e t n' := by
  unfold v9Gen
  rw [map_add]
  rfl

@[simp] private theorem v9Gen_zero_left (n : V9Inner K Γ a b c d e) :
    v9Gen K Γ a b c d e 0 n = 0 := by
  unfold v9Gen
  rw [map_zero, LinearMap.zero_apply]
  rfl

@[simp] private theorem v9Gen_add_left (t t' : FusionColumn (Γ.fuse a b))
    (n : V9Inner K Γ a b c d e) :
    v9Gen K Γ a b c d e (t + t') n
      = v9Gen K Γ a b c d e t n + v9Gen K Γ a b c d e t' n := by
  unfold v9Gen
  rw [map_add, LinearMap.add_apply]
  rfl

@[elab_as_elim]
private theorem v9Inner_induction_on {motive : V9Inner K Γ a b c d e → Prop}
    (z : V9Inner K Γ a b c d e)
    (zero : motive 0)
    (mk : ∀ (n : GBR Γ c d e) (p : FusionColumn (Γ.fuse (a + b) (c + d + e))),
      motive (v9InnerGen K Γ a b c d e n p))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
    (FusionColumn (Γ.fuse (a + b) (c + d + e))) z zero mk add

@[elab_as_elim]
private theorem v9_induction_on {motive : V9 K Γ a b c d e → Prop}
    (z : V9 K Γ a b c d e)
    (zero : motive 0)
    (mk : ∀ (t : FusionColumn (Γ.fuse a b)) (n : V9Inner K Γ a b c d e),
      motive (v9Gen K Γ a b c d e t n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (a + b)).carrier
    (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) z zero mk add

/-- The edge-21 recognition identity on a fully split homogeneous
generator.  This is the only branch where signs are computed. -/
private theorem recog_E21M_alt_generator {ju jw js : ZMod 2}
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    {s : FusionColumn (Γ.fuse c (d + e))}
    (hs : s ∈ FusionColumn.grading (Γ.fuse c (d + e)) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    omegaV14Alt K Γ a b c d e
        (E21M K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
              (FusionColumn (Γ.fuse (a + b) (c + d + e)))
              (GBR.mk Γ c d e w s) p)))
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeE21Map K Γ a b c d e)
          (gParity K Γ a b (c + (d + e))) (pdeE21Map_hg K Γ a b c d e)
          (omegaV9 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier
              (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                (GBR.mk Γ c d e w s) p))) := by
  have sign_id : ∀ p ju jw js : ZMod 2,
      (jw + js) * (ju + p) = jw * ju + p * jw + js * (p + ju) := by decide
  have hLHS : omegaV14Alt K Γ a b c d e
          (E21M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier
              (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                (GBR.mk Γ c d e w s) p)))
        = ((sgn ((jw + js) *
            (ju + gParity K Γ a b (c + (d + e)))) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
              (gq4Close K Γ a b c (d + e)
                (GQ4r.mk K Γ a b c (d + e) s
                  (gTCanon K Γ a b (c + (d + e))
                    (GBL.mk Γ a b (c + (d + e)) t
                      (e21ShiftedColumn K Γ a b c d e p))))) :=
    omegaV14Alt_E21M_leaf K Γ a b c d e ht hw hs p
  have hRHS : smap (Γ.D (d + e)).grading
          (FusionColumn.grading (Γ.fuse d e))
          (pdeE21Map K Γ a b c d e)
          (gParity K Γ a b (c + (d + e))) (pdeE21Map_hg K Γ a b c d e)
          (omegaV9 K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier
              (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                (GBR.mk Γ c d e w s) p)))
        = ((sgn (jw * ju) *
              sgn (gParity K Γ a b (c + (d + e)) * jw) *
              sgn (js * (gParity K Γ a b (c + (d + e)) + ju)) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
              (gq4Close K Γ a b c (d + e)
                (GQ4r.mk K Γ a b c (d + e) s
                  (gTCanon K Γ a b (c + (d + e))
                    (GBL.mk Γ a b (c + (d + e)) t
                      (e21ShiftedColumn K Γ a b c d e p))))) := by
    rw [← e21V9Gen_raw K Γ a b c d e w s p,
      omegaV9_e21_mk_of_mem K Γ a b c d e ht hw s p]
    refine (map_zsmul _ _ _).trans ?_
    rw [smap_mk_of_mem (Γ.D (d + e)).grading
        (FusionColumn.grading (Γ.fuse d e))
        (pdeE21Map K Γ a b c d e)
        (gParity K Γ a b (c + (d + e)))
        (pdeE21Map_hg K Γ a b c d e) hw,
      pdeE21Map_mk_of_mem K Γ a b c d e ht hs
        (e21ShiftedColumn K Γ a b c d e p),
      map_zsmul, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul]
  rw [hLHS, hRHS]
  congr 2
  rw [← sgn_add, ← sgn_add, sign_id]

/-- **`recog_E21M_alt`**: edge 21 is the shifted closed `GE5`, after
extracting the `F_{d,e}` spectator with `omegaV14Alt`. -/
theorem recog_E21M_alt :
    (omegaV14Alt K Γ a b c d e).toLinearMap ∘ₗ E21M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeE21Map K Γ a b c d e)
          (gParity K Γ a b (c + (d + e))) (pdeE21Map_hg K Γ a b c d e)
          ∘ₗ (omegaV9 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using v9_induction_on K Γ a b c d e with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk t n =>
      induction n using v9Inner_induction_on K Γ a b c d e with
      | zero => simp only [v9Gen_zero_right, map_zero]
      | add x y hx hy =>
          simp only [v9Gen_add_right, map_add, hx, hy]
      | mk n p =>
          induction n using GBR.induction_on_gen2 K Γ c d e with
          | zero => simp only [v9InnerGen_zero, v9Gen_zero_right, map_zero]
          | add n n' hn hn' =>
              simp only [v9InnerGen_add, v9Gen_add_right, map_add,
                hn, hn']
          | @homog jw js w s hw hs =>
              induction t using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse a b)) with
              | zero => simp only [v9Gen_zero_left, map_zero]
              | add t t' ht ht' =>
                  simp only [v9Gen_add_left, map_add, ht, ht']
              | @homogeneous ju xt =>
                  exact recog_E21M_alt_generator K Γ a b c d e xt.2 hw hs p

/-- The standard-form edge-21 recognition, obtained by identifying the
two extensionally equal `V14` extraction presentations. -/
theorem recog_E21M :
    (omegaV14 K Γ a b c d e).toLinearMap ∘ₗ E21M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (pdeE21Map K Γ a b c d e)
          (gParity K Γ a b (c + (d + e))) (pdeE21Map_hg K Γ a b c d e)
          ∘ₗ (omegaV9 K Γ a b c d e).toLinearMap := by
  rw [← omegaV14Alt_eq_omegaV14 K Γ a b c d e]
  exact recog_E21M_alt K Γ a b c d e

end RecogE21MAlt

/-! ### The new column-level recast on `F_{c,d+e}`, at `D_{c+d+e}` -/

section GV14ColumnRecast

/-- The right action of the *left-associated* coefficient algebra
`D_{c+d+e}` on `F_{c,d+e}`, pulled back along the gauge-index cast
`Γ.gaugeCast (add_assoc c d e)` -- the 3-letter mirror of `Quint.lean`'s
`instModuleFusionColumnRecast4` (there at 4 letters), needed so that
`RelTensor.assoc`/`gThreeCast`'s own balancing at `D_{c+d+e}` typecheck. -/
noncomputable instance instModuleGV14ColumnRecast :
    Module ((Γ.D (c + d + e)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse c (d + e))) :=
  Module.compHom _ (((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv.toRingHom).op)

theorem gV14ColumnRecast_op_smul_def (t : (Γ.D (c + d + e)).carrier)
    (v : FusionColumn (Γ.fuse c (d + e))) :
    MulOpposite.op t • v
      = MulOpposite.op ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv t) • v := rfl

instance instSMulCommClassGV14ColumnRecast : SMulCommClass (Γ.D (d + e)).carrier
    ((Γ.D (c + d + e)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse c (d + e))) :=
  ⟨fun y t v => smul_comm y
    (MulOpposite.op ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv (MulOpposite.unop t))) v⟩

instance instIsScalarTowerGV14ColumnRecast : IsScalarTower K
    ((Γ.D (c + d + e)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse c (d + e))) :=
  ⟨fun k t v => by
    show (MulOpposite.op ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv
        (MulOpposite.unop (k • t)))) • v
      = k • ((MulOpposite.op ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv
          (MulOpposite.unop t))) • v)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ v⟩

end GV14ColumnRecast

/-! ### Stage A+B: cancel `gV14StepFinal`, then split `GBR Γ c d e`'s own
raw columns -/

section GV14Split

/-- **`gV14Split`**: `V14 ≃ F_{d,e} ⊗ (F_{c,d+e} ⊗_{D_{cde}} Y_{-}type)`,
via `(gV14StepFinal).symm` (a GENERAL cancellation of `E21M`'s own
closing move, valid for any argument) then a plain `RelTensor.assoc`. -/
noncomputable def gV14Split : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))) :=
  (gV14StepFinal K Γ a b c d e).symm.trans
    (RelTensor.assoc K (Γ.D (d + e)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse c (d + e)))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e)))))

/-- **`gV14SplitC`**: regroup `F_{c,d+e}` with `Y_{-}type`'s own first
factor `F_{b,c+d+e}`, via a plain `RelTensor.assoc.symm` -- GENERAL in
`Y`, since `assoc_symm_mk`'s formula never touches its own `M`-slot
(`F_{c,d+e}`, the only thing this stage moves). -/
noncomputable def gV14SplitC :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))))
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e)))).symm

end GV14Split

/-! ### `gThreeCast`, THE NEW DEVICE: closing `F_{c,d+e} ⊗ F_{b,c+d+e} ≃
GBR Γ b c (d+e)` -/

section GThreeCast

/-- The `D_{d+e}`-slot action on the compound `F_{c,d+e} ⊗ F_{b,c+d+e}`,
propagated (via `leftModule`) from `F_{c,d+e}`'s own `SlotRight`. Needed
so `RelTensor.mapEquivRight` typechecks when wrapping `gV14SplitC` under
the outer `F_{d,e}` spectator. -/
noncomputable instance instModuleInnerDe :
    Module ((Γ.D (d + e)).carrier)
    (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e)))) :=
  leftModule K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
    (FusionColumn (Γ.fuse b (c + d + e))) (B := (Γ.D (d + e)).carrier)

/-- The `D_{d+e}`-slot (`leftModule`-propagated) and the `D_{bcde}}ᵐᵒᵖ`-slot
(`rightModule`-propagated, from `F_{b,c+d+e}`'s own recast) commute,
sign-free -- `leftActionEnd_comm_rightActionEnd` specialized. -/
instance instSMulCommClassInnerDe :
    SMulCommClass ((Γ.D (d + e)).carrier) ((Γ.D (b + c + d + e)).carrier)ᵐᵒᵖ
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e)))) :=
  ⟨fun x t v => LinearMap.congr_fun
    (leftActionEnd_comm_rightActionEnd K (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) x t) v⟩

/-- `leftActionEnd`'s own `K`-linearity gives `IsScalarTower K (D_{d+e})`
on the compound, via `map_smul`. -/
instance instIsScalarTowerInnerDe :
    IsScalarTower K ((Γ.D (d + e)).carrier)
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e)))) :=
  ⟨fun k x z => by
    show (k • x) • z = k • (x • z)
    have hmap : leftActionEnd K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))) (k • x)
      = k • leftActionEnd K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))) x := map_smul _ k x
    exact LinearMap.congr_fun hmap z⟩

private noncomputable def gThreeCastFwdBilin :
    FusionColumn (Γ.fuse c (d + e)) →ₗ[K]
      FusionColumn (Γ.fuse b (c + d + e)) →ₗ[K] GBR Γ b c (d + e) :=
  (GBR.mk Γ b c (d + e)).compl₂
    (fusionColumnCast K Γ b (add_assoc c d e)).toLinearMap

private theorem gThreeCastFwdBilin_apply (u : FusionColumn (Γ.fuse c (d + e)))
    (v : FusionColumn (Γ.fuse b (c + d + e))) :
    gThreeCastFwdBilin K Γ b c d e u v
      = GBR.mk Γ b c (d + e) u (fusionColumnCast K Γ b (add_assoc c d e) v) := rfl

private theorem fusionColumnCast_xslot_local (p : G) {x y : G} (h : x = y)
    (τ : (Γ.D x).carrier) (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p h (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv τ • fusionColumnCast K Γ p h w := by
  subst h
  rfl

private theorem gThreeCastFwd_balanced :
    RelTensor.IsBalanced (Γ.D (c + d + e)).carrier (gThreeCastFwdBilin K Γ b c d e) := by
  intro t u v
  rw [gThreeCastFwdBilin_apply, gThreeCastFwdBilin_apply, gV14ColumnRecast_op_smul_def]
  show GBR.mk Γ b c (d + e)
      (MulOpposite.op ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv t) • u)
      (fusionColumnCast K Γ b (add_assoc c d e) v)
    = GBR.mk Γ b c (d + e) u
        (fusionColumnCast K Γ b (add_assoc c d e) (t • v))
  rw [fusionColumnCast_xslot_local]
  exact RelTensor.mk_op_smul K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
    (FusionColumn (Γ.fuse b (c + (d + e)))) ((Γ.gaugeCast (add_assoc c d e)).toAlgEquiv t) u
    (fusionColumnCast K Γ b (add_assoc c d e) v)

private noncomputable def gThreeCastFwd :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))) →ₗ[K]
      GBR Γ b c (d + e) :=
  RelTensor.lift (gThreeCastFwdBilin K Γ b c d e) (gThreeCastFwd_balanced K Γ b c d e)

private theorem gThreeCastFwd_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (v : FusionColumn (Γ.fuse b (c + d + e))) :
    gThreeCastFwd K Γ b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v)
      = GBR.mk Γ b c (d + e) u (fusionColumnCast K Γ b (add_assoc c d e) v) := by
  show RelTensor.lift (gThreeCastFwdBilin K Γ b c d e) (gThreeCastFwd_balanced K Γ b c d e)
      (RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v) = _
  rw [RelTensor.lift_mk, gThreeCastFwdBilin_apply]

private noncomputable def gThreeCastBwdBilin :
    FusionColumn (Γ.fuse c (d + e)) →ₗ[K]
      FusionColumn (Γ.fuse b (c + (d + e))) →ₗ[K]
        RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))) :=
  (RelTensor.mk K (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e)))).compl₂
    (fusionColumnCast K Γ b (add_assoc c d e)).symm.toLinearMap

private theorem gThreeCastBwdBilin_apply (u : FusionColumn (Γ.fuse c (d + e)))
    (v : FusionColumn (Γ.fuse b (c + (d + e)))) :
    gThreeCastBwdBilin K Γ b c d e u v
      = RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u
          ((fusionColumnCast K Γ b (add_assoc c d e)).symm v) := rfl

private theorem fusionColumnCast_symm_xslot_local (p : G) {x y : G} (h : x = y)
    (τ : (Γ.D y).carrier) (w : FusionColumn (Γ.fuse p y)) :
    (fusionColumnCast K Γ p h).symm (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (fusionColumnCast K Γ p h).symm w := by
  subst h
  rfl

private theorem gThreeCastBwd_balanced :
    RelTensor.IsBalanced (Γ.D (c + (d + e))).carrier (gThreeCastBwdBilin K Γ b c d e) := by
  intro s u v
  rw [gThreeCastBwdBilin_apply, gThreeCastBwdBilin_apply, fusionColumnCast_symm_xslot_local,
    ← RelTensor.mk_op_smul, gV14ColumnRecast_op_smul_def, AlgEquiv.apply_symm_apply]

private noncomputable def gThreeCastBwd :
    GBR Γ b c (d + e) →ₗ[K]
      RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))) :=
  RelTensor.lift (gThreeCastBwdBilin K Γ b c d e) (gThreeCastBwd_balanced K Γ b c d e)

private theorem gThreeCastBwd_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (v : FusionColumn (Γ.fuse b (c + (d + e)))) :
    gThreeCastBwd K Γ b c d e (GBR.mk Γ b c (d + e) u v)
      = RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u
          ((fusionColumnCast K Γ b (add_assoc c d e)).symm v) := by
  show RelTensor.lift (gThreeCastBwdBilin K Γ b c d e) (gThreeCastBwd_balanced K Γ b c d e)
      (RelTensor.mk K (Γ.D (c + (d + e))).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + (d + e)))) u v) = _
  rw [RelTensor.lift_mk, gThreeCastBwdBilin_apply]

private theorem gThreeCastFwd_bwd :
    (gThreeCastFwd K Γ b c d e).comp (gThreeCastBwd K Γ b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun u v => ?_
  show gThreeCastFwd K Γ b c d e (gThreeCastBwd K Γ b c d e (GBR.mk Γ b c (d + e) u v))
    = GBR.mk Γ b c (d + e) u v
  rw [gThreeCastBwd_mk, gThreeCastFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gThreeCastBwd_fwd :
    (gThreeCastBwd K Γ b c d e).comp (gThreeCastFwd K Γ b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun u v => ?_
  show gThreeCastBwd K Γ b c d e (gThreeCastFwd K Γ b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v
  rw [gThreeCastFwd_mk, gThreeCastBwd_mk, LinearEquiv.symm_apply_apply]

/-- **`gThreeCast`**: identity on the shared first factor `F_{c,d+e}`,
`fusionColumnCast` on the second -- the `gq4TotalCast`-mirror one level
shallower, closing `F_{c,d+e} ⊗_{D_{c+d+e}} F_{b,c+d+e} ≃ GBR Γ b c (d+e)`. -/
noncomputable def gThreeCast :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))) ≃ₗ[K]
      GBR Γ b c (d + e) :=
  LinearEquiv.ofLinear (gThreeCastFwd K Γ b c d e) (gThreeCastBwd K Γ b c d e)
    (gThreeCastFwd_bwd K Γ b c d e) (gThreeCastBwd_fwd K Γ b c d e)

theorem gThreeCast_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (v : FusionColumn (Γ.fuse b (c + d + e))) :
    gThreeCast K Γ b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v)
      = GBR.mk Γ b c (d + e) u (fusionColumnCast K Γ b (add_assoc c d e) v) :=
  gThreeCastFwd_mk K Γ b c d e u v

/-- The bridge between `fusionColumnCast`'s two `D_{bcde}`-flavoured
recast instances (`instModuleFusionColumnRecast4` on the source,
`instModuleFusionColumnRecastABR` on the target), derived from the
ALREADY-PUBLIC `fusionColumnCast_bcd_recast` (`QuintEdges2.lean`) by a
round trip. -/
theorem fusionColumnCast_cde_recast (τ : (Γ.D (b + c + d + e)).carrier)
    (v : FusionColumn (Γ.fuse b (c + d + e))) :
    fusionColumnCast K Γ b (add_assoc c d e) (MulOpposite.op τ • v)
      = MulOpposite.op τ • fusionColumnCast K Γ b (add_assoc c d e) v := by
  rw [fusionColumnRecast4_op_smul_def, fusionColumnCast_coeff, gaugeCast_trans',
    fusionColumnRecastABR_op_smul_def]

/-- `gThreeCast`'s `D_{b+c+d+e}`-slot right-equivariance, unconditionally
-- the shape `PentagonB.RelTensor.mapEquivLeft` needs. -/
theorem gThreeCast_rightTotal (τ : (Γ.D (b + c + d + e)).carrier)
    (n : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (FusionColumn (Γ.fuse b (c + d + e)))) :
    gThreeCast K Γ b c d e (MulOpposite.op τ • n)
      = MulOpposite.op τ • gThreeCast K Γ b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk u v =>
      have hL : (MulOpposite.op τ • RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v
          : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
        = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))) u (MulOpposite.op τ • v) :=
        rightActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))) (MulOpposite.op τ) u v
      have hR : (MulOpposite.op τ • gThreeCast K Γ b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e))) u v)
          : GBR Γ b c (d + e))
        = GBR.mk Γ b c (d + e) u (MulOpposite.op τ • fusionColumnCast K Γ b (add_assoc c d e) v) := by
        rw [gThreeCast_mk, GBRTotal4_op_smul_def]
        show (rightActionEnd K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + (d + e)))) (MulOpposite.op τ))
            (RelTensor.mk K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + (d + e)))) u
              (fusionColumnCast K Γ b (add_assoc c d e) v)) = _
        rw [rightActionEnd_mk]
        rfl
      rw [hL, gThreeCast_mk, hR, fusionColumnCast_cde_recast]
  | add p q hp hq =>
      rw [smul_add, map_add, map_add, smul_add, hp, hq]

/-- `gThreeCast`'s `D_{d+e}`-slot left-equivariance (the `cslot`-style
action on its own untouched shared first factor `F_{c,d+e}`,
unconditionally). -/
theorem gThreeCast_leftEquivDe (τ : (Γ.D (d + e)).carrier)
    (n : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (FusionColumn (Γ.fuse b (c + d + e)))) :
    gThreeCast K Γ b c d e (τ • n) = τ • gThreeCast K Γ b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk u v =>
      have hL : (τ • RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))) u v
          : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
        = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))) (τ • u) v :=
        leftActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))) τ u v
      rw [hL, gThreeCast_mk, gThreeCast_mk, GBR.cslot_smul_mk]
  | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]

end GThreeCast

/-! ### Wrapping the two new stages under the `F_{d,e}` spectator -/

section Wrapping

set_option maxHeartbeats 1000000 in
/-- **`gV14SplitC`'s `D_{d+e}`-slot left-equivariance**, unconditionally
(needed to wrap it under the outer `F_{d,e}` spectator via
`RelTensor.mapEquivRight`). Proved by nested `RelTensor.induction_on`
(the outer `X`, then `Y` -- GENERAL in `Y`, matching `gV14SplitC`'s own
generic-in-`Y` construction). -/
theorem gV14SplitC_leftEquiv (τ : (Γ.D (d + e)).carrier)
    (X : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))))) :
    gV14SplitC K Γ a b c d e (τ • X) = τ • gV14SplitC K Γ a b c d e X := by
  induction X using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk m Y =>
      have hτm : (τ • RelTensor.mk K (Γ.D (c + d + e)).carrier
          (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) m Y
          : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))))
        = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m) Y :=
        leftActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) τ m Y
      rw [hτm]
      clear hτm
      induction Y using RelTensor.induction_on with
      | zero =>
          rw [show RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) m
                (0 : RelTensor K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
              = 0 from by simp only [map_zero],
            show RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m)
                (0 : RelTensor K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
              = 0 from by simp only [map_zero],
            map_zero, smul_zero]
      | mk n p =>
          show gV14SplitC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
                (FusionColumn (Γ.fuse c (d + e))) (RelTensor K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
                (τ • m) (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                  n p))
            = τ • gV14SplitC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
                (FusionColumn (Γ.fuse c (d + e))) (RelTensor K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
                m (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                  n p))
          show (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))).symm
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m)
                (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))) n p))
            = τ • (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
                (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))).symm
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) m
                (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))) n p))
          rw [RelTensor.assoc_symm_mk, RelTensor.assoc_symm_mk]
          exact (leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier
            (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
            (FusionColumn (Γ.fuse a (b + c + d + e))) τ
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))) m n) p).symm
      | add x y hx hy =>
          have e1 : RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))) m (x + y)
            = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) m x
              + RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) m y := map_add _ _ _
          have e2 : RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m) (x + y)
            = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m) x
              + RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • m) y := map_add _ _ _
          rw [e1, e2, map_add, map_add, hx, hy, smul_add]
  | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]

/-- `gV14SplitC`, wrapped by the outer `F_{d,e}` spectator via
`RelTensor.mapEquivRight`. -/
noncomputable def gV14SplitCWrapped :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))))
      ≃ₗ[K]
      RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.mapEquivRight K (gV14SplitC K Γ a b c d e) (gV14SplitC_leftEquiv K Γ a b c d e)

/-- `gThreeCast`, applied to the "inner" first factor of `V14`'s
regrouped shape, via `PentagonB.RelTensor.mapEquivLeft`. -/
noncomputable def mapEquivLeftGThreeCast :
    RelTensor K (Γ.D (b + c + d + e)).carrier
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))))
        (FusionColumn (Γ.fuse a (b + c + d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  PentagonB.RelTensor.mapEquivLeft K (gThreeCast K Γ b c d e) (gThreeCast_rightTotal K Γ b c d e)

/-- `GBR Γ b c (d+e)`'s own `D_{d+e}`-slot (its "cslot", since the fourth
argument of `GBR Γ b c (d+e)` is `d+e`) -- already registered
generically, found via `infer_instance`. -/
noncomputable instance instModuleGBRcde :
    Module ((Γ.D (d + e)).carrier) (GBR Γ b c (d + e)) :=
  inferInstanceAs (Module ((Γ.D (d + e)).carrier) (GBR Γ b c (d + e)))

instance instSMulCommClassGBRcde :
    SMulCommClass ((Γ.D (d + e)).carrier) ((Γ.D (b + c + d + e)).carrier)ᵐᵒᵖ (GBR Γ b c (d + e)) :=
  inferInstance

instance instIsScalarTowerGBRcde :
    IsScalarTower K ((Γ.D (d + e)).carrier) (GBR Γ b c (d + e)) :=
  inferInstance

/-- `mapEquivLeftGThreeCast`'s `D_{d+e}`-slot left-equivariance, chasing
`gThreeCast_leftEquivDe` through the outer `mk` (`RelTensor.map_mk`). -/
theorem mapEquivLeftGThreeCast_leftEquiv (τ : (Γ.D (d + e)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    mapEquivLeftGThreeCast K Γ a b c d e (τ • n) = τ • mapEquivLeftGThreeCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk m p =>
      have hL : (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e))) m p
          : RelTensor K (Γ.D (b + c + d + e)).carrier
              (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (FusionColumn (Γ.fuse b (c + d + e))))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
        = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
            (FusionColumn (Γ.fuse a (b + c + d + e))) (τ • m) p :=
        leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e))) τ m p
      have hR : ∀ m' : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (FusionColumn (Γ.fuse b (c + d + e))),
          (mapEquivLeftGThreeCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
                (FusionColumn (Γ.fuse b (c + d + e))))
              (FusionColumn (Γ.fuse a (b + c + d + e))) m' p)
              : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
                  (FusionColumn (Γ.fuse a (b + c + d + e))))
            = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
                (FusionColumn (Γ.fuse a (b + c + d + e))) (gThreeCast K Γ b c d e m') p :=
        fun m' => RelTensor.map_mk (gThreeCast K Γ b c d e).toLinearMap
          (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d + e))
            →ₗ[K] FusionColumn (Γ.fuse a (b + c + d + e)))
          (gThreeCast_rightTotal K Γ b c d e) (fun _ _ => rfl) m' p
      have hRHS : (τ • mapEquivLeftGThreeCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e))) m p)
          : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
        = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) (τ • gThreeCast K Γ b c d e m) p := by
        rw [hR m]
        exact leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) τ (gThreeCast K Γ b c d e m) p
      rw [hL, hR (τ • m), gThreeCast_leftEquivDe, ← hRHS]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

end Wrapping

/-! ### `omegaV14'` -/

/-- **`omegaV14'`**: the re-ordered ("peel-before-regroup") spelling,
landing `V14 ≃ F_{d,e} ⊗ GQ4 K Γ a b c (d+e)` via `gV14StepFinal.symm`
(cancelling `E21M`'s own closing move, generally, no `mk`-shape needed),
then `gV14SplitC` (regroup, wrapped), then `gThreeCast` (the new device
closing `GBR Γ b c (d+e)`, wrapped via `mapEquivLeft` then wrapped
again), then `gq4TotalCast` (already-landed outer-bracket recast,
wrapped). Every stage is UNSIGNED. -/
noncomputable def omegaV14' : V14 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) :=
  (gV14Split K Γ a b c d e).trans
    ((gV14SplitCWrapped K Γ a b c d e).trans
      ((RelTensor.mapEquivRight K (mapEquivLeftGThreeCast K Γ a b c d e)
          (mapEquivLeftGThreeCast_leftEquiv K Γ a b c d e)).trans
        (RelTensor.mapEquivRight K (gq4TotalCast K Γ a b c d e)
          (gq4TotalCast_dSlot K Γ a b c d e))))

end GaugeChi

end Superfusion
