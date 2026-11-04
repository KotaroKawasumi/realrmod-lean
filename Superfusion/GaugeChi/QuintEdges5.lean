/-
Superfusion / GaugeChi / QuintEdges5

Milestone M13-2⁗′ of the abstract `(p, χ)` arc: **the cluster edge `E14M`**
(`V6 → V9`, the move `t_{a+b,c,d+e}`, owning faces `PAB`, `PDE`) — the
`E11M` mirror, but with a genuinely different toolkit requirement: `V6`'s
own reassociation does NOT expose `GBL(a+b,c,d+e)` through a chain of
plain associators (as `V3` did for `E11M`) — instead it needs the
**middle swap** (`Bimod.MiddleSwap.midSwap`, previously instantiated only
for `gq5Swap`, `Pentagon.lean`) to exchange the roles of the `F_{d,e}`
pairing column and the `GBL(a+b,c,d+e)` cluster.

**The route, in five stages** (`E14Mequiv`):

* `gV6AssocA` (plain `RelTensor.assoc`): `V6 ≃ F_{a,b} ⊗_{D_{a+b}}
  (F_{a+b,c} ⊗_{D_{a+b+c}} GBR(a+b+c,d,e))` — unfolding `GBL(a,b,c)`
  outward, exactly `gV3AssocA`'s own shape.
* `gV6Swap` (`Bimod.midSwap`, mirroring `gq5Swap`'s own instantiation):
  `F_{a+b,c} ⊗_{D_{a+b+c}} GBR(a+b+c,d,e) ≃ F_{d,e} ⊗_{D_{d+e}}
  GBL(a+b,c,d+e)`, Koszul-signed on generators — the mirror-image sign
  laws are `GBR.aslot_smul_mk_of_mem` (for `GBR(a+b+c,d,e)`'s own
  `D_{a+b+c}`-aslot) and `GBL.cslot_smul_mk_of_mem` (for
  `GBL(a+b,c,d+e)`'s own `D_{d+e}`-cslot) — the direct analogues of
  `gq5LawA`/`gq5LawB`. Wrapped, via the outer `F_{a,b}`-slot
  (`RelTensor.mapEquivRight`), using a FRESH nested-induction
  equivariance proof (`gV6Swap_aSlot`/`_leaf`, mirroring `gV3StepB`'s own
  discipline) — needing a NEW supercommutation fact
  `gblPslotRslotSuperComm` (`GBL(a+b,c,d+e)`'s own `P`-slot `(a+b)`
  versus its own `R`-slot `(d+e)`, via `leftActionEnd_anticommutes_
  midAlgHom`, mirroring `gbrBslotAslotSuperComm`'s proof shape with
  `GBL` in place of `GBR`).
* `gE14InnerStep` (`PentagonB.smapEquiv` of `gTCanon Γ (a+b) c (d+e)` at
  its own `(d+e)`-slot, via `gCanonHphi5`, mirroring `E15M`'s
  `gE15Step`): the `(d+e)`-slot move, landing `GBR(a+b,c,d+e)`.
* `gE14OuterStep` (`PentagonB.smapEquiv` of `gE14InnerStep` at the
  `(a+b)`-slot, hypothesis `gE14OuterHg` assembled from
  `smap_comm_midEnd` (`QuintEdges4.lean`, already general) +
  `gCanonHphi4`): the outer whisker of the inner move.
* `gE14FinalStep`: **REUSED VERBATIM** — `Pentagon.lean`'s own
  `gq4Close K Γ (a+b) c d e : GQ4r K Γ (a+b) c d e ≃ₗ[K] GQ4 K Γ (a+b) c d e`
  is *definitionally* the closing recast needed here: `GQ4r K Γ (a+b) c d e`
  unfolds to exactly `F_{d,e} ⊗_{D_{d+e}} GBR(a+b,c,d+e)` (`gE14OuterStep`'s
  own codomain) and `GQ4 K Γ (a+b) c d e` unfolds to exactly
  `V9Inner K Γ a b c d e` (both built from the SAME generic `GBR`-recast
  instance ledger) — no new recast content, wrapped by the same outer
  `F_{a,b}`-slot naturality package assembled for `gV6Swap`.

`E14M`/`E14M_bijective` assemble as `LinearEquiv`/`.bijective` projections.
-/
import Superfusion.GaugeChi.QuintEdges4
import Superfusion.Bimod.MiddleSwap

namespace Superfusion
namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v
variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

variable (a b c d e : G)

/-! ### `E14M` toolkit piece 1: `GBL`'s own `P`-slot vs `R`-slot
supercommutation (the `gbrBslotAslotSuperComm` mirror) -/

theorem gblPslotRslotSuperComm :
    SuperCommSMul (Γ.D (a + b)).grading (Γ.D (d + e)).grading (GBL Γ (a + b) c (d + e)) := by
  intro i k x τ hx hτ w
  show (leftActionEnd K (Γ.D ((a + b) + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (FusionColumn (Γ.fuse ((a + b) + c) (d + e))) x)
      ((midAlgHom (Γ.D ((a + b) + c)).grading (FusionColumn.grading (Γ.fuse (a + b) c))
          (Γ.D (d + e)).grading
          (FusionColumn.superCommSMul (Γ.fuse ((a + b) + c) (d + e))) τ) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((midAlgHom (Γ.D ((a + b) + c)).grading (FusionColumn.grading (Γ.fuse (a + b) c))
            (Γ.D (d + e)).grading
            (FusionColumn.superCommSMul (Γ.fuse ((a + b) + c) (d + e))) τ)
          ((leftActionEnd K (Γ.D ((a + b) + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse ((a + b) + c) (d + e))) x) w))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D ((a + b) + c)).grading
    (FusionColumn.grading (Γ.fuse (a + b) c)) (Γ.D (d + e)).grading
    (Γ.D (a + b)).grading
    (FusionColumn.superCommSMul (Γ.fuse ((a + b) + c) (d + e)))
    (⟨x, hx⟩ : (Γ.D (a + b)).grading i) (⟨τ, hτ⟩ : (Γ.D (d + e)).grading k)
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow, show k * i = i * k from mul_comm k i]
  rfl

noncomputable instance instModuleE14DEABSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))) :=
  Module.compHom _
    ((midAlgHom (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
        (gblPslotRslotSuperComm K Γ a b c d e))).toRingHom)

theorem instModuleE14DEABSlot_smul_def (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))) :
    τ • n
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
            (gblPslotRslotSuperComm K Γ a b c d e)) τ n := rfl

/-! ### `E14M` toolkit piece 2: the middle swap `gV6Swap` -/

private theorem gV6LawA :
    MidSignLaw K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b + c) (b := d) (c := e) hx hn p

private theorem gV6LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse (a + b) c)) := by
  intro l i z hz m hm p
  exact GBL.cslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c) (c := d + e) hz hm p

/-- **`gV6Swap`**: the middle swap exposing `GBL(a+b,c,d+e)` from `V6`'s
own reassociated structure `F_{a+b,c} ⊗_{D_{a+b+c}} GBR(a+b+c,d,e)`
(mirroring `gq5Swap`'s own instantiation of `Bimod.midSwap`). -/
noncomputable def gV6Swap :
    RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)) :=
  midSwap K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse (a + b) c))
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse (a + b) c)) (FusionColumn.grading (Γ.fuse d e))
    (gV6LawA K Γ a b c d e) (gV6LawB K Γ a b c d e)

/-- **The sign law of `gV6Swap` on homogeneous generators** (term-mode:
`midSwapMap_mk_of_mem` unifies directly against the `GBR.mk`-headed
statement by elaboration-time defeq, sidestepping the `rw`-level
`GBR`-registered/raw-`RelTensor` instance mismatch — the same discipline
`gV3StepB_leaf`'s `keyAssoc1`/`keyAssoc2` use for `RelTensor.assoc_mk`). -/
theorem gV6Swap_mk_of_mem {i j : ZMod 2} {u : FusionColumn (Γ.fuse (a + b) c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse (a + b) c) i) {v : FusionColumn (Γ.fuse d e)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j) (p : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    gV6Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))
            v (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p) :=
  midSwapMap_mk_of_mem K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier
    (FusionColumn (Γ.fuse (a + b) c)) (FusionColumn (Γ.fuse d e))
    (FusionColumn (Γ.fuse (a + b + c) (d + e))) (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse (a + b) c)) (FusionColumn.grading (Γ.fuse d e))
    (gV6LawA K Γ a b c d e) (gV6LawB K Γ a b c d e) hv hu p

/-! ### `E14M` toolkit piece 3: the outer `(a+b)`-slot on `gV6Swap`'s
domain, and `gV6Swap`'s own `(a+b)`-equivariance -/

/-- The `(a+b)`-slot on `gV6Swap`'s domain: reaches through the FIRST
factor `F_{a+b,c}`'s own natural `P₁`-slot, `leftActionEnd`, UNSIGNED at
the outer level (the sign, when it appears, comes from `F_{a+b,c}`'s own
grading shift, not from crossing the outer tensor). -/
noncomputable instance instModuleE14ABSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e)) :=
  Module.compHom _
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (GBR Γ (a + b + c) d e) (B := (Γ.D (a + b)).carrier)).toRingHom)

theorem instModuleE14ABSlot_smul_def (x : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (GBR Γ (a + b + c) d e)) :
    x • n
      = leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) x n := rfl

theorem gV6Swap_leaf {i j k : ZMod 2} {u : FusionColumn (Γ.fuse (a + b) c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse (a + b) c) i)
    {v : FusionColumn (Γ.fuse d e)} (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j)
    (p : FusionColumn (Γ.fuse (a + b + c) (d + e)))
    {x : (Γ.D (a + b)).carrier} (hx : x ∈ (Γ.D (a + b)).grading k) :
    gV6Swap K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = x • gV6Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)) := by
  have step1 : x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p) :=
    leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (GBR Γ (a + b + c) d e) x u (GBR.mk Γ (a + b + c) d e v p)
  have hxu : x • u ∈ FusionColumn.grading (Γ.fuse (a + b) c) (k + i) := by
    have hmem := SetLike.GradedSMul.smul_mem (A := (Γ.D (a + b)).grading)
      (B := FusionColumn.grading (Γ.fuse (a + b) c)) hx hu
    rwa [vadd_eq_add] at hmem
  let vGen1 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GBL Γ (a + b) c (d + e)) :=
    RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)) v
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) (x • u) p)
  let vGen2 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GBL Γ (a + b) c (d + e)) :=
    RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)) v
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)
  have keyL : gV6Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * (k + i)) : ℤˣ) : ℤ) • vGen1 :=
    gV6Swap_mk_of_mem K Γ a b c d e hxu hv p
  have keyR0 : gV6Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * i) : ℤˣ) : ℤ) • vGen2 :=
    gV6Swap_mk_of_mem K Γ a b c d e hu hv p
  have keyTarget : x • vGen2 = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 := by
    have step := midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
        (gblPslotRslotSuperComm K Γ a b c d e)) hv hx
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)
    have hleft : (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p : GBL Γ (a + b) c (d + e)))
        = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) (x • u) p :=
      leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) x u p
    calc x • vGen2
        = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
              (gblPslotRslotSuperComm K Γ a b c d e)) x vGen2 := rfl
      _ = ((sgn (k * j) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBL Γ (a + b) c (d + e)) v
              (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)) := step
      _ = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 :=
          congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·)
            (congrArg (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBL Γ (a + b) c (d + e)) v) hleft)
  have hcomm : x • (((sgn (j * i) : ℤˣ) : ℤ) • vGen2)
      = ((sgn (j * i) : ℤˣ) : ℤ) • (x • vGen2) := by
    rw [instModuleE14DEABSlot_smul_def, instModuleE14DEABSlot_smul_def, map_zsmul]
  calc gV6Swap K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = gV6Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p)) := by rw [step1]
    _ = ((sgn (j * (k + i)) : ℤˣ) : ℤ) • vGen1 := keyL
    _ = ((sgn (j * k + j * i) : ℤˣ) : ℤ) • vGen1 := by rw [mul_add]
    _ = ((sgn (k * j + j * i) : ℤˣ) : ℤ) • vGen1 := by rw [show k * j = j * k from mul_comm k j]
    _ = ((sgn (k * j) : ℤˣ) * (sgn (j * i) : ℤˣ) : ℤ) • vGen1 := by rw [← Units.val_mul, ← sgn_add]
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • (((sgn (j * i) : ℤˣ) : ℤ) • vGen1) := by rw [smul_smul]
    _ = ((sgn (j * i) : ℤˣ) : ℤ) • (((sgn (k * j) : ℤˣ) : ℤ) • vGen1) := smul_comm _ _ _
    _ = ((sgn (j * i) : ℤˣ) : ℤ) • (x • vGen2) := by rw [← keyTarget]
    _ = x • (((sgn (j * i) : ℤˣ) : ℤ) • vGen2) := hcomm.symm
    _ = x • gV6Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)) := by rw [keyR0]

/-- **`gV6Swap`'s `(a+b)`-equivariance, for homogeneous `x`** (the nested
`RelTensor.induction_on`/`DirectSum.Decomposition.inductionOn` descent to
the leaf `gV6Swap_leaf`, mirroring `gE11GBRAssoc_aSlot`'s discipline). -/
theorem gV6Swap_aSlot {k : ZMod 2} {x : (Γ.D (a + b)).carrier}
    (hx : x ∈ (Γ.D (a + b)).grading k)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (GBR Γ (a + b + c) d e)) :
    gV6Swap K Γ a b c d e (x • n) = x • gV6Swap K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | mk u v =>
      induction u using DirectSum.Decomposition.inductionOn
          (FusionColumn.grading (Γ.fuse (a + b) c)) with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse (a + b) c)) v
              = (0 : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e)) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e))) v).trans
              (LinearMap.zero_apply _)
          calc gV6Swap K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse (a + b) c)) v)
              = gV6Swap K Γ a b c d e (x • (0 : RelTensor K (Γ.D (a + b + c)).carrier
                  (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e))) :=
                congrArg (fun z => gV6Swap K Γ a b c d e (x • z)) e0
            _ = gV6Swap K Γ a b c d e 0 := congrArg (gV6Swap K Γ a b c d e) (smul_zero x)
            _ = 0 := map_zero _
            _ = x • (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBL Γ (a + b) c (d + e))) := (smul_zero x).symm
            _ = x • gV6Swap K Γ a b c d e 0 := congrArg (fun z => x • z) (map_zero _).symm
            _ = x • gV6Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse (a + b) c)) v) :=
                congrArg (fun z => x • gV6Swap K Γ a b c d e z) e0.symm
      | add u u' hu hu' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)) u u' v
          calc gV6Swap K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e) (u + u') v)
              = gV6Swap K Γ a b c d e
                  (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) u v
                    + RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) u' v)) :=
                congrArg (fun z => gV6Swap K Γ a b c d e (x • z)) e1
            _ = gV6Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u v
                  + x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u' v) :=
                congrArg (gV6Swap K Γ a b c d e) (smul_add x _ _)
            _ = gV6Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u v)
                + gV6Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u' v) := map_add _ _ _
            _ = x • gV6Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u v)
                + x • gV6Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) u' v) := congrArg₂ (· + ·) hu hu'
            _ = x • (gV6Swap K Γ a b c d e
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) u v)
                  + gV6Swap K Γ a b c d e
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) u' v)) := (smul_add x _ _).symm
            _ = x • gV6Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) (u + u') v) :=
                congrArg (fun z => x • gV6Swap K Γ a b c d e z) e1.symm
      | homogeneous xu =>
          induction v using RelTensor.induction_on with
          | zero =>
              have e0 : (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                    (0 : GBR Γ (a + b + c) d e) : _)
                  = (0 : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e)) :=
                map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)))
              calc gV6Swap K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                      (0 : GBR Γ (a + b + c) d e))
                  = gV6Swap K Γ a b c d e (x • (0 : RelTensor K (Γ.D (a + b + c)).carrier
                      (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e))) :=
                    congrArg (fun z => gV6Swap K Γ a b c d e (x • z)) e0
                _ = 0 := by rw [smul_zero, map_zero]
                _ = x • gV6Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                        (0 : GBR Γ (a + b + c) d e)) := by
                    rw [e0, map_zero, smul_zero]
          | add v v' hv hv' =>
              have e1 := map_add (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                (xu : FusionColumn (Γ.fuse (a + b) c))) v v'
              calc gV6Swap K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                      (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) (v + v'))
                  = gV6Swap K Γ a b c d e
                      (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse (a + b) c)) v
                        + RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v')) :=
                    congrArg (fun z => gV6Swap K Γ a b c d e (x • z)) e1
                _ = gV6Swap K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v)
                    + gV6Swap K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v') := by
                    rw [smul_add, map_add]
                _ = x • gV6Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v)
                    + x • gV6Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v') :=
                    congrArg₂ (· + ·) hv hv'
                _ = x • (gV6Swap K Γ a b c d e
                        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v)
                      + gV6Swap K Γ a b c d e
                        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) v')) :=
                    (smul_add x _ _).symm
                _ = x • gV6Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c)) (v + v')) :=
                    congrArg (fun z => x • gV6Swap K Γ a b c d e z) e1.symm
          | mk v p =>
              induction v using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse d e)) with
              | zero =>
                  have e0 : (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p
                        : GBR Γ (a + b + c) d e)
                      = (0 : GBR Γ (a + b + c) d e) :=
                    (LinearMap.congr_fun (map_zero (GBR.mk Γ (a + b + c) d e)) p).trans
                      (LinearMap.zero_apply _)
                  calc gV6Swap K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse (a + b) c))
                          (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p))
                      = gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) (0 : GBR Γ (a + b + c) d e)) :=
                        congrArg (fun z => gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) z)) e0
                    _ = x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                            (0 : GBR Γ (a + b + c) d e)) := by
                        have e0' : (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse (a + b) c)) (0 : GBR Γ (a + b + c) d e) : _)
                            = (0 : RelTensor K (Γ.D (a + b + c)).carrier
                                (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)) :=
                          map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)))
                        rw [e0']
                        simp
                    _ = x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                            (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p)) :=
                        congrArg (fun z => x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) z)) e0.symm
              | add v v' hv hv' =>
                  have e1 := LinearMap.map_add₂ (GBR.mk Γ (a + b + c) d e) v v' p
                  calc gV6Swap K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse (a + b) c))
                          (GBR.mk Γ (a + b + c) d e (v + v') p))
                      = gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c))
                            (GBR.mk Γ (a + b + c) d e v p + GBR.mk Γ (a + b + c) d e v' p)) :=
                        congrArg (fun z => gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) z)) e1
                    _ = gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) (GBR.mk Γ (a + b + c) d e v p))
                        + gV6Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) (GBR.mk Γ (a + b + c) d e v' p)) := by
                        rw [map_add, smul_add, map_add]
                    _ = x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                            (GBR.mk Γ (a + b + c) d e v p))
                        + x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                            (GBR.mk Γ (a + b + c) d e v' p)) := congrArg₂ (· + ·) hv hv'
                    _ = x • (gV6Swap K Γ a b c d e
                            (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse (a + b) c)) (GBR.mk Γ (a + b + c) d e v p))
                          + gV6Swap K Γ a b c d e
                            (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse (a + b) c)) (GBR.mk Γ (a + b + c) d e v' p))) :=
                        (smul_add x _ _).symm
                    _ = x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse (a + b) c))
                            (GBR.mk Γ (a + b + c) d e (v + v') p)) :=
                        congrArg (fun z => x • gV6Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse (a + b) c)) z)) e1.symm
              | homogeneous xv =>
                  exact gV6Swap_leaf K Γ a b c d e xu.2 xv.2 p hx

/-- **`gV6Swap`'s `(a+b)`-equivariance, generalized to all `x`** (linearity
extension via `x`'s own `DirectSum.Decomposition.inductionOn`, mirroring
`gE11GBRAssoc_aSlot_general`). -/
theorem gV6Swap_aSlot_general (x : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
      (GBR Γ (a + b + c) d e)) :
    gV6Swap K Γ a b c d e (x • n) = x • gV6Swap K Γ a b c d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (a + b)).grading with
  | zero =>
      calc gV6Swap K Γ a b c d e ((0 : (Γ.D (a + b)).carrier) • n)
          = gV6Swap K Γ a b c d e (0 : RelTensor K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (a + b)).carrier) • gV6Swap K Γ a b c d e n := (zero_smul _ _).symm
  | add x x' hx hx' =>
      calc gV6Swap K Γ a b c d e ((x + x') • n)
          = gV6Swap K Γ a b c d e (x • n + x' • n) := by rw [add_smul]
        _ = gV6Swap K Γ a b c d e (x • n) + gV6Swap K Γ a b c d e (x' • n) := map_add _ _ _
        _ = x • gV6Swap K Γ a b c d e n + x' • gV6Swap K Γ a b c d e n :=
            congrArg₂ (· + ·) hx hx'
        _ = (x + x') • gV6Swap K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xx =>
      exact gV6Swap_aSlot K Γ a b c d e xx.2 n

/-! ### `E14M` toolkit piece 4: the `(d+e)`-slot move (`gE14InnerStep`) and
its outer `(a+b)`-wrap -/

/-- `GBR`'s own `C`-slot (`d+e`, natural via the first factor) vs `A`-slot
(`a+b`, aslot via the second factor) supercommutation — the `gbrBslotAslotSuperComm`
mirror at `GBR Γ (a+b) c (d+e)`, needed for `GQ4r`'s own `(a+b)`-slot
(`instModuleE14GBRSlot`) and the `gE14OuterHg` square. -/
theorem gbrCslotAslotSuperComm :
    SuperCommSMul (Γ.D (d + e)).grading (Γ.D (a + b)).grading (GBR Γ (a + b) c (d + e)) := by
  intro i k y τ hy hτ w
  show (leftActionEnd K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
      (FusionColumn (Γ.fuse (a + b) (c + (d + e)))) y)
      ((midAlgHom (Γ.D (c + (d + e))).grading (FusionColumn.grading (Γ.fuse c (d + e)))
          (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + (d + e))).grading
            (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + (d + e))))) τ) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((midAlgHom (Γ.D (c + (d + e))).grading (FusionColumn.grading (Γ.fuse c (d + e)))
            (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + (d + e))).grading
              (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + (d + e))))) τ)
          ((leftActionEnd K (Γ.D (c + (d + e))).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse (a + b) (c + (d + e)))) y) w))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (c + (d + e))).grading
    (FusionColumn.grading (Γ.fuse c (d + e))) (Γ.D (a + b)).grading
    (Γ.D (d + e)).grading
    (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + (d + e))).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + (d + e)))))
    (⟨y, hy⟩ : (Γ.D (d + e)).grading i) (⟨τ, hτ⟩ : (Γ.D (a + b)).grading k)
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow, show k * i = i * k from mul_comm k i]
  rfl

noncomputable instance instModuleE14GBRSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :=
  Module.compHom _
    ((midAlgHom (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
      (gbrCslotAslotSuperComm K Γ a b c d e)).toRingHom)

theorem instModuleE14GBRSlot_smul_def (x : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :
    x • n
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
          (gbrCslotAslotSuperComm K Γ a b c d e) x n := rfl

/-- The `(d+e)`-slot amplification of `gTCanon Γ (a+b) c (d+e)`, landing
`GBR(a+b,c,d+e)` (mirrors `gE15Step`, keyed to `gCanonHphi5`'s `(z+w)`-slot
conjunct). -/
noncomputable def gE14InnerStep :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)) :=
  PentagonB.smapEquiv K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
    (gTCanon K Γ (a + b) c (d + e)) (gParity K Γ (a + b) c (d + e)) (gCanonHphi5 K Γ (a + b) c d e)

theorem gE14OuterHg :
    ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄, x ∈ (Γ.D (a + b)).grading i →
      ∀ n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)),
        gE14InnerStep K Γ a b c d e (x • n)
          = ((sgn (gParity K Γ (a + b) c (d + e) * i) : ℤˣ) : ℤ) •
              (x • gE14InnerStep K Γ a b c d e n) := by
  intro i x hx n
  have h := LinearMap.congr_fun
    (smap_comm_midEnd K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
        (gblPslotRslotSuperComm K Γ a b c d e))
      (gbrCslotAslotSuperComm K Γ a b c d e)
      (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
      (gCanonHphi4 K Γ a b c (d + e)) hx) n
  rw [instModuleE14DEABSlot_smul_def, instModuleE14GBRSlot_smul_def]
  show (smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gParity K Γ (a + b) c (d + e))
        (gCanonHphi5 K Γ (a + b) c d e))
      (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (d + e)).grading
          (gblPslotRslotSuperComm K Γ a b c d e)) x n)
    = ((sgn (gParity K Γ (a + b) c (d + e) * i) : ℤˣ) : ℤ) •
        midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
          (gbrCslotAslotSuperComm K Γ a b c d e) x
          ((smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
              (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gParity K Γ (a + b) c (d + e))
              (gCanonHphi5 K Γ (a + b) c d e)) n)
  exact h

/-- The outer `(a+b)`-slot amplification of `gE14InnerStep` (mirrors
`gE11OuterStep`). -/
noncomputable def gE14OuterStep :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :=
  PentagonB.smapEquiv K (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (gE14InnerStep K Γ a b c d e) (gParity K Γ (a + b) c (d + e)) (gE14OuterHg K Γ a b c d e)

/-! ### `E14M` toolkit piece 5: the closing step, reusing `Pentagon.lean`'s
`gq4Close` verbatim -/

/-- **`gE14FinalStep`**: `Pentagon.lean`'s own `gq4Close`, instantiated at
`(a+b,c,d,e)` — `GQ4r K Γ (a+b) c d e` unfolds to exactly
`F_{d,e} ⊗_{D_{d+e}} GBR(a+b,c,d+e)` (`gE14OuterStep`'s own codomain's
inner factor) and `GQ4 K Γ (a+b) c d e` unfolds to exactly
`V9Inner K Γ a b c d e` (both built from the SAME generic `GBR`-recast
instance ledger as `Quint.lean`'s `V9Inner`) — no new recast content. -/
noncomputable def gE14FinalStep :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
      ≃ₗ[K] V9Inner K Γ a b c d e :=
  gq4Close K Γ (a + b) c d e

/-- **`fusionColumnCast`'s untouched first-index (fixed) slot commutes
trivially** (the `subst`-`rfl` mirror of `gColumnCastFst_dslot`, one index
over). -/
theorem fusionColumnCast_aslot {x y : G} (h : x = y) (p : G) (τ : (Γ.D p).carrier)
    (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p h (τ • w) = τ • fusionColumnCast K Γ p h w := by
  subst h
  rfl

/-- **The leaf computation of `gE14FinalStep`'s `(a+b)`-equivariance**:
`gq4Close_mk` (sign-free) combined with `GBR.aslot_smul_mk_of_mem`'s and
`instModuleE14GBRSlot`/`instModuleV9InnerASlot`'s own Koszul signs, both
landing the SAME combined degree `k * (j + i)` (`GBR.mk_mem_grading`). -/
theorem gE14FinalStep_leaf {i j k : ZMod 2} {v : FusionColumn (Γ.fuse d e)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j)
    {u : FusionColumn (Γ.fuse c (d + e))} (hu : u ∈ FusionColumn.grading (Γ.fuse c (d + e)) i)
    (w : FusionColumn (Γ.fuse (a + b) (c + (d + e))))
    {x : (Γ.D (a + b)).carrier} (hx : x ∈ (Γ.D (a + b)).grading k) :
    gE14FinalStep K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w))
      = x • gE14FinalStep K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w)) := by
  have step1 : x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w)
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.mk K (Γ.D (d + e)).carrier
          (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)) v
          (x • GBR.mk Γ (a + b) c (d + e) u w) :=
    midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (a + b)).grading
      (gbrCslotAslotSuperComm K Γ a b c d e) hv hx _
  have step2 : x • GBR.mk Γ (a + b) c (d + e) u w
      = ((sgn (k * i) : ℤˣ) : ℤ) • GBR.mk Γ (a + b) c (d + e) u (x • w) :=
    GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c) (c := d + e) hx hu w
  let vTarget1 : V9Inner K Γ a b c d e :=
    RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBR.mk Γ c d e v u)
      (fusionColumnCast K Γ (a + b) (add_assoc c d e).symm (x • w))
  let vTarget2 : V9Inner K Γ a b c d e :=
    RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBR.mk Γ c d e v u)
      (fusionColumnCast K Γ (a + b) (add_assoc c d e).symm w)
  have keyClose : gE14FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u (x • w)))
      = vTarget1 :=
    gq4Close_mk K Γ (a + b) c d e v u (x • w)
  have keyClose2 : gE14FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w))
      = vTarget2 :=
    gq4Close_mk K Γ (a + b) c d e v u w
  have hvu : GBR.mk Γ c d e v u ∈ GBR.grading Γ c d e (j + i) :=
    GBR.mk_mem_grading Γ c d e hv hu
  have keyTarget : x • vTarget2 = ((sgn (k * (j + i)) : ℤˣ) : ℤ) • vTarget1 := by
    have hshow : x • vTarget2
        = midEnd (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
              (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) x vTarget2 := rfl
    rw [hshow]
    show midEnd (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) x
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBR.mk Γ c d e v u)
          (fusionColumnCast K Γ (a + b) (add_assoc c d e).symm w))
      = ((sgn (k * (j + i)) : ℤˣ) : ℤ) • vTarget1
    rw [midEnd_mk_of_mem (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) hvu hx,
      ← fusionColumnCast_aslot]
    rfl
  have keyMid : x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w)
      = (((sgn (k * j) : ℤˣ) : ℤ) * ((sgn (k * i) : ℤˣ) : ℤ)) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u (x • w)) := by
    rw [step1, step2, map_zsmul, smul_smul]
  calc gE14FinalStep K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w))
      = gE14FinalStep K Γ a b c d e
          (((sgn (k * (j + i)) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u (x • w))) := by
        rw [keyMid, ← Units.val_mul, ← sgn_add, ← mul_add]
    _ = ((sgn (k * (j + i)) : ℤˣ) : ℤ) •
          gE14FinalStep K Γ a b c d e
            (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u (x • w))) := map_zsmul _ _ _
    _ = ((sgn (k * (j + i)) : ℤˣ) : ℤ) • vTarget1 := congrArg (((sgn (k * (j + i)) : ℤˣ) : ℤ) • ·) keyClose
    _ = x • vTarget2 := keyTarget.symm
    _ = x • gE14FinalStep K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) v (GBR.mk Γ (a + b) c (d + e) u w)) :=
        congrArg (x • ·) keyClose2.symm

/-- **`gE14FinalStep`'s `(a+b)`-equivariance, for homogeneous `x`** (the
nested induction descent to `gE14FinalStep_leaf`, mirroring `gV6Swap_aSlot`'s
discipline). -/
theorem gE14FinalStep_aSlot {k : ZMod 2} {x : (Γ.D (a + b)).carrier}
    (hx : x ∈ (Γ.D (a + b)).grading k)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :
    gE14FinalStep K Γ a b c d e (x • n) = x • gE14FinalStep K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | mk v n' =>
      induction v using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse d e))
          with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                (GBR Γ (a + b) c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n'
              = (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ (a + b) c (d + e))) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))) n').trans
              (LinearMap.zero_apply _)
          calc gE14FinalStep K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ (a + b) c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n')
              = gE14FinalStep K Γ a b c d e (x • (0 : RelTensor K (Γ.D (d + e)).carrier
                  (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))) :=
                congrArg (fun z => gE14FinalStep K Γ a b c d e (x • z)) e0
            _ = gE14FinalStep K Γ a b c d e 0 := congrArg (gE14FinalStep K Γ a b c d e) (smul_zero x)
            _ = 0 := map_zero _
            _ = x • (0 : V9Inner K Γ a b c d e) := (smul_zero x).symm
            _ = x • gE14FinalStep K Γ a b c d e 0 := congrArg (fun z => x • z) (map_zero _).symm
            _ = x • gE14FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n') :=
                congrArg (fun z => x • gE14FinalStep K Γ a b c d e z) e0.symm
      | add v v' hv hv' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (d + e)).carrier
            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) v v' n'
          calc gE14FinalStep K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ (a + b) c (d + e)) (v + v') n')
              = gE14FinalStep K Γ a b c d e
                  (x • (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) v n'
                    + RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) v' n')) :=
                congrArg (fun z => gE14FinalStep K Γ a b c d e (x • z)) e1
            _ = gE14FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v n'
                  + x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v' n') :=
                congrArg (gE14FinalStep K Γ a b c d e) (smul_add x _ _)
            _ = gE14FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v n')
                + gE14FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v' n') := map_add _ _ _
            _ = x • gE14FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v n')
                + x • gE14FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) v' n') := congrArg₂ (· + ·) hv hv'
            _ = x • (gE14FinalStep K Γ a b c d e
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) v n')
                  + gE14FinalStep K Γ a b c d e
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) v' n')) := (smul_add x _ _).symm
            _ = x • gE14FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) (v + v') n') :=
                congrArg (x • ·) ((map_add (gE14FinalStep K Γ a b c d e) _ _).symm.trans
                  (congrArg (gE14FinalStep K Γ a b c d e) e1.symm))
      | homogeneous xv =>
          induction n' using RelTensor.induction_on with
          | zero =>
              have e0 : (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                    (0 : GBR Γ (a + b) c (d + e)) : _)
                  = (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e))) :=
                map_zero (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)))
              calc gE14FinalStep K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                      (0 : GBR Γ (a + b) c (d + e)))
                  = gE14FinalStep K Γ a b c d e (x • (0 : RelTensor K (Γ.D (d + e)).carrier
                      (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))) :=
                    congrArg (fun z => gE14FinalStep K Γ a b c d e (x • z)) e0
                _ = 0 := by rw [smul_zero, map_zero]
                _ = x • gE14FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                        (0 : GBR Γ (a + b) c (d + e))) := by
                    rw [e0, map_zero, smul_zero]
          | add n' n'' hn' hn'' =>
              have e1 := map_add (RelTensor.mk K (Γ.D (d + e)).carrier
                (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                (xv : FusionColumn (Γ.fuse d e))) n' n''
              calc gE14FinalStep K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) (n' + n''))
                  = gE14FinalStep K Γ a b c d e
                      (x • (RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                          (xv : FusionColumn (Γ.fuse d e)) n'
                        + RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'')) :=
                    congrArg (fun z => gE14FinalStep K Γ a b c d e (x • z)) e1
                _ = gE14FinalStep K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                    + gE14FinalStep K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'') := by
                    rw [smul_add, map_add]
                _ = x • gE14FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                    + x • gE14FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'') :=
                    congrArg₂ (· + ·) hn' hn''
                _ = x • (gE14FinalStep K Γ a b c d e
                        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                      + gE14FinalStep K Γ a b c d e
                        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'')) :=
                    (smul_add x _ _).symm
                _ = x • gE14FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e)) (n' + n'')) :=
                    congrArg (x • ·) ((map_add (gE14FinalStep K Γ a b c d e) _ _).symm.trans
                      (congrArg (gE14FinalStep K Γ a b c d e) e1.symm))
          | mk u w =>
              induction u using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse c (d + e))) with
              | zero =>
                  have e0 : (GBR.mk Γ (a + b) c (d + e) (0 : FusionColumn (Γ.fuse c (d + e))) w
                        : GBR Γ (a + b) c (d + e))
                      = (0 : GBR Γ (a + b) c (d + e)) :=
                    (LinearMap.congr_fun (map_zero (GBR.mk Γ (a + b) c (d + e))) w).trans
                      (LinearMap.zero_apply _)
                  calc gE14FinalStep K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                          (xv : FusionColumn (Γ.fuse d e))
                          (GBR.mk Γ (a + b) c (d + e) (0 : FusionColumn (Γ.fuse c (d + e))) w))
                      = gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (0 : GBR Γ (a + b) c (d + e))) :=
                        congrArg (fun z => gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e0
                    _ = x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (0 : GBR Γ (a + b) c (d + e))) := by
                        have e0' : (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (0 : GBR Γ (a + b) c (d + e)) : _)
                            = (0 : RelTensor K (Γ.D (d + e)).carrier
                                (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :=
                          map_zero (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)))
                        rw [e0']
                        simp
                    _ = x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ (a + b) c (d + e) (0 : FusionColumn (Γ.fuse c (d + e))) w)) :=
                        congrArg (fun z => x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e0.symm
              | add u u' hu hu' =>
                  have e1 := LinearMap.map_add₂ (GBR.mk Γ (a + b) c (d + e)) u u' w
                  calc gE14FinalStep K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                          (xv : FusionColumn (Γ.fuse d e))
                          (GBR.mk Γ (a + b) c (d + e) (u + u') w))
                      = gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ (a + b) c (d + e) u w
                              + GBR.mk Γ (a + b) c (d + e) u' w)) :=
                        congrArg (fun z => gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e1
                    _ = gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ (a + b) c (d + e) u w))
                        + gE14FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ (a + b) c (d + e) u' w)) := by
                        rw [map_add, smul_add, map_add]
                    _ = x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ (a + b) c (d + e) u w))
                        + x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ (a + b) c (d + e) u' w)) := congrArg₂ (· + ·) hu hu'
                    _ = x • (gE14FinalStep K Γ a b c d e
                            (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ (a + b) c (d + e) u w))
                          + gE14FinalStep K Γ a b c d e
                            (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ (a + b) c (d + e) u' w))) :=
                        (smul_add x _ _).symm
                    _ = x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ (a + b) c (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ (a + b) c (d + e) (u + u') w)) :=
                        congrArg (fun z => x • gE14FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e1.symm
              | homogeneous xu =>
                  exact gE14FinalStep_leaf K Γ a b c d e xv.2 xu.2 w hx

/-- **`gE14FinalStep`'s `(a+b)`-equivariance, generalized to all `x`**. -/
theorem gE14FinalStep_aSlot_general (x : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) :
    gE14FinalStep K Γ a b c d e (x • n) = x • gE14FinalStep K Γ a b c d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (a + b)).grading with
  | zero =>
      calc gE14FinalStep K Γ a b c d e ((0 : (Γ.D (a + b)).carrier) • n)
          = gE14FinalStep K Γ a b c d e (0 : RelTensor K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (a + b)).carrier) • gE14FinalStep K Γ a b c d e n := (zero_smul _ _).symm
  | add x x' hx hx' =>
      calc gE14FinalStep K Γ a b c d e ((x + x') • n)
          = gE14FinalStep K Γ a b c d e (x • n + x' • n) := by rw [add_smul]
        _ = gE14FinalStep K Γ a b c d e (x • n) + gE14FinalStep K Γ a b c d e (x' • n) := map_add _ _ _
        _ = x • gE14FinalStep K Γ a b c d e n + x' • gE14FinalStep K Γ a b c d e n :=
            congrArg₂ (· + ·) hx hx'
        _ = (x + x') • gE14FinalStep K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xx =>
      exact gE14FinalStep_aSlot K Γ a b c d e xx.2 n

/-! ### `E14M`: the assembly -/

/-- **`gV6AssocA`**: `V6`'s own re-association, exposing `F_{a+b,c} ⊗
GBR(a+b+c,d,e)` under the `F_{a,b}`-whisker — a single, cast-free
`RelTensor.assoc` (mirrors `gV3AssocA`). -/
noncomputable def gV6AssocA : V6 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e)) :=
  RelTensor.assoc K (Γ.D (a + b)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)

/-- `gV6Swap`, wrapped by the outer `F_{a,b}`-slot. -/
noncomputable def gV6SwapWrapped :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e))
      ≃ₗ[K]
      RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ (a + b) c (d + e))) :=
  RelTensor.mapEquivRight K (gV6Swap K Γ a b c d e) (gV6Swap_aSlot_general K Γ a b c d e)

/-- `gE14FinalStep`, wrapped by the outer `F_{a,b}`-slot, landing `V9`
exactly. -/
noncomputable def gE14FinalStepWrapped :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ (a + b) c (d + e)))
      ≃ₗ[K] V9 K Γ a b c d e :=
  RelTensor.mapEquivRight K (gE14FinalStep K Γ a b c d e) (gE14FinalStep_aSlot_general K Γ a b c d e)

/-- **`E14M`, as a `LinearEquiv`**: `V6 → V9`, the move `t_{a+b,c,d+e}` —
`gV6AssocA` then the middle-swap `gV6SwapWrapped` (exposing `GBL(a+b,c,d+e)`)
then the signed `(d+e)`/`(a+b)`-nested amplification of `gTCanon Γ (a+b) c
(d+e)` (`gE14OuterStep`) then the closing `gE14FinalStepWrapped` (reusing
`Pentagon.lean`'s `gq4Close`). -/
noncomputable def E14Mequiv : V6 K Γ a b c d e ≃ₗ[K] V9 K Γ a b c d e :=
  (gV6AssocA K Γ a b c d e).trans
    ((gV6SwapWrapped K Γ a b c d e).trans
      ((gE14OuterStep K Γ a b c d e).trans (gE14FinalStepWrapped K Γ a b c d e)))

/-- **Edge 14** `E14M : V6 → V9`, `t_{a+b,c,d+e}` (owning faces `PAB`,
`PDE`). -/
noncomputable def E14M : V6 K Γ a b c d e →ₗ[K] V9 K Γ a b c d e :=
  (E14Mequiv K Γ a b c d e).toLinearMap

theorem E14M_bijective : Function.Bijective (E14M K Γ a b c d e) :=
  (E14Mequiv K Γ a b c d e).bijective

end GaugeChi
end Superfusion
