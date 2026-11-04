/-
Superfusion / GaugeChi / QuintEdges8

Milestone M13-2-8 of the abstract `(p, χ)` arc: **the final two quintuple
edges `E19M`, `E21M`**, closing the 21-edge scaffold (`QuintEdges..
QuintEdges7` land the other 19).

**`E19M` (`V8 → V13`, `t_{a,b,(c+d)+e}`, faces `PCD`/`S3`)**: `V8 = (ab)((cd)e)
= F_{a,b} ⊗_{D_{a+b}} V8Inner` (`V8Inner = GBL(c,d,e) ⊗_{D_{c+d+e}} F_{a+b,c+d+e}`,
`Quint.lean`'s M13-1′ fix). Route (`E19Mequiv`, six composed equivalences):

* `gV8Swap` (`Bimod.midSwap`, mirroring `gV6Swap`/`gV7Swap`'s own
  instantiation, but with NO preceding `assoc` peel — `V8` is *already*
  `F_{a,b} ⊗_{D_{a+b}} (GBL(c,d,e) ⊗_{D_{c+d+e}} F_{a+b,c+d+e})`, the exact
  `midSwap` shape `M ⊗[A] (N ⊗[B] P)` with `M := F_{a,b}`, `N := GBL(c,d,e)`,
  `P := F_{a+b,c+d+e}`): both `MidSignLaw` witnesses are free — `gV8LawA`
  mirrors `V8Inner`'s own `(a+b)`-slot construction (`Quint.lean`'s
  `instModuleV8InnerASlot`/`V8InnerASlot_smul_def`, via `midEnd_mk_of_mem`),
  `gV8LawB` is `GBL.cslot_smul_mk_of_mem` literally. Lands
  `GBL(c,d,e) ⊗_{D_{c+d+e}} GBL(a,b,c+d+e)` (the second factor `F_{a,b} ⊗
  F_{a+b,c+d+e}` unfolds definitionally to `GBL Γ a b (c+d+e)`, no cast:
  `(a+b)` is literal).
* `gE19InnerStep` (`PentagonB.smapEquiv` of `gTCanon Γ a b (c+d+e)` at its
  own `(c+d+e)`-slot, via `gCanonHphi5 K Γ a b (c+d) e` — reused verbatim,
  NO cast: `(c+d)+e = c+d+e` syntactically): lands
  `GBL(c,d,e) ⊗_{D_{c+d+e}} GBR(a,b,c+d+e)`.
* **`gq3rCast`, THE NEW DEVICE** (a GBR-mirror of `ChiCanon.lean`'s
  `gq2rCast`, built the same way — two `RelTensor.lift` legs glued by
  `LinearEquiv.ofLinear`, identity on the shared first factor `F_{b,c+d+e}`,
  `fusionColumnCast` (Pentagon.lean, casting the SECOND index, first fixed)
  on the second, via the generic `add_assoc_four b c d e` proof term from
  `Quint.lean` and the ALREADY-PUBLIC recast instance
  `instModuleFusionColumnRecast4 K Γ b c d e`): recasts `GBR Γ a b (c+d+e)`
  (natural coefficient `D_{b+(c+d+e)}`) to the LEFT-total raw pair
  `F_{b,c+d+e} ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e}`. The one slot-compatibility law
  needed by the closing (`gq3rCast_bSlot`, the mirror of `gq2rCast_bcSlot`)
  is UNCONDITIONAL/sign-free: the shared first factor `F_{b,c+d+e}`'s own
  `(c+d+e)`-slot (its `P₂`-slot, `leftActionEnd`) is untouched by the cast,
  matching `GBR`'s own natural `(c+d+e)`-slot (`GBR.cslot_smul_mk`) on the
  other side — both built the SAME way (`leftActionEnd` reaching the shared
  first factor), so no sign law is needed (a `gq2rCast_dSlot`-STYLE proof —
  unconditional despite the surrounding structure — but landing on the
  `bcSlot`-shaped hypothesis since it is the SHARED first factor here, not
  a second-factor coefficient). Wrapped (`gq3rCastWrapped`, `RelTensor.
  mapEquivRight` of `gq3rCast.symm` via `leftEquivariant_symm`) under the
  outer `GBL(c,d,e)` spectator: lands `GBL(c,d,e) ⊗_{D_{c+d+e}}
  (F_{b,c+d+e} ⊗_{D_{bcde}} F_{a,bcde})`.
* `gV13StepA` (plain `RelTensor.assoc`, peeling `F_{c,d}` off `GBL(c,d,e)`,
  the third factor kept opaque — `RelTensor.assoc`'s `P`-slot is generic):
  lands `F_{c,d} ⊗_{D_{c+d}} (F_{c+d,e} ⊗_{D_{c+d+e}} (F_{b,c+d+e}
  ⊗_{D_{bcde}} F_{a,bcde}))`.
* `gV13Regroup` (plain `RelTensor.assoc.symm`, combining `F_{c+d,e}` with
  `F_{b,c+d+e}` into `GQ3Inner K Γ b c d e` while keeping `F_{a,bcde}`
  outside — SIGN-FREE, both factors here use only `leftActionEnd`-style
  actions), wrapped (`gV13RegroupWrapped`, `RelTensor.mapEquivRight`) under
  the outer `F_{c,d}` spectator via a fresh nested-induction naturality proof
  (`gV13Regroup_leaf`/`_aSlot`, mirroring `gE11GBRAssoc_leaf`/`_aSlot`'s
  discipline but SIGN-FREE throughout — no `midEnd`/Koszul sign anywhere,
  since the outer `(c+d)`-slot reaches `GQ3Inner`'s own already-public
  `(c+d)`-slot, `Pentagon.lean`, via plain `leftActionEnd` on both sides):
  lands `F_{c,d} ⊗_{D_{c+d}} (GQ3Inner K Γ b c d e ⊗_{D_{bcde}} F_{a,bcde})`.
* `gV13StepB` (plain `RelTensor.assoc.symm`, combining `F_{c,d}` with
  `GQ3Inner K Γ b c d e` into `GQ3 K Γ b c d e` — `GQ3`'s own definition IS
  `F_{c,d} ⊗_{D_{c+d}} GQ3Inner`, so this is cast-free): lands
  `GQ3(b,c,d,e) ⊗_{D_{bcde}} F_{a,bcde} = V13` exactly.

**`E21M` (`V9 → V14`, `t_{a,b,c+(d+e)}`, faces `PDE`/`S3`)**: the STRICT
mirror with `GBR`-flavoured spellings — turns out to need `gq3rCast`
UNCHANGED (the move triple `(a,b,c+d+e)` is the SAME group element and the
SAME `gTCanon`/`gCanonHphi5` instantiation regardless of whether the OUTER
cluster spectator is `GBL(c,d,e)` or `GBR(c,d,e)`, since `gq3rCast`'s domain/
codomain never reference the outer spectator at all) — and turns out
SIMPLER than `E19M` past the swap, since `GQ4 K Γ b c d e` is *definitionally*
`GBR(c,d,e) ⊗_{D_{c+d+e}} F_{b,c+d+e}` (no further internal `GQ4Inner`
decomposition the way `GQ3` needs `GQ3Inner`), so the closing needs only ONE
more plain `RelTensor.assoc.symm`, no regroup/wrap step at all. Route
(`E21Mequiv`, four composed equivalences):

* `gV9Swap` (`Bimod.midSwap`, `V9`'s own `M := F_{a,b}`, `N := GBR(c,d,e)`,
  `P := F_{a+b,c+d+e}` shape, no assoc peel needed — `V9 = F_{a,b}
  ⊗_{D_{a+b}} V9Inner` already, `Quint.lean`'s M13-1′ fix): `gV9LawA` mirrors
  `V9Inner`'s own `(a+b)`-slot construction (`instModuleV9InnerASlot`),
  `gV9LawB` is the SAME `GBL.cslot_smul_mk_of_mem` call as `E19M`'s
  `gV8LawB` (it only ever sees `M := F_{a,b}`, `P := F_{a+b,c+d+e}`,
  independent of `N`). Lands `GBR(c,d,e) ⊗_{D_{c+d+e}} GBL(a,b,c+d+e)`.
* `gE21InnerStep` (`PentagonB.smapEquiv` of the SAME `gTCanon Γ a b
  (c+d+e)` at its `(c+d+e)`-slot, via the SAME `gCanonHphi5 K Γ a b (c+d) e`
  — only the outer base grading changes, `GBR.grading Γ c d e` in place of
  `GBL.grading Γ c d e`): lands `GBR(c,d,e) ⊗_{D_{c+d+e}} GBR(a,b,c+d+e)`.
* `gq3rCastWrappedR` (`RelTensor.mapEquivRight` of `gq3rCast.symm`, REUSED
  VERBATIM from `E19M` — zero new content, only the outer spectator's own
  `leftEquivariant_symm`/`mapEquivRight` instantiation changes from
  `GBL(c,d,e)` to `GBR(c,d,e)`): lands `GBR(c,d,e) ⊗_{D_{c+d+e}}
  (F_{b,c+d+e} ⊗_{D_{bcde}} F_{a,bcde})`.
* `gV14StepFinal` (a SINGLE plain `RelTensor.assoc.symm`, `M := GBR(c,d,e)`,
  `N := F_{b,c+d+e}`, `P := F_{a,bcde}` — `GBR(c,d,e) ⊗_{D_{c+d+e}}
  F_{b,c+d+e}` unfolds *definitionally* to `GQ4 K Γ b c d e`, so no regroup
  is needed the way `E19M`'s `GQ3` did): lands `GQ4(b,c,d,e) ⊗_{D_{bcde}}
  F_{a,bcde} = V14` exactly.

`E19M`/`E19M_bijective` and `E21M`/`E21M_bijective` assemble as
`LinearEquiv`/`.bijective` projections, mirroring every earlier edge's own
style — the 21-edge scaffold is now complete.
-/
import Superfusion.GaugeChi.QuintEdges7

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

/-! ### Edge 19, Stage 1: `gV8Swap`, the middle swap at `V8`'s own top level -/

/-- `inferInstanceAs` bridge: the signed `(a+b)`-slot action of `V8Inner` in
the raw `RelTensor` spelling (the inner factor of `V8` as the middle swap
sees it). -/
noncomputable instance instModuleV8SwapASlot : Module (Γ.D (a + b)).carrier
    (RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))) :=
  inferInstanceAs (Module (Γ.D (a + b)).carrier (V8Inner K Γ a b c d e))

private theorem gV8LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier (GBL Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (Γ.D (a + b)).grading (GBL.grading Γ c d e) := by
  intro l i x hx n hn p
  show midEnd (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) x
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p)
    = ((sgn (l * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) n (x • p)
  exact midEnd_mk_of_mem (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading
    (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) hn hx p

private theorem gV8LawB :
    MidSignLaw K (Γ.D (c + d + e)).carrier (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (Γ.D (c + d + e)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  exact GBL.cslot_smul_mk_of_mem (Γ := Γ) (a := a) (b := b) (c := c + d + e) hz hm p

/-- **`gV8Swap`**: the middle swap at `V8`'s own top level (no preceding
`assoc` peel — `V8` is already the `midSwap` shape `F_{a,b} ⊗ (GBL(c,d,e) ⊗
F_{a+b,c+d+e})`). Lands `GBL(c,d,e) ⊗_{D_{c+d+e}} GBL(a,b,c+d+e)` (the
second factor `F_{a,b} ⊗ F_{a+b,c+d+e}` unfolds definitionally to
`GBL Γ a b (c+d+e)`). -/
noncomputable def gV8Swap :
    V8 K Γ a b c d e
      ≃ₗ[K] RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e)) :=
  midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse a b))
    (GBL Γ c d e) (FusionColumn (Γ.fuse (a + b) (c + d + e)))
    (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
    (FusionColumn.grading (Γ.fuse a b)) (GBL.grading Γ c d e)
    (gV8LawA K Γ a b c d e) (gV8LawB K Γ a b c d e)

/-- **The sign law of `gV8Swap` on homogeneous generators** (term-mode:
`midSwapMap_mk_of_mem` unifies directly against the raw `RelTensor.mk`-headed
statement by elaboration-time defeq — the same discipline `gV6Swap_mk_of_mem`/
`gV7Swap_mk_of_mem` use, exported here so the recognition-leaf round can reach
past `gV8LawA`/`gV8LawB`'s own `private` visibility). -/
theorem gV8Swap_mk_of_mem {i j : ZMod 2} {n : GBL Γ c d e} (hn : n ∈ GBL.grading Γ c d e i)
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    gV8Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e)) n
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p) :=
  midSwapMap_mk_of_mem K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse a b)) (GBL Γ c d e) (FusionColumn (Γ.fuse (a + b) (c + d + e)))
    (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
    (FusionColumn.grading (Γ.fuse a b)) (GBL.grading Γ c d e)
    (gV8LawA K Γ a b c d e) (gV8LawB K Γ a b c d e) hn ht p

/-! ### Edge 19, Stage 2: the `(c+d+e)`-slot move `gE19InnerStep` -/

/-- The `(c+d+e)`-slot amplification of `gTCanon Γ a b (c+d+e)`, landing
`GBR(a,b,c+d+e)` (mirrors `gE14InnerStep`/`gE15Step`, keyed to
`gCanonHphi5`'s own `(c+d)+e = c+d+e` syntactic match, reused verbatim). -/
noncomputable def gE19InnerStep :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e))
      ≃ₗ[K] RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e)) :=
  PentagonB.smapEquiv K (Γ.D (c + d + e)).grading (GBL.grading Γ c d e)
    (gTCanon K Γ a b (c + d + e)) (gParity K Γ a b (c + d + e)) (gCanonHphi5 K Γ a b (c + d) e)

/-! ### Edge 19, Stage 3 (THE NEW DEVICE): `gq3rCast`, the GBR-mirror of
`ChiCanon.lean`'s `gq2rCast`

Recasts `GBR Γ a b (c+d+e)` (natural coefficient `D_{b+(c+d+e)}`) against the
LEFT-total raw pair `F_{b,c+d+e} ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e}` — built
exactly as `gq2rCast`: two `RelTensor.lift` legs glued by
`LinearEquiv.ofLinear`, identity on the shared first factor `F_{b,c+d+e}`,
`fusionColumnCast` (Pentagon.lean, casting the SECOND index of a column,
first index fixed — the mirror of `gColumnCastFst`, which casts the FIRST
index) on the second, via `add_assoc_four b c d e` (`Quint.lean`) and the
already-public `instModuleFusionColumnRecast4 K Γ b c d e` recast instance. -/

private theorem fusionColumnCast_xslot (p : G) {x y : G} (h : x = y) (τ : (Γ.D x).carrier)
    (w : FusionColumn (Γ.fuse p x)) :
    fusionColumnCast K Γ p h (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv τ • fusionColumnCast K Γ p h w := by
  subst h
  rfl

private theorem fusionColumnCast_symm_xslot (p : G) {x y : G} (h : x = y) (τ : (Γ.D y).carrier)
    (w : FusionColumn (Γ.fuse p y)) :
    (fusionColumnCast K Γ p h).symm (τ • w)
      = (Γ.gaugeCast h).toAlgEquiv.symm τ • (fusionColumnCast K Γ p h).symm w := by
  subst h
  rfl

private noncomputable def gq3rFwdBilin :
    FusionColumn (Γ.fuse b (c + d + e)) →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + d + e)) →ₗ[K] GBR Γ a b (c + d + e) :=
  (GBR.mk Γ a b (c + d + e)).compl₂
    (fusionColumnCast K Γ a (add_assoc_four b c d e)).toLinearMap

private theorem gq3rFwdBilin_apply (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq3rFwdBilin K Γ a b c d e u w
      = GBR.mk Γ a b (c + d + e) u (fusionColumnCast K Γ a (add_assoc_four b c d e) w) := rfl

private theorem GBR_mk_eq (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    GBR.mk Γ a b (c + d + e) u w
      = RelTensor.mk K (Γ.D (b + (c + d + e))).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + (c + d + e)))) u w :=
  rfl

private theorem gq3rFwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + c + d + e)).carrier (gq3rFwdBilin K Γ a b c d e) := by
  intro t u w
  rw [gq3rFwdBilin_apply, gq3rFwdBilin_apply, fusionColumnCast_xslot, GBR_mk_eq, GBR_mk_eq,
    fusionColumnRecast4_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gq3rFwd :
    RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) →ₗ[K]
      GBR Γ a b (c + d + e) :=
  RelTensor.lift (gq3rFwdBilin K Γ a b c d e) (gq3rFwd_balanced K Γ a b c d e)

private theorem gq3rFwd_mk (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq3rFwd K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u w)
      = GBR.mk Γ a b (c + d + e) u (fusionColumnCast K Γ a (add_assoc_four b c d e) w) := by
  show RelTensor.lift (gq3rFwdBilin K Γ a b c d e) (gq3rFwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) u w) = _
  rw [RelTensor.lift_mk, gq3rFwdBilin_apply]

private noncomputable def gq3rBwdBilin :
    FusionColumn (Γ.fuse b (c + d + e)) →ₗ[K]
      FusionColumn (Γ.fuse a (b + (c + d + e))) →ₗ[K]
        RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))).compl₂
    (fusionColumnCast K Γ a (add_assoc_four b c d e)).symm.toLinearMap

private theorem gq3rBwdBilin_apply (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    gq3rBwdBilin K Γ a b c d e u w
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u
          ((fusionColumnCast K Γ a (add_assoc_four b c d e)).symm w) := rfl

private theorem gq3rBwd_balanced :
    RelTensor.IsBalanced (Γ.D (b + (c + d + e))).carrier (gq3rBwdBilin K Γ a b c d e) := by
  intro s u w
  rw [gq3rBwdBilin_apply, gq3rBwdBilin_apply, fusionColumnCast_symm_xslot,
    show (MulOpposite.op s • u : FusionColumn (Γ.fuse b (c + d + e)))
        = MulOpposite.op ((Γ.gaugeCast (add_assoc_four b c d e)).toAlgEquiv.symm s) • u from by
      rw [fusionColumnRecast4_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gq3rBwd :
    GBR Γ a b (c + d + e) →ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  RelTensor.lift (gq3rBwdBilin K Γ a b c d e) (gq3rBwd_balanced K Γ a b c d e)

private theorem gq3rBwd_mk (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    gq3rBwd K Γ a b c d e (GBR.mk Γ a b (c + d + e) u w)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u
          ((fusionColumnCast K Γ a (add_assoc_four b c d e)).symm w) := by
  show RelTensor.lift (gq3rBwdBilin K Γ a b c d e) (gq3rBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + (c + d + e))).carrier
        (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + (c + d + e)))) u w) = _
  rw [RelTensor.lift_mk, gq3rBwdBilin_apply]

private theorem gq3rFwd_bwd :
    (gq3rFwd K Γ a b c d e).comp (gq3rBwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun u w => ?_
  show gq3rFwd K Γ a b c d e (gq3rBwd K Γ a b c d e (GBR.mk Γ a b (c + d + e) u w))
    = GBR.mk Γ a b (c + d + e) u w
  rw [gq3rBwd_mk, gq3rFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gq3rBwd_fwd :
    (gq3rBwd K Γ a b c d e).comp (gq3rFwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun u w => ?_
  show gq3rBwd K Γ a b c d e (gq3rFwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) u w))
    = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) u w
  rw [gq3rFwd_mk, gq3rBwd_mk, LinearEquiv.symm_apply_apply]

/-- **`gq3rCast`**: the GBR-mirror of `gq2rCast`, the four-letter recast
device this round's edges need (deliverable 1). -/
noncomputable def gq3rCast :
    RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) ≃ₗ[K]
      GBR Γ a b (c + d + e) :=
  LinearEquiv.ofLinear (gq3rFwd K Γ a b c d e) (gq3rBwd K Γ a b c d e)
    (gq3rFwd_bwd K Γ a b c d e) (gq3rBwd_fwd K Γ a b c d e)

theorem gq3rCast_mk (u : FusionColumn (Γ.fuse b (c + d + e)))
    (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq3rCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u w)
      = GBR.mk Γ a b (c + d + e) u (fusionColumnCast K Γ a (add_assoc_four b c d e) w) :=
  gq3rFwd_mk K Γ a b c d e u w

/-- **`gq3rCast`'s `(c+d+e)`-slot commutation, unconditionally** (the mirror
of `gq2rCast_bcSlot`, the slot-compatibility law the closing needs): the
action only ever touches the untouched shared first factor `F_{b,c+d+e}`
(its own `P₂`-slot, matching `GBR`'s own natural `(c+d+e)`-slot on the other
side — both `leftActionEnd`-built, so degree-0/sign-free). -/
theorem gq3rCast_bSlot (τ : (Γ.D (c + d + e)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    gq3rCast K Γ a b c d e (τ • n) = τ • gq3rCast K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk u w =>
      have hR : τ • gq3rCast K Γ a b c d e (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u w)
        = GBR.mk Γ a b (c + d + e) (τ • u) (fusionColumnCast K Γ a (add_assoc_four b c d e) w) := by
        rw [gq3rCast_mk, GBR.cslot_smul_mk]
      have hL : gq3rCast K Γ a b c d e (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u w)
        = GBR.mk Γ a b (c + d + e) (τ • u) (fusionColumnCast K Γ a (add_assoc_four b c d e) w) := by
        rw [show (τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) u w
              : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))))
            = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e))) (τ • u) w from
          leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) τ u w,
          gq3rCast_mk]
      rw [hL, hR]
  | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]

/-- `gq3rCast.symm`, wrapped by the outer `GBL(c,d,e)` spectator
(`RelTensor.mapEquivRight`, via `leftEquivariant_symm`). -/
noncomputable def gq3rCastWrapped :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e))
      ≃ₗ[K]
      RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.mapEquivRight K (gq3rCast K Γ a b c d e).symm
    (leftEquivariant_symm K (gq3rCast K Γ a b c d e) (gq3rCast_bSlot K Γ a b c d e))

/-! ### Edge 19, Stage 4: `gV13StepA`, peeling `F_{c,d}` off `GBL(c,d,e)` -/

/-- **`gV13StepA`**: a plain `RelTensor.assoc`, peeling `F_{c,d}` off the
outer `GBL(c,d,e)` spectator (the third factor kept opaque — `RelTensor.
assoc`'s `P`-slot is generic in its type). -/
noncomputable def gV13StepA :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))) :=
  RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e))))

/-! ### Edge 19, Stage 5: `gV13Regroup`, combining `F_{c+d,e}` with
`F_{b,c+d+e}` into `GQ3Inner K Γ b c d e` -/

instance instIsScalarTowerGQ3InnerCDSlot :
    IsScalarTower K (Γ.D (c + d)).carrier (GQ3Inner K Γ b c d e) :=
  ⟨fun k' x n => by
    show (leftActionEnd K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e))) (k' • x)) n
      = k' • (leftActionEnd K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e))) x) n
    rw [map_smul, LinearMap.smul_apply]⟩

/-- `GQ3Inner K Γ b c d e`'s own already-public `(c+d)`-slot (`Pentagon.
lean`), lifted to `GQ3Inner K Γ b c d e ⊗ F_{a,bcde}` via `leftActionEnd`. -/
noncomputable instance instModuleGV13RegroupTargetCDSlot : Module (Γ.D (c + d)).carrier
    (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  Module.compHom _
    ((leftActionEnd K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e))) (B := (Γ.D (c + d)).carrier)).toRingHom)

/-- `inferInstanceAs` bridge: the `(c+d)`-slot action of `GQ3Inner K Γ b c d e
⊗ F_{a,bcde}` in the raw `RelTensor` spelling (the codomain of `gV13Regroup`
as its own naturality lemma sees it). -/
noncomputable instance instModuleGV13RegroupTargetCDSlotRaw : Module (Γ.D (c + d)).carrier
    (RelTensor K (Γ.D (b + c + d + e)).carrier
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e))))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  inferInstanceAs (Module (Γ.D (c + d)).carrier
    (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))))

/-- **`gV13Regroup`**: a plain `RelTensor.assoc.symm`, combining `F_{c+d,e}`
with `F_{b,c+d+e}` into `GQ3Inner K Γ b c d e` while keeping `F_{a,bcde}`
outside. -/
noncomputable def gV13Regroup :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse (c + d) e)) (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e)))).symm

/-- **The leaf computation of `gV13Regroup`'s `(c+d)`-equivariance**: purely
mechanical (SIGN-FREE — no `midEnd`/Koszul sign anywhere, since both sides
use only `leftActionEnd`), via `RelTensor.assoc_symm_mk` and
`leftActionEnd_mk` (twice, once for each nesting level). -/
theorem gV13Regroup_leaf (τ : (Γ.D (c + d)).carrier) (u : FusionColumn (Γ.fuse (c + d) e))
    (v : FusionColumn (Γ.fuse b (c + d + e))) (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV13Regroup K Γ a b c d e
        (τ • RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))
          u (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) v x))
      = τ • gV13Regroup K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            u (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
              v x)) := by
  show gV13Regroup K Γ a b c d e
      (τ • RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        u (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) v x))
    = τ • gV13Regroup K Γ a b c d e (RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        u (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
          v x))
  have hτu : τ • RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        u (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))) v x)
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))
          (τ • u) (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) v x) :=
    leftActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e)))) τ u
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) v x)
  rw [hτu]
  show (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse (c + d) e)) (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))).symm
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • u)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
          v x))
    = τ • (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e)) (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e)))).symm
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) u
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
          v x))
  rw [RelTensor.assoc_symm_mk, RelTensor.assoc_symm_mk]
  show RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
        (FusionColumn (Γ.fuse b (c + d + e))) (τ • u) v) x
    = τ • RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
        (FusionColumn (Γ.fuse a (b + c + d + e)))
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (FusionColumn (Γ.fuse b (c + d + e))) u v) x
  have hτuv : τ • RelTensor.mk K (Γ.D (c + d + e)).carrier
        (FusionColumn (Γ.fuse (c + d) e)) (FusionColumn (Γ.fuse b (c + d + e))) u v
      = RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (FusionColumn (Γ.fuse b (c + d + e))) (τ • u) v :=
    leftActionEnd_mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
      (FusionColumn (Γ.fuse b (c + d + e))) τ u v
  rw [← hτuv]
  exact (leftActionEnd_mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) τ
    (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
      (FusionColumn (Γ.fuse b (c + d + e))) u v) x).symm

/-- **`gV13Regroup`'s `(c+d)`-equivariance, generalized** (the nested
`RelTensor.induction_on` descent to `gV13Regroup_leaf`; SIGN-FREE, so no
`DirectSum.Decomposition.inductionOn`/degree bookkeeping is needed anywhere,
unlike the signed `*Swap`/`*FinalStep` naturality proofs elsewhere in this
arc). -/
theorem gV13Regroup_aSlot (τ : (Γ.D (c + d)).carrier)
    (n : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))))) :
    gV13Regroup K Γ a b c d e (τ • n) = τ • gV13Regroup K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | mk u w =>
      induction w using RelTensor.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | add p q hp hq => simp only [map_add, smul_add, hp, hq]
      | mk v x => exact gV13Regroup_leaf K Γ a b c d e τ u v x

/-- `gV13Regroup`, wrapped by the outer `F_{c,d}` spectator. -/
noncomputable def gV13RegroupWrapped :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))))
      ≃ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.mapEquivRight K (gV13Regroup K Γ a b c d e) (gV13Regroup_aSlot K Γ a b c d e)

/-! ### Edge 19, Stage 6: `gV13StepB`, closing `V13` -/

/-- **`gV13StepB`**: a plain `RelTensor.assoc.symm`, combining `F_{c,d}`
with `GQ3Inner K Γ b c d e` into `GQ3 K Γ b c d e` (`GQ3`'s own definition IS
`F_{c,d} ⊗ GQ3Inner`, so this is cast-free) — lands `V13` exactly. -/
noncomputable def gV13StepB :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K] V13 K Γ a b c d e :=
  (RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse c d)) (GQ3Inner K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e)))).symm

/-! ### Edge 19: the assembly -/

/-- **`E19M`, as a `LinearEquiv`**: `V8 → V13`, the move `t_{a,b,(c+d)+e}` —
`gV8Swap` then the signed `(c+d+e)`-slot move `gE19InnerStep` then the
closing recast `gq3rCastWrapped` (`gq3rCast`, THE new device) then the
three plain reassociations `gV13StepA`, `gV13RegroupWrapped`, `gV13StepB`. -/
noncomputable def E19Mequiv : V8 K Γ a b c d e ≃ₗ[K] V13 K Γ a b c d e :=
  (gV8Swap K Γ a b c d e).trans
    ((gE19InnerStep K Γ a b c d e).trans
      ((gq3rCastWrapped K Γ a b c d e).trans
        ((gV13StepA K Γ a b c d e).trans
          ((gV13RegroupWrapped K Γ a b c d e).trans (gV13StepB K Γ a b c d e)))))

/-- **Edge 19** `E19M : V8 → V13`, `t_{a,b,(c+d)+e}` (owning faces `PCD`,
`S3`). -/
noncomputable def E19M : V8 K Γ a b c d e →ₗ[K] V13 K Γ a b c d e :=
  (E19Mequiv K Γ a b c d e).toLinearMap

theorem E19M_bijective : Function.Bijective (E19M K Γ a b c d e) :=
  (E19Mequiv K Γ a b c d e).bijective

/-! ### Edge 21, Stage 1: `gV9Swap`, the middle swap at `V9`'s own top level

The strict mirror of `gV8Swap`, `GBR(c,d,e)` in place of `GBL(c,d,e)`;
`gV9LawB` is the SAME `GBL.cslot_smul_mk_of_mem` call as `gV8LawB` (it only
ever sees `M := F_{a,b}`, `P := F_{a+b,c+d+e}`, independent of `N`). -/

/-- `inferInstanceAs` bridge: the signed `(a+b)`-slot action of `V9Inner` in
the raw `RelTensor` spelling. -/
noncomputable instance instModuleV9SwapASlot : Module (Γ.D (a + b)).carrier
    (RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))) :=
  inferInstanceAs (Module (Γ.D (a + b)).carrier (V9Inner K Γ a b c d e))

private theorem gV9LawA :
    MidSignLaw K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier (GBR Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (Γ.D (a + b)).grading (GBR.grading Γ c d e) := by
  intro l i x hx n hn p
  show midEnd (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) x
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p)
    = ((sgn (l * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) n (x • p)
  exact midEnd_mk_of_mem (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading
    (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) hn hx p

private theorem gV9LawB :
    MidSignLaw K (Γ.D (c + d + e)).carrier (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (Γ.D (c + d + e)).grading (FusionColumn.grading (Γ.fuse a b)) := by
  intro l i z hz m hm p
  exact GBL.cslot_smul_mk_of_mem (Γ := Γ) (a := a) (b := b) (c := c + d + e) hz hm p

/-- **`gV9Swap`**: the middle swap at `V9`'s own top level. Lands
`GBR(c,d,e) ⊗_{D_{c+d+e}} GBL(a,b,c+d+e)`. -/
noncomputable def gV9Swap :
    V9 K Γ a b c d e
      ≃ₗ[K] RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e)) :=
  midSwap K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse a b))
    (GBR Γ c d e) (FusionColumn (Γ.fuse (a + b) (c + d + e)))
    (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
    (FusionColumn.grading (Γ.fuse a b)) (GBR.grading Γ c d e)
    (gV9LawA K Γ a b c d e) (gV9LawB K Γ a b c d e)

/-- **The sign law of `gV9Swap` on homogeneous generators** (the `gV8Swap_mk_of_mem`
mirror, `GBR(c,d,e)` in place of `GBL(c,d,e)`). -/
theorem gV9Swap_mk_of_mem {i j : ZMod 2} {n : GBR Γ c d e} (hn : n ∈ GBR.grading Γ c d e i)
    {t : FusionColumn (Γ.fuse a b)} (ht : t ∈ FusionColumn.grading (Γ.fuse a b) j)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    gV9Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e)) n
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p) :=
  midSwapMap_mk_of_mem K (Γ.D (a + b)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse a b)) (GBR Γ c d e) (FusionColumn (Γ.fuse (a + b) (c + d + e)))
    (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
    (FusionColumn.grading (Γ.fuse a b)) (GBR.grading Γ c d e)
    (gV9LawA K Γ a b c d e) (gV9LawB K Γ a b c d e) hn ht p

/-! ### Edge 21, Stage 2: the `(c+d+e)`-slot move `gE21InnerStep`

The SAME `gTCanon Γ a b (c+d+e)` at the SAME `(c+d+e)`-slot, via the SAME
`gCanonHphi5 K Γ a b (c+d) e` — only the outer base grading changes from
`GBL.grading Γ c d e` to `GBR.grading Γ c d e`. -/
noncomputable def gE21InnerStep :
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e))
      ≃ₗ[K] RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBR Γ a b (c + d + e)) :=
  PentagonB.smapEquiv K (Γ.D (c + d + e)).grading (GBR.grading Γ c d e)
    (gTCanon K Γ a b (c + d + e)) (gParity K Γ a b (c + d + e)) (gCanonHphi5 K Γ a b (c + d) e)

/-! ### Edge 21, Stage 3: `gq3rCast` REUSED verbatim, wrapped under the
`GBR(c,d,e)` spectator -/

/-- `gq3rCast.symm`, wrapped by the outer `GBR(c,d,e)` spectator — the SAME
device as `gq3rCastWrapped`, only the outer spectator/`mapEquivRight`
instantiation changes. -/
noncomputable def gq3rCastWrappedR :
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBR Γ a b (c + d + e))
      ≃ₗ[K]
      RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.mapEquivRight K (gq3rCast K Γ a b c d e).symm
    (leftEquivariant_symm K (gq3rCast K Γ a b c d e) (gq3rCast_bSlot K Γ a b c d e))

/-! ### Edge 21, Stage 4: `gV14StepFinal`, closing `V14` in one plain
`assoc.symm`

`GBR(c,d,e) ⊗_{D_{c+d+e}} F_{b,c+d+e}` unfolds *definitionally* to
`GQ4 K Γ b c d e` (no further internal decomposition the way `GQ3` needed
`GQ3Inner` — this is why `E21M` needs no regroup/wrap step past the swap). -/
noncomputable def gV14StepFinal :
    RelTensor K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K] V14 K Γ a b c d e :=
  (RelTensor.assoc K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
    (GBR Γ c d e) (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e)))).symm

/-! ### Edge 21: the assembly -/

/-- **`E21M`, as a `LinearEquiv`**: `V9 → V14`, the move `t_{a,b,c+(d+e)}` —
`gV9Swap` then the signed `(c+d+e)`-slot move `gE21InnerStep` then the
closing recast `gq3rCastWrappedR` (`gq3rCast` reused verbatim) then the
single plain reassociation `gV14StepFinal`. -/
noncomputable def E21Mequiv : V9 K Γ a b c d e ≃ₗ[K] V14 K Γ a b c d e :=
  (gV9Swap K Γ a b c d e).trans
    ((gE21InnerStep K Γ a b c d e).trans
      ((gq3rCastWrappedR K Γ a b c d e).trans (gV14StepFinal K Γ a b c d e)))

/-- **Edge 21** `E21M : V9 → V14`, `t_{a,b,c+(d+e)}` (owning faces `PDE`,
`S3`) — the final edge, closing the 21-edge scaffold. -/
noncomputable def E21M : V9 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  (E21Mequiv K Γ a b c d e).toLinearMap

theorem E21M_bijective : Function.Bijective (E21M K Γ a b c d e) :=
  (E21Mequiv K Γ a b c d e).bijective

end GaugeChi

end Superfusion
