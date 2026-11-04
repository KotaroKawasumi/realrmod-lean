/-
Superfusion / GaugeChi / QuintEdges4

Milestone M13-2⁗ of the abstract `(p, χ)` arc: **the cluster edge `E11M`**
(`V3 → V8`, the move `t_{a+b,c+d,e}`, owning faces `PAB`, `PCD`) —
the first of the K₅ chain's "@-genre" cluster edges, whose route reassociates
`V3 = GQ5(a,b,c,d) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e}` down to expose
`GBL(a+b,c+d,e)` through the `F_{a,b}`/`F_{c,d}` whiskers, applies the
signed `gTCanon Γ (a+b) (c+d) e` move through TWO nested mid-actions, and
recasts the result onto `V8`'s FIXED four-column shape
`F_{a,b} ⊗_{D_{a+b}} (GBL(c,d,e) ⊗_{D_{c+d+e}} F_{a,b,c+d+e})` (`Quint.lean`'s
M13-1′ `V8`).

**The two new pieces of infrastructure this scoping anticipated, both
delivered:**

1. **The deeper nested mid-action**: the `(a+b)`-slot acts on `V3`'s own
   reassociated shape (and later on `V8`'s own `V8Inner`) through TWO
   levels of `midAlgHom`/`midEnd` — once through `F_{c,d}` reaching
   `GBL(a+b,c+d,e)`/`GBR(a+b,c+d,e)`, once more through `F_{a,b}` reaching
   the whole `F_{c,d} ⊗ (…)` tensor. Each level needs its OWN
   `SuperCommSMul` witness (`gblSuperComm`, `gbrBslotAslotSuperComm`,
   `gq2rInnerSuperComm`), all built via the SAME general fact
   `leftActionEnd_leftActionEnd_supercomm` (`Bimod/QuadEnvModule2.lean`)
   — supercommutation of two `leftActionEnd`-lifted actions reduces
   directly to the underlying `FusionColumn`'s own two-index-slot
   supercommutation (`FusionColumn.superCommSMul`) — or, for the
   `GBR`-flavoured aslot/bslot pair, to `leftActionEnd_anticommutes_
   midAlgHom` (`Bimod/MiddleActionHom.lean`) applied at `GBR`'s own
   internal construction (`gbrBslotAslotSuperComm`).
2. **The `smap`-vs-`midEnd` square lemma** (`smap_comm_midEnd`, new
   general toolkit piece): `smap`'s own signed second-slot amplification
   commutes with a further outer `midEnd` (ALSO reaching through the
   second slot, keyed to the SAME first-slot degree) up to `sgn(e·k)`,
   provided the underlying amplified map is *itself* signed-equivariant
   for the outer algebra with the SAME degree `e` — exactly the shape
   `gTCanon`'s own two slot-equivariances (`gCanonMidSlot`, the `(c+d)`
   mid-slot; `gCanonHphi4`, the `(a+b)` aslot, both ALREADY public) supply
   for `E11M`'s outer `(a+b)`-wrap of the inner `(c+d)`-move.

**The route, in five composed equivalences** (`E11Mequiv`):

* `gV3AssocA` (plain `RelTensor.assoc`): `V3 ≃ F_{a,b} ⊗_{D_{a+b}}
  (GBR(a+b,c,d) ⊗_{D_{a+b+c+d}} F_{a+b+c+d,e})`.
* `gV3AssocABC` (`gV3AssocA` then `RelTensor.mapEquivRight` of
  `gV3AssocBC := gV3StepB.trans gV3StepC`, itself `RelTensor.assoc` then
  the recast `gq2rCast Γ (a+b) c d e`, general-`τ` naturality assembled
  from the homogeneous `gV3StepB_aSlot`/`gV3StepC_aSlot` plus a
  `DirectSum.Decomposition.inductionOn`-linearity lift, mirroring
  `gt2Canon_rightSlot_general`'s pattern): `V3 ≃ F_{a,b} ⊗_{D_{a+b}}
  (F_{c,d} ⊗_{D_{c+d}} GBL(a+b,c+d,e))` — exposing `GBL(a+b,c+d,e)`
  through BOTH whiskers, no cast remaining (`(a+b)+c+d = a+b+c+d` and
  `(c+d)+e = c+d+e` syntactically; the genuine `(a+b)+(c+d)` vs
  `a+b+c+d` spelling mismatch is absorbed by `gq2rCast`, reused
  UNCHANGED from `ChiCanon.lean` at the four-letter instantiation
  `(a+b,c,d,e)`).
* `gE11InnerStep` (`PentagonB.smapEquiv` of `gTCanon Γ (a+b) (c+d) e` at
  its own `(c+d)`-mid-slot, via `gCanonMidSlot`, mirroring `E15M`'s
  `gE15Step`): the `(c+d)`-slot move, landing `GBR(a+b,c+d,e)`.
* `gE11OuterStep` (`PentagonB.smapEquiv` of `gE11InnerStep` at the
  `(a+b)`-slot, hypothesis `gE11OuterHg` assembled from `smap_comm_midEnd`
  + `gCanonHphi4`): the outer whisker of the inner move — the deliverable
  (1) above, discharged.
* `gE11FinalStep` (`RelTensor.mapEquivRight` of `gE11GBRAssoc`, the
  `RelTensor.assoc` closing `F_{c,d} ⊗ GBR(a+b,c+d,e)` onto `V8Inner`,
  naturality `gE11GBRAssoc_aSlot`/`_general`): lands exactly `V8`'s FIXED
  four-column shape.

Each naturality fact (`gV3StepB_aSlot`, `gV3StepC_aSlot`,
`gE11GBRAssoc_aSlot`) is proved by a nested nested
`RelTensor.induction_on`/`DirectSum.Decomposition.inductionOn` nest down
to the fully-homogeneous generator (`gV3StepB_leaf`, `gV3StepC_leaf`,
`gE11GBRAssoc_leaf`), following the file discipline recorded in
`QuintEdges.lean`'s toolkit notes: term-mode `calc`/`congrArg` throughout
(never `rw` on a hypothesis mixing a `def`-wrapped vertex type's folded
and raw spellings), with the `mk`-level sign identities discharged via
`midEnd_mk_of_mem`/`smap_mk_of_mem`/`GBR.aslot_smul_mk_of_mem`/
`assoc_mk`/`assoc_symm_mk` and `Units.val_mul`/`sgn_add` bookkeeping.

`E11M`/`E11M_bijective` assemble as `LinearEquiv`/`.bijective` projections,
mirroring `ChiCanon.lean`'s and the earlier edges' own style.
-/
import Superfusion.GaugeChi.QuintEdges3
import Superfusion.Bimod.QuadEnvModule2

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

section SmapMidEndSquareLemma

variable {A' : Type*} [Ring A'] [Algebra K A']
variable (𝒜' : ZMod 2 → Submodule K A') [GradedAlgebra 𝒜']
variable {M' : Type*} [AddCommGroup M'] [Module K M'] [Module A'ᵐᵒᵖ M']
variable (ℳ' : ZMod 2 → Submodule K M') [DirectSum.Decomposition ℳ'] [GradedRightSMul 𝒜' ℳ']
variable {N₁ : Type*} [AddCommGroup N₁] [Module K N₁] [Module A' N₁]
variable {N₁' : Type*} [AddCommGroup N₁'] [Module K N₁'] [Module A' N₁']
variable {C' : Type*} [Ring C'] [Algebra K C']
variable (𝒞' : ZMod 2 → Submodule K C') [GradedAlgebra 𝒞']
variable [Module C' N₁] [IsScalarTower K C' N₁]
variable [Module C' N₁'] [IsScalarTower K C' N₁']

private theorem zmod2_smapmidend_deg :
    ∀ e j k : ZMod 2, k * j + e * j + e * k = e * k + e * j + k * j := by
  decide +revert

omit [Invertible (2 : K)] in
/-- **The `smap`-vs-`midEnd` square lemma, BOTH in the second slot**:
`smap`'s own signed second-slot amplification (keyed to the first
factor's degree) commutes with `midEnd`'s Koszul-signed action (ALSO
keyed to the first factor's degree, reaching a *further* outer algebra
`C'`) up to `sgn(e·k)`, PROVIDED the underlying map `g` amplified by
`smap` is *itself* signed-`C'`-equivariant with the SAME degree `e` — the
general fact powering `E11M`'s nested `(a+b)`/`(c+d)`-mid-action
amplification (both the smap's own inner move and the outer wrap reach
through the SAME first-slot degree bookkeeping). -/
theorem smap_comm_midEnd
    (hsc : SuperCommSMul 𝒜' 𝒞' N₁) (hsc' : SuperCommSMul 𝒜' 𝒞' N₁')
    (g : N₁ →ₗ[K] N₁') {e : ZMod 2}
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A'⦄, a ∈ 𝒜' i → ∀ n : N₁,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    (hgc : ∀ ⦃i' : ZMod 2⦄ ⦃c : C'⦄, c ∈ 𝒞' i' → ∀ n : N₁,
      g (c • n) = ((sgn (e * i') : ℤˣ) : ℤ) • (c • g n))
    {k : ZMod 2} {c : C'} (hc : c ∈ 𝒞' k) :
    (smap 𝒜' ℳ' g e hg).comp (midEnd 𝒜' ℳ' 𝒞' hsc c)
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (midEnd 𝒜' ℳ' 𝒞' hsc' c).comp (smap 𝒜' ℳ' g e hg) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ' with
  | zero => simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm', smul_add]
  | homogeneous xm =>
      rw [midEnd_mk_of_mem 𝒜' ℳ' 𝒞' hsc xm.2 hc, map_zsmul, smap_mk_of_mem 𝒜' ℳ' g e hg xm.2, hgc hc,
        map_zsmul, smap_mk_of_mem 𝒜' ℳ' g e hg xm.2, map_zsmul, midEnd_mk_of_mem 𝒜' ℳ' 𝒞' hsc' xm.2 hc,
        smul_smul, smul_smul, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, ← sgn_add, ← sgn_add,
        zmod2_smapmidend_deg]

end SmapMidEndSquareLemma

theorem gblSuperComm :
    SuperCommSMul (Γ.D (a + b)).grading (Γ.D (c + d)).grading (GBL Γ (a + b) (c + d) e) := by
  intro i k x y hx hy w
  show (leftActionEnd K (Γ.D ((a+b)+(c+d))).carrier (FusionColumn (Γ.fuse (a+b) (c+d)))
      (FusionColumn (Γ.fuse ((a+b)+(c+d)) e)) x)
      ((leftActionEnd K (Γ.D ((a+b)+(c+d))).carrier (FusionColumn (Γ.fuse (a+b) (c+d)))
      (FusionColumn (Γ.fuse ((a+b)+(c+d)) e)) y) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((leftActionEnd K (Γ.D ((a+b)+(c+d))).carrier (FusionColumn (Γ.fuse (a+b) (c+d)))
      (FusionColumn (Γ.fuse ((a+b)+(c+d)) e)) y)
      ((leftActionEnd K (Γ.D ((a+b)+(c+d))).carrier (FusionColumn (Γ.fuse (a+b) (c+d)))
      (FusionColumn (Γ.fuse ((a+b)+(c+d)) e)) x) w))
  exact leftActionEnd_leftActionEnd_supercomm
    (Γ.D (a+b)).grading (Γ.D (c+d)).grading (FusionColumn.superCommSMul (Γ.fuse (a+b) (c+d)))
    hx hy w

noncomputable instance instModuleE11ABSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) :=
  Module.compHom _
    ((midAlgHom (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gblSuperComm K Γ a b c d e))).toRingHom)

theorem instModuleE11ABSlot_smul_def (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) :
    τ • n
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gblSuperComm K Γ a b c d e)) τ n := rfl


theorem gbrBslotAslotSuperComm :
    SuperCommSMul (Γ.D (c + d)).grading (Γ.D (a + b)).grading (GBR Γ (a + b) (c + d) e) := by
  intro i k y τ hy hτ w
  show (leftActionEnd K (Γ.D ((c + d) + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
      (FusionColumn (Γ.fuse (a + b) ((c + d) + e))) y)
      ((midAlgHom (Γ.D ((c + d) + e)).grading (FusionColumn.grading (Γ.fuse (c + d) e))
          (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D ((c + d) + e)).grading
            (FusionColumn.superCommSMul (Γ.fuse (a + b) ((c + d) + e)))) τ) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((midAlgHom (Γ.D ((c + d) + e)).grading (FusionColumn.grading (Γ.fuse (c + d) e))
            (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D ((c + d) + e)).grading
              (FusionColumn.superCommSMul (Γ.fuse (a + b) ((c + d) + e)))) τ)
          ((leftActionEnd K (Γ.D ((c + d) + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
            (FusionColumn (Γ.fuse (a + b) ((c + d) + e))) y) w))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D ((c + d) + e)).grading
    (FusionColumn.grading (Γ.fuse (c + d) e)) (Γ.D (a + b)).grading
    (Γ.D (c + d)).grading
    (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D ((c + d) + e)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b) ((c + d) + e))))
    (⟨y, hy⟩ : (Γ.D (c + d)).grading i) (⟨τ, hτ⟩ : (Γ.D (a + b)).grading k)
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow, show k * i = i * k from mul_comm k i]
  rfl

noncomputable def gE11GBRAssoc :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
      ≃ₗ[K] V8Inner K Γ a b c d e :=
  (RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
    (FusionColumn (Γ.fuse (a + b) (c + d + e)))).symm

theorem gE11GBRAssoc_leaf {i j' k : ZMod 2} {xu : FusionColumn (Γ.fuse c d)}
    (hxu : xu ∈ FusionColumn.grading (Γ.fuse c d) i)
    {xv' : FusionColumn (Γ.fuse (c + d) e)} (hxv' : xv' ∈ FusionColumn.grading (Γ.fuse (c + d) e) j')
    (x : FusionColumn (Γ.fuse (a + b) (c + d + e)))
    {τ : (Γ.D (a + b)).carrier} (hτ : τ ∈ (Γ.D (a + b)).grading k) :
    gE11GBRAssoc K Γ a b c d e
        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (gbrBslotAslotSuperComm K Γ a b c d e) τ
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x)))
      = τ • gE11GBRAssoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x)) := by
  have step1 : midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (gbrBslotAslotSuperComm K Γ a b c d e) τ
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (τ • GBR.mk Γ (a + b) (c + d) e xv' x) :=
    midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (gbrBslotAslotSuperComm K Γ a b c d e) hxu hτ _
  have step2 : τ • GBR.mk Γ (a + b) (c + d) e xv' x
      = ((sgn (k * j') : ℤˣ) : ℤ) • GBR.mk Γ (a + b) (c + d) e xv' (τ • x) :=
    GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c + d) (c := e) hτ hxv' x
  have keyMid : midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (gbrBslotAslotSuperComm K Γ a b c d e) τ
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x))
      = ((sgn (k * i) : ℤˣ) * (sgn (k * j') : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' (τ • x)) := by
    rw [step1, step2, map_zsmul, smul_smul]
  -- The V8Inner-typed generators, ascribed explicitly so registered smul resolves.
  let vGen1 : V8Inner K Γ a b c d e :=
    RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (GBL.mk Γ c d e xu xv') (τ • x)
  let vGen2 : V8Inner K Γ a b c d e :=
    RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (GBL.mk Γ c d e xu xv') x
  have keyAssoc :
      gE11GBRAssoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' (τ • x)))
        = vGen1 :=
    RelTensor.assoc_symm_mk K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
      (FusionColumn (Γ.fuse (a + b) (c + d + e))) xu xv' (τ • x)
  have keyAssoc2 :
      gE11GBRAssoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x))
        = vGen2 :=
    RelTensor.assoc_symm_mk K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
      (FusionColumn (Γ.fuse (a + b) (c + d + e))) xu xv' x
  have keyTarget : τ • vGen2 = ((sgn (k * (i + j')) : ℤˣ) : ℤ) • vGen1 := by
    have hshow : τ • vGen2
        = midEnd (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
              (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) τ vGen2 := rfl
    rw [hshow]
    show midEnd (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))) τ
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBL.mk Γ c d e xu xv') x)
      = ((sgn (k * (i + j')) : ℤˣ) : ℤ) • vGen1
    rw [midEnd_mk_of_mem (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
        (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e))))
      (GBL.mk_mem_grading Γ c d e hxu hxv') hτ]
    rfl
  calc gE11GBRAssoc K Γ a b c d e
        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (gbrBslotAslotSuperComm K Γ a b c d e) τ
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x)))
      = gE11GBRAssoc K Γ a b c d e
          (((sgn (k * i) : ℤˣ) * (sgn (k * j') : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' (τ • x))) :=
        congrArg (gE11GBRAssoc K Γ a b c d e) keyMid
    _ = ((sgn (k * i) : ℤˣ) * (sgn (k * j') : ℤˣ) : ℤ) •
          gE11GBRAssoc K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' (τ • x))) := map_zsmul _ _ _
    _ = ((sgn (k * i) : ℤˣ) * (sgn (k * j') : ℤˣ) : ℤ) • vGen1 :=
        congrArg (((sgn (k * i) : ℤˣ) * (sgn (k * j') : ℤˣ) : ℤ) • ·) keyAssoc
    _ = ((sgn (k * (i + j')) : ℤˣ) : ℤ) • vGen1 := by
        rw [← Units.val_mul, ← sgn_add, show k * i + k * j' = k * (i + j') from by ring]
    _ = τ • vGen2 := keyTarget.symm
    _ = τ • gE11GBRAssoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e) xu (GBR.mk Γ (a + b) (c + d) e xv' x)) :=
        congrArg (τ • ·) keyAssoc2.symm


theorem gE11GBRAssoc_aSlot {k : ZMod 2} {τ : (Γ.D (a + b)).carrier}
    (hτ : τ ∈ (Γ.D (a + b)).grading k)
    (n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) :
    gE11GBRAssoc K Γ a b c d e
      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (gbrBslotAslotSuperComm K Γ a b c d e) τ n)
      = τ • gE11GBRAssoc K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add n n' hn hn' => simp only [map_add, smul_add, hn, hn']
  | mk u v =>
      induction u using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse c d))
          with
      | zero =>
          have e0 : (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GBR Γ (a + b) (c + d) e) (0 : FusionColumn (Γ.fuse c d)) v : _)
              = (0 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ (a + b) (c + d) e)) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (c + d)).carrier
              (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))) v).trans
              (LinearMap.zero_apply _)
          calc gE11GBRAssoc K Γ a b c d e
                (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) (0 : FusionColumn (Γ.fuse c d)) v))
              = gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ 0) :=
                congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ z)) e0
            _ = gE11GBRAssoc K Γ a b c d e 0 := by rw [map_zero]
            _ = 0 := map_zero _
            _ = τ • (0 : V8Inner K Γ a b c d e) := (smul_zero τ).symm
            _ = τ • gE11GBRAssoc K Γ a b c d e 0 := congrArg (τ • ·) (map_zero _).symm
            _ = τ • gE11GBRAssoc K Γ a b c d e
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) (0 : FusionColumn (Γ.fuse c d)) v) :=
                congrArg (fun z => τ • gE11GBRAssoc K Γ a b c d e z) e0.symm
      | add u u' hu hu' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) u u' v
          calc gE11GBRAssoc K Γ a b c d e
                (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) (u + u') v))
              = gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) u v
                      + RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) u' v)) :=
                congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ z)) e1
            _ = gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u v)
                  + midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u' v)) := by
                rw [map_add]
            _ = gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u v))
                + gE11GBRAssoc K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u' v)) := map_add _ _ _
            _ = τ • gE11GBRAssoc K Γ a b c d e
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) u v)
                + τ • gE11GBRAssoc K Γ a b c d e
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) u' v) := congrArg₂ (· + ·) hu hu'
            _ = τ • (gE11GBRAssoc K Γ a b c d e
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u v)
                  + gE11GBRAssoc K Γ a b c d e
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e) u' v)) := (smul_add τ _ _).symm
            _ = τ • gE11GBRAssoc K Γ a b c d e
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) (u + u') v) :=
                congrArg (fun z => τ • gE11GBRAssoc K Γ a b c d e z) e1.symm
      | homogeneous xu =>
          induction v using RelTensor.induction_on with
          | zero =>
              have e0 : (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                    (0 : GBR Γ (a + b) (c + d) e) : _)
                  = (0 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GBR Γ (a + b) (c + d) e)) :=
                map_zero (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)))
              calc gE11GBRAssoc K Γ a b c d e
                    (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                      (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                        (0 : GBR Γ (a + b) (c + d) e)))
                  = gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ 0) :=
                    congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ z)) e0
                _ = 0 := by rw [map_zero, map_zero]
                _ = τ • gE11GBRAssoc K Γ a b c d e
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                        (0 : GBR Γ (a + b) (c + d) e)) := by
                    rw [e0, map_zero, smul_zero]
          | add v v' hv hv' =>
              have e1 := map_add (RelTensor.mk K (Γ.D (c + d)).carrier
                (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)
                (xu : FusionColumn (Γ.fuse c d))) v v'
              calc gE11GBRAssoc K Γ a b c d e
                    (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                      (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) (v + v')))
                  = gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v
                          + RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v')) :=
                    congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ z)) e1
                _ = gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v)
                      + midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v')) := by
                    rw [map_add]
                _ = gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v))
                    + gE11GBRAssoc K Γ a b c d e
                      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                        (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v')) :=
                    map_add _ _ _
                _ = τ • gE11GBRAssoc K Γ a b c d e
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v)
                    + τ • gE11GBRAssoc K Γ a b c d e
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v') :=
                    congrArg₂ (· + ·) hv hv'
                _ = τ • (gE11GBRAssoc K Γ a b c d e
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v)
                      + gE11GBRAssoc K Γ a b c d e
                        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                          (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) v')) :=
                    (smul_add τ _ _).symm
                _ = τ • gE11GBRAssoc K Γ a b c d e
                      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) (v + v')) :=
                    congrArg (fun z => τ • gE11GBRAssoc K Γ a b c d e z) e1.symm
          | mk v' x =>
              induction v' using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse (c + d) e)) with
              | zero =>
                  have e0 : (GBR.mk Γ (a + b) (c + d) e (0 : FusionColumn (Γ.fuse (c + d) e)) x
                        : GBR Γ (a + b) (c + d) e)
                      = (0 : GBR Γ (a + b) (c + d) e) :=
                    (LinearMap.congr_fun (map_zero (GBR.mk Γ (a + b) (c + d) e)) x).trans
                      (LinearMap.zero_apply _)
                  calc gE11GBRAssoc K Γ a b c d e
                        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                          (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e (0 : FusionColumn (Γ.fuse (c + d) e)) x)))
                      = gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (0 : GBR Γ (a + b) (c + d) e))) :=
                        congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) z))) e0
                    _ = τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (0 : GBR Γ (a + b) (c + d) e)) := by
                        have e0' : (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (0 : GBR Γ (a + b) (c + d) e) : _)
                            = (0 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                                (GBR Γ (a + b) (c + d) e)) :=
                          map_zero (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)))
                        rw [e0', map_zero, map_zero, smul_zero]
                    _ = τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e (0 : FusionColumn (Γ.fuse (c + d) e)) x)) :=
                        congrArg (fun z => τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) z)) e0.symm
              | add v' v'' hv' hv'' =>
                  have e1 := LinearMap.map_add₂ (GBR.mk Γ (a + b) (c + d) e) v' v'' x
                  calc gE11GBRAssoc K Γ a b c d e
                        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                          (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e (v' + v'') x)))
                      = gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v' x + GBR.mk Γ (a + b) (c + d) e v'' x))) :=
                        congrArg (fun z => gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) z))) e1
                    _ = gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v' x))
                          + midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v'' x))) := by
                        rw [map_add, map_add]
                    _ = gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v' x)))
                        + gE11GBRAssoc K Γ a b c d e
                          (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                            (Γ.D (a + b)).grading (gbrBslotAslotSuperComm K Γ a b c d e) τ
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v'' x))) := map_add _ _ _
                    _ = τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e v' x))
                        + τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e v'' x)) := congrArg₂ (· + ·) hv' hv''
                    _ = τ • (gE11GBRAssoc K Γ a b c d e
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v' x))
                          + gE11GBRAssoc K Γ a b c d e
                            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                              (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                              (GBR.mk Γ (a + b) (c + d) e v'' x))) := (smul_add τ _ _).symm
                    _ = τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d))
                            (GBR.mk Γ (a + b) (c + d) e (v' + v'') x)) :=
                        congrArg (fun z => τ • gE11GBRAssoc K Γ a b c d e
                          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                            (GBR Γ (a + b) (c + d) e) (xu : FusionColumn (Γ.fuse c d)) z)) e1.symm
              | homogeneous xv' =>
                  exact gE11GBRAssoc_leaf K Γ a b c d e xu.2 xv'.2 x hτ


theorem gq2rCast_aSlot (x : (Γ.D a).carrier) (n : GQ2rInner K Γ a b c d) :
    gq2rCast K Γ a b c d (x • n) = x • gq2rCast K Γ a b c d n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk v w =>
      have hR : x • gq2rCast K Γ a b c d (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d (x • v) (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [gq2rCast_mk, GBL.aslot_smul_mk]
      have hL : gq2rCast K Γ a b c d (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d (x • v) (gColumnCastFst K Γ d (add_assoc a b c) w) := by
        rw [show (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
              : GQ2rInner K Γ a b c d)
            = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w from
          leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) x v w,
          gq2rCast_mk]
      rw [hL, hR]
  | add x' y' hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]


theorem gq2rInnerSuperComm :
    SuperCommSMul (Γ.D (a + b)).grading (Γ.D (c + d)).grading (GQ2rInner K Γ (a + b) c d e) := by
  intro i k x y hx hy w
  show (leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
      (FusionColumn (Γ.fuse (a + b + c + d) e)) x)
      ((leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) y) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) y)
        ((leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) x) w))
  exact leftActionEnd_leftActionEnd_supercomm
    (Γ.D (a + b)).grading (Γ.D (c + d)).grading (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d)))
    hx hy w

instance instIsScalarTowerGQ2rInnerABSlot :
    IsScalarTower K (Γ.D (a + b)).carrier (GQ2rInner K Γ (a + b) c d e) :=
  ⟨fun k' x n => by
    show (leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (k' • x)) n
      = k' • (leftActionEnd K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) x) n
    rw [map_smul, LinearMap.smul_apply]⟩

noncomputable instance instModuleGQ2rInnerABSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)) :=
  Module.compHom _
    ((midAlgHom (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gq2rInnerSuperComm K Γ a b c d e))).toRingHom)


noncomputable def gV3StepB :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) ≃ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) :=
  RelTensor.assoc K (Γ.D (c + d)).carrier (Γ.D (a + b + c + d)).carrier
    (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
    (FusionColumn (Γ.fuse (a + b + c + d) e))

theorem gV3StepB_leaf {j k : ZMod 2} {v : FusionColumn (Γ.fuse c d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse c d) j)
    (x : FusionColumn (Γ.fuse (a + b) (c + d)))
    (p : FusionColumn (Γ.fuse (a + b + c + d) e))
    {τ : (Γ.D (a + b)).carrier} (hτ : τ ∈ (Γ.D (a + b)).grading k) :
    gV3StepB K Γ a b c d e
        (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p)
      = τ • gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p) := by
  have step1 : τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (τ • GBR.mk Γ (a + b) c d v x) p :=
    leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e)) τ (GBR.mk Γ (a + b) c d v x) p
  have step2 : τ • GBR.mk Γ (a + b) c d v x
      = ((sgn (k * j) : ℤˣ) : ℤ) • GBR.mk Γ (a + b) c d v (τ • x) :=
    GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b) (b := c) (c := d) hτ hv x
  let vGen1 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2rInner K Γ (a + b) c d e) :=
    RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2rInner K Γ (a + b) c d e) v
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (τ • x) p)
  let vGen2 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2rInner K Γ (a + b) c d e) :=
    RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2rInner K Γ (a + b) c d e) v
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) x p)
  have keyAssoc1 : gV3StepB K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v (τ • x)) p)
      = vGen1 :=
    RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
      (FusionColumn (Γ.fuse (a + b + c + d) e)) v (τ • x) p
  have keyAssoc2 : gV3StepB K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p)
      = vGen2 :=
    RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (a + b) (c + d)))
      (FusionColumn (Γ.fuse (a + b + c + d) e)) v x p
  have keyTarget : τ • vGen2 = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 := by
    have hshow : τ • vGen2
        = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
            (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
              (gq2rInnerSuperComm K Γ a b c d e)) τ vGen2 := rfl
    rw [hshow]
    show midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
          (gq2rInnerSuperComm K Γ a b c d e)) τ
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GQ2rInner K Γ (a + b) c d e) v
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
            (FusionColumn (Γ.fuse (a + b + c + d) e)) x p))
      = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1
    rw [midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gq2rInnerSuperComm K Γ a b c d e)) hv hτ]
    have hL : τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (FusionColumn (Γ.fuse (a + b) (c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e)) x p
        = RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (FusionColumn (Γ.fuse (a + b) (c + d))) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (τ • x) p :=
      leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b) (c + d)))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) τ x p
    rw [hL]
  have argEq : RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) (τ • GBR.mk Γ (a + b) c d v x) p
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v (τ • x)) p := by
    rw [step2, map_zsmul, LinearMap.smul_apply]

  calc gV3StepB K Γ a b c d e
        (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p)
      = gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (τ • GBR.mk Γ (a + b) c d v x) p) := by
        rw [step1]
    _ = gV3StepB K Γ a b c d e
          (((sgn (k * j) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v (τ • x)) p) :=
        congrArg (gV3StepB K Γ a b c d e) argEq
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v (τ • x)) p) :=
        map_zsmul _ _ _
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 := congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·) keyAssoc1
    _ = τ • vGen2 := keyTarget.symm
    _ = τ • gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) (GBR.mk Γ (a + b) c d v x) p) :=
        congrArg (τ • ·) keyAssoc2.symm


theorem gV3StepB_aSlot {k : ZMod 2} {τ : (Γ.D (a + b)).carrier}
    (hτ : τ ∈ (Γ.D (a + b)).grading k)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gV3StepB K Γ a b c d e (τ • n) = τ • gV3StepB K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | mk g p =>
      induction g using RelTensor.induction_on with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) (0 : GBR Γ (a + b) c d) p
              = (0 : RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
              (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)))) p).trans
              (LinearMap.zero_apply _)
          calc gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                (0 : GBR Γ (a + b) c d) p)
              = gV3StepB K Γ a b c d e (τ • (0 : RelTensor K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)))) :=
                congrArg (fun z => gV3StepB K Γ a b c d e (τ • z)) e0
            _ = gV3StepB K Γ a b c d e 0 := congrArg (gV3StepB K Γ a b c d e) (smul_zero τ)
            _ = 0 := map_zero _
            _ = τ • (0 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GQ2rInner K Γ (a + b) c d e)) := (smul_zero τ).symm
            _ = τ • gV3StepB K Γ a b c d e 0 := congrArg (τ • ·) (map_zero _).symm
            _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                  (0 : GBR Γ (a + b) c d) p) :=
                congrArg (fun z => τ • gV3StepB K Γ a b c d e z) e0.symm
      | add g g' hg hg' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))) g g' p
          calc gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) (g + g') p)
              = gV3StepB K Γ a b c d e (τ • (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g p
                  + RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g' p)) :=
                congrArg (fun z => gV3StepB K Γ a b c d e (τ • z)) e1
            _ = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g p
                  + τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g' p) :=
                congrArg (gV3StepB K Γ a b c d e) (smul_add τ _ _)
            _ = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g p)
                + gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g' p) := map_add _ _ _
            _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g p)
                + τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g' p) :=
                congrArg₂ (· + ·) hg hg'
            _ = τ • (gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g p)
                  + gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) g' p)) :=
                (smul_add τ _ _).symm
            _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                  (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) (g + g') p) :=
                congrArg (τ • ·) (congrArg (gV3StepB K Γ a b c d e) e1).symm
      | mk v x =>
          induction v using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse c d))
              with
          | zero =>
              have e0 : (GBR.mk Γ (a + b) c d (0 : FusionColumn (Γ.fuse c d)) x
                    : GBR Γ (a + b) c d)
                  = (0 : GBR Γ (a + b) c d) :=
                (LinearMap.congr_fun (map_zero (GBR.mk Γ (a + b) c d)) x).trans
                  (LinearMap.zero_apply _)
              calc gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                    (GBR.mk Γ (a + b) c d (0 : FusionColumn (Γ.fuse c d)) x) p)
                  = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                      (0 : GBR Γ (a + b) c d) p) :=
                    congrArg (fun z => gV3StepB K Γ a b c d e (τ •
                      RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                        (FusionColumn (Γ.fuse (a + b + c + d) e)) z p)) e0
                _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                      (0 : GBR Γ (a + b) c d) p) := by
                    have e0' : RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                          (FusionColumn (Γ.fuse (a + b + c + d) e)) (0 : GBR Γ (a + b) c d) p
                        = (0 : RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                            (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
                      (LinearMap.congr_fun (map_zero (RelTensor.mk K
                        (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                        (FusionColumn (Γ.fuse (a + b + c + d) e)))) p).trans
                        (LinearMap.zero_apply _)
                    rw [e0', smul_zero, map_zero, smul_zero]
                _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                      (GBR.mk Γ (a + b) c d (0 : FusionColumn (Γ.fuse c d)) x) p) :=
                    congrArg (fun z => τ • gV3StepB K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                        (FusionColumn (Γ.fuse (a + b + c + d) e)) z p)) e0.symm
          | add v v' hv hv' =>
              have e1 := LinearMap.map_add₂ (GBR.mk Γ (a + b) c d) v v' x
              calc gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                    (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                    (GBR.mk Γ (a + b) c d (v + v') x) p)
                  = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                      (GBR.mk Γ (a + b) c d v x + GBR.mk Γ (a + b) c d v' x) p) :=
                    congrArg (fun z => gV3StepB K Γ a b c d e (τ •
                      RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                        (FusionColumn (Γ.fuse (a + b + c + d) e)) z p)) e1
                _ = gV3StepB K Γ a b c d e (τ • (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v x) p
                      + RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v' x) p)) := by
                    rw [LinearMap.map_add₂]
                _ = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v x) p
                      + τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v' x) p) :=
                    congrArg (gV3StepB K Γ a b c d e) (smul_add τ _ _)
                _ = gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v x) p)
                    + gV3StepB K Γ a b c d e (τ • RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v' x) p) := map_add _ _ _
                _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v x) p)
                    + τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                        (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                        (GBR.mk Γ (a + b) c d v' x) p) := congrArg₂ (· + ·) hv hv'
                _ = τ • (gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                          (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                          (GBR.mk Γ (a + b) c d v x) p)
                      + gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                          (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                          (GBR.mk Γ (a + b) c d v' x) p)) := (smul_add τ _ _).symm
                _ = τ • gV3StepB K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
                      (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
                      (GBR.mk Γ (a + b) c d (v + v') x) p) :=
                    congrArg (fun z => τ • gV3StepB K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                        (FusionColumn (Γ.fuse (a + b + c + d) e)) z p)) e1.symm
          | homogeneous xv =>
              exact gV3StepB_leaf K Γ a b c d e xv.2 x p hτ



noncomputable def gV3StepC :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)
      ≃ₗ[K] RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) :=
  RelTensor.mapEquivRight K (gq2rCast K Γ (a + b) c d e) (gq2rCast_bcSlot K Γ (a + b) c d e)

theorem gV3StepC_leaf {j k : ZMod 2} {v : FusionColumn (Γ.fuse c d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse c d) j)
    (n : GQ2rInner K Γ (a + b) c d e)
    {τ : (Γ.D (a + b)).carrier} (hτ : τ ∈ (Γ.D (a + b)).grading k) :
    gV3StepC K Γ a b c d e
        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gq2rInnerSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ2rInner K Γ (a + b) c d e) v n))
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gblSuperComm K Γ a b c d e)) τ
          (gV3StepC K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (GQ2rInner K Γ (a + b) c d e) v n)) := by
  have step1 : midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
          (gq2rInnerSuperComm K Γ a b c d e)) τ
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GQ2rInner K Γ (a + b) c d e) v n)
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ2rInner K Γ (a + b) c d e) v (τ • n) :=
    midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gq2rInnerSuperComm K Γ a b c d e)) hv hτ n
  have keyAssoc2 : gV3StepC K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2rInner K Γ (a + b) c d e) v n)
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBL Γ (a + b) (c + d) e) v (gq2rCast K Γ (a + b) c d e n) := rfl
  have step2 : gq2rCast K Γ (a + b) c d e (τ • n) = τ • gq2rCast K Γ (a + b) c d e n :=
    gq2rCast_aSlot K Γ (a + b) c d e τ n
  have keyTarget : midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
          (gblSuperComm K Γ a b c d e)) τ
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBL Γ (a + b) (c + d) e) v (gq2rCast K Γ (a + b) c d e n))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ (a + b) (c + d) e) v (τ • gq2rCast K Γ (a + b) c d e n) :=
    midEnd_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
        (gblSuperComm K Γ a b c d e)) hv hτ (gq2rCast K Γ (a + b) c d e n)
  have keyAssoc1 : gV3StepC K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (GQ2rInner K Γ (a + b) c d e) v (τ • n))
      = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (GBL Γ (a + b) (c + d) e) v (gq2rCast K Γ (a + b) c d e (τ • n)) := rfl
  calc gV3StepC K Γ a b c d e
        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gq2rInnerSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ2rInner K Γ (a + b) c d e) v n))
      = gV3StepC K Γ a b c d e (((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ2rInner K Γ (a + b) c d e) v (τ • n)) := congrArg (gV3StepC K Γ a b c d e) step1
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • gV3StepC K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GQ2rInner K Γ (a + b) c d e) v (τ • n)) := map_zsmul _ _ _
    _ = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ (a + b) (c + d) e) v (gq2rCast K Γ (a + b) c d e (τ • n)) :=
        congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·) keyAssoc1
    _ = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ (a + b) (c + d) e) v (τ • gq2rCast K Γ (a + b) c d e n) :=
        congrArg (fun z => ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ (a + b) (c + d) e) v z) step2
    _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gblSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBL Γ (a + b) (c + d) e) v (gq2rCast K Γ (a + b) c d e n)) := keyTarget.symm


theorem gV3StepC_aSlot {k : ZMod 2} {τ : (Γ.D (a + b)).carrier}
    (hτ : τ ∈ (Γ.D (a + b)).grading k)
    (m : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)) :
    gV3StepC K Γ a b c d e
        (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gq2rInnerSuperComm K Γ a b c d e)) τ m)
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gblSuperComm K Γ a b c d e)) τ (gV3StepC K Γ a b c d e m) := by
  induction m using RelTensor.induction_on with
  | zero => simp only [map_zero]
  | add m m' hm hm' => simp only [map_add, hm, hm']
  | mk v n =>
      induction v using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse c d))
          with
      | zero =>
          have e0 : (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GQ2rInner K Γ (a + b) c d e) (0 : FusionColumn (Γ.fuse c d)) n : _)
              = (0 : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (GQ2rInner K Γ (a + b) c d e)) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (c + d)).carrier
              (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e))) n).trans
              (LinearMap.zero_apply _)
          calc gV3StepC K Γ a b c d e
                (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GQ2rInner K Γ (a + b) c d e) (0 : FusionColumn (Γ.fuse c d)) n))
              = gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ 0) :=
                congrArg (fun z => gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ z)) e0
            _ = gV3StepC K Γ a b c d e 0 := by rw [map_zero]
            _ = 0 := map_zero _
            _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ 0 := (map_zero _).symm
            _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ2rInner K Γ (a + b) c d e) (0 : FusionColumn (Γ.fuse c d)) n)) :=
                congrArg (fun z => midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e z)) e0.symm
      | add v v' hv hv' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (c + d)).carrier
            (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e)) v v' n
          calc gV3StepC K Γ a b c d e
                (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GQ2rInner K Γ (a + b) c d e) (v + v') n))
              = gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GQ2rInner K Γ (a + b) c d e) v n
                      + RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                        (GQ2rInner K Γ (a + b) c d e) v' n)) :=
                congrArg (fun z => gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ z)) e1
            _ = gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ2rInner K Γ (a + b) c d e) v n)
                  + midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ2rInner K Γ (a + b) c d e) v' n)) := by rw [map_add]
            _ = gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ2rInner K Γ (a + b) c d e) v n))
                + gV3StepC K Γ a b c d e
                  (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                    (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                      (Γ.D (c + d)).grading (gq2rInnerSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ2rInner K Γ (a + b) c d e) v' n)) := map_add _ _ _
            _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) v n))
                + midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) v' n)) :=
                congrArg₂ (· + ·) hv hv'
            _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                      (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) v n)
                    + gV3StepC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                      (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) v' n)) := by
                rw [map_add]
            _ = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ
                  (gV3StepC K Γ a b c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                    (FusionColumn (Γ.fuse c d)) (GQ2rInner K Γ (a + b) c d e) (v + v') n)) :=
                congrArg (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
                  (Γ.D (a + b)).grading (superCommSMul_symm (Γ.D (a + b)).grading
                    (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e)) τ)
                  ((map_add (gV3StepC K Γ a b c d e) _ _).symm.trans
                    (congrArg (gV3StepC K Γ a b c d e) e1.symm))
      | homogeneous xv =>
          exact gV3StepC_leaf K Γ a b c d e xv.2 n hτ


noncomputable instance instModuleE11GBRSlot :
    Module (Γ.D (a + b)).carrier
      (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) :=
  Module.compHom _
    ((midAlgHom (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
      (gbrBslotAslotSuperComm K Γ a b c d e)).toRingHom)

theorem instModuleE11GBRSlot_smul_def (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) :
    τ • n
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (gbrBslotAslotSuperComm K Γ a b c d e) τ n := rfl

/-- **`gE11GBRAssoc`'s D_ab-equivariance, generalized to all `τ` (not just
homogeneous)**: linearity extension of `gE11GBRAssoc_aSlot` via `midEnd`'s
own additivity (`midEnd_zero`/`midEnd_add`), needed for `RelTensor.
mapEquivRight`'s general hypothesis shape. -/
theorem gE11GBRAssoc_aSlot_general (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) :
    gE11GBRAssoc K Γ a b c d e (τ • n) = τ • gE11GBRAssoc K Γ a b c d e n := by
  induction τ using DirectSum.Decomposition.inductionOn (Γ.D (a + b)).grading with
  | zero =>
      calc gE11GBRAssoc K Γ a b c d e ((0 : (Γ.D (a + b)).carrier) • n)
          = gE11GBRAssoc K Γ a b c d e (0 : RelTensor K (Γ.D (c + d)).carrier
              (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (a + b)).carrier) • gE11GBRAssoc K Γ a b c d e n := (zero_smul _ _).symm
  | add τ τ' hτ hτ' =>
      calc gE11GBRAssoc K Γ a b c d e ((τ + τ') • n)
          = gE11GBRAssoc K Γ a b c d e (τ • n + τ' • n) := by rw [add_smul]
        _ = gE11GBRAssoc K Γ a b c d e (τ • n) + gE11GBRAssoc K Γ a b c d e (τ' • n) := map_add _ _ _
        _ = τ • gE11GBRAssoc K Γ a b c d e n + τ' • gE11GBRAssoc K Γ a b c d e n :=
            congrArg₂ (· + ·) hτ hτ'
        _ = (τ + τ') • gE11GBRAssoc K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xτ =>
      rw [instModuleE11GBRSlot_smul_def, V8InnerASlot_smul_def]
      exact gE11GBRAssoc_aSlot K Γ a b c d e xτ.2 n


theorem instModuleGQ2rInnerABSlot_smul_def (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (GQ2rInner K Γ (a + b) c d e)) :
    τ • n
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gq2rInnerSuperComm K Γ a b c d e)) τ n := rfl

noncomputable def gV3AssocBC :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) ≃ₗ[K]
      RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e) :=
  (gV3StepB K Γ a b c d e).trans (gV3StepC K Γ a b c d e)

theorem gV3AssocBC_aSlot_hom {k : ZMod 2} {τ : (Γ.D (a + b)).carrier}
    (hτ : τ ∈ (Γ.D (a + b)).grading k)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gV3AssocBC K Γ a b c d e (τ • n)
      = midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading
            (gblSuperComm K Γ a b c d e)) τ (gV3AssocBC K Γ a b c d e n) := by
  show gV3StepC K Γ a b c d e (gV3StepB K Γ a b c d e (τ • n)) = _
  rw [gV3StepB_aSlot K Γ a b c d e hτ n, instModuleGQ2rInnerABSlot_smul_def,
    gV3StepC_aSlot K Γ a b c d e hτ]
  rfl

theorem gV3AssocBC_aSlot_general (τ : (Γ.D (a + b)).carrier)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gV3AssocBC K Γ a b c d e (τ • n) = τ • gV3AssocBC K Γ a b c d e n := by
  induction τ using DirectSum.Decomposition.inductionOn (Γ.D (a + b)).grading with
  | zero =>
      calc gV3AssocBC K Γ a b c d e ((0 : (Γ.D (a + b)).carrier) • n)
          = gV3AssocBC K Γ a b c d e (0 : RelTensor K (Γ.D (a + b + c + d)).carrier
              (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (a + b)).carrier) • gV3AssocBC K Γ a b c d e n := (zero_smul _ _).symm
  | add τ τ' hτ hτ' =>
      calc gV3AssocBC K Γ a b c d e ((τ + τ') • n)
          = gV3AssocBC K Γ a b c d e (τ • n + τ' • n) := by rw [add_smul]
        _ = gV3AssocBC K Γ a b c d e (τ • n) + gV3AssocBC K Γ a b c d e (τ' • n) := map_add _ _ _
        _ = τ • gV3AssocBC K Γ a b c d e n + τ' • gV3AssocBC K Γ a b c d e n :=
            congrArg₂ (· + ·) hτ hτ'
        _ = (τ + τ') • gV3AssocBC K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xτ =>
      rw [instModuleE11ABSlot_smul_def]
      exact gV3AssocBC_aSlot_hom K Γ a b c d e xτ.2 n

noncomputable def gV3AssocA :
    V3 K Γ a b c d e ≃ₗ[K]
      RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))) :=
  RelTensor.assoc K (Γ.D (a + b)).carrier (Γ.D (a + b + c + d)).carrier
    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e))

noncomputable def gV3AssocABC : V3 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
      (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)) :=
  (gV3AssocA K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (gV3AssocBC K Γ a b c d e) (gV3AssocBC_aSlot_general K Γ a b c d e))

noncomputable def gE11InnerStep :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e)
      ≃ₗ[K] RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e) :=
  PentagonB.smapEquiv K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
    (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
    (gCanonMidSlot K Γ (a + b) (c + d) e)

theorem gE11OuterHg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (a + b)).carrier⦄, τ ∈ (Γ.D (a + b)).grading i →
      ∀ n : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e),
        gE11InnerStep K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ (a + b) (c + d) e * i) : ℤˣ) : ℤ) •
              (τ • gE11InnerStep K Γ a b c d e n) := by
  intro i τ hτ n
  have h := LinearMap.congr_fun
    (smap_comm_midEnd K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (Γ.D (a + b)).grading
      (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e))
      (gbrBslotAslotSuperComm K Γ a b c d e)
      (gTCanon K Γ (a + b) (c + d) e).toLinearMap (gCanonMidSlot K Γ (a + b) (c + d) e)
      (gCanonHphi4 K Γ a b (c + d) e) hτ) n
  rw [instModuleE11ABSlot_smul_def, instModuleE11GBRSlot_smul_def]
  show (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
        (gTCanon K Γ (a + b) (c + d) e).toLinearMap (gParity K Γ (a + b) (c + d) e)
        (gCanonMidSlot K Γ (a + b) (c + d) e))
      (midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
        (superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d)).grading (gblSuperComm K Γ a b c d e))
        τ n)
    = ((sgn (gParity K Γ (a + b) (c + d) e * i) : ℤˣ) : ℤ) •
        midEnd (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) (Γ.D (a + b)).grading
          (gbrBslotAslotSuperComm K Γ a b c d e) τ
          ((smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
              (gTCanon K Γ (a + b) (c + d) e).toLinearMap (gParity K Γ (a + b) (c + d) e)
              (gCanonMidSlot K Γ (a + b) (c + d) e)) n)
  exact h

noncomputable def gE11OuterStep :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e))
      ≃ₗ[K]
      RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e)) :=
  PentagonB.smapEquiv K (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (gE11InnerStep K Γ a b c d e) (gParity K Γ (a + b) (c + d) e) (gE11OuterHg K Γ a b c d e)

noncomputable def gE11FinalStep :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))
      ≃ₗ[K] V8 K Γ a b c d e :=
  RelTensor.mapEquivRight K (gE11GBRAssoc K Γ a b c d e) (gE11GBRAssoc_aSlot_general K Γ a b c d e)

/-- **`E11M`, as a `LinearEquiv`**: `V3 → V8`, the move `t_{a+b,c+d,e}` —
the composite `gV3AssocABC` (reassociating `V3` to expose `GBL(a+b,c+d,e)`
through the `F_ab`/`F_cd` whiskers) then `gE11InnerStep`/`gE11OuterStep`
(the signed double-nested `(a+b)`/`(c+d)`-mid-action amplification of
`gTCanon Γ (a+b) (c+d) e`) then `gE11FinalStep` (the closing recast onto
`V8`'s exact `GBL(c,d,e) ⊗ F_{ab,c+d+e}` shape). -/
noncomputable def E11Mequiv : V3 K Γ a b c d e ≃ₗ[K] V8 K Γ a b c d e :=
  (gV3AssocABC K Γ a b c d e).trans
    ((gE11OuterStep K Γ a b c d e).trans (gE11FinalStep K Γ a b c d e))

noncomputable def E11M : V3 K Γ a b c d e →ₗ[K] V8 K Γ a b c d e :=
  (E11Mequiv K Γ a b c d e).toLinearMap

theorem E11M_bijective : Function.Bijective (E11M K Γ a b c d e) :=
  (E11Mequiv K Γ a b c d e).bijective

end GaugeChi
end Superfusion
