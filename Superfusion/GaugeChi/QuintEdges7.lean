/-
Superfusion / GaugeChi / QuintEdges7

Milestone M13-2-7 of the abstract `(p, χ)` arc: the final three quintuple
edges `E17M`, `E19M`, `E21M`, continuing `GaugeChi.QuintEdges6` (18 of 21
landed there).

**`E17M` (`V7 → V12`, `t_{a,b+c,d+e}`, faces `PBC`/`PDE`)**: `V7 =
(a(bc))(de)` unfolds directly to `GBR(a,b,c) ⊗_{D_{a+b+c}}
GBR(a+b+c,d,e)`. Route (five stages, `E17Mequiv`):

* `gV7AssocA` (plain `RelTensor.assoc`, reusing `Pentagon.lean`'s own
  generic raw recast instance on `FusionColumn (Γ.fuse a (b+c))` — exactly
  the device `gq2Assoc` already needs): peels `F_{b,c}` off the first
  `GBR`, exposing `F_{a,b+c}` adjacent to `GBR(a+b+c,d,e)`.
* `gV7Swap` (`Bimod.midSwap`, mirroring `gq5Swap`'s/`gV6Swap`'s own
  instantiation with `M := F_{a,b+c}`): exchanges `F_{d,e}` past it,
  landing `F_{d,e} ⊗ (GQ2rInner K Γ a b c (d+e))` — NOT yet the natural
  `GBL Γ a (b+c) (d+e)` (the two differ by the SAME recast `gq2rCast`
  already reconciles in `ChiCanon.lean`, since `a+(b+c) ≠ a+b+c`
  syntactically: the genuine reason this edge needs its own device beyond
  a literal copy of `gV6Swap`/`gq5Swap`).
* `gV7Cast` (`RelTensor.mapEquivRight` of `gq2rCast K Γ a b c (d+e)`, via
  `gq2rCast_dSlot K Γ a b c (d+e)` — BOTH already public and fully
  generic in `ChiCanon.lean`'s own 4th argument, reused VERBATIM at the
  shifted instantiation `d := d+e`, zero new content): closes the recast,
  landing `F_{d,e} ⊗ GBL Γ a (b+c) (d+e)`.
* `gE17InnerStep` (`PentagonB.smapEquiv` of `gTCanon Γ a (b+c) (d+e)` at
  its own `(d+e)`-slot, via `gCanonHphi5`): the `(d+e)`-slot move, landing
  `GBR Γ a (b+c) (d+e)`.
* `gE17OuterStep` (`PentagonB.smapEquiv` of `gE17InnerStep` at the outer
  `(b+c)`-slot, hypothesis assembled from `smap_comm_midEnd` +
  `gCanonMidSlot` — `(b+c)` is `gTCanon`'s own MIDDLE argument here,
  unlike `E11M`/`E14M`'s outer-`FIRST`-argument wraps, so this needs a
  genuinely new supercommutation instantiation, `gblQslotRslotSuperComm`
  (`GBL`'s own `Q`-slot vs `R`-slot, one `leftActionEnd_leftActionEnd_
  supercomm` application mirroring `QuintEdges4`'s `gblSuperComm`) in
  place of `E14M`'s `gblPslotRslotSuperComm`.

Both wrap layers (`gV7Swap`/`gV7Cast`, wrapped by the outer `F_{b,c}`
spectator via `gV7AssocA`) need their OWN naturality w.r.t. `(b+c)`,
proved via nested induction to the fully-homogeneous generator — the
`gV7Swap`-side one (`gV7Swap_leaf`/`_aSlot`) needs a fresh `GQ2rInner`-vs-
`(b+c)` supercommutation (`gq2rInnerBCSlotDESlotSuperComm`, a
`leftActionEnd_anticommutes_midAlgHom` application mirroring
`QuintEdges4`'s `gbrCslotAslotSuperComm`); the `gV7Cast`-side one
(`gV7Cast_leaf`/`_aSlot`) bridges the two SIGN LAWS via `gq2rCast_bcSlot`
(ALSO already public and generic, reused verbatim) — sign-free, mirroring
`E11M`'s `gV3StepC_leaf`/`_aSlot` with the roles of `ChiCanon.lean`'s two
unconditional `gq2rCast` commutation laws (`_bcSlot`/`_dSlot`) transposed.

The closing step reuses `Pentagon.lean`'s `gq4Close` VERBATIM at the
shifted instantiation `(a, b+c, d, e)`: `GQ4r K Γ a (b+c) d e` unfolds to
exactly `gE17OuterStep`'s own codomain's inner factor, and `GQ4 K Γ a
(b+c) d e` unfolds to exactly `V12`'s own inner structure (`GBR(b+c,d,e)
⊗_{D_{bcde}} F_{a,bcde}`) — discovered by direct unfold comparison (the
"reuse-at-shifted-instantiation" device `QuintEdges5`/`6` already
established for `gq4Close`/`gCanonMidSlot`/`gFourCast`). The outer
`(b+c)`-wrap of `gq4Close` is UNSIGNED (`RelTensor.mapEquivRight`,
mirroring `gE14FinalStep`'s own net-unsigned equivariance), needing one
fresh instance (`instModuleGQ4BCSlot`, `D_{b+c}` reaching `GQ4`'s own
first `GBR` factor via its ALREADY-SIGNED aslot, passed through unsigned
via `leftActionEnd`) since `GQ4 K Γ a (b+c) d e` is not literally any of
`Quint.lean`'s named `V*Inner` types.

`gV12Assoc` (mirroring `gV3AssocA`/`gV10Assoc`/`gV11Assoc`: a SINGLE,
cast-free `RelTensor.assoc`, since `GBR Γ (b+c) d e`'s own recast total
`D_{(b+c)+d+e} = D_{b+c+d+e}` syntactically) closes `V12`.
-/
import Superfusion.GaugeChi.QuintEdges6

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

/-! ### `E17M` toolkit piece 1: `gV7AssocA`, peeling `F_{b,c}` off `V7` -/

/-- **`gV7AssocA`**: `V7`'s own re-association, exposing `F_{a,b+c} ⊗
GBR(a+b+c,d,e)` under the `F_{b,c}`-whisker — a single `RelTensor.assoc`,
reusing `Pentagon.lean`'s own generic raw recast instance `Module
((Γ.D (a+b+c)).carrier)ᵐᵒᵖ (FusionColumn (Γ.fuse a (b+c)))` (needed for
`gq2Assoc` itself, hence already public and in scope) and `GBR`'s own
generic `aslot` instance on `GBR Γ (a+b+c) d e`. -/
noncomputable def gV7AssocA : V7 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e)) :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)

/-! ### `E17M` toolkit piece 2: the middle swap `gV7Swap` -/

private theorem gV7LawA :
    MidSignLaw K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse d e)) := by
  intro l i x hx n hn p
  exact GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := a + b + c) (b := d) (c := e) hx hn p

/-- **`gV7LawB`**: `D_{d+e}` acting on `GQ2rInner K Γ a b c (d+e)` (via its
OWN already-public signed `d`-slot instance, `GQ2rInner.dslotModule`,
`PentagonEdgeEquiv.lean` — generic in `ChiCanon.lean`'s own 4th argument,
reused VERBATIM at `d := d+e`) is a Koszul-signed middle action against
`F_{a,b+c}`'s degree — exactly `MidSignLaw`'s shape, discharged by
`GQ2rInner.dslot_smul_of_mem` (ALSO already public and generic). -/
private theorem gV7LawB :
    MidSignLaw K (Γ.D (d + e)).carrier (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) (d + e)))
      (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse a (b + c))) := by
  intro l i z hz m hm p
  exact GE2.GQ2rInner.dslot_smul_of_mem K Γ a b c (d + e) hz hm p

/-- **`gV7Swap`**: the middle swap exposing `GQ2rInner K Γ a b c (d+e)`
from `V7`'s own reassociated structure `F_{a,b+c} ⊗_{D_{a+b+c}}
GBR(a+b+c,d,e)` (mirroring `gq5Swap`'s/`gV6Swap`'s own instantiation of
`Bimod.midSwap`, with the raw first factor `F_{a,b+c}` in place of
`F_{c,d}`/`F_{a+b,c}`). Lands `GQ2rInner`, NOT `GBL Γ a (b+c) (d+e)`
directly — `gV7Cast` (below) closes the gap. -/
noncomputable def gV7Swap :
    RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ2rInner K Γ a b c (d + e)) :=
  midSwap K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse a (b + c)))
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse (a + b + c) (d + e)))
    (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse d e))
    (gV7LawA K Γ a b c d e) (gV7LawB K Γ a b c d e)

theorem gV7Swap_mk_of_mem {i j : ZMod 2} {u : FusionColumn (Γ.fuse a (b + c))}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a (b + c)) i) {v : FusionColumn (Γ.fuse d e)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j) (p : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    gV7Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * i) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e))
            v (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p) :=
  midSwapMap_mk_of_mem K (Γ.D (a + b + c)).carrier (Γ.D (d + e)).carrier
    (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse d e))
    (FusionColumn (Γ.fuse (a + b + c) (d + e))) (Γ.D (a + b + c)).grading (Γ.D (d + e)).grading
    (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse d e))
    (gV7LawA K Γ a b c d e) (gV7LawB K Γ a b c d e) hv hu p

/-! ### `E17M` toolkit piece 3: the outer `(b+c)`-slot on `gV7Swap`'s
domain, and `gV7Swap`'s own `(b+c)`-equivariance -/

/-- The `(b+c)`-slot on `gV7Swap`'s domain: reaches through the SECOND
factor `F_{a,b+c}`'s own natural `P₂`-slot (`instModuleSlotRight`,
`FusionColumn.lean`), `leftActionEnd`, UNSIGNED at the outer level. -/
noncomputable instance instModuleE17BCSlot :
    Module (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e)) :=
  Module.compHom _
    ((leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e) (B := (Γ.D (b + c)).carrier)).toRingHom)

theorem instModuleE17BCSlot_smul_def (x : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    x • n
      = leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) x n := rfl

/-- **The `IsScalarTower` witness for `GQ2rInner`'s own automatic
`(b+c)`-slot** (found via `Bimod.OuterActions`'s file-local `leftModule`
instance, reaching `F_{a,b+c}`'s own `P₂`-slot): needed as a side
condition for `midAlgHom` to typecheck against `N := GQ2rInner K Γ a b c
(d+e)` below (mirrors `QuintEdges4`'s `instIsScalarTowerGQ2rInnerABSlot`,
at the `P₂`- instead of `P₁`-slot). -/
instance instIsScalarTowerGQ2rInnerBCSlot :
    IsScalarTower K (Γ.D (b + c)).carrier (GQ2rInner K Γ a b c (d + e)) :=
  ⟨fun k' x n => by
    show (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) (k' • x)) n
      = k' • (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) x) n
    rw [map_smul, LinearMap.smul_apply]⟩

/-- **`GQ2rInner`'s own `(b+c)`-slot vs `(d+e)`-slot supercommutation**
(the `gblPslotRslotSuperComm` mirror — `D_{b+c}` reaches `M = F_{a,b+c}`
directly via its own `P₂`-slot `leftActionEnd` [UNSIGNED internally], and
`D_{d+e}` reaches `N` via `GQ2rInner`'s own signed `d`-slot `midAlgHom`
[at `d := d+e`]: one `leftActionEnd_anticommutes_midAlgHom` application,
`D_{b+c}` FIRST to match `leftActionEnd`'s own natural orientation). -/
theorem gq2rInnerBCSlotDESlotSuperComm :
    SuperCommSMul (Γ.D (b + c)).grading (Γ.D (d + e)).grading (GQ2rInner K Γ a b c (d + e)) := by
  intro i k τ y hτ hy w
  show (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + b + c) (d + e))) τ)
      ((midAlgHom (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse a (b + c)))
          (Γ.D (d + e)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + b + c) (d + e))) y) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((midAlgHom (Γ.D (a + b + c)).grading (FusionColumn.grading (Γ.fuse a (b + c)))
            (Γ.D (d + e)).grading
            (FusionColumn.superCommSMul (Γ.fuse (a + b + c) (d + e))) y)
          ((leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) τ) w))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (a + b + c)).grading
    (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D (d + e)).grading (Γ.D (b + c)).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b + c) (d + e)))
    (⟨τ, hτ⟩ : (Γ.D (b + c)).grading i) (⟨y, hy⟩ : (Γ.D (d + e)).grading k)
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow, show k * i = i * k from mul_comm k i]
  rfl

noncomputable instance instModuleE17GQ2rInnerBCSlot :
    Module (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ2rInner K Γ a b c (d + e))) :=
  Module.compHom _
    ((midAlgHom (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e))).toRingHom)

theorem instModuleE17GQ2rInnerBCSlot_smul_def (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GQ2rInner K Γ a b c (d + e))) :
    τ • n
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ n := rfl

theorem gV7Swap_leaf {i j k : ZMod 2} {u : FusionColumn (Γ.fuse a (b + c))}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a (b + c)) i)
    {v : FusionColumn (Γ.fuse d e)} (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j)
    (p : FusionColumn (Γ.fuse (a + b + c) (d + e)))
    {x : (Γ.D (b + c)).carrier} (hx : x ∈ (Γ.D (b + c)).grading k) :
    gV7Swap K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = x • gV7Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)) := by
  have step1 : x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p) :=
    leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e) x u (GBR.mk Γ (a + b + c) d e v p)
  have hxu : x • u ∈ FusionColumn.grading (Γ.fuse a (b + c)) (k + i) := by
    have hmem := SetLike.GradedSMul.smul_mem (A := (Γ.D (b + c)).grading)
      (B := FusionColumn.grading (Γ.fuse a (b + c))) hx hu
    rwa [vadd_eq_add] at hmem
  let vGen1 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GQ2rInner K Γ a b c (d + e)) :=
    RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) (x • u) p)
  let vGen2 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
      (GQ2rInner K Γ a b c (d + e)) :=
    RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)
  have keyL : gV7Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * (k + i)) : ℤˣ) : ℤ) • vGen1 :=
    gV7Swap_mk_of_mem K Γ a b c d e hxu hv p
  have keyR0 : gV7Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = ((sgn (j * i) : ℤˣ) : ℤ) • vGen2 :=
    gV7Swap_mk_of_mem K Γ a b c d e hu hv p
  have keyTarget : x • vGen2 = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 := by
    have step := midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) hv hx
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)
    have hleft : (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p : GQ2rInner K Γ a b c (d + e)))
        = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) (x • u) p :=
      leftActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) x u p
    calc x • vGen2
        = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
            (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) x vGen2 := rfl
      _ = ((sgn (k * j) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GQ2rInner K Γ a b c (d + e)) v
              (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) u p)) := step
      _ = ((sgn (k * j) : ℤˣ) : ℤ) • vGen1 :=
          congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·)
            (congrArg (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GQ2rInner K Γ a b c (d + e)) v) hleft)
  have hcomm : x • (((sgn (j * i) : ℤˣ) : ℤ) • vGen2)
      = ((sgn (j * i) : ℤˣ) : ℤ) • (x • vGen2) := by
    rw [instModuleE17GQ2rInnerBCSlot_smul_def, instModuleE17GQ2rInnerBCSlot_smul_def, map_zsmul]
  calc gV7Swap K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p))
      = gV7Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) (x • u) (GBR.mk Γ (a + b + c) d e v p)) := by rw [step1]
    _ = ((sgn (j * (k + i)) : ℤˣ) : ℤ) • vGen1 := keyL
    _ = ((sgn (j * k + j * i) : ℤˣ) : ℤ) • vGen1 := by rw [mul_add]
    _ = ((sgn (k * j + j * i) : ℤˣ) : ℤ) • vGen1 := by rw [show k * j = j * k from mul_comm k j]
    _ = ((sgn (k * j) : ℤˣ) * (sgn (j * i) : ℤˣ) : ℤ) • vGen1 := by rw [← Units.val_mul, ← sgn_add]
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • (((sgn (j * i) : ℤˣ) : ℤ) • vGen1) := by rw [smul_smul]
    _ = ((sgn (j * i) : ℤˣ) : ℤ) • (((sgn (k * j) : ℤˣ) : ℤ) • vGen1) := smul_comm _ _ _
    _ = ((sgn (j * i) : ℤˣ) : ℤ) • (x • vGen2) := by rw [← keyTarget]
    _ = x • (((sgn (j * i) : ℤˣ) : ℤ) • vGen2) := hcomm.symm
    _ = x • gV7Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) u (GBR.mk Γ (a + b + c) d e v p)) := by rw [keyR0]

/-- **`gV7Swap`'s `(a+b)`-equivariance, for homogeneous `x`** (the nested
`RelTensor.induction_on`/`DirectSum.Decomposition.inductionOn` descent to
the leaf `gV7Swap_leaf`, mirroring `gE11GBRAssoc_aSlot`'s discipline). -/
theorem gV7Swap_aSlot {k : ZMod 2} {x : (Γ.D (b + c)).carrier}
    (hx : x ∈ (Γ.D (b + c)).grading k)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    gV7Swap K Γ a b c d e (x • n) = x • gV7Swap K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | mk u v =>
      induction u using DirectSum.Decomposition.inductionOn
          (FusionColumn.grading (Γ.fuse a (b + c))) with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse a (b + c))) v
              = (0 : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (GBR Γ (a + b + c) d e)) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e))) v).trans
              (LinearMap.zero_apply _)
          calc gV7Swap K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse a (b + c))) v)
              = gV7Swap K Γ a b c d e (x • (0 : RelTensor K (Γ.D (a + b + c)).carrier
                  (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e))) :=
                congrArg (fun z => gV7Swap K Γ a b c d e (x • z)) e0
            _ = gV7Swap K Γ a b c d e 0 := congrArg (gV7Swap K Γ a b c d e) (smul_zero x)
            _ = 0 := map_zero _
            _ = x • (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ2rInner K Γ a b c (d + e))) := (smul_zero x).symm
            _ = x • gV7Swap K Γ a b c d e 0 := congrArg (fun z => x • z) (map_zero _).symm
            _ = x • gV7Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) (0 : FusionColumn (Γ.fuse a (b + c))) v) :=
                congrArg (fun z => x • gV7Swap K Γ a b c d e z) e0.symm
      | add u u' hu hu' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)) u u' v
          calc gV7Swap K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (GBR Γ (a + b + c) d e) (u + u') v)
              = gV7Swap K Γ a b c d e
                  (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) u v
                    + RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) u' v)) :=
                congrArg (fun z => gV7Swap K Γ a b c d e (x • z)) e1
            _ = gV7Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u v
                  + x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u' v) :=
                congrArg (gV7Swap K Γ a b c d e) (smul_add x _ _)
            _ = gV7Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u v)
                + gV7Swap K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u' v) := map_add _ _ _
            _ = x • gV7Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u v)
                + x • gV7Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) u' v) := congrArg₂ (· + ·) hu hu'
            _ = x • (gV7Swap K Γ a b c d e
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) u v)
                  + gV7Swap K Γ a b c d e
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) u' v)) := (smul_add x _ _).symm
            _ = x • gV7Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) (u + u') v) :=
                congrArg (fun z => x • gV7Swap K Γ a b c d e z) e1.symm
      | homogeneous xu =>
          induction v using RelTensor.induction_on with
          | zero =>
              have e0 : (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                    (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                    (0 : GBR Γ (a + b + c) d e) : _)
                  = (0 : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e)) :=
                map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                  (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))))
              calc gV7Swap K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                      (0 : GBR Γ (a + b + c) d e))
                  = gV7Swap K Γ a b c d e (x • (0 : RelTensor K (Γ.D (a + b + c)).carrier
                      (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e))) :=
                    congrArg (fun z => gV7Swap K Γ a b c d e (x • z)) e0
                _ = 0 := by rw [smul_zero, map_zero]
                _ = x • gV7Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                        (0 : GBR Γ (a + b + c) d e)) := by
                    rw [e0, map_zero, smul_zero]
          | add v v' hv hv' =>
              have e1 := map_add (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                (xu : FusionColumn (Γ.fuse a (b + c)))) v v'
              calc gV7Swap K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) (v + v'))
                  = gV7Swap K Γ a b c d e
                      (x • (RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse a (b + c))) v
                        + RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v')) :=
                    congrArg (fun z => gV7Swap K Γ a b c d e (x • z)) e1
                _ = gV7Swap K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v)
                    + gV7Swap K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v') := by
                    rw [smul_add, map_add]
                _ = x • gV7Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v)
                    + x • gV7Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v') :=
                    congrArg₂ (· + ·) hv hv'
                _ = x • (gV7Swap K Γ a b c d e
                        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v)
                      + gV7Swap K Γ a b c d e
                        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                          (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) v')) :=
                    (smul_add x _ _).symm
                _ = x • gV7Swap K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c))) (v + v')) :=
                    congrArg (fun z => x • gV7Swap K Γ a b c d e z) e1.symm
          | mk v p =>
              induction v using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse d e)) with
              | zero =>
                  have e0 : (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p
                        : GBR Γ (a + b + c) d e)
                      = (0 : GBR Γ (a + b + c) d e) :=
                    (LinearMap.congr_fun (map_zero (GBR.mk Γ (a + b + c) d e)) p).trans
                      (LinearMap.zero_apply _)
                  calc gV7Swap K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse a (b + c)))
                          (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p))
                      = gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) (0 : GBR Γ (a + b + c) d e)) :=
                        congrArg (fun z => gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) z)) e0
                    _ = x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                            (0 : GBR Γ (a + b + c) d e)) := by
                        have e0' : (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse a (b + c))) (0 : GBR Γ (a + b + c) d e) : _)
                            = (0 : RelTensor K (Γ.D (a + b + c)).carrier
                                (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)) :=
                          map_zero (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))))
                        rw [e0']
                        simp
                    _ = x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                            (GBR.mk Γ (a + b + c) d e (0 : FusionColumn (Γ.fuse d e)) p)) :=
                        congrArg (fun z => x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) z)) e0.symm
              | add v v' hv hv' =>
                  have e1 := LinearMap.map_add₂ (GBR.mk Γ (a + b + c) d e) v v' p
                  calc gV7Swap K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                          (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                          (xu : FusionColumn (Γ.fuse a (b + c)))
                          (GBR.mk Γ (a + b + c) d e (v + v') p))
                      = gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c)))
                            (GBR.mk Γ (a + b + c) d e v p + GBR.mk Γ (a + b + c) d e v' p)) :=
                        congrArg (fun z => gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) z)) e1
                    _ = gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) (GBR.mk Γ (a + b + c) d e v p))
                        + gV7Swap K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) (GBR.mk Γ (a + b + c) d e v' p)) := by
                        rw [map_add, smul_add, map_add]
                    _ = x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                            (GBR.mk Γ (a + b + c) d e v p))
                        + x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                            (GBR.mk Γ (a + b + c) d e v' p)) := congrArg₂ (· + ·) hv hv'
                    _ = x • (gV7Swap K Γ a b c d e
                            (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse a (b + c))) (GBR.mk Γ (a + b + c) d e v p))
                          + gV7Swap K Γ a b c d e
                            (RelTensor.mk K (Γ.D (a + b + c)).carrier
                              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                              (xu : FusionColumn (Γ.fuse a (b + c))) (GBR.mk Γ (a + b + c) d e v' p))) :=
                        (smul_add x _ _).symm
                    _ = x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                            (GBR Γ (a + b + c) d e) (xu : FusionColumn (Γ.fuse a (b + c)))
                            (GBR.mk Γ (a + b + c) d e (v + v') p)) :=
                        congrArg (fun z => x • gV7Swap K Γ a b c d e
                          (RelTensor.mk K (Γ.D (a + b + c)).carrier
                            (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
                            (xu : FusionColumn (Γ.fuse a (b + c))) z)) e1.symm
              | homogeneous xv =>
                  exact gV7Swap_leaf K Γ a b c d e xu.2 xv.2 p hx

/-- **`gV7Swap`'s `(a+b)`-equivariance, generalized to all `x`** (linearity
extension via `x`'s own `DirectSum.Decomposition.inductionOn`, mirroring
`gE11GBRAssoc_aSlot_general`). -/
theorem gV7Swap_aSlot_general (x : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    gV7Swap K Γ a b c d e (x • n) = x • gV7Swap K Γ a b c d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (b + c)).grading with
  | zero =>
      calc gV7Swap K Γ a b c d e ((0 : (Γ.D (b + c)).carrier) • n)
          = gV7Swap K Γ a b c d e (0 : RelTensor K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (b + c)).carrier) • gV7Swap K Γ a b c d e n := (zero_smul _ _).symm
  | add x x' hx hx' =>
      calc gV7Swap K Γ a b c d e ((x + x') • n)
          = gV7Swap K Γ a b c d e (x • n + x' • n) := by rw [add_smul]
        _ = gV7Swap K Γ a b c d e (x • n) + gV7Swap K Γ a b c d e (x' • n) := map_add _ _ _
        _ = x • gV7Swap K Γ a b c d e n + x' • gV7Swap K Γ a b c d e n :=
            congrArg₂ (· + ·) hx hx'
        _ = (x + x') • gV7Swap K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xx =>
      exact gV7Swap_aSlot K Γ a b c d e xx.2 n


/-! ### `E17M` toolkit piece 4: `gV7Cast`, closing the recast -/

/-- **`gV7Cast`**: closes the recast between `gV7Swap`'s landing spot
`GQ2rInner K Γ a b c (d+e)` and the natural `GBL Γ a (b+c) (d+e)` — a
single `RelTensor.mapEquivRight` of `gq2rCast K Γ a b c (d+e)`, via
`gq2rCast_dSlot K Γ a b c (d+e)` (BOTH already public and fully generic
in `ChiCanon.lean`'s own 4th argument, reused VERBATIM at the shifted
instantiation `d := d+e` — zero new content). -/
noncomputable def gV7Cast :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e))
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBL Γ a (b + c) (d + e)) :=
  RelTensor.mapEquivRight K (gq2rCast K Γ a b c (d + e)) (gq2rCast_dSlot K Γ a b c (d + e))

/-! ### `E17M` toolkit piece 5: `GBL`'s own `Q`-slot vs `R`-slot
supercommutation (the `gblPslotRslotSuperComm` mirror, at `GBL`'s SECOND
argument instead of its first — needed for the outer `(b+c)`-wrap of
`gV7Cast`'s CODOMAIN `GBL Γ a (b+c) (d+e)`, matching its own `q`-argument,
not its `p`-argument). -/

theorem gblQslotRslotSuperComm :
    SuperCommSMul (Γ.D (b + c)).grading (Γ.D (d + e)).grading (GBL Γ a (b + c) (d + e)) := by
  intro i k x τ hx hτ w
  show (leftActionEnd K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
      (FusionColumn (Γ.fuse (a + (b + c)) (d + e))) x)
      ((midAlgHom (Γ.D (a + (b + c))).grading (FusionColumn.grading (Γ.fuse a (b + c)))
          (Γ.D (d + e)).grading
          (FusionColumn.superCommSMul (Γ.fuse (a + (b + c)) (d + e))) τ) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((midAlgHom (Γ.D (a + (b + c))).grading (FusionColumn.grading (Γ.fuse a (b + c)))
            (Γ.D (d + e)).grading
            (FusionColumn.superCommSMul (Γ.fuse (a + (b + c)) (d + e))) τ)
          ((leftActionEnd K (Γ.D (a + (b + c))).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + (b + c)) (d + e))) x) w))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  have h := leftActionEnd_anticommutes_midAlgHom (Γ.D (a + (b + c))).grading
    (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D (d + e)).grading
    (Γ.D (b + c)).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + (b + c)) (d + e)))
    (⟨x, hx⟩ : (Γ.D (b + c)).grading i) (⟨τ, hτ⟩ : (Γ.D (d + e)).grading k)
  rw [h, Units.smul_def, ← sgn_eq_neg_one_uzpow, show k * i = i * k from mul_comm k i]
  rfl

noncomputable instance instModuleE17GBLBCSlot :
    Module (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))) :=
  Module.compHom _
    ((midAlgHom (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gblQslotRslotSuperComm K Γ a b c d e))).toRingHom)

theorem instModuleE17GBLBCSlot_smul_def (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))) :
    τ • n
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gblQslotRslotSuperComm K Γ a b c d e)) τ n := rfl

/-- **The leaf computation of `gV7Cast`'s `(b+c)`-equivariance**: `gq2rCast
K Γ a b c (d+e)`'s own generator formula is `rfl`-transparent through
`RelTensor.mapEquivRight`'s construction, so this reduces to bridging the
TWO sign laws (`gq2rInnerBCSlotDESlotSuperComm` on the domain,
`gblQslotRslotSuperComm` on the codomain) via `gq2rCast_bcSlot`
(ALREADY public and generic, `ChiCanon.lean`, reused VERBATIM) — mirrors
`E11M`'s `gV3StepC_leaf` with the roles of `gq2rCast`'s two unconditional
commutation laws (`_bcSlot`/`_dSlot`) transposed. -/
theorem gV7Cast_leaf {j k : ZMod 2} {v : FusionColumn (Γ.fuse d e)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j)
    (n : GQ2rInner K Γ a b c (d + e))
    {τ : (Γ.D (b + c)).carrier} (hτ : τ ∈ (Γ.D (b + c)).grading k) :
    gV7Cast K Γ a b c d e
        (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e)) v n))
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gblQslotRslotSuperComm K Γ a b c d e)) τ
          (gV7Cast K Γ a b c d e
            (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GQ2rInner K Γ a b c (d + e)) v n)) := by
  have step1 : midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
        (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
          (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ2rInner K Γ a b c (d + e)) v n)
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e)) v (τ • n) :=
    midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) hv hτ n
  have keyAssoc2 : gV7Cast K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ2rInner K Γ a b c (d + e)) v n)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ a (b + c) (d + e)) v (gq2rCast K Γ a b c (d + e) n) := rfl
  have step2 : gq2rCast K Γ a b c (d + e) (τ • n) = τ • gq2rCast K Γ a b c (d + e) n :=
    gq2rCast_bcSlot K Γ a b c (d + e) τ n
  have keyTarget : midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
          (gblQslotRslotSuperComm K Γ a b c d e)) τ
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ a (b + c) (d + e)) v (gq2rCast K Γ a b c (d + e) n))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) v (τ • gq2rCast K Γ a b c (d + e) n) :=
    midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gblQslotRslotSuperComm K Γ a b c d e)) hv hτ (gq2rCast K Γ a b c (d + e) n)
  have keyAssoc1 : gV7Cast K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GQ2rInner K Γ a b c (d + e)) v (τ • n))
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ a (b + c) (d + e)) v (gq2rCast K Γ a b c (d + e) (τ • n)) := rfl
  calc gV7Cast K Γ a b c d e
        (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e)) v n))
      = gV7Cast K Γ a b c d e (((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e)) v (τ • n)) := congrArg (gV7Cast K Γ a b c d e) step1
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • gV7Cast K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ2rInner K Γ a b c (d + e)) v (τ • n)) := map_zsmul _ _ _
    _ = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) v (gq2rCast K Γ a b c (d + e) (τ • n)) :=
        congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·) keyAssoc1
    _ = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) v (τ • gq2rCast K Γ a b c (d + e) n) :=
        congrArg (fun z => ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) v z) step2
    _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gblQslotRslotSuperComm K Γ a b c d e)) τ
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) v (gq2rCast K Γ a b c (d + e) n)) := keyTarget.symm

theorem gV7Cast_aSlot {k : ZMod 2} {τ : (Γ.D (b + c)).carrier}
    (hτ : τ ∈ (Γ.D (b + c)).grading k)
    (m : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e))) :
    gV7Cast K Γ a b c d e
        (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ m)
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gblQslotRslotSuperComm K Γ a b c d e)) τ (gV7Cast K Γ a b c d e m) := by
  induction m using RelTensor.induction_on with
  | zero => simp only [map_zero]
  | add m m' hm hm' => simp only [map_add, hm, hm']
  | mk v n =>
      induction v using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse d e))
          with
      | zero =>
          have e0 : (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                (GQ2rInner K Γ a b c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n : _)
              = (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ2rInner K Γ a b c (d + e))) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)))) n).trans
              (LinearMap.zero_apply _)
          calc gV7Cast K Γ a b c d e
                (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GQ2rInner K Γ a b c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n))
              = gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ 0) :=
                congrArg (fun z => gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ z)) e0
            _ = gV7Cast K Γ a b c d e 0 := by rw [map_zero]
            _ = 0 := map_zero _
            _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ 0 := (map_zero _).symm
            _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GQ2rInner K Γ a b c (d + e)) (0 : FusionColumn (Γ.fuse d e)) n)) :=
                congrArg (fun z => midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e z)) e0.symm
      | add v v' hv hv' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (d + e)).carrier
            (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e))) v v' n
          calc gV7Cast K Γ a b c d e
                (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GQ2rInner K Γ a b c (d + e)) (v + v') n))
              = gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GQ2rInner K Γ a b c (d + e)) v n
                      + RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GQ2rInner K Γ a b c (d + e)) v' n)) :=
                congrArg (fun z => gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ z)) e1
            _ = gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GQ2rInner K Γ a b c (d + e)) v n)
                  + midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GQ2rInner K Γ a b c (d + e)) v' n)) := by rw [map_add]
            _ = gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GQ2rInner K Γ a b c (d + e)) v n))
                + gV7Cast K Γ a b c d e
                  (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                    (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gq2rInnerBCSlotDESlotSuperComm K Γ a b c d e)) τ
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GQ2rInner K Γ a b c (d + e)) v' n)) := map_add _ _ _
            _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e (RelTensor.mk K (Γ.D (d + e)).carrier
                    (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v n))
                + midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e (RelTensor.mk K (Γ.D (d + e)).carrier
                    (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v' n)) :=
                congrArg₂ (· + ·) hv hv'
            _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e (RelTensor.mk K (Γ.D (d + e)).carrier
                      (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v n)
                    + gV7Cast K Γ a b c d e (RelTensor.mk K (Γ.D (d + e)).carrier
                      (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) v' n)) := by
                rw [map_add]
            _ = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ
                  (gV7Cast K Γ a b c d e (RelTensor.mk K (Γ.D (d + e)).carrier
                    (FusionColumn (Γ.fuse d e)) (GQ2rInner K Γ a b c (d + e)) (v + v') n)) :=
                congrArg (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                  (Γ.D (b + c)).grading (superCommSMul_symm (Γ.D (b + c)).grading
                    (Γ.D (d + e)).grading (gblQslotRslotSuperComm K Γ a b c d e)) τ)
                  ((map_add (gV7Cast K Γ a b c d e) _ _).symm.trans
                    (congrArg (gV7Cast K Γ a b c d e) e1.symm))
      | homogeneous xv =>
          exact gV7Cast_leaf K Γ a b c d e xv.2 n hτ

/-! ### `E17M` toolkit piece 6: `gV7AssocABC`, wrapping `gV7Swap.trans
gV7Cast` by the outer `F_{b,c}` spectator -/

/-- `gV7Swap` then `gV7Cast`, closing the whole inner reassociation:
`F_{a,b+c} ⊗_{D_{a+b+c}} GBR(a+b+c,d,e) ≃ F_{d,e} ⊗_{D_{d+e}} GBL(a,b+c,d+e)`. -/
noncomputable def gV7SwapCast :
    RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBL Γ a (b + c) (d + e)) :=
  (gV7Swap K Γ a b c d e).trans (gV7Cast K Γ a b c d e)

theorem gV7SwapCast_aSlot_hom {k : ZMod 2} {τ : (Γ.D (b + c)).carrier}
    (hτ : τ ∈ (Γ.D (b + c)).grading k)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    gV7SwapCast K Γ a b c d e (τ • n)
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gblQslotRslotSuperComm K Γ a b c d e)) τ (gV7SwapCast K Γ a b c d e n) := by
  show gV7Cast K Γ a b c d e (gV7Swap K Γ a b c d e (τ • n)) = _
  rw [gV7Swap_aSlot K Γ a b c d e hτ n, instModuleE17GQ2rInnerBCSlot_smul_def,
    gV7Cast_aSlot K Γ a b c d e hτ]
  rfl

theorem gV7SwapCast_aSlot_general (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
      (GBR Γ (a + b + c) d e)) :
    gV7SwapCast K Γ a b c d e (τ • n) = τ • gV7SwapCast K Γ a b c d e n := by
  induction τ using DirectSum.Decomposition.inductionOn (Γ.D (b + c)).grading with
  | zero =>
      calc gV7SwapCast K Γ a b c d e ((0 : (Γ.D (b + c)).carrier) • n)
          = gV7SwapCast K Γ a b c d e (0 : RelTensor K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (b + c)).carrier) • gV7SwapCast K Γ a b c d e n := (zero_smul _ _).symm
  | add τ τ' hτ hτ' =>
      calc gV7SwapCast K Γ a b c d e ((τ + τ') • n)
          = gV7SwapCast K Γ a b c d e (τ • n + τ' • n) := by rw [add_smul]
        _ = gV7SwapCast K Γ a b c d e (τ • n) + gV7SwapCast K Γ a b c d e (τ' • n) := map_add _ _ _
        _ = τ • gV7SwapCast K Γ a b c d e n + τ' • gV7SwapCast K Γ a b c d e n :=
            congrArg₂ (· + ·) hτ hτ'
        _ = (τ + τ') • gV7SwapCast K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xτ =>
      rw [instModuleE17BCSlot_smul_def]
      exact gV7SwapCast_aSlot_hom K Γ a b c d e xτ.2 n

/-- **`gV7AssocABC`**: `V7`'s full reassociation, exposing `F_{b,c} ⊗_{D_{b+c}}
(F_{d,e} ⊗_{D_{d+e}} GBL(a,b+c,d+e))` — `gV7AssocA` then the outer
`(b+c)`-wrap of `gV7SwapCast`. -/
noncomputable def gV7AssocABC : V7 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBL Γ a (b + c) (d + e))) :=
  (gV7AssocA K Γ a b c d e).trans
    (RelTensor.mapEquivRight K (gV7SwapCast K Γ a b c d e) (gV7SwapCast_aSlot_general K Γ a b c d e))

/-! ### `E17M` toolkit piece 7: the move `gTCanon Γ a (b+c) (d+e)`, at its
own `(d+e)`-slot, wrapped by the outer `(b+c)`-slot -/

/-- The `(d+e)`-slot amplification of `gTCanon Γ a (b+c) (d+e)`, landing
`GBR(a,b+c,d+e)` (mirrors `gE14InnerStep`/`gE15Step`, keyed to
`gCanonHphi5`'s `(z+w)`-slot conjunct). -/
noncomputable def gE17InnerStep :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))
      ≃ₗ[K] RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ a (b + c) (d + e)) :=
  PentagonB.smapEquiv K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
    (gTCanon K Γ a (b + c) (d + e)) (gParity K Γ a (b + c) (d + e)) (gCanonHphi5 K Γ a (b + c) d e)

/-- **`GBR`'s own `Q`-slot vs `R`-slot supercommutation** (the
`gbrCslotAslotSuperComm` mirror at `GBR`'s SECOND argument, needed for
`GBR Γ a (b+c) (d+e)`'s own `(b+c)`-slot — `GBR`'s `C`-slot [natural,
matches `d+e`] vs its `B`-slot [natural, matches `b+c`], BOTH reaching
the SAME first raw factor `F_{b+c,d+e}` via `leftActionEnd`: one
`leftActionEnd_leftActionEnd_supercomm` application mirroring
`QuintEdges4`'s `gblSuperComm`, NOT `gbrCslotAslotSuperComm`'s own
`leftActionEnd_anticommutes_midAlgHom` shape — `GBR`'s `A`-slot [the
signed one, matching `a`] is untouched here. -/
theorem gbrQslotCslotSuperComm :
    SuperCommSMul (Γ.D (b + c)).grading (Γ.D (d + e)).grading (GBR Γ a (b + c) (d + e)) := by
  intro i k x y hx hy w
  show (leftActionEnd K (Γ.D ((b + c) + (d + e))).carrier (FusionColumn (Γ.fuse (b + c) (d + e)))
      (FusionColumn (Γ.fuse a ((b + c) + (d + e)))) x)
      ((leftActionEnd K (Γ.D ((b + c) + (d + e))).carrier (FusionColumn (Γ.fuse (b + c) (d + e)))
        (FusionColumn (Γ.fuse a ((b + c) + (d + e)))) y) w)
    = ((sgn (i * k) : ℤˣ) : ℤ) •
        ((leftActionEnd K (Γ.D ((b + c) + (d + e))).carrier (FusionColumn (Γ.fuse (b + c) (d + e)))
          (FusionColumn (Γ.fuse a ((b + c) + (d + e)))) y)
        ((leftActionEnd K (Γ.D ((b + c) + (d + e))).carrier (FusionColumn (Γ.fuse (b + c) (d + e)))
          (FusionColumn (Γ.fuse a ((b + c) + (d + e)))) x) w))
  exact leftActionEnd_leftActionEnd_supercomm
    (Γ.D (b + c)).grading (Γ.D (d + e)).grading (FusionColumn.superCommSMul (Γ.fuse (b + c) (d + e)))
    hx hy w

noncomputable instance instModuleE17GBRBCSlot :
    Module (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) :=
  Module.compHom _
    ((midAlgHom (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gbrQslotCslotSuperComm K Γ a b c d e))).toRingHom)

theorem instModuleE17GBRBCSlot_smul_def (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) :
    τ • n
      = midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gbrQslotCslotSuperComm K Γ a b c d e)) τ n := rfl

/-- **The square hypothesis for `gE17OuterStep`**: `gE17InnerStep`'s own
`(b+c)`-degree equivariance (`smap_comm_midEnd`, general, `QuintEdges4.lean`),
using `gTCanon Γ a (b+c) (d+e)`'s TWO relevant slot conjuncts —
`gCanonHphi5 K Γ a (b+c) d e` for its own `(d+e)`-slot (matching the
smap's own inner degree) and `gCanonMidSlot K Γ a (b+c) (d+e)` for its
own `(b+c)`-slot (matching the outer wrap's degree — `(b+c)` is
`gTCanon`'s OWN MIDDLE argument here, unlike `E11M`/`E14M`'s outer-FIRST-
argument wraps). -/
theorem gE17OuterHg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄, τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e)),
        gE17InnerStep K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a (b + c) (d + e) * i) : ℤˣ) : ℤ) •
              (τ • gE17InnerStep K Γ a b c d e n) := by
  intro i τ hτ n
  have h := LinearMap.congr_fun
    (smap_comm_midEnd K (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gblQslotRslotSuperComm K Γ a b c d e))
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gbrQslotCslotSuperComm K Γ a b c d e))
      (gTCanon K Γ a (b + c) (d + e)).toLinearMap (gCanonHphi5 K Γ a (b + c) d e)
      (gCanonMidSlot K Γ a (b + c) (d + e)) hτ) n
  rw [instModuleE17GBLBCSlot_smul_def, instModuleE17GBRBCSlot_smul_def]
  show (smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (gTCanon K Γ a (b + c) (d + e)).toLinearMap (gParity K Γ a (b + c) (d + e))
        (gCanonHphi5 K Γ a (b + c) d e))
      (midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
        (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
          (gblQslotRslotSuperComm K Γ a b c d e)) τ n)
    = ((sgn (gParity K Γ a (b + c) (d + e) * i) : ℤˣ) : ℤ) •
        midEnd (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
          (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
            (gbrQslotCslotSuperComm K Γ a b c d e)) τ
          ((smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
              (gTCanon K Γ a (b + c) (d + e)).toLinearMap (gParity K Γ a (b + c) (d + e))
              (gCanonHphi5 K Γ a (b + c) d e)) n)
  exact h

/-- The outer `(b+c)`-slot amplification of `gE17InnerStep` (mirrors
`gE11OuterStep`/`gE14OuterStep`). -/
noncomputable def gE17OuterStep :
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ a (b + c) (d + e))) :=
  PentagonB.smapEquiv K (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    (gE17InnerStep K Γ a b c d e) (gParity K Γ a (b + c) (d + e)) (gE17OuterHg K Γ a b c d e)

/-! ### `E17M` toolkit piece 8: the closing step — `gq4Close` reused
VERBATIM at the shifted instantiation `(a, b+c, d, e)` -/

/-- **`gE17FinalStep`**: `Pentagon.lean`'s own `gq4Close`, instantiated at
`(a, b+c, d, e)` — `GQ4r K Γ a (b+c) d e` unfolds to EXACTLY
`gE17OuterStep`'s own codomain's inner factor (`RelTensor K (D_{d+e})
F_{d,e} (GBR Γ a (b+c) (d+e))`), and `GQ4 K Γ a (b+c) d e` unfolds to
EXACTLY `V12`'s own inner structure (`GBR(b+c,d,e) ⊗_{D_{b+c+d+e}}
F_{a,b+c+d+e}`) — no new recast content. -/
noncomputable def gE17FinalStep :
    RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
      ≃ₗ[K] GQ4 K Γ a (b + c) d e :=
  gq4Close K Γ a (b + c) d e

/-- **`GQ4 K Γ a (b+c) d e`'s own `(b+c)`-slot**: `D_{b+c}` reaching `GQ4`'s
own FIRST factor `GBR Γ (b+c) d e` via its ALREADY-SIGNED `aslot`
(`RouteBimod.lean`, generic, since `b+c` plays `GBR`'s own `p`-argument
here), passed through UNSIGNED at the outer wrap level via `leftActionEnd`
(mirrors `instModuleGQ1Total`'s recipe): needs `instSMulCommClassGBRAslotRecast`/
`instIsScalarTowerGBRAslotRecast` (`Quint.lean`, generic, at `p,q,r :=
b+c,d,e`, ALREADY public) as the side conditions `leftActionEnd` needs,
since `GQ4`'s own outer coefficient IS `GBR`'s RECAST total (matching
`instModuleGQ4Total`'s own recipe). -/
noncomputable instance instModuleGQ4BCSlot :
    Module (Γ.D (b + c)).carrier (GQ4 K Γ a (b + c) d e) :=
  Module.compHom
    (RelTensor K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
      (FusionColumn (Γ.fuse a ((b + c) + d + e))))
    ((leftActionEnd K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
      (FusionColumn (Γ.fuse a ((b + c) + d + e))) (B := (Γ.D (b + c)).carrier)).toRingHom)

/-- **The leaf computation of `gE17FinalStep`'s `(b+c)`-equivariance**:
`gq4Close_mk` (sign-free) combined with `GBR.bslot_smul_mk`'s (UNSIGNED,
matching `GBR Γ a (b+c) (d+e)`'s own `Q`-slot=`b+c`) and `GBR.aslot_smul_
mk_of_mem`'s (SIGNED, matching `GBR Γ (b+c) d e`'s own `P`-slot=`b+c`)
Koszul signs — the TWO mechanisms land the SAME combined sign `sgn(k·j)`
(keyed only to `v`'s degree, `w` never shifts, UNLIKE `E14M`'s
`gE14FinalStep_leaf` where `x` shifted `w` — the genuine structural
difference from wrapping `GQ4`'s SECOND vs FIRST pentagon argument). -/
theorem gE17FinalStep_leaf {i j k : ZMod 2} {v : FusionColumn (Γ.fuse d e)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse d e) j)
    {u : FusionColumn (Γ.fuse (b + c) (d + e))}
    (_hu : u ∈ FusionColumn.grading (Γ.fuse (b + c) (d + e)) i)
    (w : FusionColumn (Γ.fuse a ((b + c) + (d + e))))
    {x : (Γ.D (b + c)).carrier} (hx : x ∈ (Γ.D (b + c)).grading k) :
    gE17FinalStep K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w))
      = x • gE17FinalStep K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w)) := by
  have step1 : x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w)
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.mk K (Γ.D (d + e)).carrier
          (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)) v
          (x • GBR.mk Γ a (b + c) (d + e) u w) :=
    midEnd_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e)) (Γ.D (b + c)).grading
      (superCommSMul_symm (Γ.D (b + c)).grading (Γ.D (d + e)).grading
        (gbrQslotCslotSuperComm K Γ a b c d e)) hv hx _
  have step2 : x • GBR.mk Γ a (b + c) (d + e) u w
      = GBR.mk Γ a (b + c) (d + e) (x • u) w :=
    GBR.bslot_smul_mk (Γ := Γ) (a := a) (b := b + c) (c := d + e) x u w
  let vTarget1 : GQ4 K Γ a (b + c) d e :=
    RelTensor.mk K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
      (FusionColumn (Γ.fuse a ((b + c) + d + e))) (GBR.mk Γ (b + c) d e v (x • u))
      (fusionColumnCast K Γ a (add_assoc (b + c) d e).symm w)
  let vTarget2 : GQ4 K Γ a (b + c) d e :=
    RelTensor.mk K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
      (FusionColumn (Γ.fuse a ((b + c) + d + e))) (GBR.mk Γ (b + c) d e v u)
      (fusionColumnCast K Γ a (add_assoc (b + c) d e).symm w)
  have keyClose : gE17FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) (x • u) w))
      = vTarget1 :=
    gq4Close_mk K Γ a (b + c) d e v (x • u) w
  have keyClose2 : gE17FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
        (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w))
      = vTarget2 :=
    gq4Close_mk K Γ a (b + c) d e v u w
  have keyTarget : x • vTarget2 = ((sgn (k * j) : ℤˣ) : ℤ) • vTarget1 := by
    have hshow : x • vTarget2
        = leftActionEnd K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
            (FusionColumn (Γ.fuse a ((b + c) + d + e))) x vTarget2 := rfl
    rw [hshow]
    show leftActionEnd K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
        (FusionColumn (Γ.fuse a ((b + c) + d + e))) x
        (RelTensor.mk K (Γ.D ((b + c) + d + e)).carrier (GBR Γ (b + c) d e)
          (FusionColumn (Γ.fuse a ((b + c) + d + e))) (GBR.mk Γ (b + c) d e v u)
          (fusionColumnCast K Γ a (add_assoc (b + c) d e).symm w))
      = ((sgn (k * j) : ℤˣ) : ℤ) • vTarget1
    rw [leftActionEnd_mk,
      GBR.aslot_smul_mk_of_mem (Γ := Γ) (a := b + c) (b := d) (c := e) hx hv u, map_zsmul,
      LinearMap.smul_apply]
    rfl
  calc gE17FinalStep K Γ a b c d e
        (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w))
      = gE17FinalStep K Γ a b c d e (((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) (x • u) w)) := by
        rw [step1, step2]
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • gE17FinalStep K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) (x • u) w)) := map_zsmul _ _ _
    _ = ((sgn (k * j) : ℤˣ) : ℤ) • vTarget1 := congrArg (((sgn (k * j) : ℤˣ) : ℤ) • ·) keyClose
    _ = x • vTarget2 := keyTarget.symm
    _ = x • gE17FinalStep K Γ a b c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) v (GBR.mk Γ a (b + c) (d + e) u w)) :=
        congrArg (x • ·) keyClose2.symm

theorem gE17FinalStep_aSlot {k : ZMod 2} {x : (Γ.D (b + c)).carrier}
    (hx : x ∈ (Γ.D (b + c)).grading k)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) :
    gE17FinalStep K Γ a b c d e (x • n) = x • gE17FinalStep K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | mk v n' =>
      induction v using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse d e))
          with
      | zero =>
          have e0 : RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                (GBR Γ a (b + c) (d + e)) (0 : FusionColumn (Γ.fuse d e)) n'
              = (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ a (b + c) (d + e))) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))) n').trans
              (LinearMap.zero_apply _)
          calc gE17FinalStep K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ a (b + c) (d + e)) (0 : FusionColumn (Γ.fuse d e)) n')
              = gE17FinalStep K Γ a b c d e (x • (0 : RelTensor K (Γ.D (d + e)).carrier
                  (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))) :=
                congrArg (fun z => gE17FinalStep K Γ a b c d e (x • z)) e0
            _ = gE17FinalStep K Γ a b c d e 0 := congrArg (gE17FinalStep K Γ a b c d e) (smul_zero x)
            _ = 0 := map_zero _
            _ = x • (0 : GQ4 K Γ a (b + c) d e) := (smul_zero x).symm
            _ = x • gE17FinalStep K Γ a b c d e 0 := congrArg (fun z => x • z) (map_zero _).symm
            _ = x • gE17FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) (0 : FusionColumn (Γ.fuse d e)) n') :=
                congrArg (fun z => x • gE17FinalStep K Γ a b c d e z) e0.symm
      | add v v' hv hv' =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (d + e)).carrier
            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) v v' n'
          calc gE17FinalStep K Γ a b c d e
                (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ a (b + c) (d + e)) (v + v') n')
              = gE17FinalStep K Γ a b c d e
                  (x • (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) v n'
                    + RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) v' n')) :=
                congrArg (fun z => gE17FinalStep K Γ a b c d e (x • z)) e1
            _ = gE17FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v n'
                  + x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v' n') :=
                congrArg (gE17FinalStep K Γ a b c d e) (smul_add x _ _)
            _ = gE17FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v n')
                + gE17FinalStep K Γ a b c d e
                  (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v' n') := map_add _ _ _
            _ = x • gE17FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v n')
                + x • gE17FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) v' n') := congrArg₂ (· + ·) hv hv'
            _ = x • (gE17FinalStep K Γ a b c d e
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) v n')
                  + gE17FinalStep K Γ a b c d e
                    (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) v' n')) := (smul_add x _ _).symm
            _ = x • gE17FinalStep K Γ a b c d e
                  (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) (v + v') n') :=
                congrArg (x • ·) ((map_add (gE17FinalStep K Γ a b c d e) _ _).symm.trans
                  (congrArg (gE17FinalStep K Γ a b c d e) e1.symm))
      | homogeneous xv =>
          induction n' using RelTensor.induction_on with
          | zero =>
              have e0 : (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                    (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                    (0 : GBR Γ a (b + c) (d + e)) : _)
                  = (0 : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e))) :=
                map_zero (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)))
              calc gE17FinalStep K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                      (0 : GBR Γ a (b + c) (d + e)))
                  = gE17FinalStep K Γ a b c d e (x • (0 : RelTensor K (Γ.D (d + e)).carrier
                      (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))) :=
                    congrArg (fun z => gE17FinalStep K Γ a b c d e (x • z)) e0
                _ = 0 := by rw [smul_zero, map_zero]
                _ = x • gE17FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                        (0 : GBR Γ a (b + c) (d + e))) := by
                    rw [e0, map_zero, smul_zero]
          | add n' n'' hn' hn'' =>
              have e1 := map_add (RelTensor.mk K (Γ.D (d + e)).carrier
                (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                (xv : FusionColumn (Γ.fuse d e))) n' n''
              calc gE17FinalStep K Γ a b c d e
                    (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                      (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) (n' + n''))
                  = gE17FinalStep K Γ a b c d e
                      (x • (RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                          (xv : FusionColumn (Γ.fuse d e)) n'
                        + RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'')) :=
                    congrArg (fun z => gE17FinalStep K Γ a b c d e (x • z)) e1
                _ = gE17FinalStep K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                    + gE17FinalStep K Γ a b c d e
                      (x • RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'') := by
                    rw [smul_add, map_add]
                _ = x • gE17FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                    + x • gE17FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'') :=
                    congrArg₂ (· + ·) hn' hn''
                _ = x • (gE17FinalStep K Γ a b c d e
                        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n')
                      + gE17FinalStep K Γ a b c d e
                        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                          (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) n'')) :=
                    (smul_add x _ _).symm
                _ = x • gE17FinalStep K Γ a b c d e
                      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                        (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e)) (n' + n'')) :=
                    congrArg (x • ·) ((map_add (gE17FinalStep K Γ a b c d e) _ _).symm.trans
                      (congrArg (gE17FinalStep K Γ a b c d e) e1.symm))
          | mk u w =>
              induction u using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse (b + c) (d + e))) with
              | zero =>
                  have e0 : (GBR.mk Γ a (b + c) (d + e) (0 : FusionColumn (Γ.fuse (b + c) (d + e))) w
                        : GBR Γ a (b + c) (d + e))
                      = (0 : GBR Γ a (b + c) (d + e)) :=
                    (LinearMap.congr_fun (map_zero (GBR.mk Γ a (b + c) (d + e))) w).trans
                      (LinearMap.zero_apply _)
                  calc gE17FinalStep K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                          (xv : FusionColumn (Γ.fuse d e))
                          (GBR.mk Γ a (b + c) (d + e) (0 : FusionColumn (Γ.fuse (b + c) (d + e))) w))
                      = gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (0 : GBR Γ a (b + c) (d + e))) :=
                        congrArg (fun z => gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e0
                    _ = x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (0 : GBR Γ a (b + c) (d + e))) := by
                        have e0' : (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (0 : GBR Γ a (b + c) (d + e)) : _)
                            = (0 : RelTensor K (Γ.D (d + e)).carrier
                                (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) :=
                          map_zero (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)))
                        rw [e0']
                        simp
                    _ = x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ a (b + c) (d + e) (0 : FusionColumn (Γ.fuse (b + c) (d + e))) w)) :=
                        congrArg (fun z => x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e0.symm
              | add u u' hu hu' =>
                  have e1 := LinearMap.map_add₂ (GBR.mk Γ a (b + c) (d + e)) u u' w
                  calc gE17FinalStep K Γ a b c d e
                        (x • RelTensor.mk K (Γ.D (d + e)).carrier
                          (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                          (xv : FusionColumn (Γ.fuse d e))
                          (GBR.mk Γ a (b + c) (d + e) (u + u') w))
                      = gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ a (b + c) (d + e) u w
                              + GBR.mk Γ a (b + c) (d + e) u' w)) :=
                        congrArg (fun z => gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e1
                    _ = gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ a (b + c) (d + e) u w))
                        + gE17FinalStep K Γ a b c d e
                          (x • RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ a (b + c) (d + e) u' w)) := by
                        rw [map_add, smul_add, map_add]
                    _ = x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ a (b + c) (d + e) u w))
                        + x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ a (b + c) (d + e) u' w)) := congrArg₂ (· + ·) hu hu'
                    _ = x • (gE17FinalStep K Γ a b c d e
                            (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ a (b + c) (d + e) u w))
                          + gE17FinalStep K Γ a b c d e
                            (RelTensor.mk K (Γ.D (d + e)).carrier
                              (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                              (xv : FusionColumn (Γ.fuse d e)) (GBR.mk Γ a (b + c) (d + e) u' w))) :=
                        (smul_add x _ _).symm
                    _ = x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                            (GBR Γ a (b + c) (d + e)) (xv : FusionColumn (Γ.fuse d e))
                            (GBR.mk Γ a (b + c) (d + e) (u + u') w)) :=
                        congrArg (fun z => x • gE17FinalStep K Γ a b c d e
                          (RelTensor.mk K (Γ.D (d + e)).carrier
                            (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
                            (xv : FusionColumn (Γ.fuse d e)) z)) e1.symm
              | homogeneous xu =>
                  exact gE17FinalStep_leaf K Γ a b c d e xv.2 xu.2 w hx

/-- **`gE17FinalStep`'s `(a+b)`-equivariance, generalized to all `x`**. -/
theorem gE17FinalStep_aSlot_general (x : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) :
    gE17FinalStep K Γ a b c d e (x • n) = x • gE17FinalStep K Γ a b c d e n := by
  induction x using DirectSum.Decomposition.inductionOn (Γ.D (b + c)).grading with
  | zero =>
      calc gE17FinalStep K Γ a b c d e ((0 : (Γ.D (b + c)).carrier) • n)
          = gE17FinalStep K Γ a b c d e (0 : RelTensor K (Γ.D (d + e)).carrier
              (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))) := by rw [zero_smul]
        _ = 0 := map_zero _
        _ = (0 : (Γ.D (b + c)).carrier) • gE17FinalStep K Γ a b c d e n := (zero_smul _ _).symm
  | add x x' hx hx' =>
      calc gE17FinalStep K Γ a b c d e ((x + x') • n)
          = gE17FinalStep K Γ a b c d e (x • n + x' • n) := by rw [add_smul]
        _ = gE17FinalStep K Γ a b c d e (x • n) + gE17FinalStep K Γ a b c d e (x' • n) := map_add _ _ _
        _ = x • gE17FinalStep K Γ a b c d e n + x' • gE17FinalStep K Γ a b c d e n :=
            congrArg₂ (· + ·) hx hx'
        _ = (x + x') • gE17FinalStep K Γ a b c d e n := (add_smul _ _ _).symm
  | homogeneous xx =>
      exact gE17FinalStep_aSlot K Γ a b c d e xx.2 n


/-- `gE17FinalStep`, wrapped by the outer `F_{b,c}`-slot. -/
noncomputable def gE17FinalStepWrapped :
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ a (b + c) (d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) :=
  RelTensor.mapEquivRight K (gE17FinalStep K Γ a b c d e) (gE17FinalStep_aSlot_general K Γ a b c d e)

/-! ### `E17M` toolkit piece 9: `gV12Assoc`, closing `V12` -/

/-- **`gV12Assoc`**: `V12`'s own re-association, exposing `F_{b,c} ⊗_{D_{b+c}}
(GBR(b+c,d,e) ⊗_{D_{b+c+d+e}} F_{a,b+c+d+e})` — a SINGLE, cast-free
`RelTensor.assoc` (mirrors `gV3AssocA`/`gV10Assoc`/`gV11Assoc`: `GBR Γ
(b+c) d e`'s own recast total `D_{(b+c)+d+e} = D_{b+c+d+e}` syntactically,
matching `GQ5`'s own construction). -/
noncomputable def gV12Assoc : V12 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse b c)) (GBR Γ (b + c) d e) (FusionColumn (Γ.fuse a (b + c + d + e)))

/-! ### `E17M`: the assembly -/

/-- **`E17M`, as a `LinearEquiv`**: `V7 → V12`, the move `t_{a,b+c,d+e}` —
`gV7AssocABC` (reassociating `V7` to expose `GBL(a,b+c,d+e)` through the
`F_{b,c}`/`F_{d,e}` whiskers, via the middle swap `gV7Swap` and the recast
closer `gV7Cast`) then `gE17OuterStep` (the signed double-nested
`(d+e)`/`(b+c)`-nested amplification of `gTCanon Γ a (b+c) (d+e)`) then
`gE17FinalStepWrapped` (reusing `Pentagon.lean`'s `gq4Close`) then
`gV12Assoc⁻¹`. -/
noncomputable def E17Mequiv : V7 K Γ a b c d e ≃ₗ[K] V12 K Γ a b c d e :=
  (gV7AssocABC K Γ a b c d e).trans
    ((gE17OuterStep K Γ a b c d e).trans
      ((gE17FinalStepWrapped K Γ a b c d e).trans (gV12Assoc K Γ a b c d e).symm))

/-- **Edge 17** `E17M : V7 → V12`, `t_{a,b+c,d+e}` (owning faces `PBC`,
`PDE`). -/
noncomputable def E17M : V7 K Γ a b c d e →ₗ[K] V12 K Γ a b c d e :=
  (E17Mequiv K Γ a b c d e).toLinearMap

theorem E17M_bijective : Function.Bijective (E17M K Γ a b c d e) :=
  (E17Mequiv K Γ a b c d e).bijective

end GaugeChi

end Superfusion
