/-
Superfusion / GaugeChi / QuintRecog5

Milestone M13-4f of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase, continuing `GaugeChi.QuintRecog`'s form (B) program): **`E19M_leaf`
and `E21M_leaf`**, the last two recognition leaves — `E19M` (`V8 → V13`,
`t_{a,b,(c+d)+e}`, owning faces `PCD`, `S3`) and `E21M` (`V9 → V14`,
`t_{a,b,c+(d+e)}`, owning faces `PDE`, `S3`), `QuintEdges8.lean`'s two
edges closing the 21-edge scaffold.

## A NEW toolkit item, exported to `QuintEdges8.lean`

Unlike every earlier middle-swap edge (`gV6Swap`/`gV7Swap`, `QuintEdges5.
lean`/`QuintEdges7.lean`), `gV8Swap`/`gV9Swap` (`QuintEdges8.lean`) had NO
public `_mk_of_mem` sign-law wrapper — only the `private` `gV8LawA`/
`gV8LawB`/`gV9LawA`/`gV9LawB` witnesses, invisible from this file. Two
small public theorems `gV8Swap_mk_of_mem`/`gV9Swap_mk_of_mem` (mirroring
`gV6Swap_mk_of_mem`'s own term-mode `midSwapMap_mk_of_mem` discipline
exactly) were added to `QuintEdges8.lean` alongside the two `def`s they
wrap — genuinely no NEW content (the private laws + `midSwapMap_mk_of_mem`
already public), just the missing bridge.

## The shape, and why it differs from `E14M_leaf`/`E17M_leaf`'s 3-way sign

`gV8Swap`/`gV9Swap` swap the OUTER `F_{a,b}` column directly against the
WHOLE inner `GBL(c,d,e)`/`GBR(c,d,e)` column (no preceding `assoc` peel —
`V8`/`V9` are already the `midSwap` shape `M ⊗ (N ⊗ P)`), unlike `gV6Swap`/
`gV7Swap`, which first `assoc`-peel a SEPARATE pairing column (`F_{a+b,c}`/
`F_{a,b+c}`) away from the REST of a `GBR`/`GBL` column before swapping.
Consequently there are only TWO independent degrees in play (the `F_{a,b}`
column's degree `ju` and the swapped `GBL(c,d,e)`/`GBR(c,d,e)` column's
OWN degree, shared identically by the swap AND the following `(c+d+e)`-slot
`smap`), not three — and the two crossings COLLAPSE into a SINGLE product
(unlike `E14M_leaf`/`E17M_leaf`'s honest 3-way sum): writing the swapped
column as `GBL.mk r s`/homogeneous `n` of degree `i`,

  `sgn(i·ju) · sgn(gParity(a,b,c+d+e)·i) = sgn(i·(ju + gParity(a,b,c+d+e)))`

by `mul_add`/`ring`, landed here as the single-product `zsmul`.

## `E19M_leaf`'s domain split, and the un-collapsible closing tail

`E19M`'s domain generator is decomposed at THREE homogeneous slots
(`t : F_{a,b}` degree `ju`, `r : F_{c,d}` degree `jr`, `s : F_{c+d,e}`
degree `js`, `p : F_{a+b,c+d+e}` arbitrary) — the swapped column is taken
as `GBL.mk Γ c d e r s` (not a bare homogeneous `GBL Γ c d e` element)
specifically so that `gV13StepA` (`QuintEdges8.lean`'s cast-free
`RelTensor.assoc` peeling `F_{c,d}` off the swapped `GBL(c,d,e)` column)
can be chased EXPLICITLY via `RelTensor.assoc_mk`, exposing `r : F_{c,d}`
as `V13`'s own second-level outer spectator (`V13 = GQ3(b,c,d,e) ⊗
F_{a,bcde}`, `GQ3 = F_{c,d} ⊗ GQ3Inner` — `r`'s own exposure is exactly
what the `S3`-face consumer `E8` (`a|b|t_{c,d,e}`, itself amplifying
`gTCanon Γ c d e` through the `F_{c,d}` slot) will need).

Past `gV13StepA`, though, the chase genuinely CANNOT be pushed further:
`gV13Regroup` (the next stage, another cast-free `RelTensor.assoc.symm`)
needs its OWN second argument split as `mk v x` to fire `RelTensor.
assoc_symm_mk` — but that argument is `(gq3rCast K Γ a b c d e).symm`
applied to `gTCanon K Γ a b (c+d+e) (GBL.mk Γ a b (c+d+e) t p)`, an
ABSTRACT canonical-intertwiner image with no known `mk`-decomposition
(exactly the obstruction `E11M_leaf`'s own `gE11GBRAssoc(mk p τ)` already
hit, `QuintRecog2.lean` — the SAME "leave the canonical image unexpanded"
convention `E4M_leaf`/`E12M_leaf`/`E14M_leaf`/`E17M_leaf` establish, here
forcing BOTH `gV13Regroup` and the final `gV13StepB` to be left as raw,
UNEXPANDED applications to their own two-level `mk` arguments — `gV13StepB`
in particular can only be applied to `mk r (gV13Regroup (mk s τ'))` as
ONE closing move, mirroring `E17M_leaf`'s own `(gV12Assoc).symm (mk u
(gq4Close (...)))` treatment of its extra plain-recast layer). No new
toolkit content beyond the two exported `_mk_of_mem` bridges: every other
step reuses `QuintEdges8.lean`'s own already-public `smap_mk_of_mem`,
`RelTensor.assoc_mk`, `RelTensor.map_mk` (via the `RelTensor.mapEquivRight`/
`PentagonB.smapEquiv` `show`-unfolding discipline `QuintRecog.lean`
established).

## `E21M_leaf`: genuinely SIMPLER — no analogous peel

`E21M`'s route needs no `gV13StepA`/`gV13Regroup`-style stage at all
(`QuintEdges8.lean`'s own docstring: `GBR(c,d,e) ⊗ F_{b,c+d+e}` unfolds
*definitionally* to `GQ4 K Γ b c d e`, `V14`'s own inner factor) — so the
swapped `GBR(c,d,e)` column is taken as a SINGLE homogeneous element `n`
(NOT split further; there is no downstream stage that would need it split,
unlike `E19M`'s `r`/`s`), and the whole closing tail is just the ONE plain
`gV14StepFinal`, left unexpanded on its own opaque `gq3rCast`-recast
argument for the identical reason. Two homogeneous hypotheses only
(`t` and `n`), not three.

## Method

Both leaves chase their edge's stages via `gV8Swap_mk_of_mem`/
`gV9Swap_mk_of_mem` (signed, term-mode), `smap_mk_of_mem` (signed, `show` +
`PentagonB.smapEquiv`-unfolding), `RelTensor.map_mk` (unsigned, `show` +
`RelTensor.mapEquivRight`-unfolding, for the `gq3rCastWrapped`/
`gq3rCastWrappedR` stage), and `RelTensor.assoc_mk` (unsigned, term-mode,
for `E19M_leaf`'s `gV13StepA` only) — `map_zsmul`/`smul_smul`/
`← Units.val_mul`/`← sgn_add` fuse the two Koszul signs into one, and a
final `ring`-driven rewrite factors the two-term sum into the single
product quoted above.
-/
import Superfusion.GaugeChi.QuintRecog4

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

/-! ### `E19M_leaf`: the `PCD`/`S3`-face leaf lemma for edge 19 (`V8 → V13`) -/

/-- **`E19M_leaf`**: `E19M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V8` (`t : F_{a,b}` degree `ju`, `r : F_{c,d}`
degree `jr`, `s : F_{c+d,e}` degree `js`, `p : F_{a+b,c+d+e}` arbitrary —
the swapped `GBL(c,d,e)` column taken as `GBL.mk Γ c d e r s` so that the
cast-free `gV13StepA` can expose `r` explicitly, `V13`'s own second-level
outer spectator) — chased through `E19M`'s six-stage definition
(`QuintEdges8.lean`) via `gV8Swap_mk_of_mem` (exported alongside this
round), `smap_mk_of_mem`, `RelTensor.map_mk`, and `RelTensor.assoc_mk`: no
new toolkit content beyond the exported bridge. The closing tail past
`gV13StepA` (`gV13RegroupWrapped`, `gV13StepB`) cannot be reduced further
— it is applied, as ONE move, to the raw `mk r (gV13Regroup (mk s (...)))`
argument the stages themselves produce (the module docstring's
obstruction discussion), mirroring `E17M_leaf`'s own extra-plain-recast
treatment. -/
theorem E19M_leaf {ju jr js : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {r : FusionColumn (Γ.fuse c d)} (hr : r ∈ FusionColumn.grading (Γ.fuse c d) jr)
    {s : FusionColumn (Γ.fuse (c + d) e)} (hs : s ∈ FusionColumn.grading (Γ.fuse (c + d) e) js)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    E19M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBL.mk Γ c d e r s) p))
      = ((sgn ((jr + js) * (ju + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
          gV13StepB K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                (FusionColumn (Γ.fuse a (b + c + d + e)))) r
              (gV13Regroup K Γ a b c d e
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) s
                  ((gq3rCast K Γ a b c d e).symm
                    (gTCanon K Γ a b (c + d + e)
                      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))))) := by
  -- Stage 1: `gV8Swap`, the top-level middle swap (signed).
  have hn : (GBL.mk Γ c d e r s) ∈ GBL.grading Γ c d e (jr + js) :=
    GBL.mk_mem_grading Γ c d e hr hs
  have h1 : gV8Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBL.mk Γ c d e r s) p))
    = ((sgn ((jr + js) * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e))
          (GBL.mk Γ c d e r s)
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p) :=
    gV8Swap_mk_of_mem K Γ a b c d e hn ht p
  -- Stage 2: `gE19InnerStep`, the `(c+d+e)`-slot signed move.
  have h2 : gE19InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e))
        (GBL.mk Γ c d e r s)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))
    = ((sgn (gParity K Γ a b (c + d + e) * (jr + js)) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e))
          (GBL.mk Γ c d e r s) (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) := by
    show smap (Γ.D (c + d + e)).grading (GBL.grading Γ c d e)
        (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
        (gCanonHphi5 K Γ a b (c + d) e)
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e))
          (GBL.mk Γ c d e r s) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) = _
    rw [smap_mk_of_mem (Γ.D (c + d + e)).grading (GBL.grading Γ c d e)
      (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
      (gCanonHphi5 K Γ a b (c + d) e) hn]
    rfl
  -- Stage 3: `gq3rCastWrapped`, the unsigned outer wrap of `gq3rCast.symm`.
  have h3 : gq3rCastWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e))
        (GBL.mk Γ c d e r s) (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        (GBL.mk Γ c d e r s)
        ((gq3rCast K Γ a b c d e).symm
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) := by
    show RelTensor.map (LinearMap.id : GBL Γ c d e →ₗ[K] GBL Γ c d e)
        (gq3rCast K Γ a b c d e).symm.toLinearMap (fun _ _ => rfl)
        (leftEquivariant_symm K (gq3rCast K Γ a b c d e) (gq3rCast_bSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e))
          (GBL.mk Γ c d e r s) (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  -- Stage 4: `gV13StepA`, the cast-free peel exposing `r : F_{c,d}`.
  have h4 : gV13StepA K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        (GBL.mk Γ c d e r s)
        ((gq3rCast K Γ a b c d e).symm
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))))
    = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))) r
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) s
          ((gq3rCast K Γ a b c d e).symm
            (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))) :=
    RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      r s ((gq3rCast K Γ a b c d e).symm
        (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))
  -- Stage 5: `gV13RegroupWrapped`, the unsigned outer wrap of `gV13Regroup`.
  have h5 : gV13RegroupWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))))) r
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) s
          ((gq3rCast K Γ a b c d e).symm
            (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))))
    = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))) r
        (gV13Regroup K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) s
            ((gq3rCast K Γ a b c d e).symm
              (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K] FusionColumn (Γ.fuse c d))
        (gV13Regroup K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gV13Regroup_aSlot K Γ a b c d e)
        (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))) r
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) s
            ((gq3rCast K Γ a b c d e).symm
              (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  show gV13StepB K Γ a b c d e
      (gV13RegroupWrapped K Γ a b c d e
        (gV13StepA K Γ a b c d e
          (gq3rCastWrapped K Γ a b c d e
            (gE19InnerStep K Γ a b c d e
              (gV8Swap K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (V8Inner K Γ a b c d e) t
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                    (FusionColumn (Γ.fuse (a + b) (c + d + e))) (GBL.mk Γ c d e r s) p)))))))
    = _
  simp only [h1, map_zsmul, h2, smul_smul, ← Units.val_mul, ← sgn_add, h3, h4, h5,
    show (jr + js) * ju + gParity K Γ a b (c + d + e) * (jr + js)
        = (jr + js) * (ju + gParity K Γ a b (c + d + e)) from by ring]

/-! ### `E21M_leaf`: the `PDE`/`S3`-face leaf lemma for edge 21 (`V9 → V14`) -/

/-- **`E21M_leaf`**: `E21M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V9` (`t : F_{a,b}` degree `ju`, the swapped
`GBR(c,d,e)` column taken as a SINGLE homogeneous element `n` of degree
`i` — no further split, since `E21M`'s route needs no analogue of `E19M`'s
`gV13StepA` peel; `p : F_{a+b,c+d+e}` arbitrary) — chased through `E21M`'s
four-stage definition (`QuintEdges8.lean`) via `gV9Swap_mk_of_mem`
(exported alongside this round), `smap_mk_of_mem`, and `RelTensor.map_mk`:
no new toolkit content beyond the exported bridge. The closing
`gV14StepFinal` is left applied, as ONE move, to the raw `mk n (...)`
argument (the module docstring's obstruction discussion — identical to
`E19M_leaf`'s `gV13StepB`/`E17M_leaf`'s `(gV12Assoc).symm`). -/
theorem E21M_leaf {ju i : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {n : GBR Γ c d e} (hn : n ∈ GBR.grading Γ c d e i)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    E21M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p))
      = ((sgn (i * (ju + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
          gV14StepFinal K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))) n
              ((gq3rCast K Γ a b c d e).symm
                (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))) := by
  -- Stage 1: `gV9Swap`, the top-level middle swap (signed).
  have h1 : gV9Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p))
    = ((sgn (i * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e)) n
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p) :=
    gV9Swap_mk_of_mem K Γ a b c d e hn ht p
  -- Stage 2: `gE21InnerStep`, the `(c+d+e)`-slot signed move.
  have h2 : gE21InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e)) n
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))
    = ((sgn (gParity K Γ a b (c + d + e) * i) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBR Γ a b (c + d + e)) n
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) := by
    show smap (Γ.D (c + d + e)).grading (GBR.grading Γ c d e)
        (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
        (gCanonHphi5 K Γ a b (c + d) e)
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBL Γ a b (c + d + e)) n
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) = _
    rw [smap_mk_of_mem (Γ.D (c + d + e)).grading (GBR.grading Γ c d e)
      (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
      (gCanonHphi5 K Γ a b (c + d) e) hn]
    rfl
  -- Stage 3: `gq3rCastWrappedR`, the unsigned outer wrap of `gq3rCast.symm`.
  have h3 : gq3rCastWrappedR K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBR Γ a b (c + d + e)) n
        (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) n
        ((gq3rCast K Γ a b c d e).symm
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) := by
    show RelTensor.map (LinearMap.id : GBR Γ c d e →ₗ[K] GBR Γ c d e)
        (gq3rCast K Γ a b c d e).symm.toLinearMap (fun _ _ => rfl)
        (leftEquivariant_symm K (gq3rCast K Γ a b c d e) (gq3rCast_bSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e) (GBR Γ a b (c + d + e)) n
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  show gV14StepFinal K Γ a b c d e
      (gq3rCastWrappedR K Γ a b c d e
        (gE21InnerStep K Γ a b c d e
          (gV9Swap K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V9Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) n p)))))
    = _
  simp only [h1, map_zsmul, h2, smul_smul, ← Units.val_mul, ← sgn_add, h3,
    show i * ju + gParity K Γ a b (c + d + e) * i = i * (ju + gParity K Γ a b (c + d + e))
      from by ring]

end GaugeChi

end Superfusion
