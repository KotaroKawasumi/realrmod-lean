/-
Superfusion / GaugeChi / QuintRecog3

Milestone M13-4c of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): **the recognition-statement leaf lemma `E14M_leaf`** for edge 14
(`E14M : V6 → V9`, the move `t_{a+b,c,d+e}`), the edge SHARED by faces
`PAB` and `PDE` — continuing `QuintRecog.lean`'s form (B) discipline
(`docs/m13-design.md`'s ledger) for the two edges already landed there
(`E4M_leaf`, `E13M_leaf`, `E12M_leaf`).

## The shape

`E14M` (`QuintEdges5.lean`) is built as FOUR composed stages,
`E14Mequiv = gV6AssocA.trans (gV6SwapWrapped.trans (gE14OuterStep.trans
gE14FinalStepWrapped))`:

* `gV6AssocA`: a plain, cast-free `RelTensor.assoc`, peeling `V6 =
  GBL(a,b,c) ⊗_{D_{a+b+c}} GBR(a+b+c,d,e)` down to `F_{a,b} ⊗_{D_{a+b}}
  (F_{a+b,c} ⊗_{D_{a+b+c}} GBR(a+b+c,d,e))`;
* `gV6SwapWrapped`: the `F_{a,b}`-whiskered middle swap `gV6Swap`
  (`Bimod.midSwap`, `QuintEdges5.lean`), exchanging `F_{a+b,c} ⊗
  GBR(a+b+c,d,e)` for `F_{d,e} ⊗_{D_{d+e}} GBL(a+b,c,d+e)` with a
  Koszul sign on the two SEPARATELY homogeneous columns it swaps;
* `gE14OuterStep`: the `F_{a,b}`-whiskered signed `(d+e)`-slot
  amplification of `gTCanon Γ (a+b) c (d+e)` (itself the composite of TWO
  nested `smap`-layers, one for the outer `F_{a,b}`-slot and one for the
  `(d+e)`-slot `gE14InnerStep`);
* `gE14FinalStepWrapped`: the `F_{a,b}`-whiskered `Pentagon.lean`'s
  `gq4Close K Γ (a+b) c d e`, reused VERBATIM (`GQ4r K Γ (a+b) c d e`
  unfolds to exactly `F_{d,e} ⊗ GBR(a+b,c,d+e)`, and `GQ4 K Γ (a+b) c d e`
  unfolds to exactly `V9Inner K Γ a b c d e`).

Consequently, on a FULLY-DECOMPOSED homogeneous `V6`-generator `u ⊗ (v ⊗
(w ⊗ x))` (`u : F_{a,b}` of degree `ju`, `v : F_{a+b,c}` of degree `jv`,
`w : F_{d,e}` of degree `jw`, `x : F_{a+b+c,d+e}` arbitrary — the flat
homogeneous generator shape, transported to `V6`'s own bracketing), THREE
Koszul signs accumulate (unlike `E4M_leaf`/`E13M_leaf`/`E12M_leaf`, which
each only accumulate ONE): the middle-swap's own crossing `jw·jv`
(`gV6Swap_mk_of_mem`), the `(d+e)`-slot `smap`'s crossing
`gParity(a+b,c,d+e)·jw` (`gE14InnerStep`, via `gCanonHphi5`), and the
outer `F_{a,b}`-slot `smap`'s crossing `gParity(a+b,c,d+e)·ju`
(`gE14OuterStep`, via `gE14OuterHg`) — combining (`sgn_add`) to
`sgn(jw·jv + gParity(a+b,c,d+e)·(ju+jw))`. This is landed here as ONE
combined `ℤ`-power `zsmul`, per the round's sign discipline; a `decide`-
provable rewrite (mirroring `PentagonEdges.lean`'s own `GE5_mk_of_mem`
sign identity `i·j+e·i=i·(e+j)`) is NOT applied here since the extra
outer wrap (absent from the plain four-letter `GE5`) prevents a further
collapse into a single product form — the three-way sum is the honest,
fully-reduced shape.

The reinsertion into `V9` is `gq4Close K Γ (a+b) c d e` applied to a raw
`mk w (gTCanon K Γ (a+b) c (d+e) (mk v x))`-shaped element of `GQ4r K Γ
(a+b) c d e` — `gTCanon`/`gq4Close`, the SAME canonical data
`gChiCanon_spec K Γ (a+b) c d e`'s own bottom route (`gBotRoute`,
`PentagonMembership.lean`) uses at its own `GE5`/close slot, left
UNEXPANDED exactly as `E4M_leaf`/`E12M_leaf` leave `gTCanon(...)`
unexpanded (no generator formula for `gTCanon` on a non-homogeneous
argument is needed or used) — matching the round's requirement that the
leaf target the exact map `gChiCanon_spec`'s bottom route uses at the
`(a+b,c,d,e)`-slot.

No new toolkit content: every step reuses `QuintEdges5.lean`'s own
public `_mk_of_mem`/`smap_mk_of_mem`/`RelTensor.assoc_mk`/
`RelTensor.map_mk` lemmas, chased through the four `.trans` stages via
`show` (defeq unfolding of `LinearEquiv.trans`/`LinearEquiv.ofLinear`,
the same discipline `E4M_leaf`/`E13M_leaf`/`E12M_leaf` use for their own
single- and double-stage unfoldings) — the "show + raw respelling before
scalar-pulling" discipline throughout.
-/
import Superfusion.GaugeChi.QuintRecog

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

/-! ### `E14M_leaf`: the `PAB`/`PDE`-face leaf lemma for edge 14 (`V6 → V9`) -/

/-- **`E14M_leaf`**: `E14M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V6` (`u : F_{a,b}` of degree `ju`, `v :
F_{a+b,c}` of degree `jv`, `w : F_{d,e}` of degree `jw`, `x :
F_{a+b+c,d+e}` arbitrary — all three of `u,v,w` individually homogeneous,
since `E14M`'s own middle-swap stage genuinely exchanges the `v`- and
`w`-columns and needs both graded) — the `PAB`/`PDE`-face leaf lemma for
edge 14, chased through `E14M`'s four-stage definition
(`QuintEdges5.lean`) via the already-public `RelTensor.assoc_mk`,
`gV6Swap_mk_of_mem`, `smap_mk_of_mem` (twice), and `RelTensor.map_mk`:
no new toolkit content. The target lands in `V9`, whose inner factor
`V9Inner K Γ a b c d e` is exactly `GQ4 K Γ (a+b) c d e`
(`gE14FinalStep`'s own codomain, `QuintEdges5.lean`), matching the module
docstring's derivation. -/
theorem E14M_leaf {ju jv jw : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (x : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    E14M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
          (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x))
      = ((sgn (jw * jv + gParity K Γ (a + b) c (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
            u
            (gq4Close K Γ (a + b) c d e
              (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                (GBR Γ (a + b) c (d + e)) w
                (gTCanon K Γ (a + b) c (d + e)
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)))) := by
  have h1 : gV6AssocA K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
        (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x))
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w x)) :=
    RelTensor.assoc_mk K (Γ.D (a + b)).carrier (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e)
      u v (GBR.mk Γ (a + b + c) d e w x)
  have h2swap : gV6Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w x))
    = ((sgn (jw * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))
          w (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x) :=
    gV6Swap_mk_of_mem K Γ a b c d e hv hw x
  have h2 : gV6SwapWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w x)))
    = ((sgn (jw * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ (a + b) c (d + e))) u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ (a + b) c (d + e)) w
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gV6Swap K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gV6Swap_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e)) u
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w x))) = _
    simp only [RelTensor.map_mk, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, h2swap,
      map_zsmul]
  have h3a : gE14OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)))
        u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ (a + b) c (d + e)) w
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)))
    = ((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))
          u
          (gE14InnerStep K Γ a b c d e
            (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBL Γ (a + b) c (d + e)) w
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x))) := by
    show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (gE14InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) c (d + e))
        (gE14OuterHg K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ (a + b) c (d + e)) w
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x))) = _
    rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (gE14InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) c (d + e))
      (gE14OuterHg K Γ a b c d e) hu]
    rfl
  have h3b : gE14InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))
        w (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x))
    = ((sgn (gParity K Γ (a + b) c (d + e) * jw) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e))
          w (gTCanon K Γ (a + b) c (d + e)
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)) := by
    show smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gParity K Γ (a + b) c (d + e))
        (gCanonHphi5 K Γ (a + b) c d e)
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e))
          w (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)) = _
    rw [smap_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gParity K Γ (a + b) c (d + e))
      (gCanonHphi5 K Γ (a + b) c d e) hw]
    rfl
  have h3 : gE14OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ (a + b) c (d + e)))
        u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ (a + b) c (d + e)) w
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)))
    = ((sgn (gParity K Γ (a + b) c (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) w
            (gTCanon K Γ (a + b) c (d + e)
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x))) := by
    simp only [h3a, h3b, map_zsmul, smul_smul, ← Units.val_mul, ← sgn_add, ← mul_add]
  have h4 : gE14FinalStepWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ (a + b) c (d + e)))
        u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ (a + b) c (d + e)) w
          (gTCanon K Γ (a + b) c (d + e)
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x))))
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
        (gq4Close K Γ (a + b) c d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) w
            (gTCanon K Γ (a + b) c (d + e)
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gE14FinalStep K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gE14FinalStep_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e))) u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e)) w
            (gTCanon K Γ (a + b) c (d + e)
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) v x)))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  show gE14FinalStepWrapped K Γ a b c d e
      (gE14OuterStep K Γ a b c d e
        (gV6SwapWrapped K Γ a b c d e
          (gV6AssocA K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
              (GBL.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w x))))) = _
  simp only [h1, h2, map_zsmul, h3, h4, smul_smul, ← Units.val_mul, ← sgn_add]
  rfl

end GaugeChi

end Superfusion
