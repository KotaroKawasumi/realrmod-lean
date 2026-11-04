/-
Superfusion / GaugeChi / QuintRecog4

Milestone M13-4e of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase, continuing `GaugeChi.QuintRecog`'s form (B) program): **`E17M_leaf`**
— the recognition leaf lemma for `E17M` (`V7 → V12`, the move
`t_{a,b+c,d+e}`, `QuintEdges7.lean`), the PDE face's hard edge (owning
faces `PBC`/`PDE`).

## The shape

`E17M` (`QuintEdges7.lean`) is built as FOUR composed stages,
`E17Mequiv = gV7AssocABC.trans (gE17OuterStep.trans (gE17FinalStepWrapped.
trans gV12Assoc.symm))`:

* `gV7AssocABC = gV7AssocA.trans (outer F_{b,c}-wrap of gV7SwapCast)`:
  `gV7AssocA` (a plain `RelTensor.assoc`, peeling `V7 = GBR(a,b,c) ⊗
  GBR(a+b+c,d,e)` down to `F_{b,c} ⊗ (F_{a,b+c} ⊗ GBR(a+b+c,d,e))`), then
  the `F_{b,c}`-whiskered `gV7SwapCast = gV7Swap.trans gV7Cast`: `gV7Swap`
  (`Bimod.midSwap`, exchanging `F_{d,e}` past `F_{a,b+c}`, with a Koszul
  sign on the two swapped homogeneous columns) then `gV7Cast` (the plain,
  sign-free recast `gq2rCast K Γ a b c (d+e)`, `ChiCanon.lean`'s own
  4th-argument-generic device reused VERBATIM at the shifted `d := d+e`),
  landing `F_{d,e} ⊗ GBL(a,b+c,d+e)`;
* `gE17OuterStep`: the `F_{b,c}`-whiskered signed amplification of
  `gE17InnerStep` (itself the `(d+e)`-slot signed amplification of
  `gTCanon Γ a (b+c) (d+e)`) — TWO nested `smap` layers, `(b+c)` being
  `gTCanon`'s own MIDDLE argument here (unlike `E11M`/`E14M`'s outer-FIRST-
  argument wraps);
* `gE17FinalStepWrapped`: the `F_{b,c}`-whiskered, UNSIGNED
  (`RelTensor.mapEquivRight`) wrap of `Pentagon.lean`'s `gq4Close`, reused
  VERBATIM at the shifted instantiation `(a, b+c, d, e)`;
* `gV12Assoc.symm`: a plain, cast-free `RelTensor.assoc.symm` closing
  `F_{b,c} ⊗ GQ4(a,b+c,d,e)` onto `V12`.

Consequently, on a FULLY-DECOMPOSED homogeneous `V7`-generator `(u ⊗ v) ⊗
(w ⊗ q)` (`u : F_{b,c}` of degree `ju`, `v : F_{a,b+c}` of degree `jv`,
`w : F_{d,e}` of degree `jw`, `q : F_{a+b+c,d+e}` arbitrary — `u,v,w`
individually homogeneous, mirroring `E14M_leaf`'s own precedent since
`gV7Swap` genuinely exchanges the `v`- and `w`-columns and needs both
graded), THREE Koszul signs accumulate: the middle-swap's own crossing
`jw·jv` (`gV7Swap_mk_of_mem`), the `(d+e)`-slot `smap`'s crossing
`gParity(a,b+c,d+e)·jw` (`gE17InnerStep`, via `gCanonHphi5`), and the
outer `F_{b,c}`-slot `smap`'s crossing `gParity(a,b+c,d+e)·ju`
(`gE17OuterStep`, via `gE17OuterHg`) — combining (`sgn_add`) to the SAME
three-way shape `E14M_leaf` found for its own shared-swap edge,
`sgn(jw·jv + gParity(a,b+c,d+e)·(ju+jw))`: this is the honest,
fully-reduced sign, landed as ONE combined `ℤ`-power `zsmul`.

## The reinsertion, and the extra `gV12Assoc.symm` layer

The reinsertion into `V12` is `(gV12Assoc K Γ a b c d e).symm` applied to
`mk u (gq4Close K Γ a (b+c) d e (mk w (gt2Canon K Γ a b c (d+e) (gTCanon K
Γ a (b+c) (d+e)) (mk v q))))` — the INNER spelling folds `gV7Cast`'s
`gq2rCast` recast back together with `gTCanon Γ a (b+c) (d+e)` into the
single `GE2`-genre application `gt2Canon K Γ a b c (d+e) (gTCanon K Γ a
(b+c) (d+e))` (via `gt2Canon_mk`), exactly `E11M_leaf`'s own spec-aligned
convention, applied to the RAW `GQ2rInner`-shaped generator `mk v q` — the
intertwiner PDE's own counterpart edge (`face_PDE`'s `GE2`-genre move
`t_{x,y+z,w}` at `(x,y,z,w) = (a,b,c,d+e)`) will need at its own
`(a,b,c,d+e)`-slot.

Unlike `E11M_leaf`/`E14M_leaf`, whose final stage lands DIRECTLY in the
target vertex (`E11M`'s `gE11GBRAssoc` is unsigned and needs no further
closing recast; `E14M`'s `GQ4 K Γ (a+b) c d e` unfolds to EXACTLY `V9Inner`,
so `gq4Close`'s own codomain already IS the target), `E17M` needs ONE MORE
plain recast (`gV12Assoc.symm`, since `GQ4 K Γ a (b+c) d e` is `V12`'s
INNER factor, not `V12` itself) after `gq4Close`. `gV12Assoc.symm`'s own
generator formula (`RelTensor.assoc_symm_mk`) would need the `GQ4`-valued
argument split into its OWN `mk gbr fac` generator — but that argument is
`gq4Close (...)` applied to a `mk w (gt2Canon (...))`-shaped element whose
SECOND (`GBR`) factor is the abstract intertwiner's image, not literally a
generator of `GBR Γ a (b+c) (d+e)`. So — mirroring the established
"leave `gTCanon(...)`/`gq4Close(...)` UNEXPANDED" convention of
`E4M_leaf`/`E12M_leaf`/`E14M_leaf` — `(gV12Assoc).symm` is ALSO left
unexpanded here, applied (via `map_zsmul`) to the raw `mk u (gq4Close
(...))` element: the honest, fully-reduced shape, wrapped in exactly the
`gq4Close`/cast layers `E17M`'s own stages dictate, per the round's
guidance.

## Method

Chased through `E17M`'s stages via their own already-public `_mk`/
`_mk_of_mem` generator lemmas (`RelTensor.assoc_mk` for `gV7AssocA`,
`gV7Swap_mk_of_mem` + `gq2rCast_mk` for `gV7SwapCast`, `smap_mk_of_mem`
(twice) for `gE17OuterStep`/`gE17InnerStep`, `RelTensor.map_mk` for the
`mapEquivRight`/`smapEquiv` outer wraps, `gt2Canon_mk` to re-fold the cast
at the very end): no new toolkit content, following `QuintRecog.lean`'s
form (B) discipline throughout (`show` + raw respelling before every `rw`
across a `def`-wrapped vertex type, `map_zsmul` for the ℤ-valued Koszul
signs, `smul_smul`/`← Units.val_mul`/`← sgn_add` to fuse sign factors).
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

/-! ### `E17M_leaf`: the `PBC`/`PDE`-face leaf lemma for edge 17 (`V7 → V12`) -/

/-- **`E17M_leaf`**: `E17M`'s generator formula on a FULLY-DECOMPOSED
homogeneous generator of `V7` (`u : F_{b,c}` of degree `ju`, `v :
F_{a,b+c}` of degree `jv`, `w : F_{d,e}` of degree `jw`, `q :
F_{a+b+c,d+e}` arbitrary — all three of `u,v,w` individually homogeneous,
since `E17M`'s own middle-swap stage genuinely exchanges the `v`- and
`w`-columns and needs both graded, mirroring `E14M_leaf`'s precedent) —
chased through `E17M`'s four-stage definition (`QuintEdges7.lean`) via the
already-public `RelTensor.assoc_mk`, `gV7Swap_mk_of_mem`, `gq2rCast_mk`,
`smap_mk_of_mem` (twice), and `RelTensor.map_mk`: no new toolkit content.
The reinsertion carries an EXTRA plain-recast layer beyond `E11M_leaf`/
`E14M_leaf` (`(gV12Assoc).symm`, left unexpanded on the `gq4Close`-valued
argument for the same reason `gq4Close` itself is left unexpanded on
`gTCanon`'s abstract image — see the module docstring). -/
theorem E17M_leaf {ju jv jw : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))} (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    E17M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))
      = ((sgn (jw * jv + gParity K Γ a (b + c) (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
          (gV12Assoc K Γ a b c d e).symm
            (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
              (GQ4 K Γ a (b + c) d e) u
              (gq4Close K Γ a (b + c) d e
                (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GBR Γ a (b + c) (d + e)) w
                  (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))
                    (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                      (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q))))) := by
  let q' : FusionColumn (Γ.fuse (a + (b + c)) (d + e)) :=
    gColumnCastFst K Γ (d + e) (add_assoc a b c) q
  -- Stage 1a: `gV7AssocA`, the plain `RelTensor.assoc` exposing `F_{b,c}`.
  have h1 : gV7AssocA K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
        (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))
    = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
          (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w q)) :=
    RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) (GBR Γ (a + b + c) d e)
      u v (GBR.mk Γ (a + b + c) d e w q)
  -- Stage 1b: `gV7SwapCast = gV7Swap.trans gV7Cast`, the swap-then-recast.
  have h2 : gV7SwapCast K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w q))
    = ((sgn (jw * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))
          w (GBL.mk Γ a (b + c) (d + e) v q') := by
    show gV7Cast K Γ a b c d e
        (gV7Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (GBR Γ (a + b + c) d e) v (GBR.mk Γ (a + b + c) d e w q))) = _
    rw [gV7Swap_mk_of_mem K Γ a b c d e hv hw q, map_zsmul]
    show ((sgn (jw * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))
          w (gq2rCast K Γ a b c (d + e)
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q)) = _
    rw [gq2rCast_mk]
  -- Stage 1a+1b combined: `gV7AssocABC`'s value on the `V7`-generator.
  have hABC : gV7AssocABC K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
        (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))
    = ((sgn (jw * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) w (GBL.mk Γ a (b + c) (d + e) v q')) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
        (gV7SwapCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gV7SwapCast_aSlot_general K Γ a b c d e)
        (gV7AssocA K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
            (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))) = _
    simp only [h1, RelTensor.map_mk, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, h2, map_zsmul]
  -- Stage 2 (outer): `gE17OuterStep`, the `(b+c)`-mid-slot signed wrap.
  have h3a : gE17OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))) u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ a (b + c) (d + e)) w (GBL.mk Γ a (b + c) (d + e) v q')))
    = ((sgn (gParity K Γ a (b + c) (d + e) * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))
          u
          (gE17InnerStep K Γ a b c d e
            (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
              (GBL Γ a (b + c) (d + e)) w (GBL.mk Γ a (b + c) (d + e) v q'))) := by
    show smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        (gE17InnerStep K Γ a b c d e).toLinearMap (gParity K Γ a (b + c) (d + e))
        (gE17OuterHg K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ a (b + c) (d + e)) w (GBL.mk Γ a (b + c) (d + e) v q'))) = _
    rw [smap_mk_of_mem (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
      (gE17InnerStep K Γ a b c d e).toLinearMap (gParity K Γ a (b + c) (d + e))
      (gE17OuterHg K Γ a b c d e) hu]
    rfl
  -- Stage 2 (inner): `gE17InnerStep`, the `(d+e)`-slot signed move.
  have h3b : gE17InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))
        w (GBL.mk Γ a (b + c) (d + e) v q'))
    = ((sgn (gParity K Γ a (b + c) (d + e) * jw) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e))
          w (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q')) := by
    show smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (gTCanon K Γ a (b + c) (d + e)).toLinearMap (gParity K Γ a (b + c) (d + e))
        (gCanonHphi5 K Γ a (b + c) d e)
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))
          w (GBL.mk Γ a (b + c) (d + e) v q')) = _
    rw [smap_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (gTCanon K Γ a (b + c) (d + e)).toLinearMap (gParity K Γ a (b + c) (d + e))
      (gCanonHphi5 K Γ a (b + c) d e) hw]
    rfl
  -- Stage 2 combined: outer and inner signs fused via `sgn_add`.
  have h3 : gE17OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBL Γ a (b + c) (d + e))) u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ a (b + c) (d + e)) w (GBL.mk Γ a (b + c) (d + e) v q')))
    = ((sgn (gParity K Γ a (b + c) (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) w
            (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q'))) := by
    rw [h3a, h3b, map_zsmul, smul_smul, ← Units.val_mul, ← sgn_add,
      show gParity K Γ a (b + c) (d + e) * ju + gParity K Γ a (b + c) (d + e) * jw
          = gParity K Γ a (b + c) (d + e) * (ju + jw) from by ring]
  -- Stages 1–2 combined, signs fused via `sgn_add`.
  have hOuterFull : gE17OuterStep K Γ a b c d e
      (gV7AssocABC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
    = ((sgn (jw * jv + gParity K Γ a (b + c) (d + e) * (ju + jw)) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) w
            (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q'))) := by
    rw [hABC, map_zsmul, h3, smul_smul, ← Units.val_mul, ← sgn_add]
  -- Stage 3: `gE17FinalStepWrapped`, the unsigned wrap of `gq4Close`.
  have h4 : gE17FinalStepWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))
        u
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ a (b + c) (d + e)) w
          (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q'))))
    = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) u
        (gq4Close K Γ a (b + c) d e
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) w
            (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q')))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
        (gE17FinalStep K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gE17FinalStep_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GBR Γ a (b + c) (d + e)))
          u
          (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ a (b + c) (d + e)) w
            (gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q')))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    rfl
  -- Re-fold `gq2rCast`+`gTCanon` into the single `GE2`-genre `gt2Canon` application.
  have hGt2 : gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q)
    = gTCanon K Γ a (b + c) (d + e) (GBL.mk Γ a (b + c) (d + e) v q') :=
    gt2Canon_mk K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e)) v q
  show (gV12Assoc K Γ a b c d e).symm
      (gE17FinalStepWrapped K Γ a b c d e
        (gE17OuterStep K Γ a b c d e
          (gV7AssocABC K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
              (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q))))) = _
  rw [hOuterFull, map_zsmul, h4, map_zsmul, ← hGt2]

end GaugeChi

end Superfusion
