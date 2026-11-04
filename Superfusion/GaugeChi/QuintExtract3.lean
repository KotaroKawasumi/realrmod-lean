/-
Superfusion / GaugeChi / QuintExtract3

Milestone M13-R3 of the `(p, χ)` arc's CLUSTER-FACE phase, executing round
R3 of `docs/m13-cluster-route.md` (the spectator-whisker recognition
route): **`recog_E17M`**, the `PDE`-face recognition at edge 17
(`omegaV12 ∘ₗ E17M = smap(GE2 …) ∘ₗ omegaV7`).

## What lands

* `omegaV7_mk_of_mem'`: `omegaV7_mk_of_mem` restated with the domain's
  first factor split as `GBR.mk u v` (`u : F_{b,c}` degree `ju`,
  `v : F_{a,b+c}` arbitrary) via `GBR.mk_mem_grading` — needed so the SAME
  generator `E17M_leaf` decomposes (`u,v,w` all individually homogeneous)
  can be chased through `omegaV7` too.
* `omegaV12_mk_of_mem'`: `omegaV12_mk_of_mem` restated with its `GQ4r.mk`
  wrapped argument respelled via the literal `RelTensor.mk` E17M_leaf's own
  conclusion uses — the `QuintFaces3` "`rw` does not see through
  `def`-wrappers" discipline (`GE1_mk'`/`GE4_mk_of_mem_canon`'s pattern):
  `GQ4r.mk` unfolds to `RelTensor.mk` by `def`, so the RESPELLED statement
  is proved by a bare term-mode application of `omegaV12_mk_of_mem` (defeq
  handles the unfold), while the respelling itself lets subsequent `rw`
  fire syntactically against `E17M_leaf`'s own raw-`RelTensor.mk` spelling.
* `GE2_mk_of_mem_canon`: `GE2_mk_of_mem`, specialized to the canonical
  second-edge intertwiner data `t₂ := (gt2Canon K Γ a b c (d+e) (gTCanon K
  Γ a (b+c) (d+e))).toLinearMap` / `ht₂ := gt2Canon_bcSlot …` and restated
  through `GQ2.mk`/`GQ3.mk` (the same `GE1_mk'`-style bridge, needed since
  `omegaV7_mk_of_mem'`'s own conclusion lands on `GQ2.mk`-shaped terms).
* **`recog_E17M`**: `(omegaV12).toLinearMap ∘ₗ E17M K Γ a b c d e =
  smap(GE2 K Γ a b c (d+e) (gParity K Γ a (b+c) (d+e)) (gt2Canon …
  (gTCanon …)).toLinearMap (gt2Canon_bcSlot …)) (gParity K Γ a (b+c)
  (d+e)) (hg2 K Γ a b c d e) ∘ₗ (omegaV7).toLinearMap`. Proved by
  `RelTensor.hom_ext` + nested induction: `n : GBR Γ (a+b+c) d e` split via
  `GBR.induction_on_left_homog` (`w` homogeneous, `q` arbitrary), then
  `m : GBR Γ a b c` split via `GBR.induction_on_gen2` (`u,v` both
  homogeneous — `E17M_leaf`'s own middle-swap stage genuinely exchanges the
  `v`- and `w`-columns and needs both graded, mirroring `E14M_leaf`'s
  precedent). The sign ledger (route doc §2, re-verified here): LHS
  `E17M_leaf`'s `sgn(jw·jv + p₂·(ju+jw))` composed with `omegaV12`'s own
  midSwap `sgn(jw·ju)` (`p₂ := gParity K Γ a (b+c) (d+e)`); RHS `omegaV7`'s
  own midSwap on the COMBINED degree `sgn(jw·(ju+jv))` composed with the
  outer `(d+e)`-slot `smap`'s `sgn(p₂·jw)` and `GE2_mk_of_mem`'s own
  `sgn(p₂·ju)` — both exponent sums reduce to the identical five-term
  expression `jw·jv + p₂·ju + p₂·jw + jw·ju` (`decide`, `ZMod 2`), matching
  termwise. The `gV12Assoc`/`gq4Close K Γ a (b+c) d e` cast tower inside
  `E17M_leaf`'s own reinsertion and `omegaV12_mk_of_mem`'s own
  reconstruction cancel AS EQUIV ROUND-TRIPS — `omegaV12_mk_of_mem'`'s
  LHS pattern `(gV12Assoc).symm (mk u (gq4Close (mk w p)))` is EXACTLY
  `E17M_leaf`'s own reinsertion shape (with `p := gt2Canon … (mk v q)`
  left UNEXPANDED, per the established "leave the canonical image
  unexpanded" convention), so no further cast bookkeeping is needed beyond
  matching the two statements' spellings.

## `recog_E21M`: NOT landed this round — the finding

`recog_E21M`'s recognized composite is `(gq4Close K Γ a b c (d+e)).toLinearMap
∘ₗ GE5 K Γ a b c (d+e) …`. Tracing `E21M_leaf`'s own conclusion
(`QuintRecog5.lean:300-315`) against `omegaV9`/`omegaV14`'s own
construction (`QuintExtract.lean`/`QuintExtract2.lean`) surfaces a
genuine ORDER-OF-OPERATIONS obstruction, distinct from (and, on inspection,
deeper than) the `gTCanon`-argument transport gate (α) already discharged
in `QuintExtract.lean`:

* On the DOMAIN side, `E21M_leaf` keeps the swapped `GBR(c,d,e)` column
  `n` as a SINGLE opaque homogeneous element (no further split — its own
  docstring: "no downstream stage … would need it split"). Matching this
  against `omegaV9`'s own leaf (`omegaV9_mk_of_mem`, which needs the
  `V9Inner`-factor pre-expressed as `omegaV9Gen w p'' := gq4Close K Γ
  (a+b) c d e (GQ4r.mk w p'')`, i.e. as the IMAGE of `gq4Close` on a SPLIT
  `GQ4r`-generator) is tractable IF `n` is split ONE level further
  (`n = GBR.mk w s`, `w : F_{d,e}` homogeneous, `s : F_{c,d+e}`
  homogeneous) — traced by hand via `gq4Close_mk` (`Pentagon.lean:568`)
  this reconciles through a SINGLE `fusionColumnCast K Γ (a+b) (add_assoc
  c d e).symm` recast on the outer column, which DOES cancel (an
  `apply_symm_apply` round-trip), so the DOMAIN side alone is tractable.
* On the CODOMAIN side, however, `E21M_leaf`'s own closing move
  `gV14StepFinal` (a plain `RelTensor.assoc.symm`) is APPLIED, per its own
  docstring, to the raw `mk n Y` argument where `Y := (gq3rCast K Γ a b c
  d e).symm (gTCanon K Γ a b (c+d+e) (mk t p))` is left UNEXPANDED (the
  established convention, since `Y` is an opaque canonical-intertwiner
  image with no further `mk`-decomposition). But `RelTensor.assoc.symm`'s
  OWN generator formula (`assoc_symm_mk`, `RelTensor.bwd_mk` composed with
  `bwdInnerFlip_mk`, `Bimod/RelTensorAssoc.lean:148-238`) requires the
  SECOND-factor argument (here `Y`, itself of the `N ⊗[B] P`-shape
  `RelTensor.assoc` splits) to ALREADY be presented as `mk s x` for KNOWN
  `s, x` to reduce past `bwd_mk`'s general (but non-`mk`-shaped) output
  `bwdInnerFlip Y n` — i.e. `gV14StepFinal (mk n Y)`, for OPAQUE `Y`, has
  NO further `mk`-shaped reduction, so `omegaV14StageA`'s own leaf
  (`mapEquivLeft (gq4Close K Γ b c d e).symm`, itself needing its argument
  in `RelTensor.mk (GQ4-value) x` shape to fire via `RelTensor.map_mk`)
  cannot be applied to `gV14StepFinal (mk n Y)` directly. This is the SAME
  underlying obstruction that already forces `E21M_leaf` itself to stop at
  `gV14StepFinal (mk n Y)` unexpanded (mirrored, one level up, against
  `omegaV14`'s own construction) — i.e. it is NOT a missing device (no
  `gq4TotalCast`-style recast is going to fix an order-of-application
  mismatch), but a genuine need for EITHER (i) a general naturality lemma
  commuting `RelTensor.map` (on the outer factor) past `RelTensor.assoc`
  (on an INNER, opaque argument) — not currently in the toolkit — OR
  (ii) a re-derivation of `omegaV14`'s OWN construction ordered so its
  `gq4Close`-peel happens BEFORE (not after) the `assoc`-regrouping that
  produces `V14`'s native `GQ4 K Γ b c d e` factor, mirroring how
  `omegaV12`'s `gV12Assoc`-then-`mapEquivRight` ordering avoided the
  analogous gap for `E17M`. Per the round brief's own fallback clause,
  `recog_E21M` is deferred rather than inventing either device under this
  round's budget; `recog_E17M` (which alone gates `face_PDE`'s top route,
  together with the already-landed `recog_E20M`) lands this round instead.
-/
import Superfusion.GaugeChi.QuintExtract2

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

/-! ### `recog_E17M` -/

section RecogE17M

/-- `omegaV7_mk_of_mem`, restated with the domain's first factor split as
`GBR.mk u v` (`u : F_{b,c}` degree `ju`, `v : F_{a,b+c}` arbitrary) via
`GBR.mk_mem_grading` — needed so the SAME generator `E17M_leaf` decomposes
(all of `u,v,w` individually homogeneous) can be chased through `omegaV7`
as well. -/
theorem omegaV7_mk_of_mem' {ju jv jw : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse a (b + c))} (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (p : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    omegaV7 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c) (GBR Γ (a + b + c) d e)
          (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w p))
      = ((sgn (jw * (ju + jv)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ2 K Γ a b c (d + e)) w
            (GQ2.mk K Γ a b c (d + e) (GBR.mk Γ a b c u v) p) :=
  omegaV7_mk_of_mem K Γ a b c d e (GBR.mk_mem_grading Γ a b c hu hv) hw p

/-- `omegaV12_mk_of_mem`, restated with the `GQ4r.mk`-wrapped argument
respelled via the literal `RelTensor.mk` `E17M_leaf`'s own conclusion
uses — the `QuintFaces3` "`rw` does not see through `def`-wrappers"
discipline: `GQ4r.mk` unfolds to `RelTensor.mk` by `def`, so this
respelling is proved by a bare term-mode application of
`omegaV12_mk_of_mem` (defeq handles the unfold), while the RESTATEMENT
lets subsequent `rw` fire syntactically against `E17M_leaf`'s own
raw-`RelTensor.mk` spelling. -/
theorem omegaV12_mk_of_mem' {ju jw : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju) {w : FusionColumn (Γ.fuse d e)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw) (p : GBR Γ a (b + c) (d + e)) :
    omegaV12 K Γ a b c d e
        ((gV12Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
            (GQ4 K Γ a (b + c) d e) u
            ((gq4Close K Γ a (b + c) d e)
              (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                (GBR Γ a (b + c) (d + e)) w p))))
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ3 K Γ a b c (d + e)) w (GQ3.mk K Γ a b c (d + e) u p) :=
  omegaV12_mk_of_mem K Γ a b c d e hu hw p

/-- `GE2_mk_of_mem`, specialized to the canonical second-edge intertwiner
data `t₂ := (gt2Canon K Γ a b c (d+e) (gTCanon K Γ a (b+c) (d+e))).
toLinearMap` / `ht₂ := gt2Canon_bcSlot …` and restated through
`GQ2.mk`/`GQ3.mk` (the `GE1_mk'`-style bridge — `rw` needs the SYNTACTIC
`GQ2.mk`-shaped domain `omegaV7_mk_of_mem'`'s own conclusion produces). -/
theorem GE2_mk_of_mem_canon {j : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j) (v : FusionColumn (Γ.fuse a (b + c)))
    (q : FusionColumn (Γ.fuse (a + b + c) (d + e))) :
    GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
        (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e)) (gParity K Γ a (b + c) (d + e))
          (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e)))
        (GQ2.mk K Γ a b c (d + e) (GBR.mk Γ a b c u v) q)
      = ((sgn (gParity K Γ a (b + c) (d + e) * j) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c (d + e) u
            (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q)) :=
  GE2_mk_of_mem K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
    (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e)) (gParity K Γ a (b + c) (d + e))
      (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e))) hu v q

/-- **`recog_E17M`**: the `PDE`-face recognition at edge 17 —
`omegaV12 ∘ₗ E17M = smap(GE2 …) ∘ₗ omegaV7`, at `GE2`'s own parity
`p₂ := gParity K Γ a (b+c) (d+e)`. Proved by `hom_ext` + nested induction
(`n : GBR Γ (a+b+c) d e` peeled to `GBR.mk w q` via
`GBR.induction_on_left_homog`; `m : GBR Γ a b c` peeled to `GBR.mk u v`,
both `u,v` split by degree via `GBR.induction_on_gen2`), landing on
`E17M_leaf`/`omegaV12_mk_of_mem'`/`omegaV7_mk_of_mem'`/`smap_mk_of_mem`/
`GE2_mk_of_mem_canon` — the sign ledger `jw·jv + p₂·(ju+jw) + jw·ju`
(LHS) vs `jw·(ju+jv) + p₂·jw + p₂·ju` (RHS) match termwise (`decide`,
`ZMod 2`). -/
theorem recog_E17M :
    (omegaV12 K Γ a b c d e).toLinearMap ∘ₗ E17M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
            (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e)) (gParity K Γ a (b + c) (d + e))
              (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e))))
          (gParity K Γ a (b + c) (d + e)) (hg2 K Γ a b c d e)
          ∘ₗ (omegaV7 K Γ a b c d e).toLinearMap := by
  have sign_id : ∀ p j jv jw : ZMod 2,
      jw * jv + p * (j + jw) + jw * j = jw * (j + jv) + p * jw + p * j := by decide
  refine RelTensor.hom_ext fun m n => ?_
  induction n using GBR.induction_on_left_homog K Γ (a + b + c) d e with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | homog jw w q hw =>
      induction m using GBR.induction_on_gen2 K Γ a b c with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
      | @homog j jv u v hu hv =>
          show (omegaV12 K Γ a b c d e)
              (E17M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (GBR Γ (a + b + c) d e) (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
            = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
                  (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
                  (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
                    (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e))))
                (gParity K Γ a (b + c) (d + e)) (hg2 K Γ a b c d e)
                ((omegaV7 K Γ a b c d e) (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                  (GBR Γ (a + b + c) d e) (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
          have hLHS : (omegaV12 K Γ a b c d e)
              (E17M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                (GBR Γ (a + b + c) d e) (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
              = ((sgn (jw * jv + gParity K Γ a (b + c) (d + e) * (j + jw)) * sgn (jw * j) : ℤˣ)
                  : ℤ) •
                RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ3 K Γ a b c (d + e)) w
                  (GQ3.mk K Γ a b c (d + e) u
                    (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q))) := by
            rw [E17M_leaf K Γ a b c d e hu hv hw q]
            refine (map_zsmul (omegaV12 K Γ a b c d e) _ _).trans ?_
            rw [omegaV12_mk_of_mem' K Γ a b c d e hu hw, smul_smul, ← Units.val_mul]
          have hRHS : smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
                  (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
                  (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
                    (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e))))
                (gParity K Γ a (b + c) (d + e)) (hg2 K Γ a b c d e)
                ((omegaV7 K Γ a b c d e) (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
                  (GBR Γ (a + b + c) d e) (GBR.mk Γ a b c u v) (GBR.mk Γ (a + b + c) d e w q)))
              = ((sgn (jw * (j + jv)) * sgn (gParity K Γ a (b + c) (d + e) * jw)
                  * sgn (gParity K Γ a (b + c) (d + e) * j) : ℤˣ) : ℤ) •
                RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
                  (GQ3 K Γ a b c (d + e)) w
                  (GQ3.mk K Γ a b c (d + e) u
                    (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))
                      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                        (FusionColumn (Γ.fuse (a + b + c) (d + e))) v q))) := by
            rw [omegaV7_mk_of_mem' K Γ a b c d e hu hv hw q]
            refine (map_zsmul _ _ _).trans ?_
            rw [smap_mk_of_mem (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
                (GE2 K Γ a b c (d + e) (gParity K Γ a (b + c) (d + e))
                  (gt2Canon K Γ a b c (d + e) (gTCanon K Γ a (b + c) (d + e))).toLinearMap
                  (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c) (d + e))
                    (gParity K Γ a (b + c) (d + e)) (gTCanon_mem_gInterSpace K Γ a (b + c) (d + e))))
                (gParity K Γ a (b + c) (d + e)) (hg2 K Γ a b c d e) hw,
              GE2_mk_of_mem_canon K Γ a b c d e hu v q, map_zsmul, smul_smul, smul_smul,
              ← Units.val_mul, ← Units.val_mul]
          rw [hLHS, hRHS]
          congr 2
          rw [← sgn_add, ← sgn_add, ← sgn_add, sign_id]

end RecogE17M

end GaugeChi

end Superfusion
