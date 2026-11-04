/-
Superfusion / GaugeChi / QuintFaces3

Milestone M13-4d-ii of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): **`face_PAB` landed**, the `(a+b)`-cluster pentagon face
(`docs/m13-design.md`'s ledger), completing the program `QuintRecog.lean`/
`QuintRecog2.lean`/`QuintRecog3.lean`/`QuintFaces2.lean` set up (the five
`PAB`-face recognition leaves `E4M_leaf`, `E11M_leaf`/`E11M_general`,
`E12M_leaf`/`E12M_general`, `E13M_leaf`, `E14M_leaf`/`E14M_general`, and the
four bridge facts `topInner1`, `topInner2`, `botInner1`, `botInner2`
identifying the `PAB`-face's inner composites with `gChiCanon_spec K Γ
(a+b) c d e`'s own `gTopRoute`/`gBotRoute`).

## The performance strategy

The previous round's diagnosis (`QuintFaces2.lean`'s module docstring)
found the FINAL assembly of `face_PAB` from these nine facts hits a
genuine Lean elaboration-performance wall when done as ONE `have`-chain
(`h1`..`h7`/`hspec`/`hcocycle`/`hsign`, all inside a single `faceCore`
theorem) — the round's prescribed fix, followed here, is to SPLIT the
assembly into independently-compiled top-level lemmas, one per genre:

* `topComposite`: the top-route pointwise reinsertion — chains
  `E4M_leaf` → `E11M_general` → `E12M_general` (three already-landed
  leaves) with `topInner1`/`topInner2`/`GE1_mk` (identifying the
  resulting inner composite with `gTopRoute K Γ (a+b) c d e`'s own value
  at the shared element `m`), landing a SINGLE combined `ℤ`-sign
  `sgn(gParity(a+b,c,d)·ju) * sgn(gParity(a+b,c+d,e)·ju) *
  sgn(gParity(c,d,e)·ju)` (left in DISTRIBUTED form, `Units.val_mul`/
  `sgn_add` combining the three `smul`s but not yet the three summands —
  matching what the chain naturally produces, deferring the
  factored-vs-distributed bridge entirely to the sign lemma).
* `botComposite`: the bottom-route pointwise reinsertion — chains
  `E13M_leaf` → `E14M_general` with `botInner1`/`botInner2` (the `GE4`
  reinsertion inverted via the standard `sgn`-self-inverse idiom,
  `sgn_mul_self'`, since `botInner1` produces `GE4(m) = sgn(·)·(mk v Z)`
  and the assembly needs the mirror `mk v Z = sgn(·)·GE4(m)`), landing
  `gBotRoute K Γ (a+b) c d e`'s value at the SAME `m`, with the honest
  THREE-term sign `gParity(a+b+c,d,e)·(ju+jv) + gParity(a+b,c,d+e)·ju +
  gParity(a+b+c,d,e)·jv` (no attempt to collapse the two
  `gParity(a+b+c,d,e)`-keyed terms here — that cancellation is exactly
  what the sign lemma below performs, algebraically, given the cocycle).
* `facePAB_signId`: a PURE `ZMod 2` algebra fact (no `RelTensor` content
  at all) bridging `topComposite`'s distributed top total to
  `botComposite`'s three-term bottom total, given `gParity_cocycle` as a
  hypothesis — closed by a four-variable `decide` after one `ring`
  normalization and one substitution. This is the hotspot the previous
  round's `hsign`/`hcocycle` pair was fused into a single deep have-chain;
  isolating it as an independent lemma with NO vertex types elaborates
  instantly.
* `facePAB_gen`: the SHORT generator-level assembly — `topComposite` +
  `botComposite` + `facePAB_signId` (bridging the two signs) +
  `gChiCanon_spec K Γ (a+b) c d e` applied pointwise (`LinearMap.congr_fun`)
  + one `smul_comm` (reordering the residual `ℤ`-sign past the `K`-scalar
  `gChiCanon`).
* `face_PAB`: the final `LinearMap.ext` + FOUR nested nested inductions
  (`RelTensor.induction_on` down to the raw `GBL a b c`-generator `mk U V`,
  then `DirectSum.Decomposition.inductionOn` on `U` then `V` to reach the
  doubly-homogeneous generator `E4M_leaf`/`E13M_leaf` need), each
  `zero`/`add` branch closed by the generic `map_zero`/`map_add` pair
  (both sides of the face equation are packaged as OPAQUE `K`-linear maps
  throughout — `E12M ∘ₗ E11M ∘ₗ E4M` and `gChiCanon • (E14M ∘ₗ E13M)` are
  never unfolded past their own `LinearMap`/`Module`-structure during the
  zero/add branches, so `map_zero`/`map_add`/`LinearMap.map_zero₂`/
  `LinearMap.map_add₂` alone close all eight trivial branches), the one
  nontrivial leaf closed by `facePAB_gen`.

**Result** (in `gChiCanon_spec`'s own orientation, matching `face_P6`/
`face_P1`'s convention, `QuintFaces.lean`):

  `E12M ∘ₗ E11M ∘ₗ E4M = gChiCanon K Γ (a+b) c d e • (E14M ∘ₗ E13M)`,
  `V1 K Γ a b c d e → V9 K Γ a b c d e`.
-/
import Superfusion.GaugeChi.QuintFaces2

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

/-! ### `topComposite`: the top-route pointwise reinsertion -/

/-- **`topComposite`**: `E12M ∘ E11M ∘ E4M`, evaluated at a fully-decomposed
`V1`-generator (`u` homogeneous of degree `ju`, `v, w, x` arbitrary),
equals a single `ℤ`-sign (left in DISTRIBUTED form) times the
`F_{a,b}`-signed-whisker of `gTopRoute K Γ (a+b) c d e`'s own canonical
data, applied at the shared shifted `GQ1`-element `m := mk (GBL.mk v w) x`.
Chains `E4M_leaf` → `E11M_general` → `E12M_general` with `topInner1`/
`topInner2`/`GE1_mk` (`QuintFaces2.lean`/`PentagonEdges.lean`), no new
toolkit content. -/
theorem topComposite {ju : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d))
    (x : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E12M K Γ a b c d e (E11M K Γ a b c d e (E4M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)))
      = ((sgn (gParity K Γ (a + b) c d * ju + gParity K Γ (a + b) (c + d) e * ju
          + gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gTopRoute K Γ (a + b) c d e
              (gTCanon K Γ (a + b) c d).toLinearMap (gCanonRight K Γ (a + b) c d)
              (gParity K Γ (a + b) (c + d) e)
              (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
              (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
                (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
              (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)) := by
  have h1 := E4M_leaf K Γ a b c d e hu v w x
  have h2 := E11M_general K Γ a b c d e hu
    (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x
  have h3 := E12M_general K Γ a b c d e hu
    (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))))
  have h4 := topInner1 K Γ a b c d e (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x
  have h5 := topInner2 K Γ a b c d e
    (GE2 K Γ (a + b) c d e (gParity K Γ (a + b) (c + d) e)
      (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
      (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
        (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))
  have h6 := GE1_mk K Γ (a + b) c d e (gTCanon K Γ (a + b) c d).toLinearMap
    (gCanonRight K Γ (a + b) c d) (GBL.mk Γ (a + b) c d v w) x
  simp only [LinearEquiv.coe_toLinearMap] at h6
  -- the inner-composite bridge: `E12MInnerEquiv W` (`W` the opaque composite `h2`/`h3` produce)
  -- equals `gTopRoute`'s own value at the shared shifted element, via `topInner1`/`topInner2`/`GE1_mk`.
  have hW : E12MInnerEquiv K Γ a b c d e
      (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))))
      = gTopRoute K Γ (a + b) c d e
          (gTCanon K Γ (a + b) c d).toLinearMap (gCanonRight K Γ (a + b) c d)
          (gParity K Γ (a + b) (c + d) e)
          (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
          (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
            (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
          (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
          (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x) := by
    rw [← h4, ← h5, ← h6]
    rfl
  calc E12M K Γ a b c d e (E11M K Γ a b c d e (E4M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)))
      = E12M K Γ a b c d e (E11M K Γ a b c d e
          (((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x)) :=
        congrArg (fun z => E12M K Γ a b c d e (E11M K Γ a b c d e z)) h1
    _ = E12M K Γ a b c d e (((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) •
          E11M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x)) :=
        congrArg (fun z => E12M K Γ a b c d e z)
          (map_zsmul (E11M K Γ a b c d e) (((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ))
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x))
    _ = ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) •
          E12M K Γ a b c d e (E11M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x)) :=
        map_zsmul (E12M K Γ a b c d e) (((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ))
          (E11M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e))
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w))) x))
    _ = ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) •
          E12M K Γ a b c d e (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) u
              (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e))
                  (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) • E12M K Γ a b c d e z) h2
    _ = ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) • (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
          E12M K Γ a b c d e (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (V8Inner K Γ a b c d e) u
            (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e))
                (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x)))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) • z)
          (map_zsmul (E12M K Γ a b c d e) (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) u
              (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e))
                  (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))))))
    _ = ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) • (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) • RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u (E12MInnerEquiv K Γ a b c d e
              (gE11GBRAssoc K Γ a b c d e (gE11InnerStep K Γ a b c d e (gV3AssocBC K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e))
                  (gTCanon K Γ (a + b) c d (GBL.mk Γ (a + b) c d v w)) x))))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) •
            (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) • z)) h3
    _ = ((sgn (gParity K Γ (a + b) c d * ju) : ℤˣ) : ℤ) • (((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) • RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gTopRoute K Γ (a + b) c d e
              (gTCanon K Γ (a + b) c d).toLinearMap (gCanonRight K Γ (a + b) c d)
              (gParity K Γ (a + b) (c + d) e)
              (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
              (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
                (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
              (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)))) := by
        rw [hW]
    _ = ((sgn (gParity K Γ (a + b) c d * ju + gParity K Γ (a + b) (c + d) e * ju
          + gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gTopRoute K Γ (a + b) c d e
              (gTCanon K Γ (a + b) c d).toLinearMap (gCanonRight K Γ (a + b) c d)
              (gParity K Γ (a + b) (c + d) e)
              (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
              (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
                (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
              (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)) := by
        rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add]

/-! ### `botComposite`: the bottom-route pointwise reinsertion -/

/-- **`botComposite`**: `E14M ∘ E13M`, evaluated at the SAME fully-decomposed
`V1`-generator (`u` homogeneous of degree `ju`, `v` homogeneous of degree
`jv`, `w, x` arbitrary), equals the honest THREE-term `ℤ`-sign times the
`F_{a,b}`-signed-whisker of `gBotRoute K Γ (a+b) c d e`'s own canonical
data, applied at the SAME `m`. Chains `E13M_leaf` → `E14M_general` with
`botInner1`/`botInner2` (`QuintFaces2.lean`), `botInner1`'s own reinsertion
inverted via the standard `sgn`-self-inverse idiom (`sgn_mul_self'`,
already used pervasively across this codebase). -/
theorem botComposite {ju jv : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) (x : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E14M K Γ a b c d e (E13M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x))
      = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
          + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gBotRoute K Γ (a + b) c d e
              (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
              (gCanonHphi4 K Γ (a + b) c d e)
              (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
              (gCanonHphi5 K Γ (a + b) c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)) := by
  have h1 := E13M_leaf K Γ a b c d e hu hv w x
  have h2 := E14M_general K Γ a b c d e hu v
    (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))
  have h3 := botInner2 K Γ a b c d e v
    (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))
  -- `h4` is re-ascribed with `GBL.mk`-wrapped spelling of `botInner1`'s own raw-`RelTensor.mk`
  -- inner argument to `gTCanon` (defeq, but the wrapped spelling needs no `GBL`-unfolding to
  -- type-check, sidestepping the `instances`-transparency trap subsequent `rw`s would otherwise
  -- hit on the raw spelling).
  have h4 : GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
      (gCanonHphi4 K Γ (a + b) c d e)
      (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)
    = ((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v
          (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)) :=
    botInner1 K Γ a b c d e hv w x
  have h4' : ((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
      GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
        (gCanonHphi4 K Γ (a + b) c d e)
        (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)
    = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) v
        (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)) :=
    (congrArg (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) • ·) h4).trans
      ((smul_smul (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
          (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v
            (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)))).trans
        ((congrArg (· • RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (GBR Γ (a + b + c) d e) v (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)))
            (show (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
                * (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ)) = 1 from by
              rw [← Units.val_mul, sgn_mul_self', Units.val_one])).trans
          (one_smul ℤ (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v
            (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))))))
  calc E14M K Γ a b c d e (E13M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x))
      = E14M K Γ a b c d e (((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
            (GBL.mk Γ a b c u v) (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))) :=
        congrArg (fun z => E14M K Γ a b c d e z) h1
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          E14M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
              (GBL.mk Γ a b c u v) (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))) :=
        map_zsmul (E14M K Γ a b c d e) (((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
            (GBL.mk Γ a b c u v) (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)))
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
              (gE14FinalStep K Γ a b c d e (gE14InnerStep K Γ a b c d e (gV6Swap K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e) v
                  (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x))))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) • z) h2
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
              (gE14FinalStep K Γ a b c d e (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
                (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
                (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                  (GBR Γ (a + b + c) d e) v
                  (gTCanon K Γ (a + b + c) d e (GBL.mk Γ (a + b + c) d e w x)))))) := by
        rw [h3]
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
              (gE14FinalStep K Γ a b c d e (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
                (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
                (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
                  GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                    (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))))) := by
        rw [← h4']
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
              (gE14FinalStep K Γ a b c d e (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
                GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
                  (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                    (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
            (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
              RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (V9Inner K Γ a b c d e) u (gE14FinalStep K Γ a b c d e z)))
          (map_zsmul (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
              (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e))
            (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
            (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
              (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)))
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V9Inner K Γ a b c d e) u
              (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
                gE14FinalStep K Γ a b c d e (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
                  (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                    (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
            (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
              RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (V9Inner K Γ a b c d e) u z))
          (map_zsmul (gE14FinalStep K Γ a b c d e)
            (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
            (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
              (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
              (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))))
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
          (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
            (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
              RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (V9Inner K Γ a b c d e) u
                (gE14FinalStep K Γ a b c d e (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
                  (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
                  (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                    (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)))))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)) : ℤˣ) : ℤ) •
            (((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) • z))
          (map_zsmul (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V9Inner K Γ a b c d e) u)
            (((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ))
            (gE14FinalStep K Γ a b c d e (GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
              (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
              (GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
                (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
                (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)))))
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
          + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gBotRoute K Γ (a + b) c d e
              (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
              (gCanonHphi4 K Γ (a + b) c d e)
              (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
              (gCanonHphi5 K Γ (a + b) c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)) := by
        rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add]
        rfl

/-! ### `facePAB_signId`: the pure `ZMod 2` sign identity -/

/-- **`facePAB_signId`**: a PURE `ZMod 2` algebra fact, no `RelTensor`
content — `topComposite`'s distributed top total equals `botComposite`'s
three-term bottom total, GIVEN the cocycle relation `P1+P2+P3 = P4+P5`
(`gParity_cocycle` at the shifted quadruple). Closed by one `ring`
normalization (distributed → factored), one substitution, and a
four-variable `decide` — no vertex types anywhere, elaborates instantly. -/
theorem facePAB_signId (P1 P2 P3 P4 P5 ju jv : ZMod 2) (hcocycle : P1 + P2 + P3 = P4 + P5) :
    P1 * ju + P2 * ju + P3 * ju = P4 * (ju + jv) + P5 * ju + P4 * jv := by
  have hpure : ∀ Q4 Q5 x y : ZMod 2, (Q4 + Q5) * x = Q4 * (x + y) + Q5 * x + Q4 * y := by
    decide +revert
  calc P1 * ju + P2 * ju + P3 * ju = (P1 + P2 + P3) * ju := by ring
    _ = (P4 + P5) * ju := by rw [hcocycle]
    _ = P4 * (ju + jv) + P5 * ju + P4 * jv := hpure P4 P5 ju jv

/-! ### `facePAB_gen`: the generator-level assembly -/

/-- **`facePAB_gen`**: the SHORT generator-level assembly — `topComposite`
+ `botComposite` + `facePAB_signId` (bridging the two signs via
`gParity_cocycle K Γ (a+b) c d e`) + `gChiCanon_spec K Γ (a+b) c d e`
applied pointwise + one `smul_comm` (reordering the residual `ℤ`-sign past
the `K`-scalar `gChiCanon`). -/
theorem facePAB_gen {ju jv : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) (x : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E12M K Γ a b c d e (E11M K Γ a b c d e (E4M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
            (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)))
      = gChiCanon K Γ (a + b) c d e •
          E14M K Γ a b c d e (E13M K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ1 K Γ a b c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e))
                (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
                  (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w) x)) := by
  rw [topComposite K Γ a b c d e hu v w x, botComposite K Γ a b c d e hu hv w x]
  rw [facePAB_signId (gParity K Γ (a + b) c d) (gParity K Γ (a + b) (c + d) e) (gParity K Γ c d e)
    (gParity K Γ (a + b + c) d e) (gParity K Γ (a + b) c (d + e)) ju jv
    (gParity_cocycle K Γ (a + b) c d e)]
  have hspec := LinearMap.congr_fun (gChiCanon_spec K Γ (a + b) c d e)
    (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)
  calc ((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
        + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
          (gTopRoute K Γ (a + b) c d e
            (gTCanon K Γ (a + b) c d).toLinearMap (gCanonRight K Γ (a + b) c d)
            (gParity K Γ (a + b) (c + d) e)
            (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
              (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
            (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
            (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))
      = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
          + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
            (gChiCanon K Γ (a + b) c d e •
              gBotRoute K Γ (a + b) c d e
                (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
                (gCanonHphi4 K Γ (a + b) c d e)
                (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
                (gCanonHphi5 K Γ (a + b) c d e)
                (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)
            + gParity K Γ (a + b) c (d + e) * ju + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V9Inner K Γ a b c d e) u z) hspec
    _ = ((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
          + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
          (gChiCanon K Γ (a + b) c d e •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
              u
              (gBotRoute K Γ (a + b) c d e
                (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
                (gCanonHphi4 K Γ (a + b) c d e)
                (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
                (gCanonHphi5 K Γ (a + b) c d e)
                (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))) :=
        congrArg (fun z => ((sgn (gParity K Γ (a + b + c) d e * (ju + jv)
            + gParity K Γ (a + b) c (d + e) * ju + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) • z)
          (map_smul (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V9Inner K Γ a b c d e) u) (gChiCanon K Γ (a + b) c d e)
            (gBotRoute K Γ (a + b) c d e
              (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
              (gCanonHphi4 K Γ (a + b) c d e)
              (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
              (gCanonHphi5 K Γ (a + b) c d e)
              (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x)))
    _ = gChiCanon K Γ (a + b) c d e •
          (((sgn (gParity K Γ (a + b + c) d e * (ju + jv) + gParity K Γ (a + b) c (d + e) * ju
              + gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
            RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
              u
              (gBotRoute K Γ (a + b) c d e
                (gParity K Γ (a + b + c) d e) (gTCanon K Γ (a + b + c) d e).toLinearMap
                (gCanonHphi4 K Γ (a + b) c d e)
                (gParity K Γ (a + b) c (d + e)) (gTCanon K Γ (a + b) c (d + e)).toLinearMap
                (gCanonHphi5 K Γ (a + b) c d e)
                (GQ1.mk K Γ (a + b) c d e (GBL.mk Γ (a + b) c d v w) x))) :=
        smul_comm _ _ _

/-! ### `face_PAB`: the `(a+b)`-cluster pentagon face -/

/-- **`face_PAB`**: the `(a+b)`-cluster pentagon face
(`docs/m13-design.md`'s ledger), in `gChiCanon_spec`'s OWN orientation
(matching `face_P6`/`face_P1`'s convention, `QuintFaces.lean`) — the
3-edge route `E12M ∘ E11M ∘ E4M : V1 → V9` equals `gChiCanon K Γ (a+b) c d
e` acting on the 2-edge route `E14M ∘ E13M : V1 → V9`. Proved by
`LinearMap.ext` + four nested inductions (`RelTensor.induction_on` down to
the raw `GBL a b c`-generator `mk U V`, then `DirectSum.Decomposition.
inductionOn` on `U` then `V` to reach the doubly-homogeneous generator
`facePAB_gen` needs), every `zero`/`add` branch closed by the generic
`map_zero`/`map_add` pair alone (both sides packaged as opaque `K`-linear
maps throughout), the one nontrivial leaf closed by `facePAB_gen`. -/
theorem face_PAB :
    E12M K Γ a b c d e ∘ₗ E11M K Γ a b c d e ∘ₗ E4M K Γ a b c d e
      = gChiCanon K Γ (a + b) c d e • (E14M K Γ a b c d e ∘ₗ E13M K Γ a b c d e) := by
  refine RelTensor.hom_ext fun m x => ?_
  induction m using GQ1.induction_on_gen2 K Γ a b c d with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | homog u v w hu hv => exact facePAB_gen K Γ a b c d e hu hv w x
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']

end GaugeChi

end Superfusion
