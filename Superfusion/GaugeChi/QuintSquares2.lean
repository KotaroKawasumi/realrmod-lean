/-
Superfusion / GaugeChi / QuintSquares2

Milestone M13-5b of the abstract `(p, χ)` arc (the K₅ chain, SQUARE
phase): **`square_S3`**, the last of the three square faces
(`docs/m13-design.md`'s ledger, `{v8,v9,v13,v14}`), built on `E12M`/
`E19M`/`E21M`/`E8M` (`QuintEdges.lean`, `QuintEdges8.lean`) and the two
recognition leaves `E19M_leaf`/`E21M_leaf` (`QuintRecog5.lean`).

**The mechanism**: unlike `S1`/`S2` (two amplifications of `gTCanon` in
DISJOINT slots of a SHARED bracketing tree, related by a single
`smap_comp_mapFirst`-style square lemma), `S3`'s two routes cross an
actual `midSwap` (`E19M`/`E21M`'s own `gV8Swap`/`gV9Swap`) on one side
and a bare `smap` (`E12M`) on the other — a genuine "swap vs `smap`"
commutation that resists a clean map-level toolkit lemma (attempted and
abandoned in an earlier round). Instead the square is assembled
GENERATOR-LEVEL, on a **fully homogeneous-decomposed generator**
`mk t (mk M p)` of `V8` (`t : F_{a,b}` degree `ju`, `M : GBL Γ c d e`
degree `J` — deliberately left OPAQUE, never split into `GBL.mk r s`,
mirroring `E12M_general`'s "opaque second argument" discipline — and
`p` fully arbitrary), then extended to all of `V8` by
`DirectSum.Decomposition.inductionOn`/`RelTensor.induction_on` linearity.

**Two new supports**:

* **`E19M_general`**: the `E19M_leaf` recognition formula with `M`'s own
  internal `GBL.mk r s` split ERASED — `E19M`'s first three stages
  (`gV8Swap`, `gE19InnerStep`, `gq3rCastWrapped`) only ever need `M`'s
  OWN total degree `J` (never `r`,`s` individually: `gV8Swap_mk_of_mem`'s
  hypothesis is already stated at `M`'s own degree, and
  `gq3rCastWrapped` is a plain, unsigned outer wrap) — so the leaf
  generalizes exactly as `E12M_general`/`E11M_general`/`E14M_general` do,
  landing `sgn (J·(ju+Q)) • gV13StepB (gV13RegroupWrapped (gV13StepA (mk
  M Z)))`, `Z := (gq3rCast).symm (gTCanon (mk t p))`, `Q := gParity
  (a,b,c+d+e)`, `M` and `Z` BOTH opaque.
* **`E8M_gV13Chain`**: the coherence identity closing the square's
  content — `E8M` applied to `gV13StepB`'s own construction agrees
  EXACTLY (sign-free) with `gV14StepFinal` applied to the `gTCanon`-
  image of `M`. Proved via two RAW-DOMAIN composite `LinearMap`s
  (`bigLHS`/`bigRHS`, avoiding the `GBL`/`GBR`-def-wrapped-type
  `instances`-transparency trap `QuintEdges.lean`'s docstring documents
  — `RelTensor.induction_on`/`map_add`/`map_zero` only behave for
  `LinearMap`s whose OWN declared domain is the raw `RelTensor A M N`
  spelling, never a `def`-wrapped vertex type), landing on the doubly-
  pure generator `mk (mk r s) (mk v x)` where BOTH routes collapse to
  the identical raw term `mk (mk (gTCanon (mk r s)) v) x` via
  `RelTensor.assoc_mk`/`assoc_symm_mk` (×3) and `E8M_mk`/`GE3_mk`.

**The sign closes to the single product exactly**: combining
`E12M_general` (sign `sgn(P·ju)`, `P := gParity(c,d,e)`) with
`E21M_leaf` (sign `sgn(i·(ju+Q))`, `i := J+P` via `gCanonDeg`/
`mem_homGrading`) gives the LHS route's total exponent
`P·ju + (J+P)·(ju+Q) = J·(ju+Q) + P·Q` (mod 2); the RHS route
(`E19M_general` then the sign-free `E8M_gV13Chain`) has exponent
`J·(ju+Q)` alone — so `LHS = sgn(P·Q) • RHS` EXACTLY, matching the
ledger's stated sign `sgn (gParity(c,d,e)·gParity(a,b,c+d+e))` on the
nose, in the orientation `E21M ∘ E12M = sign • (E8M ∘ E19M)`.
-/
import Superfusion.GaugeChi.QuintFaces
import Superfusion.GaugeChi.QuintFaces2
import Superfusion.GaugeChi.QuintRecog5

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

/-! ### `E8M_gV13Chain`: the sign-free coherence closing the square

Built via two RAW-domain composite `LinearMap`s (never `GBL`/`GBR`
`def`-wrapped types as the DECLARED domain of a map we induct on), so
that `RelTensor.induction_on`/`map_add`/`map_zero` apply cleanly. -/

private noncomputable def bigLHS
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
      →ₗ[K] V14 K Γ a b c d e :=
  (E8M K Γ a b c d e).comp
    ((gV13StepB K Γ a b c d e).toLinearMap.comp
      ((gV13RegroupWrapped K Γ a b c d e).toLinearMap.comp
        ((gV13StepA K Γ a b c d e).toLinearMap.comp
          ((RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e))))).flip Z))))

private noncomputable def bigRHS
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
      →ₗ[K] V14 K Γ a b c d e :=
  (gV14StepFinal K Γ a b c d e).toLinearMap.comp
    (((RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))).flip Z).comp (gTCanon K Γ c d e).toLinearMap)

theorem bigLHS_apply
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e))))
    (M : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (c + d) e))) :
    bigLHS K Γ a b c d e Z M
      = E8M K Γ a b c d e
          (gV13StepB K Γ a b c d e
            (gV13RegroupWrapped K Γ a b c d e
              (gV13StepA K Γ a b c d e
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                  (RelTensor K (Γ.D (b + c + d + e)).carrier
                    (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
                  M Z)))) :=
  rfl

theorem bigRHS_apply
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e))))
    (M : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (c + d) e))) :
    bigRHS K Γ a b c d e Z M
      = gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) (gTCanon K Γ c d e M) Z) :=
  rfl

theorem bigLHS_eq_bigRHS
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    bigLHS K Γ a b c d e Z = bigRHS K Γ a b c d e Z := by
  refine LinearMap.ext fun M => ?_
  induction M using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add M1 M2 hM1 hM2 => rw [map_add, map_add, hM1, hM2]
  | mk r s =>
      show E8M K Γ a b c d e
          (gV13StepB K Γ a b c d e
            (gV13RegroupWrapped K Γ a b c d e
              (gV13StepA K Γ a b c d e
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                  (RelTensor K (Γ.D (b + c + d + e)).carrier
                    (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e))))
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (FusionColumn (Γ.fuse (c + d) e)) r s) Z))))
        = gV14StepFinal K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e))))
              (gTCanon K Γ c d e (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (FusionColumn (Γ.fuse (c + d) e)) r s)) Z)
      induction Z using RelTensor.induction_on with
      | zero => simp only [map_zero]
      | add Z1 Z2 hZ1 hZ2 => simp only [map_add]; rw [hZ1, hZ2]
      | mk v x =>
          have step1 : gV13StepA K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))))
                (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (FusionColumn (Γ.fuse (c + d) e)) r s)
                (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))) v x))
              = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                      (FusionColumn (Γ.fuse a (b + c + d + e))))) r
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                      (FusionColumn (Γ.fuse a (b + c + d + e)))) s
                    (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                      (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                      v x)) :=
            RelTensor.assoc_mk K (Γ.D (c + d)).carrier (Γ.D (c + d + e)).carrier
              (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))) r s
              (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e))) v x)
          have step2 : gV13Regroup K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) s
                (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                  v x))
              = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                  (FusionColumn (Γ.fuse a (b + c + d + e)))
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                    (FusionColumn (Γ.fuse b (c + d + e))) s v) x :=
            RelTensor.assoc_symm_mk K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse (c + d) e)) (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))) s v x
          have step2' : gV13RegroupWrapped K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                      (FusionColumn (Γ.fuse a (b + c + d + e))))) r
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                      (FusionColumn (Γ.fuse a (b + c + d + e)))) s
                    (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                      (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                      v x)))
              = RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) r
                  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                    (FusionColumn (Γ.fuse a (b + c + d + e)))
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                      (FusionColumn (Γ.fuse b (c + d + e))) s v) x) := by
            show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K] _)
                (gV13Regroup K Γ a b c d e).toLinearMap (fun _ _ => rfl)
                (gV13Regroup_aSlot K Γ a b c d e) _ = _
            rw [RelTensor.map_mk, LinearMap.id_apply]
            simp only [LinearEquiv.coe_toLinearMap]
            rw [step2]
          have step3 : gV13StepB K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) r
                  (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3Inner K Γ b c d e)
                    (FusionColumn (Γ.fuse a (b + c + d + e)))
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                      (FusionColumn (Γ.fuse b (c + d + e))) s v) x))
              = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3 K Γ b c d e)
                  (FusionColumn (Γ.fuse a (b + c + d + e)))
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GQ3Inner K Γ b c d e) r
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                      (FusionColumn (Γ.fuse b (c + d + e))) s v)) x :=
            RelTensor.assoc_symm_mk K (Γ.D (c + d)).carrier (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse c d)) (GQ3Inner K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e))) r
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                (FusionColumn (Γ.fuse b (c + d + e))) s v) x
          have step4 : E8M K Γ a b c d e
              (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ3 K Γ b c d e)
                  (FusionColumn (Γ.fuse a (b + c + d + e)))
                  (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                    (GQ3Inner K Γ b c d e) r
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                      (FusionColumn (Γ.fuse b (c + d + e))) s v)) x)
              = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
                  (FusionColumn (Γ.fuse a (b + c + d + e)))
                  (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
                    (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                      (GQ3Inner K Γ b c d e) r
                      (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                        (FusionColumn (Γ.fuse b (c + d + e))) s v))) x :=
            E8M_mk K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GQ3Inner K Γ b c d e) r
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                  (FusionColumn (Γ.fuse b (c + d + e))) s v)) x
          have step5 : GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e)
              (RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
                (GQ3Inner K Γ b c d e) r
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse (c + d) e))
                  (FusionColumn (Γ.fuse b (c + d + e))) s v))
              = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                  (FusionColumn (Γ.fuse b (c + d + e)))
                  ((gTCanon K Γ c d e).toLinearMap (GBL.mk Γ c d e r s)) v :=
            GE3_mk K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e) r s v
          have step6 : gV14StepFinal K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e))))
                (gTCanon K Γ c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                  (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e)) r s))
                (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
                  (FusionColumn (Γ.fuse b (c + d + e))) (FusionColumn (Γ.fuse a (b + c + d + e)))
                  v x))
              = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
                  (FusionColumn (Γ.fuse a (b + c + d + e)))
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                    (FusionColumn (Γ.fuse b (c + d + e)))
                    (gTCanon K Γ c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                      (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e)) r s)) v) x :=
            RelTensor.assoc_symm_mk K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
              (GBR Γ c d e) (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))
              (gTCanon K Γ c d e (RelTensor.mk K (Γ.D (c + d)).carrier
                (FusionColumn (Γ.fuse c d)) (FusionColumn (Γ.fuse (c + d) e)) r s)) v x
          rw [step1, step2', step3, step4, step5, step6]
          rfl

/-- **`E8M_gV13Chain`**: `E8M` applied to `gV13StepB`'s own construction
agrees, sign-free, with `gV14StepFinal` applied to the `gTCanon`-image of
`M` — for `M`, `Z` BOTH completely arbitrary (no homogeneity, no purity
needed). -/
theorem E8M_gV13Chain
    (M : RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
      (FusionColumn (Γ.fuse (c + d) e)))
    (Z : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    E8M K Γ a b c d e
        (gV13StepB K Γ a b c d e
          (gV13RegroupWrapped K Γ a b c d e
            (gV13StepA K Γ a b c d e
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                  (FusionColumn (Γ.fuse a (b + c + d + e)))) M Z))))
      = gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) (gTCanon K Γ c d e M) Z) := by
  rw [← bigLHS_apply, ← bigRHS_apply, bigLHS_eq_bigRHS]

/-! ### `E19M_general`: `E19M_leaf` with `M`'s own `GBL.mk r s` split
ERASED

`E19M`'s first three stages (`gV8Swap`, `gE19InnerStep`, `gq3rCastWrapped`)
only ever need `M`'s OWN total degree `J` — `gV8Swap_mk_of_mem`'s
hypothesis is already stated at `M`'s own degree, and `gq3rCastWrapped`
is a plain, unsigned outer wrap — so the leaf generalizes exactly as
`E12M_general`/`E11M_general`/`E14M_general` do (`M` stays a free,
opaque parameter throughout — no `RelTensor.induction_on`, hence no
`GBL`-def-wrapped-vs-raw transparency trap). -/

theorem E19M_general {ju J : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju)
    {M : GBL Γ c d e} (hM : M ∈ GBL.grading Γ c d e J)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    E19M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p))
      = ((sgn (J * (ju + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
          gV13StepB K Γ a b c d e
            (gV13RegroupWrapped K Γ a b c d e
              (gV13StepA K Γ a b c d e
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                  (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                    (FusionColumn (Γ.fuse a (b + c + d + e)))) M
                  ((gq3rCast K Γ a b c d e).symm
                    (gTCanon K Γ a b (c + d + e)
                      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                        (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))))) := by
  -- Stage 1: `gV8Swap`, the top-level middle swap (signed, keyed to `M`'s own degree `J`).
  have h1 : gV8Swap K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p))
    = ((sgn (J * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e)) M
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p) :=
    gV8Swap_mk_of_mem K Γ a b c d e hM ht p
  -- Stage 2: `gE19InnerStep`, the `(c+d+e)`-slot signed move.
  have h2 : gE19InnerStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e)) M
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))
    = ((sgn (gParity K Γ a b (c + d + e) * J) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e)) M
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) := by
    show smap (Γ.D (c + d + e)).grading (GBL.grading Γ c d e)
        (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
        (gCanonHphi5 K Γ a b (c + d) e)
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBL Γ a b (c + d + e)) M
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)) = _
    rw [smap_mk_of_mem (Γ.D (c + d + e)).grading (GBL.grading Γ c d e)
      (gTCanon K Γ a b (c + d + e)).toLinearMap (gParity K Γ a b (c + d + e))
      (gCanonHphi5 K Γ a b (c + d) e) hM]
    rfl
  -- Stage 3: `gq3rCastWrapped`, the unsigned outer wrap of `gq3rCast.symm`.
  have h3 : gq3rCastWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e)) M
        (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier
          (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))
    = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) M
        ((gq3rCast K Γ a b c d e).symm
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) := by
    show RelTensor.map (LinearMap.id : GBL Γ c d e →ₗ[K] GBL Γ c d e)
        (gq3rCast K Γ a b c d e).symm.toLinearMap (fun _ _ => rfl)
        (leftEquivariant_symm K (gq3rCast K Γ a b c d e) (gq3rCast_bSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e) (GBR Γ a b (c + d + e)) M
          (gTCanon K Γ a b (c + d + e) (RelTensor.mk K (Γ.D (a + b)).carrier
            (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p))) = _
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
                    (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p)))))))
    = _
  simp only [h1, map_zsmul, h2, smul_smul, ← Units.val_mul, ← sgn_add, h3,
    show J * ju + gParity K Γ a b (c + d + e) * J = J * (ju + gParity K Γ a b (c + d + e))
      from by ring]

/-! ### `square_S3`: the assembly

Built via two RAW-domain composite `LinearMap`s (`bigLHS3`/`bigRHS3`,
`V8`'s own `RelTensor K (Γ.D(a+b)) F_{a,b} V8Inner` spelling, never the
`def`-wrapped `V8 K Γ a b c d e` itself), extended from the fully
homogeneous-decomposed generator `mk t (mk M p)` (`t` degree `ju`, `M`
degree `J`, `p` arbitrary — the SIGN of the theorem's own conclusion is
FIXED, independent of `ju`/`J`, so the `zero`/`add` cases of every
intermediate decomposition close by plain linearity, with no `ju`/`J`
bookkeeping needed until the final homogeneous generator is reached). -/

private noncomputable def bigLHS3 :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
      →ₗ[K] V14 K Γ a b c d e :=
  (E21M K Γ a b c d e).comp (E12M K Γ a b c d e)

private noncomputable def bigRHS3 :
    RelTensor K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
      →ₗ[K] V14 K Γ a b c d e :=
  (E8M K Γ a b c d e).comp (E19M K Γ a b c d e)

theorem bigLHS3_apply
    (t : FusionColumn (Γ.fuse a b)) (W : V8Inner K Γ a b c d e) :
    bigLHS3 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
          t W)
      = E21M K Γ a b c d e
          (E12M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) t W)) :=
  rfl

theorem bigRHS3_apply
    (t : FusionColumn (Γ.fuse a b)) (W : V8Inner K Γ a b c d e) :
    bigRHS3 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
          t W)
      = E8M K Γ a b c d e
          (E19M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) t W)) :=
  rfl

/-! ### `bigLHS3W`/`bigRHS3W`: `bigLHS3`/`bigRHS3` restricted to a fixed
`t`, with the SECOND factor's domain re-declared at `V8Inner`'s own RAW
spelling — needed so that `RelTensor.induction_on`/`DirectSum.Decomposition.
inductionOn` can decompose it cleanly (mirroring `bigLHS`/`bigRHS`'s own
fix, one level up: `V8Inner K Γ a b c d e` is ALSO a `def`-wrapped type,
so it cannot itself be the target of `RelTensor.induction_on`). -/

private noncomputable def bigLHS3W (t : FusionColumn (Γ.fuse a b)) :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      →ₗ[K] V14 K Γ a b c d e :=
  (bigLHS3 K Γ a b c d e).comp
    (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t)

private noncomputable def bigRHS3W (t : FusionColumn (Γ.fuse a b)) :
    RelTensor K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
        (FusionColumn (Γ.fuse (a + b) (c + d + e)))
      →ₗ[K] V14 K Γ a b c d e :=
  (bigRHS3 K Γ a b c d e).comp
    (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) t)

theorem bigLHS3W_apply (t : FusionColumn (Γ.fuse a b)) (M : GBL Γ c d e)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    bigLHS3W K Γ a b c d e t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p)
      = E21M K Γ a b c d e
          (E12M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p))) :=
  rfl

theorem bigRHS3W_apply (t : FusionColumn (Γ.fuse a b)) (M : GBL Γ c d e)
    (p : FusionColumn (Γ.fuse (a + b) (c + d + e))) :
    bigRHS3W K Γ a b c d e t
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
          (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p)
      = E8M K Γ a b c d e
          (E19M K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) t
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) M p))) :=
  rfl

/-- The `ZMod 2` sign identity behind `square_S3`'s closing:
`P·ju + (J+P)·(ju+Q) = P·Q + J·(ju+Q)` — `decide` (not `ring`, which does
not automatically fold `2·x = 0` for `ZMod 2` coefficients; the
established discipline elsewhere in the codebase, e.g.
`QuadInterface2.lean`'s `sgn_rightGenerator_cancel`). -/
private theorem zmod2_S3_cancel : ∀ P Q J ju : ZMod 2,
    P * ju + (J + P) * (ju + Q) = P * Q + J * (ju + Q) := by decide

set_option maxHeartbeats 1000000 in
/-- **`bigLHS3W_eq_bigRHS3W`**: `bigLHS3W`/`bigRHS3W` at a FIXED
homogeneous `t` (degree `ju`) agree, with the SAME fixed sign
`sgn(P·Q)` square_S3's own conclusion needs — combining `E12M_general`
(sign `sgn(P·ju)`), `E21M_leaf` (sign `sgn(i·(ju+Q))`, `i := J+P`) on
the LHS route against `E19M_general` (sign `sgn(J·(ju+Q))`) then the
sign-free `E8M_gV13Chain` on the RHS route: `P·ju + (J+P)·(ju+Q) =
J·(ju+Q) + P·Q` (mod 2), so the `J·(ju+Q)` factor cancels, leaving
`sgn(P·Q)` alone, INDEPENDENT of `J`. -/
theorem bigLHS3W_eq_bigRHS3W {ju : ZMod 2} {t : FusionColumn (Γ.fuse a b)}
    (ht : t ∈ FusionColumn.grading (Γ.fuse a b) ju) :
    bigLHS3W K Γ a b c d e t
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : ℤˣ) : ℤ) •
          bigRHS3W K Γ a b c d e t := by
  refine LinearMap.ext fun w => ?_
  induction w using RelTensor.induction_on with
  | zero => simp
  | add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2]
  | mk M p =>
      induction M using DirectSum.Decomposition.inductionOn (GBL.grading Γ c d e) with
      | zero => simp
      | add M1 M2 h1 h2 =>
          have e1 : RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
              (FusionColumn (Γ.fuse (a + b) (c + d + e))) (M1 + M2) p
              = RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                  (FusionColumn (Γ.fuse (a + b) (c + d + e))) M1 p
                + RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                    (FusionColumn (Γ.fuse (a + b) (c + d + e))) M2 p := by
            rw [map_add, LinearMap.add_apply]
          rw [e1, map_add, map_add, h1, h2]
      | @homogeneous J M' =>
          rw [bigLHS3W_apply, LinearMap.smul_apply, bigRHS3W_apply]
          have hM' : (M' : GBL Γ c d e) ∈ GBL.grading Γ c d e J := M'.2
          have hi : gTCanon K Γ c d e (M' : GBL Γ c d e)
              ∈ GBR.grading Γ c d e (J + gParity K Γ c d e) :=
            (mem_homGrading (GBL.grading Γ c d e) (GBR.grading Γ c d e)).mp
              (gCanonDeg K Γ c d e) J (M' : GBL Γ c d e) hM'
          have hE12 : E12M K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                (V8Inner K Γ a b c d e) t
                (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                  (FusionColumn (Γ.fuse (a + b) (c + d + e))) (M' : GBL Γ c d e) p))
              = ((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
                  RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (V9Inner K Γ a b c d e) t
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                      (gTCanon K Γ c d e (M' : GBL Γ c d e)) p) :=
            E12M_general K Γ a b c d e ht
              (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                (FusionColumn (Γ.fuse (a + b) (c + d + e))) (M' : GBL Γ c d e) p)
          have hE21 := E21M_leaf K Γ a b c d e ht hi p
          have hE19 := E19M_general K Γ a b c d e ht hM' p
          have hE8 := E8M_gV13Chain K Γ a b c d e (M' : GBL Γ c d e)
            ((gq3rCast K Γ a b c d e).symm
              (gTCanon K Γ a b (c + d + e)
                (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))
          have hLHS : E21M K Γ a b c d e
              (E12M K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (V8Inner K Γ a b c d e) t
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                    (FusionColumn (Γ.fuse (a + b) (c + d + e))) (M' : GBL Γ c d e) p)))
              = ((sgn (gParity K Γ c d e * ju
                    + (J + gParity K Γ c d e) * (ju + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
                  gV14StepFinal K Γ a b c d e
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                      (RelTensor K (Γ.D (b + c + d + e)).carrier
                        (FusionColumn (Γ.fuse b (c + d + e)))
                        (FusionColumn (Γ.fuse a (b + c + d + e))))
                      (gTCanon K Γ c d e (M' : GBL Γ c d e))
                      ((gq3rCast K Γ a b c d e).symm
                        (gTCanon K Γ a b (c + d + e)
                          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))) := by
            have step2 : E21M K Γ a b c d e
                (((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
                  RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (V9Inner K Γ a b c d e) t
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                      (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                      (gTCanon K Γ c d e (M' : GBL Γ c d e)) p))
                = ((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
                    E21M K Γ a b c d e
                      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                        (V9Inner K Γ a b c d e) t
                        (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                          (FusionColumn (Γ.fuse (a + b) (c + d + e)))
                          (gTCanon K Γ c d e (M' : GBL Γ c d e)) p)) :=
              map_zsmul (E21M K Γ a b c d e) _ _
            rw [hE12, step2, hE21, smul_smul, ← Units.val_mul, ← sgn_add]
          have hRHS : E8M K Γ a b c d e
              (E19M K Γ a b c d e
                (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (V8Inner K Γ a b c d e) t
                  (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBL Γ c d e)
                    (FusionColumn (Γ.fuse (a + b) (c + d + e))) (M' : GBL Γ c d e) p)))
              = ((sgn (J * (ju + gParity K Γ a b (c + d + e))) : ℤˣ) : ℤ) •
                  gV14StepFinal K Γ a b c d e
                    (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
                      (RelTensor K (Γ.D (b + c + d + e)).carrier
                        (FusionColumn (Γ.fuse b (c + d + e)))
                        (FusionColumn (Γ.fuse a (b + c + d + e))))
                      (gTCanon K Γ c d e (M' : GBL Γ c d e))
                      ((gq3rCast K Γ a b c d e).symm
                        (gTCanon K Γ a b (c + d + e)
                          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                            (FusionColumn (Γ.fuse (a + b) (c + d + e))) t p)))) := by
            rw [hE19, map_zsmul, hE8]
          rw [hLHS, hRHS, smul_smul, ← Units.val_mul, ← sgn_add,
            zmod2_S3_cancel (gParity K Γ c d e) (gParity K Γ a b (c + d + e)) J ju]

/-- **`square_S3`**: the last of the three square faces, `V8 → V14`
(`docs/m13-design.md`'s ledger, `{v8,v9,v13,v14}`), in the orientation
matching `square_S1`/`square_S2`'s own sign spelling exactly. -/
theorem square_S3 :
    E21M K Γ a b c d e ∘ₗ E12M K Γ a b c d e
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : ℤˣ) : ℤ) •
          (E8M K Γ a b c d e ∘ₗ E19M K Γ a b c d e) := by
  show bigLHS3 K Γ a b c d e
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : ℤˣ) : ℤ) •
          bigRHS3 K Γ a b c d e
  refine LinearMap.ext fun x => ?_
  induction x using RelTensor.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | mk t W =>
      induction t using DirectSum.Decomposition.inductionOn (FusionColumn.grading (Γ.fuse a b))
          with
      | zero => simp
      | add t1 t2 h1 h2 =>
          have e1 : RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
              (V8Inner K Γ a b c d e) (t1 + t2) W
              = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                  (V8Inner K Γ a b c d e) t1 W
                + RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
                    (V8Inner K Γ a b c d e) t2 W := by
            rw [map_add, LinearMap.add_apply]
          rw [e1, map_add, map_add, h1, h2]
      | homogeneous t' =>
          have main := bigLHS3W_eq_bigRHS3W K Γ a b c d e t'.2
          exact LinearMap.congr_fun main W

end GaugeChi

end Superfusion
