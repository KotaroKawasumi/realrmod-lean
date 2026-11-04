/-
Superfusion / GaugeChi / QuintFaces2

Milestone M13-4d of the abstract `(p, χ)` arc (the K₅ chain, CLUSTER-FACE
phase): **partial progress toward `face_PAB`**, the `(a+b)`-cluster
pentagon face (`docs/m13-design.md`'s ledger), built on the five
`PAB`-face recognition leaves landed in
`QuintRecog.lean`/`QuintRecog2.lean`/`QuintRecog3.lean` (`E4M_leaf`,
`E11M_leaf`, `E12M_leaf`, `E13M_leaf`, `E14M_leaf`).

**STATUS: `face_PAB` itself is NOT landed.** This file lands the nine
supporting facts the face's proof needs (all compile, no `sorry`), and
the mathematical content of the whole face has been verified BY HAND in
full (see below) — but the FINAL assembly (`faceCore`, chaining these
nine facts plus `gChiCanon_spec`/`gParity_cocycle`) hits a genuine Lean
ELABORATION-PERFORMANCE wall: the `have`-chain (`h1`..`h7`/`hspec`/
`hcocycle`/`hsign`, no problem individually verified in isolation) times
out even at `set_option maxHeartbeats 4000000` (20× the default), with
the timeout occurring even when the closing scalar-bookkeeping steps are
elided — i.e. the slowdown is somewhere in `h1`–`hsign` themselves, NOT
isolated to a specific step in the time available. This was NOT chased
further given the round's time budget; see the handoff report for the
precise diagnosis and a concrete continuation plan.

## The mechanism (verified, worked by hand)

Each `PAB`-face edge is, by its own module-docstring analysis, a
`F_{a,b}`-SIGNED-WHISKER (an outer `smap` keyed to `F_{a,b}`'s grading
alone) of a pentagon-edge-style map at the SHIFTED quadruple
`(a+b,c,d,e)`, wrapping an INNER composite that never itself needs
`F_{a,b}` decomposed. Concretely (all facts proved here, no new
induction beyond the outer `F_{a,b}` decomposition already forced by
`E4M_leaf`/`E13M_leaf`):

* `E11M_general`/`E12M_general`/`E14M_general`: the `EkM_leaf`s
  generalized from a raw `GBR`/`GBL`-generator with a SECOND
  homogeneous slot to an ARBITRARY (opaque) second argument — legitimate
  because each of `E11M`'s/`E12M`'s/`E14M`'s outer `smap` layer is keyed
  *only* to the `F_{a,b}`-slot (`smap_mk_of_mem`'s hypothesis needs
  nothing about the amplified map's own argument).
* `topInner1`/`topInner2`: the top route's inner composite
  (`gV3AssocBC`/`gE11InnerStep`, then `gE11GBRAssoc`/`E12MInnerEquiv`)
  agrees with `GE2`/`GE3` at the shifted quadruple `(a+b,c,d,e)` — via
  `gq2Assoc = gV3StepB` and `gE11GBRAssoc = (gq3Assoc).symm` (literal,
  `rfl`, at this instantiation) and the new general toolkit fact
  `smap_comp_eq` (`smap` of a composite commutes past an unsigned
  precomposition — proved ONCE via `smap`'s own general, non-leaf,
  closed form `smap_mk`, no induction).
* `botInner1`/`botInner2`: the bottom route's inner composite
  (`gV6Swap`/`gE14InnerStep`, then `gE14FinalStep = gq4Close`) agrees
  with `GE5`/`GE4` similarly (`gq5Swap = gV6Swap`, literal), with `GE4`'s
  OWN `v`-keyed sign (`GE4_mk_of_mem`, direct) contributing an EXTRA
  `sgn (gParity (a+b+c) d e * jv)` factor that squares away against
  itself inside `gBotRoute`'s own definition.

Chaining `E4M_leaf`/`E13M_leaf` (the outer `u,v`-homogeneous
decomposition) with these nine facts reduces `face_PAB`'s target to ONE
pointwise instance of `gChiCanon_spec K Γ (a+b) c d e` (at the shifted
`GQ1`-element `m := mk (GBL.mk v w) n`), with the residual sign identity
closing via EXACTLY ONE application of `gParity_cocycle K Γ (a+b) c d e`
— hand-verified in full: writing `SUM := gParity(a+b,c,d) + gParity(a+b)
(c+d)e + gParity(c,d,e)` (the top route's combined `ju`-keyed sign) and
using `gParity_cocycle` (`SUM = gParity(a+b+c,d,e) + gParity(a+b)c(d+e)`),
the top total sign `SUM*ju` equals the bottom total sign
`gParity(a+b+c,d,e)*(ju+jv) + gParity(a+b)c(d+e)*ju + gParity(a+b+c,d,e)*jv`
(the two `gParity(a+b+c,d,e)*jv` contributions — one from `E13M_leaf`'s
own `(ju+jv)`-keyed sign, one from `GE4`'s `botInner1`-derived sign —
cancel `mod 2`), matching exactly. No genuine sign mismatch: the
obstruction below is purely one of Lean elaboration performance, not of
mathematical content.

## Reusable toolkit added

`smap_comp_mk`/`smap_comp_eq` (general, `smap` vs. an unsigned
precomposition — Sections `SmapComp`) and `zsmul_smul_reorder` (a
`ℤ`-scalar/`K`-scalar reordering identity, general).
-/
import Superfusion.GaugeChi.QuintRecog3
namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### A general toolkit fact: `smap` commutes with an unsigned
precomposition on its amplified map -/

section SmapComp

variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ] [GradedRightSMul 𝒜 ℳ]
variable {N N' N'' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']
variable [AddCommGroup N''] [Module K N''] [Module A N'']

omit [Invertible (2 : K)] in
/-- **`smap` of a raw generator, precomposed by an unsigned equivariant
map**: `smap (φ ∘ ψ) e (mk m n) = smap φ e (mk m (ψ n))` — a direct
consequence of `smap_mk`'s own closed form (general in `m`, via
`modProj`), needing nothing beyond `LinearMap.comp_apply`. -/
theorem smap_comp_mk (φ : N' →ₗ[K] N'') {e : ZMod 2}
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N',
      φ (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • φ n))
    (ψ : N →ₗ[K] N')
    (hφψ : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      (φ.comp ψ) (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • (φ.comp ψ) n))
    (m : M) (n : N) :
    smap 𝒜 ℳ (φ.comp ψ) e hφψ (RelTensor.mk K A M N m n)
      = smap 𝒜 ℳ φ e hφ (RelTensor.mk K A M N' m (ψ n)) := by
  rw [smap_mk, smap_mk, smapBilin_apply, smapBilin_apply, LinearMap.comp_apply]

omit [Invertible (2 : K)] in
/-- **`smap` of a composite, as a `LinearMap` identity**: the map-level
lift of `smap_comp_mk` via `RelTensor.hom_ext` — needed since the
argument `smap` is ultimately applied to (`gV3AssocBC (mk Y n)`,
`gV6Swap (mk v Z)`) is not itself a raw generator. -/
theorem smap_comp_eq (φ : N' →ₗ[K] N'') {e : ZMod 2}
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N',
      φ (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • φ n))
    (ψ : N →ₗ[K] N') (hψ : ∀ (a : A) (n : N), ψ (a • n) = a • ψ n)
    (hφψ : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      (φ.comp ψ) (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • (φ.comp ψ) n)) :
    smap 𝒜 ℳ (φ.comp ψ) e hφψ
      = (smap 𝒜 ℳ φ e hφ).comp
          (RelTensor.map (LinearMap.id : M →ₗ[K] M) ψ (fun _ _ => rfl) hψ) := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [LinearMap.comp_apply, RelTensor.map_mk, LinearMap.id_apply, smap_comp_mk]

end SmapComp

variable (a b c d e : G)

/-! ### `E11M_general`: `E11M` on an arbitrary (not necessarily
generator) `GBR (a+b) c d` second slot -/

/-- **`E11M_general`**: the `F_{a,b}`-only-keyed generalization of
`E11M_leaf` — `Y : GBR Γ (a+b) c d` is left COMPLETELY OPAQUE (`E11M`'s
outer `smap` layer, `gE11OuterStep`, is keyed *only* to `F_{a,b}`'s own
grading, per `smap_mk_of_mem`'s hypothesis shape — its amplified
argument needs no structure at all). -/
theorem E11M_general {ju : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    (Y : GBR Γ (a + b) c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E11M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
            Y) n)
      = ((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
            u
            (gE11GBRAssoc K Γ a b c d e
              (gE11InnerStep K Γ a b c d e
                (gV3AssocBC K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                    (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)))) := by
  show gE11FinalStep K Γ a b c d e
      (gE11OuterStep K Γ a b c d e
        (gV3AssocABC K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)
              u Y) n))) = _
  have h1 : gV3AssocA K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          Y) n)
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))) u
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n) :=
    RelTensor.assoc_mk K (Γ.D (a + b)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) (FusionColumn (Γ.fuse (a + b + c + d) e)) u
      Y n
  have h2 : gV3AssocABC K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          Y) n)
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e))
        u
        (gV3AssocBC K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gV3AssocBC K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gV3AssocBC_aSlot_general K Γ a b c d e)
        (gV3AssocA K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ5 K Γ a b c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e))
            (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d)
              u Y) n)) = _
    rw [h1, RelTensor.map_mk, LinearMap.id_apply]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h2]
  have h3 : gE11OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e))
        u
        (gV3AssocBC K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)))
    = ((sgn (gParity K Γ (a + b) (c + d) e * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))
          u
          (gE11InnerStep K Γ a b c d e
            (gV3AssocBC K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n))) := by
    show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (gE11InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) (c + d) e)
        (gE11OuterHg K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBL Γ (a + b) (c + d) e))
          u
          (gV3AssocBC K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n))) = _
    rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (gE11InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) (c + d) e)
      (gE11OuterHg K Γ a b c d e) hu]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h3, map_zsmul]
  have h4 : gE11FinalStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ (a + b) (c + d) e))
        u
        (gE11InnerStep K Γ a b c d e
          (gV3AssocBC K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n))))
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) u
        (gE11GBRAssoc K Γ a b c d e
          (gE11InnerStep K Γ a b c d e
            (gV3AssocBC K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gE11GBRAssoc K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gE11GBRAssoc_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d))
            (GBR Γ (a + b) (c + d) e)) u
          (gE11InnerStep K Γ a b c d e
            (gV3AssocBC K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h4]
  rfl

/-! ### `E12M_general`: `E12M` on an arbitrary `V8Inner` argument -/

/-- **`E12M_general`**: `E12M`'s own defining `smap`, keyed only to
`F_{a,b}`'s grading, applied to a completely opaque `W : V8Inner`. -/
theorem E12M_general {ju : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju) (W : V8Inner K Γ a b c d e) :
    E12M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e)
          u W)
      = ((sgn (gParity K Γ c d e * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
            u (E12MInnerEquiv K Γ a b c d e W) := by
  show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (E12MInnerEquiv K Γ a b c d e).toLinearMap (gParity K Γ c d e)
      (E12MInnerEquiv_aSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V8Inner K Γ a b c d e) u
        W) = _
  rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (E12MInnerEquiv K Γ a b c d e).toLinearMap (gParity K Γ c d e)
    (E12MInnerEquiv_aSlot K Γ a b c d e) hu]
  simp only [LinearEquiv.coe_toLinearMap]

/-! ### `E14M_general`: `E14M` on an arbitrary `GBR (a+b+c) d e` second
slot -/

/-- **`E14M_general`**: the `F_{a,b}`-only-keyed generalization of
`E14M_leaf` — `v : F_{a+b,c}` and `Z : GBR Γ (a+b+c) d e` are BOTH left
opaque (`E14M`'s middle swap `gV6SwapWrapped` and inner amplification
`gE14InnerStep` need `v`/`Z`'s own homogeneity for a CLEAN individual
sign, but `E14M`'s OUTER `smap` layer, `gE14OuterStep`, is keyed only to
`F_{a,b}`, and needs nothing about its own amplified argument, which we
leave as the fully opaque composite `gE14InnerStep (gV6Swap (mk v Z))`). -/
theorem E14M_general {ju : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) ju)
    (v : FusionColumn (Γ.fuse (a + b) c)) (Z : GBR Γ (a + b + c) d e) :
    E14M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
          (GBL.mk Γ a b c u v) Z)
      = ((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e)
            u
            (gE14FinalStep K Γ a b c d e
              (gE14InnerStep K Γ a b c d e
                (gV6Swap K Γ a b c d e
                  (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                    (GBR Γ (a + b + c) d e) v Z)))) := by
  show gE14FinalStepWrapped K Γ a b c d e
      (gE14OuterStep K Γ a b c d e
        (gV6SwapWrapped K Γ a b c d e
          (gV6AssocA K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
              (GBL.mk Γ a b c u v) Z)))) = _
  have h1 : gV6AssocA K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c) (GBR Γ (a + b + c) d e)
        (GBL.mk Γ a b c u v) Z)
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v Z) :=
    RelTensor.assoc_mk K (Γ.D (a + b)).carrier (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a b)) (FusionColumn (Γ.fuse (a + b) c)) (GBR Γ (a + b + c) d e) u v Z
  have h2 : gV6SwapWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e)) u
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v Z))
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ (a + b) c (d + e))) u
        (gV6Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v Z)) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gV6Swap K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gV6Swap_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e)) u
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v Z)) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h1, h2]
  have h3 : gE14OuterStep K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBL Γ (a + b) c (d + e))) u
        (gV6Swap K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v Z)))
    = ((sgn (gParity K Γ (a + b) c (d + e) * ju) : ℤˣ) : ℤ) •
        RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e))) u
          (gE14InnerStep K Γ a b c d e
            (gV6Swap K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (GBR Γ (a + b + c) d e) v Z))) := by
    show smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
        (gE14InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) c (d + e))
        (gE14OuterHg K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBL Γ (a + b) c (d + e))) u
          (gV6Swap K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (GBR Γ (a + b + c) d e) v Z))) = _
    rw [smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      (gE14InnerStep K Γ a b c d e).toLinearMap (gParity K Γ (a + b) c (d + e))
      (gE14OuterHg K Γ a b c d e) hu]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h3, map_zsmul]
  have h4 : gE14FinalStepWrapped K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
        (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GBR Γ (a + b) c (d + e))) u
        (gE14InnerStep K Γ a b c d e
          (gV6Swap K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (GBR Γ (a + b + c) d e) v Z))))
    = RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (V9Inner K Γ a b c d e) u
        (gE14FinalStep K Γ a b c d e
          (gE14InnerStep K Γ a b c d e
            (gV6Swap K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (GBR Γ (a + b + c) d e) v Z)))) := by
    show RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse a b) →ₗ[K] FusionColumn (Γ.fuse a b))
        (gE14FinalStep K Γ a b c d e).toLinearMap (fun _ _ => rfl)
        (gE14FinalStep_aSlot_general K Γ a b c d e)
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b))
          (RelTensor K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GBR Γ (a + b) c (d + e))) u
          (gE14InnerStep K Γ a b c d e
            (gV6Swap K Γ a b c d e
              (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
                (GBR Γ (a + b + c) d e) v Z)))) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [h4]
  rfl

/-! ### The two bridge facts identifying the opaque inner composites with
`gChiCanon_spec K Γ (a+b) c d e`'s own `gTopRoute`/`gBotRoute` -/

/-- **`topInner1`**: `GE2` at the shifted quadruple, applied to `mk Y n`
(`Y` arbitrary), equals the opaque `gE11InnerStep (gV3AssocBC (mk Y n))`
— `GE2`'s own `gq2Assoc` is LITERALLY `gV3StepB` at this instantiation,
and `GE2`'s `t₂ := gt2Canon (gTCanon (a+b) (c+d) e)` is LITERALLY
`gTCanon (a+b) (c+d) e).toLinearMap.comp (gq2rCast).toLinearMap` (`gt2Canon`'s
own `.trans` definition) — `smap_comp_eq` (general, no induction) then
identifies the two `smap`s. -/
theorem topInner1 (Y : GBR Γ (a + b) c d) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    GE2 K Γ (a + b) c d e (gParity K Γ (a + b) (c + d) e)
        (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
        (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
          (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)
      = gE11InnerStep K Γ a b c d e
          (gV3AssocBC K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) := by
  show (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      (gt2Canon K Γ (a + b) c d e (gTCanon K Γ (a + b) (c + d) e)).toLinearMap
      (gParity K Γ (a + b) (c + d) e)
      (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
        (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e)))
      (gq2Assoc K Γ (a + b) c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) = _
  have hassoc : gq2Assoc K Γ (a + b) c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)
    = gV3StepB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n) := rfl
  rw [hassoc]
  show (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      ((gTCanon K Γ (a + b) (c + d) e).toLinearMap.comp
        (gq2rCast K Γ (a + b) c d e).toLinearMap)
      (gParity K Γ (a + b) (c + d) e) _)
      (gV3StepB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) = _
  have hcomp := smap_comp_eq (K := K) (𝒜 := (Γ.D (c + d)).grading)
    (ℳ := FusionColumn.grading (Γ.fuse c d)) (gTCanon K Γ (a + b) (c + d) e).toLinearMap
    (gCanonMidSlot K Γ (a + b) (c + d) e) (gq2rCast K Γ (a + b) c d e).toLinearMap
    (gq2rCast_bcSlot K Γ (a + b) c d e)
    (gt2Canon_bcSlot K Γ (gTCanon K Γ (a + b) (c + d) e) (gParity K Γ (a + b) (c + d) e)
      (gTCanon_mem_gInterSpace K Γ (a + b) (c + d) e))
  have hpt := LinearMap.congr_fun hcomp
    (gV3StepB K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n))
  simp only [LinearMap.comp_apply] at hpt
  rw [hpt]
  have hV3StepC : gV3StepC K Γ a b c d e
      (gV3StepB K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n))
    = RelTensor.map (LinearMap.id : FusionColumn (Γ.fuse c d) →ₗ[K] FusionColumn (Γ.fuse c d))
        (gq2rCast K Γ (a + b) c d e).toLinearMap (fun _ _ => rfl)
        (gq2rCast_bcSlot K Γ (a + b) c d e)
        (gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) := by
    show RelTensor.mapEquivRight K (gq2rCast K Γ (a + b) c d e)
        (gq2rCast_bcSlot K Γ (a + b) c d e)
        (gV3StepB K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBR Γ (a + b) c d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) Y n)) = _
    rfl
  rw [← hV3StepC]
  rfl

/-- **`topInner2`**: `GE3` at the shifted quadruple, applied to `GE2`'s
output, equals `E12MInnerEquiv (gE11GBRAssoc (·))` — `GE3`'s own
`gq3Assoc.symm` is LITERALLY `gE11GBRAssoc`, and `GE3`'s `t₃ := gTCanon c
d e` is LITERALLY `E12MInnerEquiv`'s own amplified map
(`E12MInnerEquiv_toLinearMap`). -/
theorem topInner2 (z : GQ3 K Γ (a + b) c d e) :
    GE3 K Γ (a + b) c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e) z
      = E12MInnerEquiv K Γ a b c d e (gE11GBRAssoc K Γ a b c d e z) := by
  show (RelTensor.map (gTCanon K Γ c d e).toLinearMap (LinearMap.id : FusionColumn
        (Γ.fuse (a + b) (c + d + e)) →ₗ[K] FusionColumn (Γ.fuse (a + b) (c + d + e)))
      (gCanonRight K Γ c d e) (fun _ _ => rfl))
      ((gq3Assoc K Γ (a + b) c d e).symm z) = _
  have hassoc : (gq3Assoc K Γ (a + b) c d e).symm z = gE11GBRAssoc K Γ a b c d e z := rfl
  rw [hassoc]
  show _ = (E12MInnerEquiv K Γ a b c d e).toLinearMap (gE11GBRAssoc K Γ a b c d e z)
  rw [E12MInnerEquiv_toLinearMap]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`botInner1`**: `GE4` at the shifted quadruple, applied to the
shifted `GQ1`-generator `mk (GBL.mk v w) n` (`v` homogeneous, `w`, `n`
arbitrary), equals the signed reinsertion `E13M_leaf` already computes —
`GE4_mk_of_mem`, direct. -/
theorem botInner1 {jv : ZMod 2}
    {v : FusionColumn (Γ.fuse (a + b) c)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) (n : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    GE4 K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
        (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e)
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ (a + b) c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GBL.mk Γ (a + b) c d v w) n)
      = ((sgn (gParity K Γ (a + b + c) d e * jv) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
            (GBR Γ (a + b + c) d e) v
            (gTCanon K Γ (a + b + c) d e
              (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (FusionColumn (Γ.fuse (a + b + c) d))
                (FusionColumn (Γ.fuse (a + b + c + d) e)) w n)) :=
  GE4_mk_of_mem K Γ (a + b) c d e (gParity K Γ (a + b + c) d e)
    (gTCanon K Γ (a + b + c) d e).toLinearMap (gCanonHphi4 K Γ (a + b) c d e) hv w n

set_option maxHeartbeats 1000000 in
/-- **`botInner2`**: `GE5` at the shifted quadruple, applied to
`mk v Z` (`v`, `Z` arbitrary), equals the opaque
`gE14InnerStep (gV6Swap (mk v Z))` — `GE5`'s own `gq5Swap` is LITERALLY
`gV6Swap` at this instantiation, and `GE5`'s `t₅ := gTCanon (a+b) c (d+e)`
is LITERALLY `gE14InnerStep`'s own amplified map. -/
theorem botInner2
    (v : FusionColumn (Γ.fuse (a + b) c)) (Z : GBR Γ (a + b + c) d e) :
    GE5 K Γ (a + b) c d e (gParity K Γ (a + b) c (d + e))
        (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gCanonHphi5 K Γ (a + b) c d e)
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v Z)
      = gE14InnerStep K Γ a b c d e
          (gV6Swap K Γ a b c d e
            (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
              (GBR Γ (a + b + c) d e) v Z)) := by
  show (smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
      (gTCanon K Γ (a + b) c (d + e)).toLinearMap (gParity K Γ (a + b) c (d + e))
      (gCanonHphi5 K Γ (a + b) c d e))
      (gq5Swap K Γ (a + b) c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v Z)) = _
  have hswap : gq5Swap K Γ (a + b) c d e
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
        (GBR Γ (a + b + c) d e) v Z)
    = gV6Swap K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse (a + b) c))
          (GBR Γ (a + b + c) d e) v Z) := rfl
  rw [hswap]
  rfl

/-! ### A general `ℤ`-scalar/`K`-scalar reordering fact (reusable toolkit,
built for the eventual `face_PAB` closing sign bookkeeping) -/

omit [Invertible (2 : K)] in
/-- **A `ℤ`-scalar/`K`-scalar reordering lemma**: `s1•s2•s3•(k•X) = k•((s1*s2*s3)•X)`
for `s1 s2 s3 : ℤ`, `k : K`, on any `K`-module `V` — three applications of
`smul_comm` (moving `k` all the way left past the three `ℤ`-smuls) then two of
`smul_smul` (combining the `ℤ`-smuls). -/
theorem zsmul_smul_reorder {V : Type*} [AddCommGroup V] [Module K V]
    (s1 s2 s3 : ℤ) (k : K) (X : V) :
    s1 • s2 • s3 • (k • X) = k • ((s1 * s2 * s3 : ℤ) • X) := by
  rw [smul_comm s3 k X, smul_comm s2 k (s3 • X), smul_comm s1 k (s2 • s3 • X), smul_smul, smul_smul]

end GaugeChi

end Superfusion
