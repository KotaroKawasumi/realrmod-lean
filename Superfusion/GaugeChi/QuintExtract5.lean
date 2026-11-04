/-
Superfusion / GaugeChi / QuintExtract5

Milestone M13-R6 of the `(p, χ)` arc's CLUSTER-FACE phase, executing round
R6 of `docs/m13-cluster-route.md` (the PBC face's extraction round): three
of the five `PBC` spectator-extraction equivalences land this round
(`omegaPbcV12`, `omegaPbcV10`, `omegaPbcV2`), each landing the face's
spectator column `F_{b,c}` at the OUTER-LEFT position of the corresponding
vertex, `V_v ≃ₗ F_{b,c} ⊗_{D_{b+c}} GQ_k(a,b+c,d,e)`, WITH full sign-free
generator-formula leaves — built only from already-landed gadgets
(`RelTensor.assoc`, `RelTensor.mapEquivLeft`, `RelTensor.mapEquivRight`,
`gq1Assoc`/`gq1Assoc_rightTotal`, `gq2Assoc`/`gq2Assoc_rightTotal`,
`gV12Assoc`, `gq2rCast`/`gq2rCast_bcSlot`, `gColumnCastFst`/
`gColumnCastFst_coeff`) plus ONE genuinely NEW device (`gblOuterCastV2`,
below), per the referee-verified STRUCTURAL FACT that `F_{b,c}` sits
leftmost(-innermost) in all five vertices — no `midSwap` anywhere, every
landed `ω` is a sign-free assoc/cast tower.

**`omegaPbcV4`/`omegaPbcV7` are DEFERRED this round** (see the deviation
note at the end) — the fallback-order priority ("the five ω's first ...
in the order V2, V4, V10, V12, V7" per the round brief, all gating
everything) was followed as far as the round's budget allowed; `V4`'s own
device is a close structural mirror of `omegaPbcV2`'s (documented below,
ready for direct reuse), while `V7`'s needs a genuinely different genre
(a `GBR`-FIRST-ARGUMENT index cast, not yet built). Consequently the four
"missing-leaf" deliverables (`E2M_leaf`, `E9M_leaf`, `E15M_leaf`,
`E16M_general`) and the PRE-ROUND GATE note on `E15M`'s smap key are ALSO
deferred — they depend on `omegaPbcV4` (`E2M_leaf`, `E15M_leaf`) or
`omegaPbcV7`/`omegaPbcV12` jointly (`E9M_leaf`), none of which are
complete without `V4`.

## What lands

* `omegaPbcV12 : V12 ≃ₗ F_{b,c} ⊗ GQ4(a,b+c,d,e)` — literally `gV12Assoc`
  (already built, `QuintEdges7.lean`, for `E17M`'s own toolkit), a single
  cast-free `RelTensor.assoc`; `omegaPbcV12_mk`.
* `omegaPbcV10 : V10 ≃ₗ F_{b,c} ⊗ GQ3(a,b+c,d,e)` — `gq1Assoc` (whiskered
  by `RelTensor.mapEquivLeft`, naturality `gq1Assoc_rightTotal`), a plain
  `RelTensor.assoc` (peeling `F_{b,c}` past the outer `D_{b+c+d+e}`), a
  plain `RelTensor.assoc` (re-bracketing `GBL(b+c,d,e) ⊗ F_{a,...}` into
  `F_{(b+c),d} ⊗ GQ3Inner(a,b+c,d,e)`, whiskered under `F_{b,c}` via
  `RelTensor.mapEquivRight`) — every group-element total re-associates
  along the SAME literal term throughout (`(b+c)` a genuine prefix
  cluster), so NO cast is needed anywhere; `omegaPbcV10_mk`.
* `omegaPbcV2 : V2 ≃ₗ F_{b,c} ⊗ GQ1(a,b+c,d,e)` — `gq2Assoc` (whiskered,
  naturality `gq2Assoc_rightTotal`), a plain `RelTensor.assoc` (peeling
  `F_{b,c}` past the outer `D_{a+b+c+d}`), then `gq2rCastWrappedV2` (=
  `mapEquivLeft(gq2rCast)` then `gblOuterCastV2`, whiskered under `F_{b,c}`
  via `RelTensor.mapEquivRight`); `omegaPbcV2` itself has NO separate `_mk`
  leaf this round (the assembly compiles and kernel-checks; the leaf
  computation is a mechanical composition of `omegaPbcV10`'s already-landed
  discipline and was cut for round-budget reasons — safe to add next
  round by mirroring `omegaPbcV10_mk`'s proof shape verbatim).

**`gblOuterCastV2`, THE NEW DEVICE (deliverable)**: `GBL Γ a (b+c) d
⊗_{D_{a+b+c+d}} F_{a+b+c+d,e} ≃ GQ1 K Γ a (b+c) d e`, mirroring
`Pentagon.lean`'s `gq4Recast` construction one level up (two
`RelTensor.lift` legs glued by `LinearEquiv.ofLinear`, identity on the
fixed first factor `GBL Γ a (b+c) d`, `gColumnCastFst` on the second),
transporting `V2`'s own native total `((a+b)+c)+d` to `GQ1`'s own native
total `(a+(b+c))+d` along `pbcHeq a b c d : a+b+c+d = a+(b+c)+d`. Needs
a NEW right-action instance on `GBL Γ a (b+c) d` at the recast total
`D_{a+b+c+d}` (`instModuleGblABCDOuterRecastV2`, pulled back from `GBL`'s
own natural total `D_{a+(b+c)+d}` via `Γ.gaugeCast (pbcHeq a b c d)`,
mirroring `RouteBimod.lean`'s `GBR`-own "coefficient recast" section
verbatim) plus its `SMulCommClass`/`IsScalarTower` cross-conditions with
`GBL`'s own slot actions (mirrors `Pentagon.lean`'s
`fusionColumn_recast`-section cross-conditions). `gq2rCast`'s own
equivariance w.r.t. this NEW instance (`gq2rCast_totalSlot`) is a direct
corollary of the ALREADY-LANDED `gColumnCastFst_coeff` (`ChiCanon.lean`) —
no new algebraic content there, only the bridging instance.

## Deviation record (fallback-order authorization used)

The round's own fallback clause ("if a close-cancelling ω spelling fights
the instance elaboration, fall back ... and absorb into affected
recognitions" / record deviations) is invoked for `omegaPbcV4`/
`omegaPbcV7`. Findings for the NEXT round attempting them:

* **`omegaPbcV4`** (`V4 ≃ₗ F_{b,c} ⊗ GQ2(a,b+c,d,e)`): `GQ3Inner K Γ a b c
  d` is DEFINITIONALLY `GBR Γ a (b+c) d` (`(b+c)+d = b+c+d` syntactically,
  so both unfold to the identical `RelTensor` application) — `V4`'s own
  native structure is ALREADY `(F_{b,c} ⊗ GBR Γ a (b+c) d) ⊗ F_{a+b+c+d,e}`
  up to this defeq identification, so a plain `RelTensor.assoc` should peel
  `F_{b,c}` out directly (no `gq2Assoc`-style intermediate needed) —
  PROVIDED the construction is spelled through `GQ3Inner`'s own name
  throughout rather than the raw/`GBR`-unfolded form (the
  instances-transparency trap this file's `omegaPbcV10Step3*` fought
  through repeatedly makes the "just use defeq" shortcut costly in
  practice). The closing step needs a `gq2rCastV4`-genre device mirroring
  `gblOuterCastV2` above VERBATIM with `M := GBR Γ a (b+c) d` in place of
  `GBL Γ a (b+c) d`, EXCEPT: `GBR Γ a (b+c) d` ALREADY carries its own
  "coefficient recast" instance at `D_{a+(b+c)+d}` (`RouteBimod.lean`'s
  generic `GBR`-recast section, since `GBR`'s recast total pattern
  `(p+q)+r` with `p:=a,q:=(b+c),r:=d` gives EXACTLY `a+(b+c)+d`), so the
  NEW device needed is a further pullback of THAT existing recast instance
  along `pbcHeq`, not a pullback of `GBR`'s natural total — a "double
  recast", mechanically the same `Module.compHom`-composition pattern.
* **`omegaPbcV7`** (`V7 ≃ₗ F_{b,c} ⊗ GQ5(a,b+c,d,e)`): a plain
  `RelTensor.assoc` peels `F_{b,c}` out of `GBR Γ a b c` directly (`V7 =
  GBR Γ a b c ⊗_{D_{a+b+c}} GBR Γ (a+b+c) d e`, and `GBR Γ a b c = F_{b,c}
  ⊗_{D_{b+c}} F_{a,(b+c)}`), landing `F_{a,(b+c)} ⊗ GBR Γ (a+b+c) d e`.
  The closing step needs a NEW device, genuinely different from
  `gblOuterCastV2`: casting `GBR`'s OWN FIRST argument along
  `add_assoc a b c : a+b+c = a+(b+c)` — i.e. a `GBR`-mirror of
  `ChiCanon.lean`'s `gColumnCastFst` (which casts a plain fusion column's
  first index), one level up, since here the SECOND factor being
  transported is a `GBR`-compound (`GBR Γ (a+b+c) d e → GBR Γ (a+(b+c)) d
  e`), not a plain fusion column, WHILE the FIRST factor `F_{a,(b+c)}` is
  fixed/opaque throughout (the mirror-image role split from `gblOuterCastV2`,
  which fixed the FIRST factor as the compound and cast the SECOND, a
  plain column). Not yet built; budget it as its own `RelTensor.lift`-glued
  construction (`GBR`'s own `right_smul_mk`/aslot-bslot-cslot cross laws
  supply the balancedness proof, mirroring `gq3rCast`'s
  `QuintEdges8.lean` precedent one level down).

**PRE-ROUND GATE (route doc R6 last line, `E15M`'s smap key) and the
`E2M_leaf`/`E9M_leaf`/`E15M_leaf`/`E16M_general` deliverables are ALL
DEFERRED**, since none of them are independent of `omegaPbcV4` (`E2M_leaf`
needs `omegaPbcV2`+`omegaPbcV4`'s split domains; `E15M_leaf` needs
`omegaPbcV4`+`omegaPbcV10`'s; `E9M_leaf` needs `omegaPbcV10`+
`omegaPbcV12`'s, so is the ONE leaf potentially in reach without `V4`/`V7`
— flagged for the next round's fallback-order restart point once `V4`
lands). `E16M_general`, called "nearly free" by the route doc
(pure `smap`-genre keyed to the whole cluster slot's total grading,
`QuintEdges6.lean`'s `E16M` itself already built), is likewise deferred
purely for round-budget reasons, not because of any discovered obstacle.

## Instances-transparency discipline (load-bearing lesson for R7)

Throughout this file, whenever a NAMED vertex type (`GBL`/`GBR`/`GQ_k`,
all plain `def`s, not `abbrev`s) needs to be INDUCTED on via
`RelTensor.induction_on` inside a nested tactic-mode proof, the induction
tactic's own motive-unfolding "pins" a RAW (unfolded) spelling into the
generated goal that a NAMED-type-based `show`/`have` ascription cannot
match under `instances` transparency (`rw`/tactic-mode elaboration is
STRICTER than the term-mode ascription that top-level `def`/`theorem`
SIGNATURES enjoy). The working pattern, used repeatedly below: (1) state
`n`'s own type using the RAW unfolded spelling wherever it is the subject
of `induction ... using RelTensor.induction_on` (never the NAMED
type, even though the `•`-action's OWN typeclass search may then need
EXTRA bridging instances registered directly on the raw form, e.g.
`instModuleRawGblBcdeBcSlot`/`instSMulCommClassRawGblBcdeBcSlot`/
`instIsScalarTowerRawGblBcdeBcSlot`, via `inferInstanceAs` from the NAMED
type); (2) factor the innermost "leaf" computation (on FULLY split
generators) into its OWN standalone theorem, NEVER inline inside the
tactic block, stated using whatever NAMED constructors (`GBL.mk`/`GQ1.mk`)
are natural — its SIGNATURE elaborates via lenient term-mode checking, and
`exact leafLemma ...` (not `rw`) closes the generated goal via full
defeq; (3) never `rw` FROM a raw `RelTensor.mk` spelling TO a NAMED
`GBL.mk`/`GQ1.mk` spelling (or vice versa) inside a goal that mixes both —
supply the NAMED-spelled fact directly via a term-mode `have ... := ...`
ascription instead.
-/
import Superfusion.GaugeChi.QuintExtract
import Superfusion.GaugeChi.QuintCross

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

/-! ### Toolkit: the `a+b+c+d = a+(b+c)+d` transport -/

/-- The group-element identity bridging `V2`/`V4`'s own native total
`((a+b)+c)+d` to `GQ1`/`GQ2`'s own native total (at the shifted quadruple
`(a,b+c,d,e)`) `(a+(b+c))+d` — `add_assoc a b c` pushed forward by `+d`. -/
theorem pbcHeq (a b c d : G) : a + b + c + d = a + (b + c) + d :=
  congrArg (· + d) (add_assoc a b c)

/-! ### `omegaPbcV12 : V12 ≃ₗ F_{b,c} ⊗ GQ4(a,b+c,d,e)` -/

section OmegaPbcV12

/-- **`omegaPbcV12`**: literally `gV12Assoc` (`QuintEdges7.lean`, built for
`E17M`'s own toolkit) — a single cast-free `RelTensor.assoc`, landing the
literal `GQ4 K Γ a (b + c) d e`. -/
noncomputable def omegaPbcV12 : V12 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) :=
  gV12Assoc K Γ a b c d e

/-- **The sign-free generator formula of `omegaPbcV12`.** -/
theorem omegaPbcV12_mk (u : FusionColumn (Γ.fuse b c)) (q : GBR Γ (b + c) d e)
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV12 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) (GQ5.mk K Γ b c d e u q) t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ4 K Γ a (b + c) d e) u
          (GQ4.mk K Γ a (b + c) d e q t) :=
  RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse b c)) (GBR Γ (b + c) d e) (FusionColumn (Γ.fuse a (b + c + d + e))) u q t

end OmegaPbcV12

/-! ### `omegaPbcV10 : V10 ≃ₗ F_{b,c} ⊗ GQ3(a,b+c,d,e)` -/

section OmegaPbcV10

/-- `mapEquivLeft (gq1Assoc K Γ b c d e)`'s naturality, whiskering into
`V10`'s own outer `D_{b+c+d+e}`-slot: `gq1Assoc`'s ALREADY-LANDED
`Total`-naturality (`QuintEdges.lean`). -/
theorem omegaPbcV10Step1Law (τ : (Γ.D (b + c + d + e)).carrier) (m : GQ1 K Γ b c d e) :
    gq1Assoc K Γ b c d e (MulOpposite.op τ • m)
      = MulOpposite.op τ • gq1Assoc K Γ b c d e m :=
  gq1Assoc_rightTotal K Γ b c d e τ m

/-- Stage 1 of `omegaPbcV10`: `gq1Assoc`, whiskered under the outer
`F_{a,b+c+d+e}` — peels `F_{b,c}` off `GBL(b,c,d)`, landing
`(F_{b,c} ⊗ GBL(b+c,d,e)) ⊗ F_{a,b+c+d+e}`. -/
noncomputable def omegaPbcV10Step1 : V10 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c + d + e)).carrier
      (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e))
      (FusionColumn (Γ.fuse a (b + c + d + e))) :=
  PentagonB.RelTensor.mapEquivLeft K (gq1Assoc K Γ b c d e) (omegaPbcV10Step1Law K Γ b c d e)

/-- **Stage 1's generator formula**: `RelTensor.map_mk` unfolds
`mapEquivLeft` directly (`LinearEquiv.ofLinear`'s coercion is its own
first argument, applied). -/
theorem omegaPbcV10Step1_mk (m : GQ1 K Γ b c d e) (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV10Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) m w)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) (gq1Assoc K Γ b c d e m) w :=
  RelTensor.map_mk (gq1Assoc K Γ b c d e).toLinearMap
    (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d + e)) →ₗ[K]
      FusionColumn (Γ.fuse a (b + c + d + e)))
    (omegaPbcV10Step1Law K Γ b c d e) (fun _ _ => rfl) m w

/-- Stage 2 of `omegaPbcV10`: a plain, cast-free `RelTensor.assoc`,
peeling `F_{b,c}` out past the outer `D_{b+c+d+e}` (`GBL(b+c,d,e)`'s own
`aslot`/natural-total instances supply the needed module structure —
`(b+c)` a prefix cluster, `(b+c)+d+e = b+c+d+e` syntactically). -/
noncomputable def omegaPbcV10Step2 :
    RelTensor K (Γ.D (b + c + d + e)).carrier
        (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e))
        (FusionColumn (Γ.fuse a (b + c + d + e)))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))) :=
  RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e) (FusionColumn (Γ.fuse a (b + c + d + e)))

/-- **The leaf computation of Stage 3's `(b+c)`-equivariance**: purely
mechanical (SIGN-FREE), via `GBL.mk`'s own defeq unfolding to `RelTensor.mk`
(the `QuintEdges3.lean`-style `GBL_mk_eq` bridge, `rfl`), then
`RelTensor.assoc_mk` twice — a STANDALONE theorem (mirroring
`QuintEdges8.lean`'s `gV13Regroup_leaf`), avoiding the instances-transparency
trap a `show`/`have` chain hits when re-ascribing a raw `RelTensor.mk` term
to the NAMED `GBL Γ (b+c) d e` inside a nested-induction tactic block. -/
theorem omegaPbcV10Step3Leaf (τ : (Γ.D (b + c)).carrier) (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse ((b + c) + d) e)) (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e (τ • v) x) w)
      = τ • (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w) := by
  have step1 : (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e (τ • v) x) w)
      = RelTensor.mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • v)
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) x w) :=
    RelTensor.assoc_mk K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
      (FusionColumn (Γ.fuse a (b + c + d + e))) (τ • v) x w
  have step2 : (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w)
      = RelTensor.mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) v
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) x w) :=
    RelTensor.assoc_mk K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
      (FusionColumn (Γ.fuse a (b + c + d + e))) v x w
  have step3 : RelTensor.mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • v)
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) x w)
      = τ • RelTensor.mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) v
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) x w) :=
    (leftActionEnd_mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e)))) τ v
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))) x w)).symm
  rw [step1, step3, ← step2]

/-- `inferInstanceAs` bridges: `GBL Γ (b+c) d e`'s own `(b+c)`-slot module
structure (and its cross-conditions with the `D_{b+c+d+e}`-total),
transported to the RAW unfolded spelling `RelTensor.induction_on` needs
(the NAMED `GBL`'s own generic registrations, `RouteBimod.lean`/
`PentagonActions.lean`, keyed to the syntactic `GBL Γ a b c` pattern, do
not automatically fire on the unfolded form). -/
noncomputable instance instModuleRawGblBcdeBcSlot :
    Module (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse ((b + c) + d) e))) :=
  inferInstanceAs (Module (Γ.D (b + c)).carrier (GBL Γ (b + c) d e))

instance instSMulCommClassRawGblBcdeBcSlot :
    SMulCommClass (Γ.D (b + c)).carrier ((Γ.D (b + c + d + e)).carrier)ᵐᵒᵖ
      (RelTensor K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse ((b + c) + d) e))) :=
  inferInstanceAs (SMulCommClass (Γ.D (b + c)).carrier ((Γ.D (b + c + d + e)).carrier)ᵐᵒᵖ
    (GBL Γ (b + c) d e))

instance instIsScalarTowerRawGblBcdeBcSlot :
    IsScalarTower K (Γ.D (b + c)).carrier
      (RelTensor K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse ((b + c) + d) e))) :=
  inferInstanceAs (IsScalarTower K (Γ.D (b + c)).carrier (GBL Γ (b + c) d e))

/-- Stage 3's core naturality, stated via `leftActionEnd` directly and via
the RAW unfolded domain type (so `leftActionEnd_mk`/`RelTensor.assoc_mk`
match syntactically inside the nested induction, avoiding the
instances-transparency trap the NAMED `GBL Γ (b+c) d e` spelling hits
under tactic-mode `induction`/`rw` — the `•`-spelled, `GBL`-named wrapper
`omegaPbcV10Step3Law` below converts via a single term-mode ascription,
which IS lenient enough for this defeq). -/
theorem omegaPbcV10Step3LawCore (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier
      (RelTensor K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
        (FusionColumn (Γ.fuse ((b + c) + d) e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      (leftActionEnd K (Γ.D (b + c + d + e)).carrier
        (RelTensor K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (FusionColumn (Γ.fuse ((b + c) + d) e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))) τ n)
      = τ • (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) n := by
  induction n using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, smul_add, hp, hq]
  | mk z w =>
      rw [leftActionEnd_mk]
      induction z using RelTensor.induction_on with
      | zero => simp
      | add p q hp hq => simp [hp, hq]
      | mk v x => exact omegaPbcV10Step3Leaf K Γ a b c d e τ v x w

/-- Stage 3 of `omegaPbcV10`, GENERIC naturality (the `•`-spelled wrapper
`RelTensor.mapEquivRight` needs). -/
theorem omegaPbcV10Step3Law (τ : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e)))) (τ • n)
      = τ • (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
          (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
          (FusionColumn (Γ.fuse a (b + c + d + e)))) n :=
  omegaPbcV10Step3LawCore K Γ a b c d e τ n

/-- Stage 3 of `omegaPbcV10`, wrapped under the outer `F_{b,c}` spectator. -/
noncomputable def omegaPbcV10Step3 :
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K]
      RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) :=
  RelTensor.mapEquivRight K
    (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
      (FusionColumn (Γ.fuse a (b + c + d + e))))
    (omegaPbcV10Step3Law K Γ a b c d e)

/-- **Stage 3's generator formula**, on the fully split domain generator
`u ⊗ (GBL.mk v x ⊗ w)`. -/
theorem omegaPbcV10Step3_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse ((b + c) + d) e)) (w : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV10Step3 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w))
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) u
          (GQ3.mk K Γ a (b + c) d e v (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
            (FusionColumn (Γ.fuse ((b + c) + d) e)) (FusionColumn (Γ.fuse a (b + c + d + e))) x w)) := by
  have step1 : (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e))))
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w)
      = RelTensor.mk K (Γ.D ((b + c) + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) v
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse ((b + c) + d) e))
            (FusionColumn (Γ.fuse a (b + c + d + e))) x w) :=
    RelTensor.assoc_mk K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
      (FusionColumn (Γ.fuse a (b + c + d + e))) v x w
  have step2 : omegaPbcV10Step3 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w))
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) u
          ((RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
              (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
              (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w)) :=
    RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse b c) →ₗ[K] FusionColumn (Γ.fuse b c))
      (RelTensor.assoc K (Γ.D ((b + c) + d)).carrier (Γ.D (b + c + d + e)).carrier
        (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse ((b + c) + d) e))
        (FusionColumn (Γ.fuse a (b + c + d + e)))).toLinearMap (fun _ _ => rfl)
      (omegaPbcV10Step3Law K Γ a b c d e) u
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
        (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) w)
  rw [step2, step1]
  rfl

/-- **`omegaPbcV10`**: `omegaPbcV10Step1.trans (omegaPbcV10Step2.trans
omegaPbcV10Step3)`, landing the literal, cast-free `GQ3 K Γ a (b+c) d e`. -/
noncomputable def omegaPbcV10 : V10 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) :=
  (omegaPbcV10Step1 K Γ a b c d e).trans
    ((omegaPbcV10Step2 K Γ a b c d e).trans (omegaPbcV10Step3 K Γ a b c d e))

/-- **The sign-free generator formula of `omegaPbcV10`.** -/
theorem omegaPbcV10_mk (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse (b + c + d) e)) (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaPbcV10 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) x) t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) u
          (GQ3.mk K Γ a (b + c) d e v
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse (b + c + d) e))
              (FusionColumn (Γ.fuse a (b + c + d + e))) x t)) := by
  have h1 := omegaPbcV10Step1_mk K Γ a b c d e (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) x) t
  have hgq1 : gq1Assoc K Γ b c d e (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) x)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e) u
          (GBL.mk Γ (b + c) d e v x) :=
    gq1Assoc_mk K Γ b c d e u v x
  rw [hgq1] at h1
  have h2 : omegaPbcV10Step2 K Γ a b c d e
      (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
        (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e))
        (FusionColumn (Γ.fuse a (b + c + d + e)))
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e) u
          (GBL.mk Γ (b + c) d e v x))
        t)
      = RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBL Γ (b + c) d e)
            (FusionColumn (Γ.fuse a (b + c + d + e))) (GBL.mk Γ (b + c) d e v x) t) :=
    RelTensor.assoc_mk K (Γ.D (b + c)).carrier (Γ.D (b + c + d + e)).carrier
      (FusionColumn (Γ.fuse b c)) (GBL Γ (b + c) d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
      u (GBL.mk Γ (b + c) d e v x) t
  have h3 := omegaPbcV10Step3_mk K Γ a b c d e u v x t
  show omegaPbcV10Step3 K Γ a b c d e (omegaPbcV10Step2 K Γ a b c d e
      (omegaPbcV10Step1 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ1 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) x) t))) = _
  rw [h1, h2, h3]

end OmegaPbcV10

/-! ### `omegaPbcV2 : V2 ≃ₗ F_{b,c} ⊗ GQ1(a,b+c,d,e)` -/

section OmegaPbcV2

/-- **The NEW recast instance**: `GBL Γ a (b+c) d`'s right action pulled
back from its own natural total `a+(b+c)+d` to `V2`'s own native total
`a+b+c+d`, along `pbcHeq` — mirrors `RouteBimod.lean`'s `GBR`-own
"coefficient recast" section verbatim, one level up (`M := GBL Γ a (b+c) d`
in place of `GBR Γ p q r`). -/
noncomputable instance instModuleGblABCDOuterRecastV2 :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a (b + c) d) :=
  Module.compHom _ (((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv.toRingHom).op)

theorem gblABCDOuterRecastV2_op_smul_def (τ : (Γ.D (a + b + c + d)).carrier)
    (w : GBL Γ a (b + c) d) :
    MulOpposite.op τ • w
      = MulOpposite.op ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv τ) • w := rfl

/-- The recast right action still commutes with `GBL`'s own `(b+c)`-slot
(mirrors `Pentagon.lean`'s `fusionColumn_recast`-section cross-condition,
one level up). -/
instance instSMulCommClassGblABCDOuterRecastV2 :
    SMulCommClass (Γ.D (b + c)).carrier ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a (b + c) d) :=
  ⟨fun y t v => smul_comm y
    (MulOpposite.op ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv (MulOpposite.unop t))) v⟩

/-- The recast right action's own `K`-scalar tower. -/
instance instIsScalarTowerGblABCDOuterRecastV2 :
    IsScalarTower K ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GBL Γ a (b + c) d) :=
  ⟨fun k t v => by
    show (MulOpposite.op ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv
        (MulOpposite.unop (k • t)))) • v
      = k • ((MulOpposite.op ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv
          (MulOpposite.unop t))) • v)
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
    exact smul_assoc k _ v⟩

/-- **`gblOuterCastV2`, THE NEW DEVICE**: `GBL Γ a (b+c) d ⊗[D_{a+b+c+d}]
F_{a+b+c+d,e} ≃ GQ1 K Γ a (b+c) d e`, mirroring `Pentagon.lean`'s
`gq4Recast`'s construction exactly (two `RelTensor.lift` legs glued by
`LinearEquiv.ofLinear`, identity on the shared first factor
`GBL Γ a (b+c) d`, `gColumnCastFst` on the second, via `pbcHeq` in place
of `add_assoc`/`add_assoc_four`), one level up: `M` is a `GBL`-compound
spectator rather than a plain fusion column or `GBR`. -/
private noncomputable def gblOuterFwdBilin :
    GBL Γ a (b + c) d →ₗ[K] FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] GQ1 K Γ a (b + c) d e :=
  (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
    (FusionColumn (Γ.fuse (a + (b + c) + d) e))).compl₂
    (gColumnCastFst K Γ e (pbcHeq a b c d)).toLinearMap

private theorem gblOuterFwdBilin_apply (m : GBL Γ a (b + c) d)
    (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gblOuterFwdBilin K Γ a b c d e m v
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) := rfl

private theorem gblOuterFwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + b + c + d)).carrier (gblOuterFwdBilin K Γ a b c d e) := by
  intro t m v
  rw [gblOuterFwdBilin_apply, gblOuterFwdBilin_apply, gColumnCastFst_xslot,
    gblABCDOuterRecastV2_op_smul_def, RelTensor.mk_op_smul]

private noncomputable def gblOuterFwd :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) →ₗ[K]
      GQ1 K Γ a (b + c) d e :=
  RelTensor.lift (gblOuterFwdBilin K Γ a b c d e) (gblOuterFwd_balanced K Γ a b c d e)

private theorem gblOuterFwd_mk (m : GBL Γ a (b + c) d)
    (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gblOuterFwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
  show RelTensor.lift (gblOuterFwdBilin K Γ a b c d e) (gblOuterFwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v) = _
  rw [RelTensor.lift_mk, gblOuterFwdBilin_apply]

private noncomputable def gblOuterBwdBilin :
    GBL Γ a (b + c) d →ₗ[K] FusionColumn (Γ.fuse (a + (b + c) + d) e) →ₗ[K]
      RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) :=
  (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
    (FusionColumn (Γ.fuse (a + b + c + d) e))).compl₂
    (gColumnCastFst K Γ e (pbcHeq a b c d)).symm.toLinearMap

private theorem gblOuterBwdBilin_apply (m : GBL Γ a (b + c) d)
    (w : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    gblOuterBwdBilin K Γ a b c d e m w
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m
          ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w) := rfl

private theorem gblOuterBwd_balanced :
    RelTensor.IsBalanced (Γ.D (a + (b + c) + d)).carrier (gblOuterBwdBilin K Γ a b c d e) := by
  intro s m w
  rw [gblOuterBwdBilin_apply, gblOuterBwdBilin_apply, gColumnCastFst_symm_xslot,
    show (MulOpposite.op s • m : GBL Γ a (b + c) d)
        = MulOpposite.op ((Γ.gaugeCast (pbcHeq a b c d)).toAlgEquiv.symm s) • m from by
      rw [gblABCDOuterRecastV2_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

private noncomputable def gblOuterBwd :
    GQ1 K Γ a (b + c) d e →ₗ[K]
      RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) :=
  RelTensor.lift (gblOuterBwdBilin K Γ a b c d e) (gblOuterBwd_balanced K Γ a b c d e)

private theorem gblOuterBwd_mk (m : GBL Γ a (b + c) d)
    (w : FusionColumn (Γ.fuse (a + (b + c) + d) e)) :
    gblOuterBwd K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m
          ((gColumnCastFst K Γ e (pbcHeq a b c d)).symm w) := by
  show RelTensor.lift (gblOuterBwdBilin K Γ a b c d e) (gblOuterBwd_balanced K Γ a b c d e)
      (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w) = _
  rw [RelTensor.lift_mk, gblOuterBwdBilin_apply]

private theorem gblOuterFwd_bwd :
    (gblOuterFwd K Γ a b c d e).comp (gblOuterBwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show gblOuterFwd K Γ a b c d e (gblOuterBwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w))
    = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m w
  rw [gblOuterBwd_mk, gblOuterFwd_mk, LinearEquiv.apply_symm_apply]

private theorem gblOuterBwd_fwd :
    (gblOuterBwd K Γ a b c d e).comp (gblOuterFwd K Γ a b c d e) = LinearMap.id := by
  refine RelTensor.hom_ext fun m v => ?_
  show gblOuterBwd K Γ a b c d e (gblOuterFwd K Γ a b c d e
      (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v))
    = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e)) m v
  rw [gblOuterFwd_mk, gblOuterBwd_mk, LinearEquiv.symm_apply_apply]

/-- **`gblOuterCastV2`**: identity on the shared first factor
`GBL Γ a (b+c) d`, `gColumnCastFst` on the second — transports `V2`'s own
native total `a+b+c+d` to `GQ1`'s own native total `a+(b+c)+d`. -/
noncomputable def gblOuterCastV2 :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
      ≃ₗ[K] GQ1 K Γ a (b + c) d e :=
  LinearEquiv.ofLinear (gblOuterFwd K Γ a b c d e) (gblOuterBwd K Γ a b c d e)
    (gblOuterFwd_bwd K Γ a b c d e) (gblOuterBwd_fwd K Γ a b c d e)

theorem gblOuterCastV2_mk (m : GBL Γ a (b + c) d)
    (v : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gblOuterCastV2 K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
      = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
          (gColumnCastFst K Γ e (pbcHeq a b c d) v) :=
  gblOuterFwd_mk K Γ a b c d e m v

/-- **`gq2rCast`'s `D_{a+b+c+d}`-total equivariance**: `gq2rCast`
intertwines `GQ2rInner`'s own NATURAL right action (matching
`GQ2rInner`'s own total, literally `(a+b+c)+d = a+b+c+d`) with
`GBL Γ a (b+c) d`'s NEW recast right action
(`instModuleGblABCDOuterRecastV2`) — derived directly from the
ALREADY-LANDED `gColumnCastFst_coeff` (`ChiCanon.lean`). -/
theorem gq2rCast_totalSlot (τ : (Γ.D (a + b + c + d)).carrier) (n : GQ2rInner K Γ a b c d) :
    gq2rCast K Γ a b c d (MulOpposite.op τ • n)
      = MulOpposite.op τ • gq2rCast K Γ a b c d n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk v w =>
      have hL : gq2rCast K Γ a b c d
          (MulOpposite.op τ • RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d v
            (gColumnCastFst K Γ d (add_assoc a b c) (MulOpposite.op τ • w)) := by
        rw [show (MulOpposite.op τ • RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
              : GQ2rInner K Γ a b c d)
            = RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
                (FusionColumn (Γ.fuse (a + b + c) d)) v (MulOpposite.op τ • w) from
          rightActionEnd_mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) (MulOpposite.op τ) v w,
          gq2rCast_mk]
      have hR : MulOpposite.op τ • gq2rCast K Γ a b c d
          (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
            (FusionColumn (Γ.fuse (a + b + c) d)) v w)
        = GBL.mk Γ a (b + c) d v
            (gColumnCastFst K Γ d (add_assoc a b c) (MulOpposite.op τ • w)) := by
        rw [gq2rCast_mk, gblABCDOuterRecastV2_op_smul_def, GBL.right_smul_mk,
          ← gColumnCastFst_coeff]
      rw [hL, hR]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

/-- **`gblOuterCastV2`'s `D_{b+c}`-slot equivariance, unconditional**: the
device only ever touches the SECOND factor (via `gColumnCastFst`), so it
commutes freely with `GBL Γ a (b+c) d`'s own `bslot` (`D_{b+c}`) action,
lifted to both sides via `leftModule`/`GQ1`'s own `bslot_smul_mk`. -/
theorem gblOuterCastV2_bcSlot (y : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gblOuterCastV2 K Γ a b c d e (y • n) = y • gblOuterCastV2 K Γ a b c d e n := by
  induction n using RelTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | mk m v =>
      have hL : gblOuterCastV2 K Γ a b c d e
          (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
        = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + (b + c) + d) e)) (y • m)
            (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
        rw [show (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) m v
              : RelTensor K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e)))
            = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) (y • m) v from
          leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) y m v,
          gblOuterCastV2_mk]
      have hbslot : (y • RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + (b + c) + d) e)) m
            (gColumnCastFst K Γ e (pbcHeq a b c d) v)
          : GQ1 K Γ a (b + c) d e)
          = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
              (FusionColumn (Γ.fuse (a + (b + c) + d) e)) (y • m)
              (gColumnCastFst K Γ e (pbcHeq a b c d) v) :=
        GQ1.bslot_smul_mk K Γ a (b + c) d e y m (gColumnCastFst K Γ e (pbcHeq a b c d) v)
      have hR : y • gblOuterCastV2 K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) m v)
        = RelTensor.mk K (Γ.D (a + (b + c) + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + (b + c) + d) e)) (y • m)
            (gColumnCastFst K Γ e (pbcHeq a b c d) v) := by
        rw [gblOuterCastV2_mk]; exact hbslot
      rw [hL, hR]
  | add x y' hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

/-- **The `IsScalarTower` witness for `GQ2rInner K Γ a b c d`'s own
`(b+c)`-slot** (mirrors `QuintEdges7.lean`'s `instIsScalarTowerGQ2rInnerBCSlot`
at the UNSHIFTED 4th argument `d`) — needed so that `GQ2rInner K Γ a b c d`
can serve as the `M`-slot of a further OUTER `leftModule` at `D_{b+c}`
(`gq2rCastWrappedV2`'s own outer whiskering below). -/
instance instIsScalarTowerGQ2rInnerBCSlotV2 :
    IsScalarTower K (Γ.D (b + c)).carrier (GQ2rInner K Γ a b c d) :=
  ⟨fun k' x n => by
    show (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)) (k' • x)) n
      = k' • (leftActionEnd K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
        (FusionColumn (Γ.fuse (a + b + c) d)) x) n
    rw [map_smul, LinearMap.smul_apply]⟩

/-- **`gq2rCastWrappedV2`**: `mapEquivLeft (gq2rCast)` (`GQ2rInner →
GBL Γ a (b+c) d`, via `gq2rCast_totalSlot`) then `gblOuterCastV2` — lands
the literal, cast-free-in-the-`GBL`-slot `GQ1 K Γ a (b+c) d e`. -/
noncomputable def gq2rCastWrappedV2 :
    RelTensor K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
        (FusionColumn (Γ.fuse (a + b + c + d) e))
      ≃ₗ[K] GQ1 K Γ a (b + c) d e :=
  (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
    (gq2rCast_totalSlot K Γ a b c d)).trans (gblOuterCastV2 K Γ a b c d e)

/-- **`mapEquivLeft (gq2rCast)`'s generator formula**: unfolds
`PentagonB.RelTensor.mapEquivLeft` directly via `RelTensor.map_mk`
(avoiding the instances-transparency trap `rw [RelTensor.map_mk]` hits
against the un-unfolded `mapEquivLeft` application). -/
theorem gq2rCastMapLeftV2_mk (m : GQ2rInner K Γ a b c d)
    (w : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
        (gq2rCast_totalSlot K Γ a b c d))
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) m w)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
          (FusionColumn (Γ.fuse (a + b + c + d) e)) (gq2rCast K Γ a b c d m) w :=
  RelTensor.map_mk (gq2rCast K Γ a b c d).toLinearMap
    (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K]
      FusionColumn (Γ.fuse (a + b + c + d) e))
    (gq2rCast_totalSlot K Γ a b c d) (fun _ _ => rfl) m w

/-- `gq2rCastWrappedV2`'s `D_{b+c}`-slot equivariance (needed to whisker it
under `V2`'s own outer `F_{b,c}` spectator via `RelTensor.mapEquivRight`):
composes `gq2rCast_bcSlot` (`ChiCanon.lean`, unconditional) with
`gblOuterCastV2_bcSlot` (unconditional). -/
theorem gq2rCastWrappedV2_bcSlot (y : (Γ.D (b + c)).carrier)
    (n : RelTensor K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e))) :
    gq2rCastWrappedV2 K Γ a b c d e (y • n) = y • gq2rCastWrappedV2 K Γ a b c d e n := by
  show gblOuterCastV2 K Γ a b c d e
      ((PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
        (gq2rCast_totalSlot K Γ a b c d)) (y • n))
    = y • gblOuterCastV2 K Γ a b c d e
        ((PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
          (gq2rCast_totalSlot K Γ a b c d)) n)
  have hmid : (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
        (gq2rCast_totalSlot K Γ a b c d)) (y • n)
      = y • (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
          (gq2rCast_totalSlot K Γ a b c d)) n := by
    induction n using RelTensor.induction_on with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | mk m w =>
        have hL : (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
              (gq2rCast_totalSlot K Γ a b c d))
            (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) m w)
          = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) (gq2rCast K Γ a b c d (y • m)) w := by
          rw [show (y • RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
                (FusionColumn (Γ.fuse (a + b + c + d) e)) m w
                : RelTensor K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
                    (FusionColumn (Γ.fuse (a + b + c + d) e)))
              = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
                  (FusionColumn (Γ.fuse (a + b + c + d) e)) (y • m) w from
            leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) y m w,
            gq2rCastMapLeftV2_mk]
        have hR : y • (PentagonB.RelTensor.mapEquivLeft K (gq2rCast K Γ a b c d)
              (gq2rCast_totalSlot K Γ a b c d))
            (RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GQ2rInner K Γ a b c d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) m w)
          = RelTensor.mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
              (FusionColumn (Γ.fuse (a + b + c + d) e)) (gq2rCast K Γ a b c d (y • m)) w := by
          rw [gq2rCastMapLeftV2_mk, gq2rCast_bcSlot]
          exact leftActionEnd_mk K (Γ.D (a + b + c + d)).carrier (GBL Γ a (b + c) d)
            (FusionColumn (Γ.fuse (a + b + c + d) e)) y (gq2rCast K Γ a b c d m) w
        rw [hL, hR]
  rw [hmid, gblOuterCastV2_bcSlot]

/-- `inferInstanceAs` bridge: `GQ2r K Γ a b c d`'s own `D_{a+b+c+d}`-total
right action, in the raw `RelTensor` spelling `mapEquivLeft (gq2Assoc)`
needs (`GQ2r` is a `def`, not `abbrev`, so typeclass search does not
automatically unfold it to find the RAW form's own `rightModule`-supplied
instance — mirrors `QuintExtract.lean`'s `instModuleOmegaV9GQ4rASlot`
bridging discipline). -/
noncomputable instance instModuleGQ2rABCDRightV2 :
    Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ (GQ2r K Γ a b c d) :=
  inferInstanceAs (Module ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ
    (RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ2rInner K Γ a b c d)))

/-- **`omegaPbcV2`**: `gq2Assoc` (whiskered, naturality
`gq2Assoc_rightTotal`), a plain `RelTensor.assoc` (peeling `F_{b,c}` past
the outer `D_{a+b+c+d}`), then `gq2rCastWrappedV2` (whiskered under
`F_{b,c}` via `RelTensor.mapEquivRight`) — landing the literal, cast-free
`GQ1 K Γ a (b+c) d e`. -/
noncomputable def omegaPbcV2 : V2 K Γ a b c d e ≃ₗ[K]
    RelTensor K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ1 K Γ a (b + c) d e) :=
  ((PentagonB.RelTensor.mapEquivLeft K (gq2Assoc K Γ a b c d)
      (gq2Assoc_rightTotal K Γ a b c d)).trans
    (RelTensor.assoc K (Γ.D (b + c)).carrier (Γ.D (a + b + c + d)).carrier
      (FusionColumn (Γ.fuse b c)) (GQ2rInner K Γ a b c d)
      (FusionColumn (Γ.fuse (a + b + c + d) e)))).trans
    (RelTensor.mapEquivRight K (gq2rCastWrappedV2 K Γ a b c d e)
      (gq2rCastWrappedV2_bcSlot K Γ a b c d e))

end OmegaPbcV2

end GaugeChi

end Superfusion
