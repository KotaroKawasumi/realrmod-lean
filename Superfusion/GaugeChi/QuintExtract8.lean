/-
Superfusion / GaugeChi / QuintExtract8

Milestone M13-R3c of the `(p, χ)` arc's CLUSTER-FACE phase, continuing
`QuintExtract4.lean`'s own closing finding: **the combined device** for
`omegaV14'`'s tail (past `gV14Split`), and the naturality lemma relating
it to `E21M_leaf`'s specific opaque `Y`-shape.

## The blocker, restated

`QuintExtract4.lean`'s module docstring traces `omegaV14'`'s own
generator formula against `E21M_leaf`'s domain shape (`mk n Y`, `n`
split-able, `Y` opaque) and finds a SECOND-STAGE obstruction: `gV14SplitC`
(a plain `RelTensor.assoc.symm`) needs its OWN second argument `Y`
`mk`-shaped to fire `RelTensor.assoc_symm_mk`. Since `Y` is never split in
`E21M_leaf`'s own statement (the established "leave the canonical image
unexpanded" convention), the STAGEWISE `_mk`-lemma chase used for
`recog_E14M`/`recog_E17M` cannot be used verbatim.

## What lands

* **`gV14TailCast`** (the device): `gV14SplitC.trans (mapEquivLeftGThreeCast.
  trans gq4TotalCast) : F_{c,d+e} ⊗_{D_{c+d+e}} Y_{-}type ≃ₗ[K]
  GQ4 K Γ a b c (d+e)` — the UNWRAPPED tail of `omegaV14'` past
  `gV14Split`, landed as ONE named equivalence rather than three
  separately-wrapped stages, consuming the joint pair `(u, Y)` in a
  single application with NO `mk`-shape required on `Y` to even STATE
  the application. **Framing deviation from the round brief's literal
  "one `RelTensor.lift` over the pair" phrasing** (recorded here): rather
  than re-deriving `gV14SplitC`'s own `RelTensor.lift`-backed
  `assoc.symm` machinery from scratch at a NEW target type (which would
  duplicate `Bimod.RelTensorAssoc`'s PRIVATE `bwd`/`bwdInnerFlip`
  construction under fresh names, needing a fresh three-instance ledger
  for a NEW `F_{c,d+e} ⊗ GBR Γ a b (c+d+e)`-shaped recast, mirroring
  `gThreeCast`'s own three-triple cost one level up), `gV14TailCast` is
  assembled from the ALREADY-LANDED `RelTensor.lift`-backed pieces
  (`gV14SplitC` itself IS `RelTensor.assoc.symm`; `gThreeCast`/
  `gq4TotalCast` are each already `RelTensor.lift`-glued
  `LinearEquiv.ofLinear`s). This is mathematically the SAME kind of
  device the brief describes — its defining property (proved below) is
  exactly what a from-scratch lift would give: `gV14TailCast (mk u Y)` is
  a well-formed value for `Y` literally opaque, and `gV14TailCast_mk`
  gives its reduced value whenever `Y` happens to be `mk`-shaped.
* **`gV14TailCast_mk`**: the closed generator formula on split
  `Y = mk n' p'` — `GQ4.mk (GBR.mk u (fusionColumnCast … n'))
  (fusionColumnCast … p')` — chased via `gV14SplitC_mk` (a direct
  `RelTensor.assoc_symm_mk` instantiation), `mapEquivLeftGThreeCast_mk`
  (a direct `PentagonB.RelTensor.mapEquivLeft`/`RelTensor.map_mk`
  instantiation, both PUBLIC), and `gThreeCast_mk`/`gq4TotalCast_mk`
  (already public).
* **`gq3rCast_symm_mk`**: the missing public backward-direction generator
  formula for `gq3rCast` (`QuintEdges8.lean` only exports the forward
  `gq3rCast_mk`) — a two-line `LinearEquiv.injective` round-trip off the
  forward formula.
* **`gV14TailCast_gq3rCast_symm_mk`**: THE NATURALITY LEMMA relating the
  device to `E21M_leaf`'s specific `Y`-shape: for `Y = (gq3rCast).symm m`
  with `m` presented as `GBR.mk n' p'` (`gq3rCast`'s own domain shape,
  `QuintEdges8.lean`), `gV14TailCast (mk u ((gq3rCast).symm
  (GBR.mk n' p')))` reduces via `gq3rCast_symm_mk` then `gV14TailCast_mk`
  — landing the closed `GQ4.mk`-formula directly in terms of `n', p'`,
  WITHOUT ever needing `gV14SplitC`'s own blocked `assoc_symm_mk` step to
  fire on the raw, unexpanded `(gq3rCast).symm m`.
* **`gV14Split_mk`**, **`gV14SplitCWrapped_mk`**, the two further
  `RelTensor.mapEquivRight`-wrap `_mk` bridges
  (`mapEquivRightGThreeCastOuter_mk`/`mapEquivRightGQ4TotalCastOuter_mk`),
  and **`omegaV14'_gV14StepFinal_mk`**: the leaf-level connection from
  `omegaV14'` ITSELF (the spelling favored here, per `QuintExtract4.lean`'s
  own closing recommendation — it is the one whose `gq4Close`-peel is
  ordered before the `assoc`-regroup, exactly the ordering `gV14StepFinal`/
  `gV14Split`/`gV14SplitC` are built around) to `gV14TailCast`, general in
  the opaque `Y` — `omegaV14' (gV14StepFinal (mk (GBR.mk w u) Y)) = mk w
  (gV14TailCast (mk u Y))`, for ANY `Y` (no `mk`-shape needed on `Y` at
  all, since every stage crossed is GENERAL in `Y`, per `QuintExtract4`'s
  own finding). Composed with `gV14TailCast_gq3rCast_symm_mk`, this fully
  reduces `omegaV14'` applied to `E21M_leaf`'s RHS whenever the swapped
  `GBR(c,d,e)`-column `n` is split as `GBR.mk w u` and the `gq3rCast.symm`
  argument `m` is split as `GBR.mk n' p'`.

## What did NOT land: `recog_E21M` itself (the fallback)

Per the round brief's own fallback clause, `recog_E21M`'s full assembly is
NOT attempted this round. Tracing the OUTER assembly needed
(`(gq4Close K Γ a b c (d+e)).toLinearMap ∘ₗ GE5 K Γ a b c (d+e) …`)
against the device above surfaces a THIRD, independent obstruction, one
level up from the two already logged (`QuintExtract.lean`'s gate (α),
`QuintExtract4.lean`'s `gV14SplitC`-vs-opaque-`Y` finding): `E21M_leaf`'s
own `m := gTCanon K Γ a b (c+d+e) (mk t p)` is, per the established
"leave the canonical image unexpanded" convention, NEVER split as
`GBR.mk n' p'` — so `gV14TailCast_gq3rCast_symm_mk` (which needs `m`
`GBR.mk`-shaped to fire) cannot be applied to it directly, and relating
`gV14TailCast`'s value at `mk u ((gq3rCast).symm (gTCanon …))` to `GE5`'s
own `gq5Swap`-built output needs a genuinely NEW fact about how
`gTCanon K Γ a b (c+d+e)` interacts with `gq3rCast.symm` — NOT a
`mk`-shape reduction (which the naturality lemma above already handles in
full generality), but a "commutes with a fixed opaque intertwiner" fact,
the SAME genre of obstruction `QuintExtract7.lean`'s independent
`recog_E15M`/`recog_E16M` deferral notes flag as the arc's recurring
missing toolkit item ("`RelTensor.map` commutes past `RelTensor.assoc` on
an opaque inner argument", `QuintExtract3.lean`'s own closing note). Per
the round brief's explicit fallback, this is left for the round that
schedules it; the device and its naturality lemma above are the entire
remaining obstruction as identified, landed here.
-/
import Superfusion.GaugeChi.QuintExtract4

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

/-! ### `gq3rCast_symm_mk`: the missing public backward generator formula -/

theorem gq3rCast_symm_mk (n' : FusionColumn (Γ.fuse b (c + d + e)))
    (p' : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    (gq3rCast K Γ a b c d e).symm (GBR.mk Γ a b (c + d + e) n' p')
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))) n'
          ((fusionColumnCast K Γ a (add_assoc_four b c d e)).symm p') := by
  apply (gq3rCast K Γ a b c d e).injective
  rw [LinearEquiv.apply_symm_apply, gq3rCast_mk, LinearEquiv.apply_symm_apply]

/-! ### `gV14SplitC_mk`, a direct `assoc_symm_mk` instantiation -/

theorem gV14SplitC_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (n' : FusionColumn (Γ.fuse b (c + d + e))) (p' : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV14SplitC K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) n' p'))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))) u n') p' :=
  RelTensor.assoc_symm_mk K (Γ.D (c + d + e)).carrier (Γ.D (b + c + d + e)).carrier
    (FusionColumn (Γ.fuse c (d + e))) (FusionColumn (Γ.fuse b (c + d + e)))
    (FusionColumn (Γ.fuse a (b + c + d + e))) u n' p'

/-! ### `mapEquivLeftGThreeCast_mk`, a direct public unfold -/

theorem mapEquivLeftGThreeCast_mk
    (m' : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (FusionColumn (Γ.fuse b (c + d + e))))
    (p : FusionColumn (Γ.fuse a (b + c + d + e))) :
    mapEquivLeftGThreeCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (FusionColumn (Γ.fuse b (c + d + e))))
          (FusionColumn (Γ.fuse a (b + c + d + e))) m' p)
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
          (FusionColumn (Γ.fuse a (b + c + d + e))) (gThreeCast K Γ b c d e m') p :=
  RelTensor.map_mk (gThreeCast K Γ b c d e).toLinearMap
    (LinearMap.id : FusionColumn (Γ.fuse a (b + c + d + e))
      →ₗ[K] FusionColumn (Γ.fuse a (b + c + d + e)))
    (gThreeCast_rightTotal K Γ b c d e) (fun _ _ => rfl) m' p

/-! ### `gV14TailCast`, the device -/

/-- **`gV14TailCast`**: the UNWRAPPED tail of `omegaV14'` past
`gV14Split` — `gV14SplitC` (itself `RelTensor.assoc.symm`) then
`mapEquivLeftGThreeCast` (`gThreeCast`, wrapped) then `gq4TotalCast`,
landed as ONE equivalence consuming the joint pair `(u, Y)` (`Y` opaque
or not) in a single application, rather than as three separately-wrapped
stages. -/
noncomputable def gV14TailCast :
    RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
          (FusionColumn (Γ.fuse a (b + c + d + e))))
      ≃ₗ[K] GQ4 K Γ a b c (d + e) :=
  (gV14SplitC K Γ a b c d e).trans
    ((mapEquivLeftGThreeCast K Γ a b c d e).trans (gq4TotalCast K Γ a b c d e))

theorem gV14TailCast_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (n' : FusionColumn (Γ.fuse b (c + d + e))) (p' : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gV14TailCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e))) n' p'))
      = GQ4.mk K Γ a b c (d + e)
          (GBR.mk Γ b c (d + e) u (fusionColumnCast K Γ b (add_assoc c d e) n'))
          (fusionColumnCast K Γ a (add_assoc (b + c) d e) p') := by
  show gq4TotalCast K Γ a b c d e
      (mapEquivLeftGThreeCast K Γ a b c d e
        (gV14SplitC K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) u
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))) n' p')))) = _
  rw [gV14SplitC_mk, mapEquivLeftGThreeCast_mk, gThreeCast_mk, gq4TotalCast_mk]

/-! ### The naturality lemma -/

/-- **The naturality lemma**: `gV14TailCast`'s value at `mk u
((gq3rCast).symm m)`, for `m` presented as `GBR.mk n' p'` (`gq3rCast`'s
own domain shape) — the specialization to `E21M_leaf`'s own `Y`-shape
that the module docstring's "combined device" finding calls for. No
`gV14SplitC`-level `assoc_symm_mk` obstruction is ever hit: the whole
computation factors through `gq3rCast_symm_mk` (turning `Y` into an
explicit `mk`-pair) followed by `gV14TailCast_mk`. -/
theorem gV14TailCast_gq3rCast_symm_mk (u : FusionColumn (Γ.fuse c (d + e)))
    (n' : FusionColumn (Γ.fuse b (c + d + e))) (p' : FusionColumn (Γ.fuse a (b + (c + d + e)))) :
    gV14TailCast K Γ a b c d e
        (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) u
          ((gq3rCast K Γ a b c d e).symm (GBR.mk Γ a b (c + d + e) n' p')))
      = GQ4.mk K Γ a b c (d + e)
          (GBR.mk Γ b c (d + e) u (fusionColumnCast K Γ b (add_assoc c d e) n'))
          (fusionColumnCast K Γ a (add_assoc (b + c) d e)
            ((fusionColumnCast K Γ a (add_assoc_four b c d e)).symm p')) := by
  rw [gq3rCast_symm_mk, gV14TailCast_mk]

/-! ### Connecting the device to `omegaV14'` -/

/-- `gV14Split`'s own generator formula, on `n` split as `GBR.mk w u` —
GENERAL in the opaque second factor `Y` (`assoc_mk`'s own formula never
touches its own `P`-slot), mirroring `QuintExtract4.lean`'s own finding
about `gV14Split`. -/
theorem gV14Split_mk (w : FusionColumn (Γ.fuse d e)) (u : FusionColumn (Γ.fuse c (d + e)))
    (Y : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    gV14Split K Γ a b c d e
        (gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (GBR.mk Γ c d e w u) Y))
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))) w
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e)))) u Y) := by
  show (RelTensor.assoc K (Γ.D (d + e)).carrier (Γ.D (c + d + e)).carrier
      (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse c (d + e)))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e)))))
      ((gV14StepFinal K Γ a b c d e).symm
        (gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (GBR.mk Γ c d e w u) Y))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact RelTensor.assoc_mk K (Γ.D (d + e)).carrier (Γ.D (c + d + e)).carrier
    (FusionColumn (Γ.fuse d e)) (FusionColumn (Γ.fuse c (d + e)))
    (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) w u Y

theorem gV14SplitCWrapped_mk (w : FusionColumn (Γ.fuse d e))
    (X : RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
      (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
        (FusionColumn (Γ.fuse a (b + c + d + e))))) :
    gV14SplitCWrapped K Γ a b c d e
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))) w X)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w (gV14SplitC K Γ a b c d e X) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K] FusionColumn (Γ.fuse d e))
    (gV14SplitC K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gV14SplitC_leftEquiv K Γ a b c d e) w X

theorem mapEquivRightGThreeCastOuter_mk (w : FusionColumn (Γ.fuse d e))
    (X : RelTensor K (Γ.D (b + c + d + e)).carrier
      (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
        (FusionColumn (Γ.fuse b (c + d + e))))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (RelTensor.mapEquivRight K (mapEquivLeftGThreeCast K Γ a b c d e)
        (mapEquivLeftGThreeCast_leftEquiv K Γ a b c d e))
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier
            (RelTensor K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (FusionColumn (Γ.fuse b (c + d + e))))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w X)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w
          (mapEquivLeftGThreeCast K Γ a b c d e X) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K] FusionColumn (Γ.fuse d e))
    (mapEquivLeftGThreeCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
    (mapEquivLeftGThreeCast_leftEquiv K Γ a b c d e) w X

theorem mapEquivRightGQ4TotalCastOuter_mk (w : FusionColumn (Γ.fuse d e))
    (X : RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    (RelTensor.mapEquivRight K (gq4TotalCast K Γ a b c d e) (gq4TotalCast_dSlot K Γ a b c d e))
        (RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (RelTensor K (Γ.D (b + c + d + e)).carrier (GBR Γ b c (d + e))
            (FusionColumn (Γ.fuse a (b + c + d + e)))) w X)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
          (gq4TotalCast K Γ a b c d e X) :=
  RelTensor.map_mk (LinearMap.id : FusionColumn (Γ.fuse d e) →ₗ[K] FusionColumn (Γ.fuse d e))
    (gq4TotalCast K Γ a b c d e).toLinearMap (fun _ _ => rfl) (gq4TotalCast_dSlot K Γ a b c d e) w X

/-- **`omegaV14'_gV14StepFinal_mk`**: connecting `omegaV14'` (the spelling
favored here) to the device `gV14TailCast`, on `n` split as `GBR.mk w u`
and `Y` LITERALLY OPAQUE — no `mk`-shape needed on `Y` anywhere in this
proof, since every stage crossed (`gV14Split`, `gV14SplitCWrapped`, the
two further `mapEquivRight`-wraps) is general in its own opaque
"spectator" argument. -/
theorem omegaV14'_gV14StepFinal_mk (w : FusionColumn (Γ.fuse d e))
    (u : FusionColumn (Γ.fuse c (d + e)))
    (Y : RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
      (FusionColumn (Γ.fuse a (b + c + d + e)))) :
    omegaV14' K Γ a b c d e
        (gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (GBR.mk Γ c d e w u) Y))
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e)) (GQ4 K Γ a b c (d + e)) w
          (gV14TailCast K Γ a b c d e
            (RelTensor.mk K (Γ.D (c + d + e)).carrier (FusionColumn (Γ.fuse c (d + e)))
              (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
                (FusionColumn (Γ.fuse a (b + c + d + e)))) u Y)) := by
  show ((gV14SplitCWrapped K Γ a b c d e).trans
      ((RelTensor.mapEquivRight K (mapEquivLeftGThreeCast K Γ a b c d e)
          (mapEquivLeftGThreeCast_leftEquiv K Γ a b c d e)).trans
        (RelTensor.mapEquivRight K (gq4TotalCast K Γ a b c d e)
          (gq4TotalCast_dSlot K Γ a b c d e))))
      (gV14Split K Γ a b c d e
        (gV14StepFinal K Γ a b c d e
          (RelTensor.mk K (Γ.D (c + d + e)).carrier (GBR Γ c d e)
            (RelTensor K (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b (c + d + e)))
              (FusionColumn (Γ.fuse a (b + c + d + e))))
            (GBR.mk Γ c d e w u) Y))) = _
  rw [gV14Split_mk, LinearEquiv.trans_apply, gV14SplitCWrapped_mk, LinearEquiv.trans_apply,
    mapEquivRightGThreeCastOuter_mk, mapEquivRightGQ4TotalCastOuter_mk]
  rfl

end GaugeChi

end Superfusion
