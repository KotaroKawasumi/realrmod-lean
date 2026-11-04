/-
Superfusion / GaugeChi / ColumnDictGauge

Items 1-3 of the §10 roadmap (the gauge `TDict` port, design memo §5): **the
gauge column dictionary** — the Γ-generic port of `Bimod/ColumnDict.lean`'s
`blColumnEquiv` and `Bimod/ColumnDict2.lean`'s `brColumnEquiv`, identifying
the two route bimodules `GBL`/`GBR` (`GaugeChi/RouteBimod.lean`) with the
fusion columns of the two composite routes (`Gauge/GaugeRoutes.lean`).

**Construction.**  `gblFirstCollapse`/`gbrFirstCollapse`
(`GaugeChi/InterSpace.lean`) already identify `GBL`/`GBR` with the
product-indexed columns over their natural right towers; reindexing along
`collapseIndexEquiv` (`Super/BWTransitivity.lean`) — THE SAME index bijection
`matrixSuperComp` uses to build the last step of `gaugeRouteL`/`gaugeRouteR`
— lands exactly on the routes' column index types (the `gaugeSizeL`/
`gaugeSizeR` components unfold definitionally to `collapseIndexEquiv`'s block
sizes), giving `gblColumnEquiv` and the native-frame `gbrNativeColumnEquiv`.

**The parity bookkeeping** needs no new `decide`: `BWTransitivity`'s
`collapseIndexEquiv_parity` is already stated for arbitrary `ℕ` block sizes
with the bare `sumParity` masks — exactly the grading data of
`Bimod.FusionColumn` over `Γ.size` — so the "gauge-generic parity lemma" of
the roadmap (`gblIndexEquiv_parity`/`gbrNativeIndexEquiv_parity`) is that
lemma instantiated verbatim (no `ZMod 8`/`fuseParity` content survives).

**The GBR frame cast** (the aligned dictionary `gbrColumnEquiv`, landing at
`FusionColumn (Γ.gaugeRouteR' a b c)`, i.e. at `gaugeRouteL`'s frame): the
stdTower blueprint's `sizeCastEquiv` was built from the concrete theorem
`sizeL_eq_sizeR`; for an abstract Γ the two composite sizes agree only up to
`frameAlign`'s three-case analysis, and the swap/odd-collapse branches shift
the COLUMN parity mask by `1` (a column has one index, not a row/column
pair, so `Sum.swap`'s `sumParity` shift does not cancel) — a shift-`0`
grading identification along a bare reindex is genuinely impossible there
(e.g. `gaugeSizeR = (n,0)`, `gaugeSizeL = (0,n)` over a purely even
`D_{a+b+c}` concentrates `GBR` and the target column in OPPOSITE parities).
The aligned dictionary therefore takes the first-branch hypothesis

  `hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c`

(under which `frameAlign` IS the pure cast, `frameAlign_of_sizes_eq` below —
the semantic-consistency lemma the roadmap anticipated), and the size cast is
the `Equiv.sumCongr`/`finCongr` port of `ColumnDict2.sizeCastEquiv`, the
value cast the `Γ.gaugeCast (add_assoc a b c).symm` port of `stdTowerCast`.
`hsz` is per-triple dischargeable at the concrete gauges (at `ZMod 8` sizes
it is `PentagonRoutes.sizeL_eq_sizeR`'s arithmetic), matching the §10 plan's
per-triple discharge of the `T`-matrix hypothesis.

**Landed deliverables** (mirroring `ColumnDict.lean`'s three, on both sides):

1. `gblColumnEquiv : GBL ≃ₗ[K] FusionColumn (Γ.gaugeRouteL a b c)`,
   `gbrNativeColumnEquiv : GBR ≃ₗ[K] FusionColumn (Γ.gaugeRouteR a b c)`
   (native frame, hypothesis-free), and
   `gbrColumnEquiv hsz : GBR ≃ₗ[K] FusionColumn (Γ.gaugeRouteR' a b c)`,
   each with `_apply`/`_mk` generator formulas.
2. Right equivariance: `gblColumnEquiv_rightEquiv` (plain, right
   `D_{(a+b)+c}`), `gbrNativeColumnEquiv_rightEquiv` (plain, native right
   `D_{a+(b+c)}`), `gbrColumnEquiv_rightEquiv` (against `GBR`'s RECAST right
   action, `RouteBimod.lean`, matching the target column's own
   `D_{(a+b)+c}`-action — the pointwise-cast compatibility is the `subst`
   port of `ColumnDict2.castAE_smul_compat`).
3. Grading correspondence, shift `0`, as an `iff` (forward by the
   `ColumnDict.lean:191` generator induction; reverse by
   `Bimod.gradedLinearEquiv_symm_mem`): `gblColumnEquiv_mem_grading_iff`,
   `gbrNativeColumnEquiv_mem_grading_iff`, `gbrColumnEquiv_mem_grading_iff`
   (the aligned one derived ENTRYWISE from the native one — no second
   induction — via `sumParity_gaugeSizeCastEquiv` and
   `Γ.gaugeCast_mem_grading`).
-/
import Superfusion.GaugeChi.ChiTower

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-! ### The reindexing equivalences and their parity laws -/

/-- **The index reindex identifying `GBL` with `FusionColumn (gaugeRouteL a b
c)`** — literally `collapseIndexEquiv` (`Super/BWTransitivity.lean`), the SAME
index bijection `matrixSuperComp` uses to build `gaugeRouteL`'s last step,
applied to the two block sizes `Γ.size a b`/`Γ.size (a+b) c`.  Its codomain
unfolds definitionally to `FusionColumn (Γ.gaugeRouteL a b c)`'s index type
(the two components of `Γ.gaugeSizeL a b c` are literally the block sizes
`collapseIndexEquiv` produces).  Port of `ColumnDict.blIndexEquiv`. -/
noncomputable def gblIndexEquiv :
    ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
        (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2))
      ≃ (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :=
  collapseIndexEquiv (Γ.size a b).1 (Γ.size a b).2
    (Γ.size (a + b) c).1 (Γ.size (a + b) c).2

/-- **The gauge-generic parity law of the left index collapse** (the roadmap's
"gauge `collapseIndexEquiv_parity`"): `BWTransitivity.collapseIndexEquiv_parity`
is already stated for arbitrary `ℕ` block sizes with the bare `sumParity`
masks — the grading data of `Bimod.FusionColumn` over `Γ.size` — so the gauge
version is that lemma instantiated verbatim. -/
theorem gblIndexEquiv_parity
    (x : (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) :
    sumParity (Γ.size a b).1 (Γ.size a b).2 x.1
        + sumParity (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 x.2
      = sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2
          (gblIndexEquiv K Γ a b c x) :=
  collapseIndexEquiv_parity (Γ.size a b).1 (Γ.size a b).2
    (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 x

/-- **The native index reindex of the right route**: `collapseIndexEquiv` at
the right route's block sizes `Γ.size b c`/`Γ.size a (b+c)`, landing
definitionally on `FusionColumn (Γ.gaugeRouteR a b c)`'s index type (the
`gaugeSizeR` frame). -/
noncomputable def gbrNativeIndexEquiv :
    ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
        (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2))
      ≃ (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :=
  collapseIndexEquiv (Γ.size b c).1 (Γ.size b c).2
    (Γ.size a (b + c)).1 (Γ.size a (b + c)).2

/-- The gauge-generic parity law of the right index collapse (mirror of
`gblIndexEquiv_parity`). -/
theorem gbrNativeIndexEquiv_parity
    (x : (Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)) :
    sumParity (Γ.size b c).1 (Γ.size b c).2 x.1
        + sumParity (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 x.2
      = sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2
          (gbrNativeIndexEquiv K Γ a b c x) :=
  collapseIndexEquiv_parity (Γ.size b c).1 (Γ.size b c).2
    (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 x

/-! ### `piCongrLeft'` commutes with any pointwise action -/

omit [Invertible (2 : K)] in
/-- **Reindexing along a fixed bijection commutes with any pointwise action**
(local copy of `ColumnDict.piCongrLeft'_smul`, `Bimod/ColumnDict.lean:105`; no
`stdFuse`/route content, recopied to keep the concrete `ZMod 8` column
dictionary out of this file's import cone). -/
private theorem piCongrLeft'_smul {ι ι' : Type*} (e : ι ≃ ι') {R M : Type*}
    [AddCommMonoid M] [Module K M] [SMul R M] (r : R) (f : ι → M) :
    (LinearEquiv.piCongrLeft' K (fun _ : ι => M) e) (r • f)
      = r • (LinearEquiv.piCongrLeft' K (fun _ : ι => M) e) f := by
  funext x
  rw [LinearEquiv.piCongrLeft'_apply, Pi.smul_apply, Pi.smul_apply,
    LinearEquiv.piCongrLeft'_apply]

/-! ### `gblColumnEquiv` -/

/-- **The column identification `GBL ≅ FusionColumn (Γ.gaugeRouteL a b c)`**
(§10 roadmap item 1, left side): `gblFirstCollapse`
(`GaugeChi/InterSpace.lean`), which identifies `GBL` with the product-indexed
column over `D_{(a+b)+c}`, followed by the reindex `gblIndexEquiv`.  Port of
`ColumnDict.blColumnEquiv`. -/
noncomputable def gblColumnEquiv :
    GBL Γ a b c ≃ₗ[K] FusionColumn (Γ.gaugeRouteL a b c) :=
  (gblFirstCollapse K Γ a b c).trans
    (LinearEquiv.piCongrLeft' K
      (fun _ : (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
          (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2) =>
        (Γ.D (a + b + c)).carrier)
      (gblIndexEquiv K Γ a b c))

/-- **`gblColumnEquiv`'s generator formula**: reindex `gblFirstCollapse`'s
value along `gblIndexEquiv`'s inverse (port of
`ColumnDict.blColumnEquiv_apply`). -/
theorem gblColumnEquiv_apply (m : GBL Γ a b c)
    (x : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    gblColumnEquiv K Γ a b c m x
      = RelTensor.freeCollapse m
          ((gblIndexEquiv K Γ a b c).symm x).1
          ((gblIndexEquiv K Γ a b c).symm x).2 := by
  show (LinearEquiv.piCongrLeft' K _ (gblIndexEquiv K Γ a b c))
      (gblFirstCollapse K Γ a b c m) x = _
  rw [LinearEquiv.piCongrLeft'_apply, gblFirstCollapse_apply]

/-- **`gblColumnEquiv` on generators**: the image of `GBL.mk u v` is the
explicit column `x ↦ (u p • v) q` for `(p, q)` the `gblIndexEquiv`-preimage
of `x` (the smul is the balancing `(a+b)`-slot action on the second fusion
column). -/
theorem gblColumnEquiv_mk (u : FusionColumn (Γ.fuse a b))
    (v : FusionColumn (Γ.fuse (a + b) c))
    (x : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v) x
      = (u ((gblIndexEquiv K Γ a b c).symm x).1 • v)
          ((gblIndexEquiv K Γ a b c).symm x).2 := by
  rw [gblColumnEquiv_apply,
    show RelTensor.freeCollapse (GBL.mk Γ a b c u v) = fun l => u l • v from
      RelTensor.freeCollapse_mk u v]

/-- **`gblColumnEquiv` is right `D_{(a+b)+c}`-equivariant** (§10 roadmap
item 2, left side), PLAIN: both `GBL`'s registered right action and
`FusionColumn`'s right action are the same pointwise action on a column of
`D_{(a+b)+c}`-values, so `gblFirstCollapse`'s own right equivariance
(`gblFirstCollapse_rightEquiv`, `GaugeChi/ChiTower.lean`) composes with the
reindex for free (`piCongrLeft'_smul`).  Port of
`ColumnDict.blColumnEquiv_rightEquiv`. -/
theorem gblColumnEquiv_rightEquiv (τ : (Γ.D (a + b + c)).carrier)
    (m : GBL Γ a b c) :
    gblColumnEquiv K Γ a b c (MulOpposite.op τ • m)
      = MulOpposite.op τ • gblColumnEquiv K Γ a b c m := by
  show (LinearEquiv.piCongrLeft' K _ (gblIndexEquiv K Γ a b c))
      (gblFirstCollapse K Γ a b c (MulOpposite.op τ • m))
    = MulOpposite.op τ •
        (LinearEquiv.piCongrLeft' K _ (gblIndexEquiv K Γ a b c))
          (gblFirstCollapse K Γ a b c m)
  rw [gblFirstCollapse_rightEquiv]
  exact piCongrLeft'_smul K (gblIndexEquiv K Γ a b c) (MulOpposite.op τ)
    (gblFirstCollapse K Γ a b c m)

/-! ### The grading correspondence, left side -/

private theorem zmod2_grading_shift :
    ∀ j₁ j₂ p1 p2 : ZMod 2, j₁ + p1 + j₂ + p2 = j₁ + j₂ + (p1 + p2) := by
  decide +revert

/-- **`gblColumnEquiv` maps homogeneous elements onto the matching graded
layer, shift `0`** (§10 roadmap item 3, left side, forward direction): port
of `ColumnDict.blColumnEquiv_mem_grading`, run through the packaged
generator induction `RelTensor.induction_on_grading`
(`Bimod/RelTensorGraded.lean`) — the two column masks combine, via
`gblIndexEquiv_parity`, into exactly the mask of the composite column. -/
theorem gblColumnEquiv_mem_grading {j : ZMod 2} {m : GBL Γ a b c}
    (hm : m ∈ GBL.grading Γ a b c j) :
    gblColumnEquiv K Γ a b c m
      ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) j := by
  refine RelTensor.mem_of_grading (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse (a + b) c))
    (gblColumnEquiv K Γ a b c).toLinearMap
    (FusionColumn.grading (Γ.gaugeRouteL a b c) j) hm ?_
  intro j₁ j₂ hjj u v hu hv
  rw [← hjj]
  show gblColumnEquiv K Γ a b c (GBL.mk Γ a b c u v)
    ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) (j₁ + j₂)
  intro y
  rw [gblColumnEquiv_apply]
  set p := ((gblIndexEquiv K Γ a b c).symm y).1
  set q := ((gblIndexEquiv K Γ a b c).symm y).2
  have hu' : u p ∈ (Γ.D (a + b)).grading
      (j₁ + sumParity (Γ.size a b).1 (Γ.size a b).2 p) := hu p
  have hsmul : u p • v ∈ FusionColumn.grading (Γ.fuse (a + b) c)
      ((j₁ + sumParity (Γ.size a b).1 (Γ.size a b).2 p) + j₂) :=
    SetLike.GradedSMul.smul_mem hu' hv
  have hval : (u p • v) q ∈ (Γ.D (a + b + c)).grading
      (((j₁ + sumParity (Γ.size a b).1 (Γ.size a b).2 p) + j₂)
        + sumParity (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 q) :=
    hsmul q
  have hfc : RelTensor.freeCollapse (GBL.mk Γ a b c u v) = fun l => u l • v :=
    RelTensor.freeCollapse_mk u v
  rw [hfc]
  have hy2 : gblIndexEquiv K Γ a b c ((gblIndexEquiv K Γ a b c).symm y) = y :=
    (gblIndexEquiv K Γ a b c).apply_symm_apply y
  have hpar : sumParity (Γ.size a b).1 (Γ.size a b).2 p
      + sumParity (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 q
      = sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2 y := by
    have h := gblIndexEquiv_parity K Γ a b c ((gblIndexEquiv K Γ a b c).symm y)
    rw [hy2] at h
    exact h
  show (u p • v) q ∈ _
  rw [show j₁ + j₂ + sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2 y
      = ((j₁ + sumParity (Γ.size a b).1 (Γ.size a b).2 p) + j₂)
        + sumParity (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 q from by
    rw [← hpar]
    exact (zmod2_grading_shift j₁ j₂
      (sumParity (Γ.size a b).1 (Γ.size a b).2 p)
      (sumParity (Γ.size (a + b) c).1 (Γ.size (a + b) c).2 q)).symm]
  exact hval

/-- The reverse direction of the left grading correspondence, by
`Bimod.gradedLinearEquiv_symm_mem` (the `TDict.lean` reversing device). -/
theorem gblColumnEquiv_symm_mem_grading {j : ZMod 2}
    {w : FusionColumn (Γ.gaugeRouteL a b c)}
    (hw : w ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) j) :
    (gblColumnEquiv K Γ a b c).symm w ∈ GBL.grading Γ a b c j :=
  gradedLinearEquiv_symm_mem (GBL.grading Γ a b c)
    (FusionColumn.grading (Γ.gaugeRouteL a b c)) (gblColumnEquiv K Γ a b c)
    (fun hm => gblColumnEquiv_mem_grading K Γ a b c hm) hw

/-- **The left grading correspondence, shift `0`, as an `iff`** (§10 roadmap
item 3, left side). -/
theorem gblColumnEquiv_mem_grading_iff {j : ZMod 2} {m : GBL Γ a b c} :
    gblColumnEquiv K Γ a b c m ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) j
      ↔ m ∈ GBL.grading Γ a b c j := by
  constructor
  · intro h
    have h2 := gblColumnEquiv_symm_mem_grading K Γ a b c h
    rwa [LinearEquiv.symm_apply_apply] at h2
  · exact gblColumnEquiv_mem_grading K Γ a b c

/-! ### `GBR`'s first collapse: generator formula and right equivariance

`gbrFirstCollapse` itself is `GaugeChi/InterSpace.lean`'s; only its `_apply`
and native right equivariance were missing (`ChiTower.lean` recorded the
`GBL` versions only) — ports of `ColumnDict2.q1FirstCollapseR_apply`/
`q1FirstCollapseR_rightEquiv`. -/

/-- `GBR`'s own right action, elementwise (the Γ-mirror of
`ColumnDict2.br_right_smul_apply`). -/
theorem gbr_right_smul_apply (τ : ((Γ.D (a + (b + c))).carrier)ᵐᵒᵖ)
    (m : GBR Γ a b c) :
    τ • m = rightActionEnd K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
      (FusionColumn (Γ.fuse a (b + c))) τ m := rfl

/-- **`GBR`'s own bare `freeCollapse`, transported along the outer native
right `D_{a+(b+c)}`-action** (the `GBR` mirror of `ChiTower.lean`'s
`freeCollapse_GBL_rightEquiv`). -/
theorem freeCollapse_GBR_rightEquiv (τ : (Γ.D (a + (b + c))).carrier)
    (m : GBR Γ a b c) :
    RelTensor.freeCollapse (MulOpposite.op τ • m)
      = MulOpposite.op τ • RelTensor.freeCollapse m := by
  have h := RelTensor.freeCollapse_rightActionEnd (K := K)
    (A := (Γ.D (b + c)).carrier) (n := Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2)
    (N := FusionColumn (Γ.fuse a (b + c))) (C := (Γ.D (a + (b + c))).carrier)
    (MulOpposite.op τ) m
  rw [gbr_right_smul_apply]
  exact h

/-- **`gbrFirstCollapse`'s generator formula** — `rfl`, mirroring
`gblFirstCollapse_apply`. -/
theorem gbrFirstCollapse_apply (m : GBR Γ a b c)
    (p : (Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
      (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2)) :
    gbrFirstCollapse K Γ a b c m p = RelTensor.freeCollapse m p.1 p.2 := rfl

/-- **`gbrFirstCollapse` intertwines the outer native right
`D_{a+(b+c)}`-action** (the pointwise action on the product-indexed column;
mirror of `gblFirstCollapse_rightEquiv`). -/
theorem gbrFirstCollapse_rightEquiv (τ : (Γ.D (a + (b + c))).carrier)
    (m : GBR Γ a b c) :
    gbrFirstCollapse K Γ a b c (MulOpposite.op τ • m)
      = MulOpposite.op τ • gbrFirstCollapse K Γ a b c m := by
  funext p
  show RelTensor.freeCollapse (MulOpposite.op τ • m) p.1 p.2
    = MulOpposite.op τ • RelTensor.freeCollapse m p.1 p.2
  exact congrFun (congrFun (freeCollapse_GBR_rightEquiv K Γ a b c τ m) p.1) p.2

/-! ### `gbrNativeColumnEquiv`: the right dictionary at the native frame -/

/-- **The native-frame column identification `GBR ≅ FusionColumn
(Γ.gaugeRouteR a b c)`** (hypothesis-free): `gaugeRouteR`'s frame — target
index `gaugeSizeR`, values `D_{a+(b+c)}` — is the one that lines up
DEFINITIONALLY with `gbrFirstCollapse`'s index product (no size or value cast
at all), so the construction is the exact mirror of `gblColumnEquiv`. -/
noncomputable def gbrNativeColumnEquiv :
    GBR Γ a b c ≃ₗ[K] FusionColumn (Γ.gaugeRouteR a b c) :=
  (gbrFirstCollapse K Γ a b c).trans
    (LinearEquiv.piCongrLeft' K
      (fun _ : (Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
          (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2) =>
        (Γ.D (a + (b + c))).carrier)
      (gbrNativeIndexEquiv K Γ a b c))

/-- **`gbrNativeColumnEquiv`'s generator formula**. -/
theorem gbrNativeColumnEquiv_apply (m : GBR Γ a b c)
    (x : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    gbrNativeColumnEquiv K Γ a b c m x
      = RelTensor.freeCollapse m
          ((gbrNativeIndexEquiv K Γ a b c).symm x).1
          ((gbrNativeIndexEquiv K Γ a b c).symm x).2 := by
  show (LinearEquiv.piCongrLeft' K _ (gbrNativeIndexEquiv K Γ a b c))
      (gbrFirstCollapse K Γ a b c m) x = _
  rw [LinearEquiv.piCongrLeft'_apply, gbrFirstCollapse_apply]

/-- **`gbrNativeColumnEquiv` on generators**: the image of `GBR.mk u v` is
the explicit column `x ↦ (u p • v) q` for `(p, q)` the
`gbrNativeIndexEquiv`-preimage of `x` (the smul is the balancing
`(b+c)`-slot action on the second fusion column). -/
theorem gbrNativeColumnEquiv_mk (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse a (b + c)))
    (x : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v) x
      = (u ((gbrNativeIndexEquiv K Γ a b c).symm x).1 • v)
          ((gbrNativeIndexEquiv K Γ a b c).symm x).2 := by
  rw [gbrNativeColumnEquiv_apply,
    show RelTensor.freeCollapse (GBR.mk Γ a b c u v) = fun l => u l • v from
      RelTensor.freeCollapse_mk u v]

/-- **`gbrNativeColumnEquiv` is right `D_{a+(b+c)}`-equivariant** (native
action on both sides), PLAIN. -/
theorem gbrNativeColumnEquiv_rightEquiv (τ : (Γ.D (a + (b + c))).carrier)
    (m : GBR Γ a b c) :
    gbrNativeColumnEquiv K Γ a b c (MulOpposite.op τ • m)
      = MulOpposite.op τ • gbrNativeColumnEquiv K Γ a b c m := by
  show (LinearEquiv.piCongrLeft' K _ (gbrNativeIndexEquiv K Γ a b c))
      (gbrFirstCollapse K Γ a b c (MulOpposite.op τ • m))
    = MulOpposite.op τ •
        (LinearEquiv.piCongrLeft' K _ (gbrNativeIndexEquiv K Γ a b c))
          (gbrFirstCollapse K Γ a b c m)
  rw [gbrFirstCollapse_rightEquiv]
  exact piCongrLeft'_smul K (gbrNativeIndexEquiv K Γ a b c) (MulOpposite.op τ)
    (gbrFirstCollapse K Γ a b c m)

/-! ### The grading correspondence, native right side -/

/-- **`gbrNativeColumnEquiv` maps homogeneous elements onto the matching
graded layer, shift `0`** (forward direction, hypothesis-free): the same
generator induction as `gblColumnEquiv_mem_grading`, run on the right route's
block data. -/
theorem gbrNativeColumnEquiv_mem_grading {j : ZMod 2} {m : GBR Γ a b c}
    (hm : m ∈ GBR.grading Γ a b c j) :
    gbrNativeColumnEquiv K Γ a b c m
      ∈ FusionColumn.grading (Γ.gaugeRouteR a b c) j := by
  refine RelTensor.mem_of_grading (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c)))
    (gbrNativeColumnEquiv K Γ a b c).toLinearMap
    (FusionColumn.grading (Γ.gaugeRouteR a b c) j) hm ?_
  intro j₁ j₂ hjj u v hu hv
  rw [← hjj]
  show gbrNativeColumnEquiv K Γ a b c (GBR.mk Γ a b c u v)
    ∈ FusionColumn.grading (Γ.gaugeRouteR a b c) (j₁ + j₂)
  intro y
  rw [gbrNativeColumnEquiv_apply]
  set p := ((gbrNativeIndexEquiv K Γ a b c).symm y).1
  set q := ((gbrNativeIndexEquiv K Γ a b c).symm y).2
  have hu' : u p ∈ (Γ.D (b + c)).grading
      (j₁ + sumParity (Γ.size b c).1 (Γ.size b c).2 p) := hu p
  have hsmul : u p • v ∈ FusionColumn.grading (Γ.fuse a (b + c))
      ((j₁ + sumParity (Γ.size b c).1 (Γ.size b c).2 p) + j₂) :=
    SetLike.GradedSMul.smul_mem hu' hv
  have hval : (u p • v) q ∈ (Γ.D (a + (b + c))).grading
      (((j₁ + sumParity (Γ.size b c).1 (Γ.size b c).2 p) + j₂)
        + sumParity (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 q) :=
    hsmul q
  have hfc : RelTensor.freeCollapse (GBR.mk Γ a b c u v) = fun l => u l • v :=
    RelTensor.freeCollapse_mk u v
  rw [hfc]
  have hy2 : gbrNativeIndexEquiv K Γ a b c
      ((gbrNativeIndexEquiv K Γ a b c).symm y) = y :=
    (gbrNativeIndexEquiv K Γ a b c).apply_symm_apply y
  have hpar : sumParity (Γ.size b c).1 (Γ.size b c).2 p
      + sumParity (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 q
      = sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 y := by
    have h := gbrNativeIndexEquiv_parity K Γ a b c
      ((gbrNativeIndexEquiv K Γ a b c).symm y)
    rw [hy2] at h
    exact h
  show (u p • v) q ∈ _
  rw [show j₁ + j₂ + sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 y
      = ((j₁ + sumParity (Γ.size b c).1 (Γ.size b c).2 p) + j₂)
        + sumParity (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 q from by
    rw [← hpar]
    exact (zmod2_grading_shift j₁ j₂
      (sumParity (Γ.size b c).1 (Γ.size b c).2 p)
      (sumParity (Γ.size a (b + c)).1 (Γ.size a (b + c)).2 q)).symm]
  exact hval

/-- The reverse direction of the native right grading correspondence. -/
theorem gbrNativeColumnEquiv_symm_mem_grading {j : ZMod 2}
    {w : FusionColumn (Γ.gaugeRouteR a b c)}
    (hw : w ∈ FusionColumn.grading (Γ.gaugeRouteR a b c) j) :
    (gbrNativeColumnEquiv K Γ a b c).symm w ∈ GBR.grading Γ a b c j :=
  gradedLinearEquiv_symm_mem (GBR.grading Γ a b c)
    (FusionColumn.grading (Γ.gaugeRouteR a b c)) (gbrNativeColumnEquiv K Γ a b c)
    (fun hm => gbrNativeColumnEquiv_mem_grading K Γ a b c hm) hw

/-- **The native right grading correspondence, shift `0`, as an `iff`**. -/
theorem gbrNativeColumnEquiv_mem_grading_iff {j : ZMod 2} {m : GBR Γ a b c} :
    gbrNativeColumnEquiv K Γ a b c m
        ∈ FusionColumn.grading (Γ.gaugeRouteR a b c) j
      ↔ m ∈ GBR.grading Γ a b c j := by
  constructor
  · intro h
    have h2 := gbrNativeColumnEquiv_symm_mem_grading K Γ a b c h
    rwa [LinearEquiv.symm_apply_apply] at h2
  · exact gbrNativeColumnEquiv_mem_grading K Γ a b c

/-! ### The frame cast of the aligned right dictionary

`FusionColumn (Γ.gaugeRouteR' a b c)` lives at `gaugeRouteL`'s frame (index
`gaugeSizeL`, values `D_{(a+b)+c}`), so the aligned dictionary needs a size
cast and a value cast on top of the native one.  The value cast is
`Γ.gaugeCast (add_assoc a b c).symm` (the Γ-mirror of `ColumnDict2`'s
`stdTowerCast (add_assoc a b c).symm`).  The size cast requires the
first-branch hypothesis `hsz : gaugeSizeR = gaugeSizeL` of `frameAlign`'s
case analysis: in the two remaining branches (`Sum.swap`, odd-unit collapse)
the column parity mask shifts by `1` under the underlying index bijection —
unlike the matrix grading, where row and column shifts cancel — so no
shift-`0` column dictionary along a bare reindex exists there (see the file
docstring for a concrete purely-even counterexample).  Under `hsz` the cast
is the exact port of `ColumnDict2.sizeCastEquiv` (there built from the
concrete theorem `sizeL_eq_sizeR`). -/

/-- The size-pair cast turning `gaugeSizeR`-frame indices into
`gaugeSizeL`-frame ones (port of `ColumnDict2.sizeCastEquiv`, with the
concrete `sizeL_eq_sizeR` replaced by the hypothesis `hsz`). -/
noncomputable def gaugeSizeCastEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) :
    (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      ≃ (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :=
  Equiv.sumCongr (finCongr (congrArg Prod.fst hsz))
    (finCongr (congrArg Prod.snd hsz))

/-- `sumParity` only depends on the `inl`/`inr` branch, so it is invariant
under `gaugeSizeCastEquiv` (an `Equiv.sumCongr` of `finCongr`s cannot cross
branches).  Port of `ColumnDict2.sumParity_sizeCastEquiv`. -/
theorem sumParity_gaugeSizeCastEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (x : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2
        (gaugeSizeCastEquiv K Γ a b c hsz x)
      = sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 x := by
  rcases x with x | x <;> rfl

/-- **The composite index reindex of the aligned right dictionary**:
the native collapse followed by the size cast. -/
noncomputable def gbrIndexEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) :
    ((Fin (Γ.size b c).1 ⊕ Fin (Γ.size b c).2) ×
        (Fin (Γ.size a (b + c)).1 ⊕ Fin (Γ.size a (b + c)).2))
      ≃ (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :=
  (gbrNativeIndexEquiv K Γ a b c).trans (gaugeSizeCastEquiv K Γ a b c hsz)

/-- **Under the sizes-equal hypothesis, `frameAlign` IS the pure frame cast**
(its first branch): the semantic-consistency lemma tying the aligned column
dictionary below to `gaugeRouteR'`'s own `frameAlign` step.  This is the
`frameAlign` lemma the §10 roadmap's GBR cast needed and that did not exist;
its content is just the first `by_cases` of `frameAlign`'s definition
(`Gauge/GaugeRoutes.lean`). -/
theorem frameAlign_of_sizes_eq
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) :
    Γ.frameAlign a b c = Γ.gaugeMatrixCast rfl hsz := by
  unfold DivisionFusionGauge.frameAlign
  split
  · rfl
  · next h1 => exact absurd hsz h1

/-- **Generic pointwise-cast compatibility** (the `subst`-generic port of
`ColumnDict2.castAE_smul_compat_generic`): for an index equality `h : x = y`,
the value cast `Γ.gaugeCast h.symm` intertwines the recast-along-`h` right
action with the plain right action — pure `subst`/`rfl`, no route content. -/
theorem gaugeCast_op_smul_compat {x y : G} (h : x = y)
    (τ : (Γ.D x).carrier) (v : (Γ.D y).carrier) :
    (Γ.gaugeCast h.symm).toAlgEquiv
        (MulOpposite.op ((Γ.gaugeCast h).toAlgEquiv τ) • v)
      = MulOpposite.op τ • (Γ.gaugeCast h.symm).toAlgEquiv v := by
  subst h
  rfl

/-! ### `gbrColumnEquiv`: the aligned right dictionary -/

/-- **The aligned column identification `GBR ≅ FusionColumn (Γ.gaugeRouteR' a
b c)`** (§10 roadmap item 1, right side), under the sizes-equal hypothesis
`hsz` (see the section header): the native dictionary, followed by the
pointwise value cast `Γ.gaugeCast (add_assoc a b c).symm` (`D_{a+(b+c)} ≅
D_{(a+b)+c}`), then the size-cast reindex.  Port of
`ColumnDict2.brColumnEquiv`. -/
noncomputable def gbrColumnEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) :
    GBR Γ a b c ≃ₗ[K] FusionColumn (Γ.gaugeRouteR' a b c) :=
  (gbrNativeColumnEquiv K Γ a b c).trans
    ((LinearEquiv.piCongrRight
        (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
          (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv.toLinearEquiv)).trans
      (LinearEquiv.piCongrLeft' K
        (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
          (Γ.D (a + b + c)).carrier)
        (gaugeSizeCastEquiv K Γ a b c hsz)))

/-- **`gbrColumnEquiv`'s generator formula**: reindex `freeCollapse`'s value
along `gbrIndexEquiv`'s inverse, cast along `Γ.gaugeCast` (port of
`ColumnDict2.brColumnEquiv_apply`). -/
theorem gbrColumnEquiv_apply
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) (m : GBR Γ a b c)
    (x : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    gbrColumnEquiv K Γ a b c hsz m x
      = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
          (RelTensor.freeCollapse m
            ((gbrIndexEquiv K Γ a b c hsz).symm x).1
            ((gbrIndexEquiv K Γ a b c hsz).symm x).2) := by
  show (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
      (gbrNativeColumnEquiv K Γ a b c m
        ((gaugeSizeCastEquiv K Γ a b c hsz).symm x)) = _
  rw [gbrNativeColumnEquiv_apply,
    show (gbrIndexEquiv K Γ a b c hsz).symm x
        = (gbrNativeIndexEquiv K Γ a b c).symm
            ((gaugeSizeCastEquiv K Γ a b c hsz).symm x) from
      Equiv.symm_trans_apply _ _ x]

/-- **`gbrColumnEquiv` on generators**: the image of `GBR.mk u v` is the
explicit column `x ↦ gaugeCast ((u p • v) q)` for `(p, q)` the
`gbrIndexEquiv`-preimage of `x`. -/
theorem gbrColumnEquiv_mk
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
    (x : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    gbrColumnEquiv K Γ a b c hsz (GBR.mk Γ a b c u v) x
      = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
          ((u ((gbrIndexEquiv K Γ a b c hsz).symm x).1 • v)
            ((gbrIndexEquiv K Γ a b c hsz).symm x).2) := by
  rw [gbrColumnEquiv_apply,
    show RelTensor.freeCollapse (GBR.mk Γ a b c u v) = fun l => u l • v from
      RelTensor.freeCollapse_mk u v]

/-- **`gbrColumnEquiv` is right `D_{(a+b)+c}`-equivariant** (§10 roadmap
item 2, right side), against `GBR`'s RECAST right action
(`GaugeChi/RouteBimod.lean`) — the spelling that matches `FusionColumn
(Γ.gaugeRouteR' a b c)`'s own right action.  PLAIN: the native right
equivariance composes with the pointwise-cast compatibility
(`gaugeCast_op_smul_compat`) and the reindex compatibility
(`piCongrLeft'_smul`).  Port of `ColumnDict2.brColumnEquiv_rightEquiv`. -/
theorem gbrColumnEquiv_rightEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (τ : (Γ.D (a + b + c)).carrier) (m : GBR Γ a b c) :
    gbrColumnEquiv K Γ a b c hsz (MulOpposite.op τ • m)
      = MulOpposite.op τ • gbrColumnEquiv K Γ a b c hsz m := by
  rw [GBR.recast_op_smul_def]
  show (LinearEquiv.piCongrLeft' K
      (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
        (Γ.D (a + b + c)).carrier)
      (gaugeSizeCastEquiv K Γ a b c hsz))
      ((LinearEquiv.piCongrRight
          (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
            (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv.toLinearEquiv))
        (gbrNativeColumnEquiv K Γ a b c
          (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv τ) • m)))
    = MulOpposite.op τ • gbrColumnEquiv K Γ a b c hsz m
  rw [gbrNativeColumnEquiv_rightEquiv]
  rw [show (LinearEquiv.piCongrRight
        (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
          (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv.toLinearEquiv))
      (MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv τ) •
        gbrNativeColumnEquiv K Γ a b c m)
    = MulOpposite.op τ •
        (LinearEquiv.piCongrRight
          (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
            (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv.toLinearEquiv))
          (gbrNativeColumnEquiv K Γ a b c m) from by
    funext p
    exact gaugeCast_op_smul_compat K Γ (add_assoc a b c) τ
      (gbrNativeColumnEquiv K Γ a b c m p)]
  exact piCongrLeft'_smul K (gaugeSizeCastEquiv K Γ a b c hsz)
    (MulOpposite.op τ)
    ((LinearEquiv.piCongrRight
      (fun _ : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2 =>
        (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv.toLinearEquiv))
      (gbrNativeColumnEquiv K Γ a b c m))

/-! ### The grading correspondence, aligned right side -/

/-- **`gbrColumnEquiv` maps homogeneous elements onto the matching graded
layer, shift `0`** (§10 roadmap item 3, right side, forward direction):
derived ENTRYWISE from the native correspondence — the value cast preserves
coefficient degree (`Γ.gaugeCast_mem_grading`), and the size cast preserves
the column mask (`sumParity_gaugeSizeCastEquiv`) — no second generator
induction. -/
theorem gbrColumnEquiv_mem_grading
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {j : ZMod 2} {m : GBR Γ a b c} (hm : m ∈ GBR.grading Γ a b c j) :
    gbrColumnEquiv K Γ a b c hsz m
      ∈ FusionColumn.grading (Γ.gaugeRouteR' a b c) j := by
  intro y
  have hnat := gbrNativeColumnEquiv_mem_grading K Γ a b c hm
    ((gaugeSizeCastEquiv K Γ a b c hsz).symm y)
  have hval : gbrColumnEquiv K Γ a b c hsz m y
      = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
          (gbrNativeColumnEquiv K Γ a b c m
            ((gaugeSizeCastEquiv K Γ a b c hsz).symm y)) := rfl
  have hcast := sumParity_gaugeSizeCastEquiv K Γ a b c hsz
    ((gaugeSizeCastEquiv K Γ a b c hsz).symm y)
  rw [Equiv.apply_symm_apply] at hcast
  rw [hval, hcast]
  exact Γ.gaugeCast_mem_grading (add_assoc a b c).symm hnat

/-- The reverse direction of the aligned right grading correspondence. -/
theorem gbrColumnEquiv_symm_mem_grading
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {j : ZMod 2} {w : FusionColumn (Γ.gaugeRouteR' a b c)}
    (hw : w ∈ FusionColumn.grading (Γ.gaugeRouteR' a b c) j) :
    (gbrColumnEquiv K Γ a b c hsz).symm w ∈ GBR.grading Γ a b c j :=
  gradedLinearEquiv_symm_mem (GBR.grading Γ a b c)
    (FusionColumn.grading (Γ.gaugeRouteR' a b c))
    (gbrColumnEquiv K Γ a b c hsz)
    (fun hm => gbrColumnEquiv_mem_grading K Γ a b c hsz hm) hw

/-- **The aligned right grading correspondence, shift `0`, as an `iff`**
(§10 roadmap item 3, right side). -/
theorem gbrColumnEquiv_mem_grading_iff
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {j : ZMod 2} {m : GBR Γ a b c} :
    gbrColumnEquiv K Γ a b c hsz m
        ∈ FusionColumn.grading (Γ.gaugeRouteR' a b c) j
      ↔ m ∈ GBR.grading Γ a b c j := by
  constructor
  · intro h
    have h2 := gbrColumnEquiv_symm_mem_grading K Γ a b c hsz h
    rwa [LinearEquiv.symm_apply_apply] at h2
  · exact gbrColumnEquiv_mem_grading K Γ a b c hsz

end GaugeChi

end Superfusion
