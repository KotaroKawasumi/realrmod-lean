/-
Superfusion / GaugeChi / ChiTower

Milestone M12-9 of the abstract `(p, χ)` arc: **the dimension arithmetic
and the discharge** — the Γ-mirror of `Superfusion.Bimod.ChiTower`, one
gtensor level up from `GaugeChi.InterSpace`'s triple-level dimension count.

1. **`finrank K GQ1 = gQuadEnvSize K Γ a b c d`.**  `GBL Γ a b c`'s own
   collapse (`gblFirstCollapse`, `InterSpace.lean`, already curried to a
   product-indexed column over `D_{a+b+c}`) transports into `GQ1 = GBL ⊗
   [D_{a+b+c}] FusionColumn (fuse (a+b+c) d)` via `RelTensor.mapEquivLeft`
   (`Bimod.PentagonB`, general), landing at a `RelTensor` that is again
   literally column-shaped, so one further `RelTensor.freeCollapse` plus a
   currying collapses it to `(idx(a,b) × idx(a+b,c) × idx(a+b+c,d)) →
   D_{a+b+c+d}` — mirroring `ChiTower.lean`'s `q1Collapse` exactly, one
   level up.  Both collapses respect the outer right `D_{a+b+c}`-action
   (`RelTensor.freeCollapse_rightActionEnd`, `Bimod.ChiTower`, general),
   so the composite is a genuine `LinearEquiv`.

2. **`finrank K GQ4 = finrank K GQ1`, the shortcut.**  `gBotRoute`'s
   bijectivity (`gBotRoute_bijective`, the Γ-mirror of `ChiAbs.lean`'s
   `botRoute_bijective`, assembled from `gq1Assoc`/`gq5Swap`/`gq4Close`'s
   own bijectivity plus `Bimod.PentagonB.smap_bijective`, for invertible
   `t₄`, `t₅`) supplies a `LinearEquiv GQ1 ≃ₗ[K] GQ4` directly — no
   separate collapse of `GQ4`'s own (differently-associated) presentation
   is needed.

3. **The discharge**: `gHspan` — assembling `mem_gQuadInterSpace_iff_gradedHomF`
   (both uses), `SplitIsotypy.gradedHomF_finrank_sum_le_one` (via
   `gQuadEnvSplit`/`gQuadEnvSize` and deliverables 1–2), and `gBotRoute_mem`
   + `gBotRoute_ne_zero_of_bijective` (`Nontrivial GQ1` from `finrank K GQ1
   = gQuadEnvSize ≠ 0`).
-/
import Superfusion.GaugeChi.QuadInterface2
import Superfusion.GaugeChi.PentagonRouteMembership
import Superfusion.Bimod.ChiTower

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

/-! ### `finrank K GQ1 = gQuadEnvSize K Γ a b c d`: the `freeCollapse`
iteration -/

/-- **`gblFirstCollapse`'s generator formula**: it computes `freeCollapse`
followed by the literal `Prod.fst`/`Prod.snd` uncurrying — `rfl`. -/
theorem gblFirstCollapse_apply (m : GBL Γ a b c)
    (p : (Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
      (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) :
    gblFirstCollapse K Γ a b c m p = RelTensor.freeCollapse m p.1 p.2 := rfl

/-- **`GBL`'s own bare `freeCollapse`, transported along the outer right
`D_{a+b+c}`-action**: the general `RelTensor.freeCollapse_rightActionEnd`
instantiated at `GBL`'s construction (`GBL.right_smul_apply` bridges the
registered right action to the generic `rightActionEnd` spelling). -/
theorem freeCollapse_GBL_rightEquiv (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c) :
    RelTensor.freeCollapse (MulOpposite.op τ • m)
      = MulOpposite.op τ • RelTensor.freeCollapse m := by
  have h := RelTensor.freeCollapse_rightActionEnd (K := K)
    (A := (Γ.D (a + b)).carrier) (n := Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2)
    (N := FusionColumn (Γ.fuse (a + b) c)) (C := (Γ.D (a + b + c)).carrier)
    (MulOpposite.op τ) m
  rw [GBL.right_smul_apply]
  exact h

/-- **`gblFirstCollapse` intertwines the outer right `D_{a+b+c}`-action**
(the pointwise action on the product-indexed column). -/
theorem gblFirstCollapse_rightEquiv (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c) :
    gblFirstCollapse K Γ a b c (MulOpposite.op τ • m)
      = MulOpposite.op τ • gblFirstCollapse K Γ a b c m := by
  funext p
  show RelTensor.freeCollapse (MulOpposite.op τ • m) p.1 p.2
    = MulOpposite.op τ • RelTensor.freeCollapse m p.1 p.2
  exact congrFun (congrFun (freeCollapse_GBL_rightEquiv K Γ a b c τ m) p.1) p.2

/-- **`GQ1` collapses to a column over the product index**: `GQ1 = GBL ⊗
[D_{a+b+c}] FusionColumn (fuse (a+b+c) d) ≅ (idx(a,b) × idx(a+b,c)) →
FusionColumn (fuse (a+b+c) d)` — transport `GBL`'s own collapse along the
outer `RelTensor` (`RelTensor.mapEquivLeft`), then collapse the (now
literally column-shaped) result with `freeCollapse` again, then curry once
more (`piProdCollapse`, general). -/
noncomputable def gq1Collapse :
    GQ1 K Γ a b c d ≃ₗ[K]
      (((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
          (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) ×
        (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
        → (Γ.D (a + b + c + d)).carrier) :=
  ((PentagonB.RelTensor.mapEquivLeft K (gblFirstCollapse K Γ a b c)
      (gblFirstCollapse_rightEquiv K Γ a b c)).trans RelTensor.freeCollapse).trans
    (piProdCollapse K ((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
        (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2))
      (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
      (Γ.D (a + b + c + d)).carrier)

omit [Invertible (2 : K)] in
/-- **`finrank K (n → M) = Fintype.card n * finrank K M`** for a
`Fintype n` and finite-dimensional `M`. -/
private theorem finrank_pi_const {M : Type*} [AddCommGroup M] [Module K M]
    [Module.Finite K M] (n : Type*) [Fintype n] :
    Module.finrank K (n → M) = Fintype.card n * Module.finrank K M := by
  rw [Module.finrank_pi_fintype K, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The composite left-route size is the product of the two factor sizes'
totals (a local copy of `InterSpace.lean`'s private `gaugeSizeL_total`). -/
private theorem gaugeSizeL_total' :
    (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2) := by
  show (Γ.size a b).1 * (Γ.size (a + b) c).1 + (Γ.size a b).2 * (Γ.size (a + b) c).2
      + ((Γ.size a b).1 * (Γ.size (a + b) c).2 + (Γ.size a b).2 * (Γ.size (a + b) c).1)
    = _
  ring

/-- The composite quadruple-route size is the product of the two factor
sizes' totals (a local copy of `QuadEnvelope.lean`'s private
`gQuadSizeL_total`). -/
private theorem gQuadSizeL_total' :
    (gQuadSizeL K Γ a b c d).1 + (gQuadSizeL K Γ a b c d).2
      = ((Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2)
          * ((Γ.size (a + b + c) d).1 + (Γ.size (a + b + c) d).2) := by
  show (Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).1
      + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).2
      + ((Γ.gaugeSizeL a b c).1 * (Γ.size (a + b + c) d).2
        + (Γ.gaugeSizeL a b c).2 * (Γ.size (a + b + c) d).1)
    = _
  ring

/-- **`gQuadEnvSize`'s value, unfolded** to the `idx`/rank product. -/
theorem gQuadEnvSize_eq :
    gQuadEnvSize K Γ a b c d
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size (a + b) c).1 + (Γ.size (a + b) c).2)
          * ((Γ.size (a + b + c) d).1 + (Γ.size (a + b + c) d).2)
          * Module.finrank K (Γ.D (a + b + c + d)).carrier := by
  show Fintype.card
      ((Fin (gQuadSizeL K Γ a b c d).1 ⊕ Fin (gQuadSizeL K Γ a b c d).2) ×
        Fin (Module.finrank K (Γ.D (a + b + c + d)).carrier)) = _
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, gQuadSizeL_total', gaugeSizeL_total']

/-- **`finrank K GQ1 = gQuadEnvSize K Γ a b c d`** (deliverable 2, `GQ1`). -/
theorem finrank_GQ1_eq_gQuadEnvSize :
    Module.finrank K (GQ1 K Γ a b c d) = gQuadEnvSize K Γ a b c d := by
  rw [(gq1Collapse K Γ a b c d).finrank_eq, gQuadEnvSize_eq,
    finrank_pi_const K (((Fin (Γ.size a b).1 ⊕ Fin (Γ.size a b).2) ×
        (Fin (Γ.size (a + b) c).1 ⊕ Fin (Γ.size (a + b) c).2)) ×
      (Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2))]
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]

/-- **`GQ1` is finite-dimensional** (transported off the collapse chain,
`gq1Collapse`). -/
theorem gq1_finite : Module.Finite K (GQ1 K Γ a b c d) := by
  haveI : Module.Finite K (FusionColumn (Γ.fuse (a + b + c) d)) :=
    inferInstanceAs (Module.Finite K
      ((Fin (Γ.size (a + b + c) d).1 ⊕ Fin (Γ.size (a + b + c) d).2)
        → (Γ.D (a + b + c + d)).carrier))
  exact Module.Finite.equiv (gq1Collapse K Γ a b c d).symm

/-- **`GQ1` is nontrivial**: `finrank K GQ1 = gQuadEnvSize K Γ a b c d ≠
0`. -/
theorem gq1_nontrivial : Nontrivial (GQ1 K Γ a b c d) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [finrank_GQ1_eq_gQuadEnvSize]
  exact Nat.pos_of_ne_zero (gQuadEnvSize_ne_zero K Γ a b c d)

/-! ### `gBotRoute`, bijective for invertible `t`'s -/

/-- **`gBotRoute` is bijective**, given `t₄`, `t₅` invertible (packaged as
`LinearEquiv`s `φ₄`, `φ₅` with the equivariance data `GE4`/`GE5`
themselves require) — the Γ-mirror of `ChiAbs.lean`'s `botRoute_bijective`. -/
theorem gBotRoute_bijective
    (e₄ : ZMod 2) (φ₄ : GBL Γ (a + b) c d ≃ₗ[K] GBR Γ (a + b) c d)
    (hφ₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        φ₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • φ₄ n))
    (e₅ : ZMod 2) (φ₅ : GBL Γ a b (c + d) ≃ₗ[K] GBR Γ a b (c + d))
    (hφ₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        φ₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • φ₅ n)) :
    Function.Bijective
      (gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) := by
  unfold gBotRoute GE4 GE5
  simp only [LinearMap.coe_comp]
  refine (gq4Close K Γ a b c d).bijective.comp ?_
  exact (PentagonB.smap_bijective K (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d))
      φ₅ e₅ hφ₅ |>.comp (gq5Swap K Γ a b c d).bijective).comp
    (PentagonB.smap_bijective K (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
      φ₄ e₄ hφ₄ |>.comp (gq1Assoc K Γ a b c d).bijective)

/-- **`finrank K GQ4 = gQuadEnvSize K Γ a b c d`** (deliverable 2, `GQ4`'s
shortcut: `gBotRoute`'s own bijectivity, for invertible `t₄`, `t₅`, already
supplies a `LinearEquiv GQ1 ≃ₗ[K] GQ4` — no separate collapse of `GQ4`'s
own presentation is needed). -/
theorem finrank_GQ4_eq_gQuadEnvSize
    {e₄ : ZMod 2} (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    {e₅ : ZMod 2} (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
    (hbij : Function.Bijective (gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)) :
    Module.finrank K (GQ4 K Γ a b c d) = gQuadEnvSize K Γ a b c d := by
  haveI := gq1_finite K Γ a b c d
  rw [← finrank_GQ1_eq_gQuadEnvSize,
    (LinearEquiv.ofBijective (gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅) hbij).finrank_eq]

/-! ### Nonzeroness from bijectivity -/

omit [Invertible (2 : K)] in
/-- **A bijective (in particular injective) linear map out of a nontrivial
source is `≠ 0`.** -/
theorem linearMap_ne_zero_of_bijective {P Q : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [Nontrivial P] {f : P →ₗ[K] Q}
    (hf : Function.Bijective f) : f ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  exact hx (hf.1 (by simp [hzero]))

/-- **`gBotRoute` is `≠ 0`** when bijective and `GQ1` is nontrivial. -/
theorem gBotRoute_ne_zero_of_bijective
    (e₄ : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (e₅ : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
    [Nontrivial (GQ1 K Γ a b c d)]
    (hbij : Function.Bijective (gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ≠ 0 :=
  linearMap_ne_zero_of_bijective K hbij

/-! ### The discharge -/

/-- **The discharge**: for invertible `t₄`, `t₅` (with their full
`gInterSpace` membership, at declared degrees `e₄`, `e₅`), every element of
`gQuadInterSpace K Γ a b c d (e₄ + e₅)` is a scalar multiple of
`gBotRoute` — the Γ-mirror of `ChiTower.lean`'s `hspanTower`. -/
theorem gHspan
    {e₄ : ZMod 2} (φ₄ : GBL Γ (a + b) c d ≃ₗ[K] GBR Γ (a + b) c d)
    (ht4 : φ₄.toLinearMap ∈ gInterSpace K Γ (a + b) c d e₄)
    {e₅ : ZMod 2} (φ₅ : GBL Γ a b (c + d) ≃ₗ[K] GBR Γ a b (c + d))
    (ht5 : φ₅.toLinearMap ∈ gInterSpace K Γ a b (c + d) e₅) :
    ∀ f ∈ gQuadInterSpace K Γ a b c d (e₄ + e₅),
      ∃ cc : K, f = cc • gBotRoute K Γ a b c d e₄ φ₄.toLinearMap
        ((mem_superEquivariant (Γ.D (a + b)).grading).mp
          ((mem_gInterSpace_iff K Γ (a + b) c d).mp ht4).2.1)
        e₅ φ₅.toLinearMap
        ((mem_superEquivariant (Γ.D (c + d)).grading).mp
          ((mem_gInterSpace_iff K Γ a b (c + d)).mp ht5).2.2.2.1) := by
  have hφ₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        φ₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • φ₄ n) :=
    (mem_superEquivariant (Γ.D (a + b)).grading).mp
      ((mem_gInterSpace_iff K Γ (a + b) c d).mp ht4).2.1
  have hφ₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        φ₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • φ₅ n) :=
    (mem_superEquivariant (Γ.D (c + d)).grading).mp
      ((mem_gInterSpace_iff K Γ a b (c + d)).mp ht5).2.2.2.1
  haveI := gq1_finite K Γ a b c d
  haveI := gq1_nontrivial K Γ a b c d
  have hbij : Function.Bijective
      (gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) :=
    gBotRoute_bijective K Γ a b c d e₄ φ₄ hφ₄ e₅ φ₅ hφ₅
  haveI : Module.Finite K (GQ4 K Γ a b c d) :=
    Module.Finite.equiv (LinearEquiv.ofBijective
      (gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) hbij)
  have hbotMem : gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅
      ∈ gQuadInterSpace K Γ a b c d (e₄ + e₅) :=
    gBotRoute_mem K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ ht4 ht5
  have hbotNe : gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ ≠ 0 :=
    gBotRoute_ne_zero_of_bijective K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ hbij
  have hbotMemG :
      gBotRoute K Γ a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅
        ∈ gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
            (GQ4.grading K Γ a b c d) (e₄ + e₅) :=
    (mem_gQuadInterSpace_iff_gradedHomF K Γ a b c d).mp hbotMem
  have hle := gradedHomF_finrank_sum_le_one
    (ℳ := GQ1.grading K Γ a b c d) (𝒯 := gQuadEnvGrading K Γ a b c d)
    (𝒩 := GQ4.grading K Γ a b c d)
    (gQuadEnvSplit K Γ a b c d) (gQuadEnvSize_ne_zero K Γ a b c d)
    (finrank_GQ1_eq_gQuadEnvSize K Γ a b c d)
    (finrank_GQ4_eq_gQuadEnvSize K Γ a b c d φ₄.toLinearMap hφ₄ φ₅.toLinearMap hφ₅ hbij)
  have hd :
      gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
          (GQ4.grading K Γ a b c d) (e₄ + e₅) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨_, hbotMemG, hbotNe⟩
  obtain ⟨-, -, hspan⟩ := parityConcentration
    (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d) (𝒩 := GQ4.grading K Γ a b c d) hle hd
  intro f hf
  have hfmemG : f ∈ gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
      (GQ4.grading K Γ a b c d) (e₄ + e₅) := (mem_gQuadInterSpace_iff_gradedHomF K Γ a b c d).mp hf
  exact hspan f hfmemG _ hbotMemG hbotNe

end GaugeChi

end Superfusion
