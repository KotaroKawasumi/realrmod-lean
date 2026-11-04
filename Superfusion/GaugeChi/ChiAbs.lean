/-
Superfusion / GaugeChi / ChiAbs

Milestone M12-10 of the abstract `(p, χ)` arc: **`gChi`, THE ABSTRACT
`χ`** — the Γ-mirror of `Superfusion.Bimod.ChiAbs`: given `gTopRoute`'s and
`gBotRoute`'s triple-intertwiner data at a **common** landing degree `e`
(`htop`), and the Schur-type spanning hypothesis `gHspan` (`ChiTower.lean`,
already a *theorem*, not a hypothesis — no one-dimensionality assumption
anywhere in this arc), `gChi` is the *unique* scalar with `gTopRoute = gChi
• gBotRoute`.  This is THE abstract paper's χ (§4) for *every* division
fusion gauge, over any field with `2` invertible.

Also: **`gTopRoute` is bijective** for invertible triple data (the
Γ-mirror of `ChiAbs.lean`'s `topRoute_bijective`, symmetric to
`ChiTower.lean`'s `gBotRoute_bijective`), and its `≠ 0` corollary; and
**degree bookkeeping** — a nonzero quadruple intertwiner has a unique
degree (`gQuadInterSpace_deg_unique`), tying `gTopRoute`'s own naturally
-computed degree back to `gChi`'s ambient common degree `e`
(`gChi_deg_eq`).
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
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### `gTopRoute`, bijective for invertible `t`'s -/

/-- **`gTopRoute` is bijective**, given `t₁`, `t₂`, `t₃` invertible
(packaged as `LinearEquiv`s `φ₁`, `φ₂`, `φ₃` with the equivariance data
`GE1`, `GE2`, `GE3` themselves require) — the Γ-mirror of `ChiAbs.lean`'s
`topRoute_bijective`. -/
theorem gTopRoute_bijective
    (φ₁ : GBL Γ a b c ≃ₗ[K] GBR Γ a b c)
    (hφ₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      φ₁ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₁ m)
    (e₂ : ZMod 2) (φ₂ : GQ2rInner K Γ a b c d ≃ₗ[K] GQ3Inner K Γ a b c d)
    (hφ₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        φ₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • φ₂ n))
    (φ₃ : GBL Γ b c d ≃ₗ[K] GBR Γ b c d)
    (hφ₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      φ₃ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₃ m) :
    Function.Bijective
      (gTopRoute K Γ a b c d φ₁.toLinearMap hφ₁ e₂ φ₂.toLinearMap hφ₂ φ₃.toLinearMap hφ₃) := by
  unfold gTopRoute GE1 GE2 GE3
  simp only [LinearMap.coe_comp]
  exact (PentagonB.RelTensor.map_bijective_left K φ₃ hφ₃ |>.comp
      (gq3Assoc K Γ a b c d).symm.bijective).comp
    ((PentagonB.smap_bijective K (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
        φ₂ e₂ hφ₂ |>.comp (gq2Assoc K Γ a b c d).bijective).comp
      (PentagonB.RelTensor.map_bijective_left K φ₁ hφ₁))

/-- **`gTopRoute` is `≠ 0`** when bijective and `GQ1` is nontrivial. -/
theorem gTopRoute_ne_zero_of_bijective
    (t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (e₂ : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
    (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    [Nontrivial (GQ1 K Γ a b c d)]
    (hbij : Function.Bijective (gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃)) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0 :=
  linearMap_ne_zero_of_bijective K hbij

/-! ### Degree bookkeeping: a nonzero quadruple intertwiner has a unique
degree -/

/-- **A nonzero quadruple intertwiner has a unique degree.** -/
theorem gQuadInterSpace_deg_unique {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d} {e e' : ZMod 2}
    (hf : f ≠ 0) (he : f ∈ gQuadInterSpace K Γ a b c d e)
    (he' : f ∈ gQuadInterSpace K Γ a b c d e') : e = e' := by
  obtain ⟨hg, -, -, -, -, -⟩ := (mem_gQuadInterSpace_iff K Γ a b c d).mp he
  obtain ⟨hg', -, -, -, -, -⟩ := (mem_gQuadInterSpace_iff K Γ a b c d).mp he'
  exact PentagonB.homGrading_deg_eq_of_ne_zero K (GQ1.grading K Γ a b c d)
    (GQ4.grading K Γ a b c d) hf hg hg'

/-! ### `gChi`: THE ABSTRACT `χ`

Given `gTopRoute`'s and `gBotRoute`'s triple-intertwiner data (`t₁`–`t₅`
and their equivariance witnesses), a **common** landing degree `e` for
`gTopRoute` (`htop`), and the Schur-type spanning hypothesis `gHspan`
(`ChiTower.lean`, a THEOREM), `gChi` is the *unique* scalar with `gTopRoute
= gChi • gBotRoute` — this holds for **any** division fusion gauge `Γ`. -/

section GChi

variable (t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c)
variable (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
  t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
variable (e₂ : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
  y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
    t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
variable (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
variable (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
variable (e₄ : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
  x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
    t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
variable (e₅ : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
  z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
    t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
variable {e : ZMod 2}
variable (htop : gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ∈ gQuadInterSpace K Γ a b c d e)
variable (hspan : ∀ f ∈ gQuadInterSpace K Γ a b c d e,
  ∃ cc : K, f = cc • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)

/-- **`gChi`**: the unique scalar with `gTopRoute = gChi • gBotRoute`
(`hspan`'s witness at `gTopRoute`, which lies in `gQuadInterSpace K Γ a b c
d e` by `htop`) — THE abstract paper's `χ`, over any division fusion
gauge `Γ`. -/
noncomputable def gChi : K :=
  (hspan _ htop).choose

/-- **The defining equation.** -/
theorem gChi_spec :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      = gChi K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan
          • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ :=
  (hspan _ htop).choose_spec

/-- **Uniqueness**: any scalar relating the two routes agrees with
`gChi`, given `gBotRoute ≠ 0` (scalar cancellation in the `K`-vector space
`Hom(GQ1, GQ4)`). -/
theorem gChi_unique {cc : K}
    (hbot_ne : gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ≠ 0)
    (hc : gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      = cc • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅) :
    cc = gChi K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan := by
  have h := gChi_spec K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan
  have hz : (cc - gChi K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan)
      • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ = 0 := by
    rw [sub_smul, ← hc, ← h, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hbot_ne

/-- **Nonvanishing**: `gChi ≠ 0` when `gTopRoute ≠ 0`. -/
theorem gChi_ne_zero
    (htop_ne : gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0) :
    gChi K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan ≠ 0 := by
  intro hzero
  apply htop_ne
  rw [gChi_spec K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan,
    hzero, zero_smul]

include htop in
/-- **Degree bookkeeping**: `gTopRoute`'s own naturally-computed degree
(any independently-known membership `gTopRoute ∈ gQuadInterSpace K Γ a b c
d e₁'`, e.g. from `gTopRoute_mem`) coincides with `gChi`'s ambient common
degree `e`, when `gTopRoute ≠ 0` (`gQuadInterSpace_deg_unique`). -/
theorem gChi_deg_eq {e₁' : ZMod 2}
    (htop_ne : gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0)
    (htop' : gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ∈ gQuadInterSpace K Γ a b c d e₁') :
    e₁' = e :=
  gQuadInterSpace_deg_unique K Γ a b c d htop_ne htop' htop

end GChi

end GaugeChi

end Superfusion
