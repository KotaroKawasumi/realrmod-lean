/-
Superfusion / GaugeChi / ConnectorRescale

**The pentagon scalar of a connector family, and its coboundary law under
change of family** (`chi_change_connector` of the design memo).

`chiOfFamily C` is `gChi` at the data of a `ConnectorFamily C` — the
literal generalization of `gChiCanon`, which is `chiOfFamily` at the
canonical family (`chiOfFamily_canonical`).

The main theorem `chiOfFamily_rescale` states: if `C'.T = ρ • C.T`
pointwise (with `ρ = ConnectorFamily.ratio C C'` the unit-valued
3-cochain), then

  `chiOfFamily C' = chiOfFamily C · ρ(b,c,d) ρ(a,b+c,d) ρ(a,b,c)
                     · ρ(a+b,c,d)⁻¹ ρ(a,b,c+d)⁻¹`,

i.e. — in the `dm₃` convention of `Cochain/Basic.lean`
(`(δρ)(a,b,c,d) = ρ(b,c,d) ρ(ab,c,d)⁻¹ ρ(a,bc,d) ρ(a,b,cd)⁻¹ ρ(a,b,c)`) —

  **`chiOfFamily C' = chiOfFamily C · (δρ)(a,b,c,d)`**
  (`chiOfFamily_rescale_dm₃`).

ORIENTATION CONVENTION (derived, not assumed): the pentagon convention is
`gTopRoute = χ • gBotRoute` with top slots `(a,b,c), (a,b+c,d), (b,c,d)`
and bottom slots `(a+b,c,d), (a,b,c+d)`; scaling every connector by `ρ`
scales the top by the three `+`-slots of `dm₃ ρ` and the bottom by the two
`−`-slots, so the coboundary appears with NO inverse:
`χ' = χ · δρ` when `C' = ρ • C`.  Consequently, for the canonical family
against a certificate family `Ttab` with `gTCanon = ρ • Ttab`, one gets
`gChiCanon = chiOfFamily Ttab · δρ`.

The proof never opens `realGauge` or any concrete gauge: it uses only the
one-dimensionality of the intertwiner spaces (`gInterSpace_spanning`),
slot-linearity of the five pentagon edges (proved here from the closed
generator forms of `RelTensor.map` and `smap`), `gChi_unique`, and the
nonvanishing of the bottom route.
-/
import Superfusion.GaugeChi.ConnectorFamily
import Superfusion.Cochain.Basic

namespace Superfusion

namespace Bimod

/-! ### Slot-linearity of the two amplification constructors -/

section MapSmul

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {M' : Type*} [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']

/-- `RelTensor.map` is linear in its first (right-equivariant) argument. -/
theorem RelTensor.map_smul_left (k : K) (f : M →ₗ[K] M') (g : N →ₗ[K] N')
    (hf : ∀ (a : A) (m : M), f (MulOpposite.op a • m) = MulOpposite.op a • f m)
    (hf' : ∀ (a : A) (m : M),
      (k • f) (MulOpposite.op a • m) = MulOpposite.op a • (k • f) m)
    (hg : ∀ (a : A) (n : N), g (a • n) = a • g n) :
    RelTensor.map (k • f) g hf' hg = k • RelTensor.map f g hf hg := by
  refine RelTensor.hom_ext fun m n => ?_
  simp only [LinearMap.smul_apply, RelTensor.map_mk, map_smul]

end MapSmul

section SMapSmul

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']
variable [GradedRightSMul 𝒜 ℳ]

/-- `smap` is linear in its amplified argument. -/
theorem smap_smul (k : K) (g : N →ₗ[K] N') (e : ZMod 2)
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    (hg' : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      (k • g) (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • (k • g) n)) :
    smap 𝒜 ℳ (k • g) e hg' = k • smap 𝒜 ℳ g e hg := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [smap_mk, LinearMap.smul_apply, smap_mk, smapBilin_apply, smapBilin_apply,
    LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K,
    map_smul, map_smul, smul_sub, smul_smul, smul_smul, mul_comm k]

end SMapSmul

end Bimod

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### Slot-linearity of the five pentagon edges -/

theorem GE1_smul (k : K) (t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (ht₁' : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      (k • t₁) (MulOpposite.op τ • m) = MulOpposite.op τ • (k • t₁) m) :
    GE1 K Γ a b c d (k • t₁) ht₁' = k • GE1 K Γ a b c d t₁ ht₁ :=
  RelTensor.map_smul_left k t₁ LinearMap.id ht₁ ht₁' (fun _ _ => rfl)

theorem GE2_smul (k : K) (e : ZMod 2)
    (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))
    (ht₂' : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        (k • t₂) (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • (k • t₂) n)) :
    GE2 K Γ a b c d e (k • t₂) ht₂' = k • GE2 K Γ a b c d e t₂ ht₂ := by
  unfold GE2
  rw [smap_smul (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) k t₂ e ht₂ ht₂',
    LinearMap.smul_comp]
  rfl

theorem GE3_smul (k : K) (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    (ht₃' : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      (k • t₃) (MulOpposite.op τ • m) = MulOpposite.op τ • (k • t₃) m) :
    GE3 K Γ a b c d (k • t₃) ht₃' = k • GE3 K Γ a b c d t₃ ht₃ := by
  unfold GE3
  rw [RelTensor.map_smul_left k t₃ LinearMap.id ht₃ ht₃' (fun _ _ => rfl),
    LinearMap.smul_comp]
  rfl

theorem GE4_smul (k : K) (e : ZMod 2)
    (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (ht₄' : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        (k • t₄) (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • (k • t₄) n)) :
    GE4 K Γ a b c d e (k • t₄) ht₄' = k • GE4 K Γ a b c d e t₄ ht₄ := by
  unfold GE4
  rw [smap_smul (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) k t₄ e ht₄ ht₄',
    LinearMap.smul_comp]
  rfl

theorem GE5_smul (k : K) (e : ZMod 2)
    (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))
    (ht₅' : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        (k • t₅) (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • (k • t₅) n)) :
    GE5 K Γ a b c d e (k • t₅) ht₅' = k • GE5 K Γ a b c d e t₅ ht₅ := by
  unfold GE5
  rw [smap_smul (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) k t₅ e ht₅ ht₅',
    LinearMap.smul_comp]
  rfl

/-! ### Route rescaling -/

/-- The top route rescales by the product of its three slot scalars. -/
theorem gTopRoute_eq_smul (k₁ k₂ k₃ : K)
    {t₁' t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c} (h₁ : t₁' = k₁ • t₁)
    (ht₁' : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t₁' (MulOpposite.op τ • m) = MulOpposite.op τ • t₁' m)
    (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (e₂ : ZMod 2)
    {t₂' t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d} (h₂ : t₂' = k₂ • t₂)
    (ht₂' : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        t₂' (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂' n))
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i → ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
    {t₃' t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d} (h₃ : t₃' = k₃ • t₃)
    (ht₃' : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃' (MulOpposite.op τ • m) = MulOpposite.op τ • t₃' m)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m) :
    gTopRoute K Γ a b c d t₁' ht₁' e₂ t₂' ht₂' t₃' ht₃'
      = (k₁ * k₂ * k₃) • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ := by
  subst h₁; subst h₂; subst h₃
  unfold gTopRoute
  rw [GE1_smul K Γ a b c d k₁ t₁ ht₁ ht₁', GE2_smul K Γ a b c d k₂ e₂ t₂ ht₂ ht₂',
    GE3_smul K Γ a b c d k₃ t₃ ht₃ ht₃']
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]

/-- The bottom route rescales by the product of its two slot scalars. -/
theorem gBotRoute_eq_smul (k₄ k₅ : K)
    (e₄ : ZMod 2)
    {t₄' t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d} (h₄ : t₄' = k₄ • t₄)
    (ht₄' : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄' (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄' n))
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i → ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (e₅ : ZMod 2)
    {t₅' t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d)} (h₅ : t₅' = k₅ • t₅)
    (ht₅' : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅' (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅' n))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i → ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n)) :
    gBotRoute K Γ a b c d e₄ t₄' ht₄' e₅ t₅' ht₅'
      = (k₄ * k₅) • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ := by
  subst h₄; subst h₅
  unfold gBotRoute
  rw [GE4_smul K Γ a b c d k₄ e₄ t₄ ht₄ ht₄', GE5_smul K Γ a b c d k₅ e₅ t₅ ht₅ ht₅']
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]

/-! ### The pentagon scalar of a connector family -/

open ConnectorFamily

variable {a b c d}

/-- The top-route membership at the data of a family, at the common
degree of its bottom route (`gParity_cocycle`). -/
theorem chiOfFamily_htop (C : ConnectorFamily K Γ) :
    gTopRoute K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
        (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
          (C.mem_gParity a (b + c) d))
        (C.T b c d) (C.right_equivariance b c d)
      ∈ gQuadInterSpace K Γ a b c d
          (gParity K Γ (a + b) c d + gParity K Γ a b (c + d)) :=
  gParity_cocycle K Γ a b c d ▸
    gTopRoute_mem K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
      (gParity K Γ a (b + c) d)
      (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
      (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
        (C.mem_gParity a (b + c) d))
      (C.T b c d) (C.right_equivariance b c d)
      (C.mem_gParity a b c)
      (gt2Canon_aSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
        (C.mem_gParity a (b + c) d))
      (gt2Canon_dSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
        (C.mem_gParity a (b + c) d))
      (gt2Canon_rightSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
        (C.mem_gParity a (b + c) d))
      (gt2Canon_mem_grading K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
        (C.mem_gParity a (b + c) d))
      (C.mem_gParity b c d)

/-- The spanning hypothesis at the bottom-route data of a family
(`gHspan`). -/
theorem chiOfFamily_hspan (C : ConnectorFamily K Γ) :
    ∀ f ∈ gQuadInterSpace K Γ a b c d
        (gParity K Γ (a + b) c d + gParity K Γ a b (c + d)),
      ∃ cc : K, f = cc • gBotRoute K Γ a b c d
        (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
        (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d) :=
  gHspan K Γ a b c d (C.equiv (a + b) c d) (C.mem_gParity (a + b) c d)
    (C.equiv a b (c + d)) (C.mem_gParity a b (c + d))

/-- **The pentagon scalar of a connector family**: `gChi` at the family's
data — the literal generalization of `gChiCanon` to an arbitrary
family. -/
noncomputable def chiOfFamily (C : ConnectorFamily K Γ) (a b c d : G) : K :=
  gChi K Γ a b c d
    (C.T a b c) (C.right_equivariance a b c)
    (gParity K Γ a (b + c) d)
    (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
    (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
      (C.mem_gParity a (b + c) d))
    (C.T b c d) (C.right_equivariance b c d)
    (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
    (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d)
    (chiOfFamily_htop K Γ C) (chiOfFamily_hspan K Γ C)

/-- The defining pentagon equation of `chiOfFamily`. -/
theorem chiOfFamily_spec (C : ConnectorFamily K Γ) :
    gTopRoute K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
        (gParity K Γ a (b + c) d)
        (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
        (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
          (C.mem_gParity a (b + c) d))
        (C.T b c d) (C.right_equivariance b c d)
      = chiOfFamily K Γ C a b c d
          • gBotRoute K Γ a b c d
              (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
              (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d) :=
  gChi_spec K Γ a b c d _ _ _ _ _ _ _ _ _ _ _ _ _
    (chiOfFamily_htop K Γ C) (chiOfFamily_hspan K Γ C)

/-- **`gChiCanon` is `chiOfFamily` at the canonical family** — the two
assemblies are definitionally identical (proof irrelevance in the
hypothesis slots). -/
theorem chiOfFamily_canonical :
    chiOfFamily K Γ (canonical K Γ) a b c d = gChiCanon K Γ a b c d := rfl

/-! ### The coboundary law -/

/-- The bottom route at a family's data is nonzero. -/
theorem gBotRoute_family_ne_zero (C : ConnectorFamily K Γ) :
    gBotRoute K Γ a b c d
        (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
        (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d) ≠ 0 := by
  haveI := gq1_finite K Γ a b c d
  haveI := gq1_nontrivial K Γ a b c d
  exact gBotRoute_ne_zero_of_bijective K Γ a b c d
    (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
    (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d)
    (gBotRoute_bijective K Γ a b c d
      (gParity K Γ (a + b) c d) (C.equiv (a + b) c d) (C.slotFour a b c d)
      (gParity K Γ a b (c + d)) (C.equiv a b (c + d)) (C.slotFive a b c d))

/-- **The coboundary law of the pentagon scalar** (`chi_change_connector`):
if `C'.T = ρ • C.T` pointwise with `ρ = ratio C C'`, then

`chiOfFamily C' = chiOfFamily C · ρ(a,b,c) ρ(a,b+c,d) ρ(b,c,d) ·
  ρ(a+b,c,d)⁻¹ ρ(a,b,c+d)⁻¹`.

The five factors are exactly the five slots of `dm₃ ρ` (with matching
signs); see `chiOfFamily_rescale_dm₃`. -/
theorem chiOfFamily_rescale (C C' : ConnectorFamily K Γ) :
    chiOfFamily K Γ C' a b c d
      = chiOfFamily K Γ C a b c d
        * (((ratio C C' a b c : Kˣ) : K)
            * ((ratio C C' a (b + c) d : Kˣ) : K)
            * ((ratio C C' b c d : Kˣ) : K))
        * ((((ratio C C' (a + b) c d)⁻¹ : Kˣ) : K)
            * (((ratio C C' a b (c + d))⁻¹ : Kˣ) : K)) := by
  set ρ₁ : Kˣ := ratio C C' a b c with hρ₁
  set ρ₂ : Kˣ := ratio C C' a (b + c) d with hρ₂
  set ρ₃ : Kˣ := ratio C C' b c d with hρ₃
  set ρ₄ : Kˣ := ratio C C' (a + b) c d with hρ₄
  set ρ₅ : Kˣ := ratio C C' a b (c + d) with hρ₅
  -- the second-edge connector rescales by ρ₂
  have h₂ : (gt2Canon K Γ a b c d (C'.equiv a (b + c) d)).toLinearMap
      = ((ρ₂ : Kˣ) : K) • (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap := by
    show (C'.equiv a (b + c) d).toLinearMap ∘ₗ (gq2rCast K Γ a b c d).toLinearMap
      = ((ρ₂ : Kˣ) : K) •
          ((C.equiv a (b + c) d).toLinearMap ∘ₗ (gq2rCast K Γ a b c d).toLinearMap)
    rw [C.equiv_toLinearMap, C'.equiv_toLinearMap, ratio_spec C C' a (b + c) d,
      LinearMap.smul_comp, hρ₂]
  -- top and bottom routes rescale
  have htopEq :
      gTopRoute K Γ a b c d (C'.T a b c) (C'.right_equivariance a b c)
          (gParity K Γ a (b + c) d)
          (gt2Canon K Γ a b c d (C'.equiv a (b + c) d)).toLinearMap
          (gt2Canon_bcSlot K Γ (C'.equiv a (b + c) d) (gParity K Γ a (b + c) d)
            (C'.mem_gParity a (b + c) d))
          (C'.T b c d) (C'.right_equivariance b c d)
        = (((ρ₁ : Kˣ) : K) * ((ρ₂ : Kˣ) : K) * ((ρ₃ : Kˣ) : K)) •
            gTopRoute K Γ a b c d (C.T a b c) (C.right_equivariance a b c)
              (gParity K Γ a (b + c) d)
              (gt2Canon K Γ a b c d (C.equiv a (b + c) d)).toLinearMap
              (gt2Canon_bcSlot K Γ (C.equiv a (b + c) d) (gParity K Γ a (b + c) d)
                (C.mem_gParity a (b + c) d))
              (C.T b c d) (C.right_equivariance b c d) :=
    gTopRoute_eq_smul K Γ a b c d _ _ _ (by rw [ratio_spec C C' a b c, hρ₁]) _ _
      (gParity K Γ a (b + c) d) h₂ _ _ (by rw [ratio_spec C C' b c d, hρ₃]) _ _
  have hbotEq :
      gBotRoute K Γ a b c d
          (gParity K Γ (a + b) c d) (C'.T (a + b) c d) (C'.slotFour a b c d)
          (gParity K Γ a b (c + d)) (C'.T a b (c + d)) (C'.slotFive a b c d)
        = (((ρ₄ : Kˣ) : K) * ((ρ₅ : Kˣ) : K)) •
            gBotRoute K Γ a b c d
              (gParity K Γ (a + b) c d) (C.T (a + b) c d) (C.slotFour a b c d)
              (gParity K Γ a b (c + d)) (C.T a b (c + d)) (C.slotFive a b c d) :=
    gBotRoute_eq_smul K Γ a b c d _ _ (gParity K Γ (a + b) c d)
      (by rw [ratio_spec C C' (a + b) c d, hρ₄]) _ _
      (gParity K Γ a b (c + d)) (by rw [ratio_spec C C' a b (c + d), hρ₅]) _ _
  -- assemble: TOP' = (χ_C ρ₁ρ₂ρ₃ (ρ₄ρ₅)⁻¹) • BOT'
  have hchain :
      gTopRoute K Γ a b c d (C'.T a b c) (C'.right_equivariance a b c)
          (gParity K Γ a (b + c) d)
          (gt2Canon K Γ a b c d (C'.equiv a (b + c) d)).toLinearMap
          (gt2Canon_bcSlot K Γ (C'.equiv a (b + c) d) (gParity K Γ a (b + c) d)
            (C'.mem_gParity a (b + c) d))
          (C'.T b c d) (C'.right_equivariance b c d)
        = (chiOfFamily K Γ C a b c d
            * (((ρ₁ : Kˣ) : K) * ((ρ₂ : Kˣ) : K) * ((ρ₃ : Kˣ) : K))
            * ((((ρ₄⁻¹ : Kˣ) : K)) * (((ρ₅⁻¹ : Kˣ) : K)))) •
            gBotRoute K Γ a b c d
              (gParity K Γ (a + b) c d) (C'.T (a + b) c d) (C'.slotFour a b c d)
              (gParity K Γ a b (c + d)) (C'.T a b (c + d)) (C'.slotFive a b c d) := by
    rw [htopEq, chiOfFamily_spec K Γ C, hbotEq, smul_smul, smul_smul]
    congr 1
    have h₄ : ((ρ₄ : Kˣ) : K) * ((ρ₄⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ρ₄
    have h₅ : ((ρ₅ : Kˣ) : K) * ((ρ₅⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ρ₅
    calc ((ρ₁ : Kˣ) : K) * ((ρ₂ : Kˣ) : K) * ((ρ₃ : Kˣ) : K) * chiOfFamily K Γ C a b c d
        = chiOfFamily K Γ C a b c d
            * (((ρ₁ : Kˣ) : K) * ((ρ₂ : Kˣ) : K) * ((ρ₃ : Kˣ) : K)) * (1 * 1) := by ring
      _ = chiOfFamily K Γ C a b c d
            * (((ρ₁ : Kˣ) : K) * ((ρ₂ : Kˣ) : K) * ((ρ₃ : Kˣ) : K))
            * ((((ρ₄ : Kˣ) : K) * ((ρ₄⁻¹ : Kˣ) : K))
                * (((ρ₅ : Kˣ) : K) * ((ρ₅⁻¹ : Kˣ) : K))) := by rw [h₄, h₅]
      _ = _ := by ring
  -- conclude by uniqueness at the C'-data
  exact (gChi_unique K Γ a b c d _ _ _ _ _ _ _ _ _ _ _ _ _
    (chiOfFamily_htop K Γ C') (chiOfFamily_hspan K Γ C')
    (gBotRoute_family_ne_zero K Γ C') hchain).symm

/-- **The coboundary law in `dm₃` form**: with `ρ = ratio C C'` read as a
`Kˣ`-valued 3-cochain on `Multiplicative G`,

`chiOfFamily C' (a,b,c,d) = chiOfFamily C (a,b,c,d) · (δρ)(a,b,c,d)`.

Orientation: NO inverse on the coboundary — `C' = ρ • C` produces
`χ' = χ · δρ` in the convention of `Cochain/Basic.lean`. -/
theorem chiOfFamily_rescale_dm₃ (C C' : ConnectorFamily K Γ)
    (x y z w : Multiplicative G) :
    chiOfFamily K Γ C' x.toAdd y.toAdd z.toAdd w.toAdd
      = chiOfFamily K Γ C x.toAdd y.toAdd z.toAdd w.toAdd
        * ((dm₃ (fun u v t : Multiplicative G =>
              ratio C C' u.toAdd v.toAdd t.toAdd) x y z w : Kˣ) : K) := by
  rw [chiOfFamily_rescale K Γ C C']
  simp only [dm₃, toAdd_mul, Units.val_mul]
  ring

end GaugeChi

end Superfusion
