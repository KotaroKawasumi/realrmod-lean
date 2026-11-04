/-
Superfusion / Bimod / ChiAbs

Milestone M8a-8c′-3 (roadmap v3): **the definition of `χ_abs`** — the
paper's `χ` (§4, the pentagon scalar), in `End`-shaped form: the
*unique* scalar relating the two pentagon routes,

  `topRoute t₁ t₂ t₃ = χ_abs · botRoute t₄ t₅`,

for any fusion data at a **common** landing degree `e`, given a
Schur-type spanning hypothesis for `quadInterSpace K a b c d e` over
`botRoute` (its one-dimensionality) and `botRoute ≠ 0` (its
nonvanishing) as *hypotheses*.  Discharging these two hypotheses at
the towers (the correspondence-theorem "1-dimensional, concentrated in
one parity" argument) is the next milestone (8d′); the eventual
identification of `χ_abs` with the concrete `pentagonChi` of
`Superfusion.Super.PentagonChi` is M8a-9.

Three deliverables:

1. **The signed-equivariant inverse, and its `LinearEquiv`-ization.**
   `signedEquivariant_symm`/`rightEquivariant_symm`: the inverse of a
   bijective (signed-)equivariant `LinearEquiv` is again
   (signed-)equivariant, of the *same* parity `e` (`e + e = 0` in
   `ZMod 2`).  `smapEquiv`/`RelTensor.mapEquivLeft`: the resulting
   `LinearEquiv`-ization of `smap`/`RelTensor.map` for an invertible
   generator — `smapEquiv` via `smap_comp_smap`'s composition law
   (the intended basis, per the track's design note), collapsing the
   composite signed amplification of parity `e + e = 0` to the
   identity through `smap_zero_eq_map`/`RelTensor.map_id`.
   `topRoute_bijective`/`botRoute_bijective`: composing these (plus
   the already-invertible associators `q1Assoc`–`q5Swap`, `q4Close`)
   shows both pentagon routes are bijective when their triple
   intertwiner data is invertible.  `topRoute_ne_zero_of_bijective`/
   `botRoute_ne_zero_of_bijective`: a bijective (in particular
   injective) linear map out of a nontrivial source is `≠ 0`.

2. **`chiAbs`** itself, `chiAbs_spec`, `chiAbs_unique`, `chiAbs_ne_zero`
   (§ "THE DEFINITION" below).

3. **The degree-bookkeeping corollary**: `quadInterSpace_deg_unique` —
   a nonzero quadruple intertwiner has a *unique* degree (two
   `homGrading` memberships at different degrees force the map to
   vanish, via the two-piece `ZMod 2`-grading directness already
   recorded by `modProj_of_mem`/`modProj_of_mem_ne`,
   `GradedModule.lean`) — and its thin corollary `chiAbs_deg_eq`,
   tying `topRoute`'s *own* naturally-computed degree back to
   `chiAbs`'s ambient common degree `e`.
-/
import Superfusion.Bimod.QuadMembership2
import Superfusion.Bimod.SignedMapEquivariance

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### General layer 1: the signed-equivariant inverse

The `LinearEquiv`-ization basis: if a `LinearEquiv` is (signed-)
equivariant, so is its inverse, of the *same* parity — proved directly
(applying the equivariance law at `φ.symm n'` and pushing `φ.symm`
through). -/

section SignedInverse

variable {A : Type*} [Ring A] [Module K A]
variable (𝒜 : ZMod 2 → Submodule K A)
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']

omit [Invertible (2 : K)] in
/-- **The signed-equivariant inverse**: if `φ : N ≃ₗ[K] N'` is signed
equivariant of parity `e` for a graded family `𝒜` (the shape `smap`'s
own equivariance hypothesis takes), so is `φ.symm`, of the *same*
parity `e`. -/
theorem signedEquivariant_symm (φ : N ≃ₗ[K] N') (e : ZMod 2)
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      φ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ n)) :
    ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n' : N',
      φ.symm (x • n') = ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ.symm n') := by
  intro i x hx n'
  have h := hφ hx (φ.symm n')
  rw [φ.apply_symm_apply] at h
  have h2 : φ.symm (φ (x • φ.symm n'))
      = φ.symm (((sgn (e * i) : ℤˣ) : ℤ) • (x • n')) := by rw [h]
  rw [φ.symm_apply_apply, map_zsmul] at h2
  have h3 : ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ.symm n')
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (((sgn (e * i) : ℤˣ) : ℤ) • φ.symm (x • n')) := by rw [h2]
  rw [smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul] at h3
  exact h3.symm

end SignedInverse

section RightInverse

variable {A : Type*} [Ring A]
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module Aᵐᵒᵖ N]
variable [AddCommGroup N'] [Module K N'] [Module Aᵐᵒᵖ N']

omit [Invertible (2 : K)] in
/-- **The right-equivariant inverse** (the unsigned, `MulOpposite`
companion, for the shape `RelTensor.map`'s own hypotheses take): if
`φ : N ≃ₗ[K] N'` is right-equivariant, so is `φ.symm`. -/
theorem rightEquivariant_symm (φ : N ≃ₗ[K] N')
    (hφ : ∀ (τ : A) (n : N), φ (MulOpposite.op τ • n) = MulOpposite.op τ • φ n) :
    ∀ (τ : A) (n' : N'), φ.symm (MulOpposite.op τ • n') = MulOpposite.op τ • φ.symm n' := by
  intro τ n'
  have h := hφ τ (φ.symm n')
  rw [φ.apply_symm_apply] at h
  have h2 : φ.symm (φ (MulOpposite.op τ • φ.symm n')) = φ.symm (MulOpposite.op τ • n') := by
    rw [h]
  rw [φ.symm_apply_apply] at h2
  exact h2.symm

end RightInverse

/-! ### General layer 2: the `LinearEquiv`-izations

`smapEquiv`: `smap`'s `LinearEquiv`-ization for an invertible generator
`φ`, via `smap_comp_smap`'s composition law — the intended basis, per
the track's design note.  `RelTensor.mapEquivLeft`: the unsigned
companion for `RelTensor.map`'s left slot. -/

section SmapEquiv

variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [GradedRightSMul 𝒜 ℳ]
variable {N N' : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [AddCommGroup N'] [Module K N'] [Module A N']

omit [Invertible (2 : K)] in
private theorem zmod2_add_self : ∀ e : ZMod 2, e + e = 0 := by decide

omit [Invertible (2 : K)] in
/-- **`smap`-congruence**: `smap` depends on its map/degree data only
up to equality (the equivariance witness is proof-irrelevant) — the
device bridging `smap_comp_smap`'s output back to the identity, without
rewriting inside a dependent proof argument in place. -/
private theorem smap_congr {f₁ f₂ : N →ₗ[K] N'}
    (hff : f₁ = f₂) {e₁ e₂ : ZMod 2} (hee : e₁ = e₂)
    {hf₁ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      f₁ (x • n) = ((sgn (e₁ * i) : ℤˣ) : ℤ) • (x • f₁ n)}
    {hf₂ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      f₂ (x • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (x • f₂ n)} :
    smap 𝒜 ℳ f₁ e₁ hf₁ = smap 𝒜 ℳ f₂ e₂ hf₂ := by
  subst hff; subst hee; rfl

/-- **The signed amplification, `LinearEquiv`-ized**: for an invertible
generator `φ : N ≃ₗ[K] N'` of signed equivariance `hφ` (parity `e`),
`smap 𝒜 ℳ φ.toLinearMap e hφ` is a `LinearEquiv` — `smap_comp_smap`'s
composition law collapses the composite (of summed parity `e + e = 0`)
to `smap _ id 0 _ = RelTensor.map id id _ _ = id` via
`smap_zero_eq_map`/`RelTensor.map_id`. -/
noncomputable def smapEquiv (φ : N ≃ₗ[K] N') (e : ZMod 2)
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      φ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ n)) :
    (M ⊗[A;K] N) ≃ₗ[K] (M ⊗[A;K] N') :=
  LinearEquiv.ofLinear
    (smap 𝒜 ℳ φ.toLinearMap e hφ)
    (smap 𝒜 ℳ φ.symm.toLinearMap e (signedEquivariant_symm K 𝒜 φ e hφ))
    (by
      have hcomp : φ.toLinearMap.comp φ.symm.toLinearMap = (LinearMap.id : N' →ₗ[K] N') := by
        ext n'; simp
      have hid : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n' : N',
          (LinearMap.id : N' →ₗ[K] N') (x • n')
            = ((sgn ((0 : ZMod 2) * i) : ℤˣ) : ℤ) • (x • (LinearMap.id : N' →ₗ[K] N') n') := by
        intro i x _ n'; simp
      have hid' : ∀ (x : A) (n' : N'),
          (LinearMap.id : N' →ₗ[K] N') (x • n') = x • (LinearMap.id : N' →ₗ[K] N') n' :=
        fun _ _ => rfl
      calc smap 𝒜 ℳ φ.toLinearMap e hφ ∘ₗ
              smap 𝒜 ℳ φ.symm.toLinearMap e (signedEquivariant_symm K 𝒜 φ e hφ)
          = smap 𝒜 ℳ (φ.toLinearMap.comp φ.symm.toLinearMap) (e + e)
              (signedEquivariant_comp 𝒜 φ.symm.toLinearMap e φ.toLinearMap e
                (signedEquivariant_symm K 𝒜 φ e hφ) hφ) :=
            smap_comp_smap 𝒜 ℳ φ.symm.toLinearMap e φ.toLinearMap e
              (signedEquivariant_symm K 𝒜 φ e hφ) hφ
        _ = smap 𝒜 ℳ (LinearMap.id : N' →ₗ[K] N') 0 hid :=
            smap_congr K 𝒜 ℳ hcomp (zmod2_add_self e)
        _ = RelTensor.map (LinearMap.id : M →ₗ[K] M) (LinearMap.id : N' →ₗ[K] N')
              (fun _ _ => rfl) (fun _ _ => rfl) :=
            smap_zero_eq_map 𝒜 ℳ LinearMap.id hid hid'
        _ = LinearMap.id := RelTensor.map_id)
    (by
      have hcomp : φ.symm.toLinearMap.comp φ.toLinearMap = (LinearMap.id : N →ₗ[K] N) := by
        ext n; simp
      have hid : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
          (LinearMap.id : N →ₗ[K] N) (x • n)
            = ((sgn ((0 : ZMod 2) * i) : ℤˣ) : ℤ) • (x • (LinearMap.id : N →ₗ[K] N) n) := by
        intro i x _ n; simp
      have hid' : ∀ (x : A) (n : N),
          (LinearMap.id : N →ₗ[K] N) (x • n) = x • (LinearMap.id : N →ₗ[K] N) n :=
        fun _ _ => rfl
      calc smap 𝒜 ℳ φ.symm.toLinearMap e (signedEquivariant_symm K 𝒜 φ e hφ) ∘ₗ
              smap 𝒜 ℳ φ.toLinearMap e hφ
          = smap 𝒜 ℳ (φ.symm.toLinearMap.comp φ.toLinearMap) (e + e)
              (signedEquivariant_comp 𝒜 φ.toLinearMap e φ.symm.toLinearMap e
                hφ (signedEquivariant_symm K 𝒜 φ e hφ)) :=
            smap_comp_smap 𝒜 ℳ φ.toLinearMap e φ.symm.toLinearMap e
              hφ (signedEquivariant_symm K 𝒜 φ e hφ)
        _ = smap 𝒜 ℳ (LinearMap.id : N →ₗ[K] N) 0 hid :=
            smap_congr K 𝒜 ℳ hcomp (zmod2_add_self e)
        _ = RelTensor.map (LinearMap.id : M →ₗ[K] M) (LinearMap.id : N →ₗ[K] N)
              (fun _ _ => rfl) (fun _ _ => rfl) :=
            smap_zero_eq_map 𝒜 ℳ LinearMap.id hid hid'
        _ = LinearMap.id := RelTensor.map_id)

omit [Invertible (2 : K)] in
theorem smapEquiv_toLinearMap (φ : N ≃ₗ[K] N') (e : ZMod 2)
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      φ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ n)) :
    (smapEquiv K 𝒜 ℳ φ e hφ).toLinearMap = smap 𝒜 ℳ φ.toLinearMap e hφ :=
  rfl

omit [Invertible (2 : K)] in
/-- **`smap` is bijective for an invertible generator.** -/
theorem smap_bijective (φ : N ≃ₗ[K] N') (e : ZMod 2)
    (hφ : ∀ ⦃i : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 i → ∀ n : N,
      φ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • φ n)) :
    Function.Bijective (smap 𝒜 ℳ φ.toLinearMap e hφ) := by
  rw [← smapEquiv_toLinearMap K 𝒜 ℳ φ e hφ]
  exact (smapEquiv K 𝒜 ℳ φ e hφ).bijective

end SmapEquiv

section MapEquivLeft

variable {A : Type*} [Ring A]
variable {M M' : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module K M'] [Module Aᵐᵒᵖ M']
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]

/-- **`RelTensor.map`'s left slot, `LinearEquiv`-ized**: for an
invertible right-equivariant generator `φ : M ≃ₗ[K] M'`,
`RelTensor.map φ.toLinearMap id hφ _` is a `LinearEquiv` — proved
directly, on generators (`RelTensor.map_mk`), since the unsigned shape
needs no sign bookkeeping. -/
noncomputable def RelTensor.mapEquivLeft (φ : M ≃ₗ[K] M')
    (hφ : ∀ (τ : A) (m : M), φ (MulOpposite.op τ • m) = MulOpposite.op τ • φ m) :
    (M ⊗[A;K] N) ≃ₗ[K] (M' ⊗[A;K] N) :=
  LinearEquiv.ofLinear
    (RelTensor.map φ.toLinearMap (LinearMap.id : N →ₗ[K] N) hφ (fun _ _ => rfl))
    (RelTensor.map φ.symm.toLinearMap (LinearMap.id : N →ₗ[K] N)
      (rightEquivariant_symm K φ hφ) (fun _ _ => rfl))
    (RelTensor.hom_ext fun m' n => by simp [RelTensor.map_mk])
    (RelTensor.hom_ext fun m n => by simp [RelTensor.map_mk])

omit [Invertible (2 : K)] in
theorem RelTensor.mapEquivLeft_toLinearMap (φ : M ≃ₗ[K] M')
    (hφ : ∀ (τ : A) (m : M), φ (MulOpposite.op τ • m) = MulOpposite.op τ • φ m) :
    (RelTensor.mapEquivLeft K φ hφ (N := N)).toLinearMap
      = RelTensor.map φ.toLinearMap (LinearMap.id : N →ₗ[K] N) hφ (fun _ _ => rfl) :=
  rfl

omit [Invertible (2 : K)] in
/-- **`RelTensor.map`'s left slot is bijective for an invertible
generator.** -/
theorem RelTensor.map_bijective_left (φ : M ≃ₗ[K] M')
    (hφ : ∀ (τ : A) (m : M), φ (MulOpposite.op τ • m) = MulOpposite.op τ • φ m) :
    Function.Bijective (RelTensor.map φ.toLinearMap (LinearMap.id : N →ₗ[K] N) hφ
      (fun _ _ => rfl)) := by
  rw [← RelTensor.mapEquivLeft_toLinearMap K φ hφ (N := N)]
  exact (RelTensor.mapEquivLeft K φ hφ (N := N)).bijective

end MapEquivLeft

/-! ### `topRoute`/`botRoute`, bijective for invertible `t`'s

`E1`/`E3` are `RelTensor.map`-based (unsigned); `E2`/`E4`/`E5` are
`smap`-based (signed); `q2Assoc`–`q5Swap`, `q4Close` are already
`LinearEquiv`s.  Unfolding `topRoute`/`botRoute` (and `E1`–`E5`) to
their defining `.comp` composites, descending to the function level
(`LinearMap.coe_comp`), and composing `RelTensor.map_bijective_left`/
`smap_bijective` with the associators' own bijectivity
(`Function.Bijective.comp`) gives both routes' bijectivity. -/

section RouteBijective

/-- **`topRoute` is bijective**, given `t₁`, `t₂`, `t₃` invertible
(packaged as `LinearEquiv`s `φ₁`, `φ₂`, `φ₃` with the equivariance data
of `E1`, `E2`, `E3`). -/
theorem topRoute_bijective
    (φ₁ : BL K a b c ≃ₗ[K] BR K a b c)
    (hφ₁ : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier) (m : BL K a b c),
      φ₁ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₁ m)
    (e₂ : ZMod 2) (φ₂ : Q2rInner K a b c d ≃ₗ[K] Q3Inner K a b c d)
    (hφ₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
      y ∈ (stdTower (K := K) (b + c)).grading i → ∀ n : Q2rInner K a b c d,
        φ₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • φ₂ n))
    (φ₃ : BL K b c d ≃ₗ[K] BR K b c d)
    (hφ₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier) (m : BL K b c d),
      φ₃ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₃ m) :
    Function.Bijective
      (topRoute K a b c d φ₁.toLinearMap hφ₁ e₂ φ₂.toLinearMap hφ₂ φ₃.toLinearMap hφ₃) := by
  unfold topRoute E1 E2 E3
  simp only [LinearMap.coe_comp]
  exact (RelTensor.map_bijective_left K φ₃ hφ₃ |>.comp (q3Assoc K a b c d).symm.bijective).comp
    ((smap_bijective K (stdTower (K := K) (b + c)).grading (TowerColumn.grading K b c)
        φ₂ e₂ hφ₂ |>.comp (q2Assoc K a b c d).bijective).comp
      (RelTensor.map_bijective_left K φ₁ hφ₁))

/-- **`botRoute` is bijective**, given `t₄`, `t₅` invertible (packaged
as `LinearEquiv`s `φ₄`, `φ₅` with the equivariance data of `E4`,
`E5`). -/
theorem botRoute_bijective
    (e₄ : ZMod 2) (φ₄ : BL K (a + b) c d ≃ₗ[K] BR K (a + b) c d)
    (hφ₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
        φ₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • φ₄ n))
    (e₅ : ZMod 2) (φ₅ : BL K a b (c + d) ≃ₗ[K] BR K a b (c + d))
    (hφ₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
        φ₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • φ₅ n)) :
    Function.Bijective
      (botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) := by
  unfold botRoute E4 E5
  simp only [LinearMap.coe_comp]
  refine (q4Close K a b c d).bijective.comp ?_
  exact (smap_bijective K (stdTower (K := K) (c + d)).grading (TowerColumn.grading K c d)
      φ₅ e₅ hφ₅ |>.comp (q5Swap K a b c d).bijective).comp
    (smap_bijective K (stdTower (K := K) (a + b)).grading (TowerColumn.grading K a b)
      φ₄ e₄ hφ₄ |>.comp (q1Assoc K a b c d).bijective)

end RouteBijective

/-! ### Nonzeroness from bijectivity -/

section NeZero

omit [Invertible (2 : K)] in
/-- **A bijective (in particular injective) linear map out of a
nontrivial source is `≠ 0`.** -/
private theorem linearMap_ne_zero_of_bijective {P Q : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [Nontrivial P] {f : P →ₗ[K] Q}
    (hf : Function.Bijective f) : f ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  exact hx (hf.1 (by simp [hzero]))

/-- **`topRoute` is `≠ 0`** when bijective and `Q1` is nontrivial. -/
theorem topRoute_ne_zero_of_bijective
    (t₁ : BL K a b c →ₗ[K] BR K a b c)
    (ht₁ : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier) (m : BL K a b c),
      t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
    (e₂ : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
      y ∈ (stdTower (K := K) (b + c)).grading i → ∀ n : Q2rInner K a b c d,
        t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
    (t₃ : BL K b c d →ₗ[K] BR K b c d)
    (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier) (m : BL K b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    [Nontrivial (Q1 K a b c d)]
    (hbij : Function.Bijective (topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃)) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0 :=
  linearMap_ne_zero_of_bijective K hbij

/-- **`botRoute` is `≠ 0`** when bijective and `Q1` is nontrivial. -/
theorem botRoute_ne_zero_of_bijective
    (e₄ : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    (e₅ : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
    [Nontrivial (Q1 K a b c d)]
    (hbij : Function.Bijective (botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ≠ 0 :=
  linearMap_ne_zero_of_bijective K hbij

end NeZero

/-! ### Degree bookkeeping: a nonzero quadruple intertwiner has a
unique degree

Two-piece `ZMod 2`-grading directness: a nonzero homogeneous element
cannot lie in two distinct `homGrading` degree parts — via
`modProj_of_mem`/`modProj_of_mem_ne` (`GradedModule.lean`). -/

section DegUnique

omit [Invertible (2 : K)] in
private theorem mem_disjoint {M : Type*} [AddCommGroup M] [Module K M]
    (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
    {j k : ZMod 2} (hjk : j ≠ k) {m : M} (hj : m ∈ ℳ j) (hk : m ∈ ℳ k) : m = 0 := by
  have h1 : modProj ℳ k m = m := modProj_of_mem ℳ hk
  have h2 : modProj ℳ k m = 0 := modProj_of_mem_ne ℳ hj hjk
  rw [h1] at h2
  exact h2

omit [Invertible (2 : K)] in
/-- **`homGrading`-directness**: a map homogeneous of *two distinct*
degrees `e ≠ e'` must vanish (its value at any `z`, decomposed via
`modProj ℳ 0 z + modProj ℳ 1 z = z`, lands in two disjoint target
pieces at each homogeneous summand). -/
theorem homGrading_eq_zero_of_ne {M : Type*} [AddCommGroup M] [Module K M]
    (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
    {N : Type*} [AddCommGroup N] [Module K N]
    (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
    {f : M →ₗ[K] N} {e e' : ZMod 2} (hee : e ≠ e')
    (hf : f ∈ homGrading ℳ 𝒩 e) (hf' : f ∈ homGrading ℳ 𝒩 e') : f = 0 := by
  refine LinearMap.ext fun z => ?_
  show f z = 0
  have hz : modProj ℳ 0 z + modProj ℳ 1 z = z := modProj_zero_add_modProj_one ℳ z
  have h0 : f (modProj ℳ 0 z) = 0 := by
    have m0 := hf 0 _ (modProj_mem ℳ 0 z)
    have m0' := hf' 0 _ (modProj_mem ℳ 0 z)
    exact mem_disjoint K 𝒩 (by simpa using hee) m0 m0'
  have h1 : f (modProj ℳ 1 z) = 0 := by
    have m1 := hf 1 _ (modProj_mem ℳ 1 z)
    have m1' := hf' 1 _ (modProj_mem ℳ 1 z)
    have hne1 : (1 : ZMod 2) + e ≠ (1 : ZMod 2) + e' := fun h => hee (add_left_cancel h)
    exact mem_disjoint K 𝒩 hne1 m1 m1'
  rw [← hz, map_add, h0, h1, add_zero]

omit [Invertible (2 : K)] in
/-- **A nonzero homogeneous map has a unique degree.** -/
theorem homGrading_deg_eq_of_ne_zero {M : Type*} [AddCommGroup M] [Module K M]
    (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
    {N : Type*} [AddCommGroup N] [Module K N]
    (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]
    {f : M →ₗ[K] N} {e e' : ZMod 2} (hf : f ≠ 0)
    (he : f ∈ homGrading ℳ 𝒩 e) (he' : f ∈ homGrading ℳ 𝒩 e') : e = e' := by
  by_contra hne
  exact hf (homGrading_eq_zero_of_ne K ℳ 𝒩 hne he he')

/-- **A nonzero quadruple intertwiner has a unique degree.** -/
theorem quadInterSpace_deg_unique {f : Q1 K a b c d →ₗ[K] Q4 K a b c d} {e e' : ZMod 2}
    (hf : f ≠ 0) (he : f ∈ quadInterSpace K a b c d e)
    (he' : f ∈ quadInterSpace K a b c d e') : e = e' := by
  obtain ⟨hg, -, -, -, -, -⟩ := (mem_quadInterSpace_iff K a b c d).mp he
  obtain ⟨hg', -, -, -, -, -⟩ := (mem_quadInterSpace_iff K a b c d).mp he'
  exact homGrading_deg_eq_of_ne_zero K (Q1.grading K a b c d) (Q4.grading K a b c d) hf hg hg'

end DegUnique

/-! ### `chiAbs`: the definition

The paper's `χ` (§4), in `End`-shaped form: given `topRoute`'s and
`botRoute`'s triple-intertwiner data (`t₁`–`t₅` and their equivariance
witnesses), a **common** landing degree `e` for `topRoute` (`htop`),
and a **Schur-type spanning hypothesis** for `quadInterSpace K a b c d
e` over `botRoute` (`hspan` — the paper's one-dimensionality, taken
here as a hypothesis; its discharge at the towers is M8a-8d′),
`chiAbs` is the *unique* scalar with `topRoute = chiAbs • botRoute`.

This holds for **any** fusion data satisfying the spanning hypothesis
— the tower instantiation and the discharge of `hspan` (plus
`botRoute ≠ 0`) follow in 8d′; the eventual identification with the
concrete `pentagonChi` (`Superfusion.Super.PentagonChi`) is M8a-9. -/

section ChiAbs

variable (t₁ : BL K a b c →ₗ[K] BR K a b c)
variable (ht₁ : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier) (m : BL K a b c),
  t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
variable (e₂ : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i → ∀ n : Q2rInner K a b c d,
    t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
variable (t₃ : BL K b c d →ₗ[K] BR K b c d)
variable (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier) (m : BL K b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
variable (e₄ : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
  x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
    t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
variable (e₅ : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
  z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
    t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
variable {e : ZMod 2}
variable (htop : topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ∈ quadInterSpace K a b c d e)
variable (hspan : ∀ f ∈ quadInterSpace K a b c d e,
  ∃ cc : K, f = cc • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)

/-- **`chiAbs`**: the unique scalar with `topRoute = chiAbs • botRoute`
(`hspan`'s witness at `topRoute`, which lies in `quadInterSpace K a b c
d e` by `htop`). -/
noncomputable def chiAbs : K :=
  (hspan _ htop).choose

/-- **The defining equation.** -/
theorem chiAbs_spec :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      = chiAbs K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan
          • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ :=
  (hspan _ htop).choose_spec

/-- **Uniqueness**: any scalar relating the two routes agrees with
`chiAbs`, given `botRoute ≠ 0` (scalar cancellation in the `K`-vector
space `Hom(Q1, Q4)`). -/
theorem chiAbs_unique {cc : K}
    (hbot_ne : botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ≠ 0)
    (hc : topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      = cc • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅) :
    cc = chiAbs K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan := by
  have h := chiAbs_spec K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan
  have hz : (cc - chiAbs K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan)
      • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ = 0 := by
    rw [sub_smul, ← hc, ← h, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hbot_ne

/-- **Nonvanishing**: `chiAbs ≠ 0` when `topRoute ≠ 0`. -/
theorem chiAbs_ne_zero
    (htop_ne : topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0) :
    chiAbs K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan ≠ 0 := by
  intro hzero
  apply htop_ne
  rw [chiAbs_spec K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ e₄ t₄ ht₄ e₅ t₅ ht₅ htop hspan,
    hzero, zero_smul]

include htop in
/-- **Degree bookkeeping**: `topRoute`'s own naturally-computed degree
(any independently-known membership `topRoute ∈ quadInterSpace K a b c
d e₁'`, e.g. from `topRoute_mem`) coincides with `chiAbs`'s ambient
common degree `e`, when `topRoute ≠ 0` (`quadInterSpace_deg_unique`). -/
theorem chiAbs_deg_eq {e₁' : ZMod 2}
    (htop_ne : topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ≠ 0)
    (htop' : topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ ∈ quadInterSpace K a b c d e₁') :
    e₁' = e :=
  quadInterSpace_deg_unique K a b c d htop_ne htop' htop

end ChiAbs

end PentagonB

end Bimod

end Superfusion
