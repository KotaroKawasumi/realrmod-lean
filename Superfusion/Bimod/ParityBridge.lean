/-
Superfusion / Bimod / ParityBridge

Milestone M8a-8d′-i (roadmap v3): **the `f ∘ P` bridge and the
parity-concentration general lemma** — general-layer results reducing
graded intertwiner spaces to ungraded `Hom`.

1. **The parity operator.** For a `K`-module `M` with grading `ℳ`
   (`[DirectSum.Decomposition ℳ]`), `parityOp ℳ : M ≃ₗ[K] M`,
   `m₀ + m₁ ↦ m₀ - m₁` (module-level analogue of `Super.ParityInvolution`'s
   `parityInvolution`/`parityAut`, built from `Bimod.GradedModule`'s
   `modProj` rather than `evenPart`/`oddPart`; no module-level parity
   operator of this shape existed prior to this file — the closest
   relative, `Super/GradedEndTensor.lean`'s `compJRight f := f ∘ₗ
   parityMap 𝒜` for `f : End K A`, is the single-algebra special case
   that suggested the general `f ∘ P` trick reused here at the level of
   an arbitrary `T`-module `M`).  `parityOp_smul_of_mem` is the twisted
   equivariance against a graded action (`SetLike.GradedSMul 𝒯 ℳ`):
   `parityOp (x • m) = (-1)^i • (x • parityOp m)` for `x` homogeneous of
   degree `i` — sign-verified independently below (§ "the twisted
   equivariance").

2. **The `f ∘ P` bridge.** `compParityOp ℳ f := f ∘ₗ parityOp ℳ`, an
   involution on `M →ₗ[K] N`.  The key general fact
   (`compParityOp_mem_superEquivariant_succ`): composing a degree-`d`
   super-equivariant map with `P` produces a degree-`(d+1)`
   super-equivariant map, for *any* `d` (not only `0`/`1`) — assembled
   into the `LinearEquiv` `superEquivariantSuccEquiv ℳ 𝒯 d :
   superEquivariant 𝒯 d ≃ₗ[K] superEquivariant 𝒯 (d + 1)`.  At `d = 0`
   the source is literally the *plain* `T`-linear maps
   (`mem_superEquivariant_zero_iff`, no sign at all, since `sgn (0 * i)
   = 1`), so the `d = 1` case is exactly the paper's claim: an odd
   equivariant map corresponds `1`-`1` to a plain `T`-linear map via
   `f ↦ f ∘ P`.  Combined with `compParityOp`'s (unconditional)
   compatibility with `homGrading` (`compParityOp` never shifts the
   `homGrading` degree, since `P` fixes each graded piece of `M` up to
   sign), `gradedHomF ℳ 𝒩 𝒯 d := homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯
   d` (the shape of one "slot" of `Intertwiner.lean`'s `interSpace`)
   bridges via `gradedHomFSuccEquiv` onto `homGrading ℳ 𝒩 d ⊓
   superEquivariant 𝒯 (d + 1)` — the *unsigned* homogeneous-degree-`d`
   piece — giving the **dimension-sum form**
   `finrank (gradedHomF ℳ 𝒩 𝒯 d) = finrank (homGrading ℳ 𝒩 d ⊓
   superEquivariant 𝒯 (d + 1))`.  (The further identification of this
   unsigned piece, together with its `d + 1`-degree companion, as an
   internal direct sum decomposing the literal Mathlib type
   `M →ₗ[T] N` needs a second "mask" construction on the *target*'s
   grading `𝒩` — the "full direct-sum packaging" flagged as optional
   in the design note; it is not built here, so `gradedHomF ℳ 𝒩 𝒯 0 ⊕
   gradedHomF ℳ 𝒩 𝒯 1 ≃ₗ[K] (M →ₗ[T] N)` itself is not landed.)

3. **Parity concentration.** `spanning_of_finrank_le_one`: the general
   vector-space fact that a submodule of `finrank ≤ 1` is spanned by
   any of its nonzero elements — in exactly the shape `ChiAbs.lean`'s
   `hspan` consumes (`∀ f ∈ S, ∃ c, f = c • g`).  `parityConcentration`
   assembles this with `homGrading`'s two-piece disjointness
   (`Submodule.one_le_finrank_iff`/`Submodule.finrank_eq_zero`, the
   `finrank` avatar of `ChiAbs.lean`'s `homGrading_eq_zero_of_ne`): given
   the **total-dimension hypothesis** `finrank (gradedHomF ℳ 𝒩 𝒯 0) +
   finrank (gradedHomF ℳ 𝒩 𝒯 1) ≤ 1` (the natural surrogate, at this
   general layer, for "the ungraded `Hom_F(M, N)` is at most
   `1`-dimensional") and a witness `gradedHomF ℳ 𝒩 𝒯 d ≠ ⊥`, the
   *other* parity's space is `⊥`, the `d`-space has `finrank = 1`, and
   it is spanned by any of its nonzero elements.
-/
import Superfusion.Bimod.HomGrading
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Superfusion

namespace Bimod

private theorem zmod2_add_one_add_one : ∀ d : ZMod 2, d + 1 + 1 = d := by decide

/-! ### The parity operator -/

section ParityOp

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]

/-- The parity map of a decomposed module, `m₀ + m₁ ↦ m₀ - m₁` (the
module-level analogue of `Super.ParityInvolution.parityMap`, built from
`modProj` instead of `evenPart`/`oddPart`). -/
noncomputable def parityMap : M →ₗ[K] M := modProj ℳ 0 - modProj ℳ 1

theorem parityMap_apply (m : M) :
    parityMap ℳ m = modProj ℳ 0 m - modProj ℳ 1 m := rfl

/-- On a homogeneous element of degree `i`, `parityMap` is the sign
`(-1)^i` (as a `ℤ`-scalar, matching `HomGrading.lean`'s `superEquivariant`
convention). -/
theorem parityMap_of_mem {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) :
    parityMap ℳ m = ((sgn i : ℤˣ) : ℤ) • m := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [parityMap_apply, modProj_of_mem ℳ hm,
      modProj_of_mem_ne ℳ hm (by decide), sub_zero, sgn_zero]
    simp
  · rw [parityMap_apply, modProj_of_mem ℳ hm,
      modProj_of_mem_ne ℳ hm (by decide), zero_sub, sgn_one]
    simp

theorem parityMap_parityMap (m : M) : parityMap ℳ (parityMap ℳ m) = m := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [map_zero, map_zero]
  | @homogeneous i x =>
      rw [parityMap_of_mem ℳ x.2, map_zsmul,
        parityMap_of_mem ℳ x.2, smul_smul, ← Units.val_mul, sgn_mul_self',
        Units.val_one, one_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The parity operator** `P : M ≃ₗ[K] M`, `m₀ + m₁ ↦ m₀ - m₁`
(module-level analogue of `Super.ParityInvolution.parityInvolution`/
`Wedderburn.GradedIdeal.parityAut`). -/
noncomputable def parityOp : M ≃ₗ[K] M :=
  LinearEquiv.ofInvolutive (parityMap ℳ) (parityMap_parityMap ℳ)

theorem parityOp_apply (m : M) : parityOp ℳ m = parityMap ℳ m := rfl

theorem parityOp_of_mem {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) :
    parityOp ℳ m = ((sgn i : ℤˣ) : ℤ) • m := by
  rw [parityOp_apply, parityMap_of_mem ℳ hm]

theorem parityOp_parityOp (m : M) : parityOp ℳ (parityOp ℳ m) = m := by
  rw [parityOp_apply, parityOp_apply, parityMap_parityMap]

theorem parityOp_mem {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) : parityOp ℳ m ∈ ℳ i := by
  rw [parityOp_of_mem ℳ hm]
  exact zsmul_mem hm _

end ParityOp

/-! ### The twisted equivariance of the parity operator -/

section TwistedEquivariance

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T)
variable [Module T M] [SetLike.GradedSMul 𝒯 ℳ]

/-- **The twisted equivariance of the parity operator**: for `x`
homogeneous of degree `i`, `P (x • m) = (-1)^i • (x • P m)` — for
*every* `m : M`, not only homogeneous `m` (both sides are additive in
`m`).  The sign content recorded by the M8a-8d′-i design note,
verified directly here. -/
theorem parityOp_smul_of_mem ⦃i : ZMod 2⦄ ⦃x : T⦄ (hx : x ∈ 𝒯 i) (m : M) :
    parityOp ℳ (x • m) = ((sgn i : ℤˣ) : ℤ) • (x • parityOp ℳ m) := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [smul_zero, map_zero, smul_zero, smul_zero]
  | @homogeneous j mm =>
      have hxm : x • (mm : M) ∈ ℳ (i + j) := SetLike.GradedSMul.smul_mem hx mm.2
      rw [parityOp_of_mem ℳ hxm, parityOp_of_mem ℳ mm.2, smul_comm (x : T),
        smul_smul, ← Units.val_mul, ← sgn_add]
  | add m m' hm hm' =>
      rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]

end TwistedEquivariance

/-! ### The `f ∘ P` bridge -/

section Bridge

variable {K : Type*} [CommRing K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N]

/-- **The `f ∘ P` bridge map**: precomposition with the source's parity
operator, as a `K`-linear endomorphism of `M →ₗ[K] N` — the module-level
analogue of `Super.GradedEndTensor.compJRight`. -/
noncomputable def compParityOp : (M →ₗ[K] N) →ₗ[K] (M →ₗ[K] N) where
  toFun f := f ∘ₗ (parityOp ℳ).toLinearMap
  map_add' f g := by ext m; simp
  map_smul' c f := by ext m; simp

theorem compParityOp_apply (f : M →ₗ[K] N) (m : M) :
    compParityOp ℳ f m = f (parityOp ℳ m) := rfl

/-- `compParityOp` is an involution (from `P² = id`). -/
theorem compParityOp_compParityOp (f : M →ₗ[K] N) :
    compParityOp ℳ (compParityOp ℳ f) = f := by
  ext m
  rw [compParityOp_apply, compParityOp_apply, parityOp_parityOp]

/-- `compParityOp` never changes `homGrading` membership: `P` fixes
each graded piece of `M` up to sign, so it does not shift the target
degree at all. -/
theorem compParityOp_mem_homGrading {𝒩 : ZMod 2 → Submodule K N} {d : ZMod 2}
    {f : M →ₗ[K] N} (hf : f ∈ homGrading ℳ 𝒩 d) :
    compParityOp ℳ f ∈ homGrading ℳ 𝒩 d := by
  intro i m hm
  rw [compParityOp_apply]
  exact hf i _ (parityOp_mem ℳ hm)

variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T)
variable [Module T M] [Module T N] [SMulCommClass K T N] [SetLike.GradedSMul 𝒯 ℳ]

/-- **Degree-`0` super-equivariance is plain `T`-linearity**: the sign
`sgn (0 * i)` is trivially `1`, so `superEquivariant 𝒯 0` is exactly the
maps intertwining the (unsigned) `T`-action on homogeneous elements —
"the even part is the plain `F`-linear maps". -/
theorem mem_superEquivariant_zero_iff {f : M →ₗ[K] N} :
    f ∈ superEquivariant 𝒯 (M := M) (N := N) 0 ↔
      ∀ ⦃i : ZMod 2⦄ ⦃x : T⦄, x ∈ 𝒯 i → ∀ m : M, f (x • m) = x • f m := by
  simp only [mem_superEquivariant, zero_mul, sgn_zero, Units.val_one, one_smul]

/-- **The key sign computation of the `f ∘ P` bridge**: composing a
degree-`d` super-equivariant map with `P` produces a degree-`(d + 1)`
super-equivariant map, for *any* degree `d` (specializing to `d = 1`
gives "odd signed ↦ even unsigned", and to `d = 0` gives "even unsigned
↦ odd signed"). -/
theorem compParityOp_mem_superEquivariant_succ {d : ZMod 2} {f : M →ₗ[K] N}
    (hf : f ∈ superEquivariant 𝒯 (M := M) (N := N) d) :
    compParityOp ℳ f ∈ superEquivariant 𝒯 (M := M) (N := N) (d + 1) := by
  rw [mem_superEquivariant] at hf ⊢
  intro i x hx m
  rw [compParityOp_apply, compParityOp_apply, parityOp_smul_of_mem ℳ 𝒯 hx, map_zsmul,
    hf hx (parityOp ℳ m), smul_smul, ← Units.val_mul, ← sgn_add,
    show i + d * i = (d + 1) * i from by ring]

/-- **The `f ∘ P` bijection**: composing with the source's parity
operator is a `K`-linear isomorphism from the degree-`d`
super-equivariant space onto the degree-`(d + 1)` super-equivariant
space, for any `d`.  At `d = 1` this is exactly the paper's claim: an
odd equivariant map corresponds `1`-`1` to a plain `T`-linear map
(`mem_superEquivariant_zero_iff` unfolds the `d = 0` target). -/
noncomputable def superEquivariantSuccEquiv (d : ZMod 2) :
    ↥(superEquivariant 𝒯 (M := M) (N := N) d) ≃ₗ[K]
      ↥(superEquivariant 𝒯 (M := M) (N := N) (d + 1)) :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ ((compParityOp ℳ).comp (superEquivariant 𝒯 d).subtype)
      (fun f => compParityOp_mem_superEquivariant_succ ℳ 𝒯 f.2))
    (LinearMap.codRestrict _
        ((compParityOp ℳ).comp (superEquivariant 𝒯 (M := M) (N := N) (d + 1)).subtype)
      (fun f => by
        have h := compParityOp_mem_superEquivariant_succ ℳ 𝒯 f.2
        rwa [zmod2_add_one_add_one] at h))
    (by
      refine LinearMap.ext fun f => ?_
      apply Subtype.ext
      exact compParityOp_compParityOp ℳ (f : M →ₗ[K] N))
    (by
      refine LinearMap.ext fun f => ?_
      apply Subtype.ext
      exact compParityOp_compParityOp ℳ (f : M →ₗ[K] N))

include ℳ in
theorem finrank_superEquivariant_eq (d : ZMod 2) :
    Module.finrank K ↥(superEquivariant 𝒯 (M := M) (N := N) d) =
      Module.finrank K ↥(superEquivariant 𝒯 (M := M) (N := N) (d + 1)) :=
  (superEquivariantSuccEquiv ℳ 𝒯 d).finrank_eq

variable (𝒩 : ZMod 2 → Submodule K N)

/-- **The precise degree-`d` graded intertwiner space matching one
"slot" of `Intertwiner.lean`'s `interSpace`**: homogeneous of degree
`d` (`homGrading`) and super-equivariant of degree `d` for the `T`-action
(`superEquivariant`). -/
noncomputable def gradedHomF (d : ZMod 2) : Submodule K (M →ₗ[K] N) :=
  homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) d

omit [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒯 ℳ] in
theorem mem_gradedHomF_iff {d : ZMod 2} {f : M →ₗ[K] N} :
    f ∈ gradedHomF ℳ 𝒯 𝒩 d ↔ f ∈ homGrading ℳ 𝒩 d ∧ f ∈ superEquivariant 𝒯 (M := M) (N := N) d :=
  Submodule.mem_inf

omit [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒯 ℳ] in
/-- **Even part, unfolded**: `gradedHomF ℳ 𝒯 𝒩 0` is exactly the plain
`T`-linear maps that preserve the grading — no sign at all. -/
theorem mem_gradedHomF_zero_iff {f : M →ₗ[K] N} :
    f ∈ gradedHomF ℳ 𝒯 𝒩 0 ↔
      (∀ i : ZMod 2, ∀ m ∈ ℳ i, f m ∈ 𝒩 i) ∧
        ∀ ⦃i : ZMod 2⦄ ⦃x : T⦄, x ∈ 𝒯 i → ∀ m : M, f (x • m) = x • f m := by
  rw [mem_gradedHomF_iff, mem_superEquivariant_zero_iff]
  simp only [mem_homGrading, add_zero]

/-- `compParityOp` sends `gradedHomF ℳ 𝒯 𝒩 d` into `homGrading ℳ 𝒩 d ⊓
superEquivariant 𝒯 (d + 1)` — the *unsigned* homogeneous-degree-`d`
companion space. -/
theorem compParityOp_mem_gradedHomF_succ {d : ZMod 2} {f : M →ₗ[K] N}
    (hf : f ∈ gradedHomF ℳ 𝒯 𝒩 d) :
    compParityOp ℳ f ∈ homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) (d + 1) :=
  ⟨compParityOp_mem_homGrading ℳ hf.1, compParityOp_mem_superEquivariant_succ ℳ 𝒯 hf.2⟩

/-- The converse direction: `compParityOp` sends the unsigned
`homGrading`-degree-`d` companion space back into `gradedHomF ℳ 𝒯 𝒩 d`
(using `compParityOp_mem_homGrading` at degree `d` directly, and
`compParityOp_mem_superEquivariant_succ` at degree `d + 1`, landing back
at `(d + 1) + 1 = d`). -/
theorem compParityOp_mem_gradedHomF_of_mem_succ {d : ZMod 2} {f : M →ₗ[K] N}
    (hf : f ∈ homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) (d + 1)) :
    compParityOp ℳ f ∈ gradedHomF ℳ 𝒯 𝒩 d := by
  refine ⟨compParityOp_mem_homGrading ℳ hf.1, ?_⟩
  have h := compParityOp_mem_superEquivariant_succ ℳ 𝒯 hf.2
  rwa [zmod2_add_one_add_one] at h

/-- **The `gradedHomF` bridge, dimension form**: composing with `P`
gives a `K`-linear isomorphism from the degree-`d` graded intertwiner
space onto the (unsigned) `homGrading`-degree-`d` companion space. -/
noncomputable def gradedHomFSuccEquiv (d : ZMod 2) :
    ↥(gradedHomF ℳ 𝒯 𝒩 d) ≃ₗ[K]
      ↥(homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) (d + 1)) :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ ((compParityOp ℳ).comp (gradedHomF ℳ 𝒯 𝒩 d).subtype)
      (fun f => compParityOp_mem_gradedHomF_succ ℳ 𝒯 𝒩 f.2))
    (LinearMap.codRestrict _
        ((compParityOp ℳ).comp
          (homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) (d + 1)).subtype)
      (fun f => compParityOp_mem_gradedHomF_of_mem_succ ℳ 𝒯 𝒩 f.2))
    (by
      refine LinearMap.ext fun f => ?_
      apply Subtype.ext
      exact compParityOp_compParityOp ℳ (f : M →ₗ[K] N))
    (by
      refine LinearMap.ext fun f => ?_
      apply Subtype.ext
      exact compParityOp_compParityOp ℳ (f : M →ₗ[K] N))

/-- **The dimension-sum form**: the degree-`d` graded intertwiner space
has the same `K`-dimension as its unsigned `homGrading`-degree-`d`
companion. -/
theorem finrank_gradedHomF_eq (d : ZMod 2) :
    Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 d) =
      Module.finrank K ↥(homGrading ℳ 𝒩 d ⊓ superEquivariant 𝒯 (M := M) (N := N) (d + 1)) :=
  (gradedHomFSuccEquiv ℳ 𝒯 𝒩 d).finrank_eq

end Bridge

/-! ### Parity concentration -/

section Spanning

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **A ≤ `1`-dimensional submodule is spanned by any of its nonzero
elements** — in exactly the shape `ChiAbs.lean`'s `hspan` consumes. -/
theorem spanning_of_finrank_le_one {S : Submodule K V} [Module.Finite K ↥S]
    (hle : Module.finrank K ↥S ≤ 1) {g : V} (hgS : g ∈ S) (hg : g ≠ 0) :
    ∀ f ∈ S, ∃ c : K, f = c • g := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle
  obtain ⟨c₀, hc₀⟩ := hv (⟨g, hgS⟩ : ↥S)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    refine hg ?_
    have h := congrArg Subtype.val hc₀
    simpa using h.symm
  have hveq : v = c₀⁻¹ • (⟨g, hgS⟩ : ↥S) := by
    rw [← hc₀, smul_smul, inv_mul_cancel₀ hc₀0, one_smul]
  intro f hfS
  obtain ⟨c, hc⟩ := hv (⟨f, hfS⟩ : ↥S)
  refine ⟨c * c₀⁻¹, ?_⟩
  have hfin : (⟨f, hfS⟩ : ↥S) = (c * c₀⁻¹) • (⟨g, hgS⟩ : ↥S) := by
    rw [← hc, hveq, smul_smul]
  have h := congrArg Subtype.val hfin
  simpa using h

end Spanning

section ParityConcentration

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N]
variable {T : Type*} [Ring T] [Algebra K T]
variable (𝒯 : ZMod 2 → Submodule K T)
variable [Module T M] [Module T N] [SMulCommClass K T N] [SetLike.GradedSMul 𝒯 ℳ]
variable (𝒩 : ZMod 2 → Submodule K N)

omit [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒯 ℳ] in
/-- **Parity concentration**: given the total-dimension hypothesis
`finrank (gradedHomF 0) + finrank (gradedHomF 1) ≤ 1` (the natural
surrogate, at this general layer, for "the ungraded `Hom_F(M, N)` is at
most `1`-dimensional") and a witness that the degree-`d` space is
nonzero, the *other* parity's space vanishes, the `d`-space is exactly
`1`-dimensional, and it is spanned by any of its nonzero elements — the
shape `ChiAbs.lean`'s `hspan` consumes. -/
theorem parityConcentration
    [Module.Finite K ↥(gradedHomF ℳ 𝒯 𝒩 0)] [Module.Finite K ↥(gradedHomF ℳ 𝒯 𝒩 1)]
    (hle : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 0)
      + Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1) ≤ 1)
    {d : ZMod 2} (hd : gradedHomF ℳ 𝒯 𝒩 d ≠ ⊥) :
    gradedHomF ℳ 𝒯 𝒩 (d + 1) = ⊥ ∧ Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 d) = 1 ∧
      ∀ f ∈ gradedHomF ℳ 𝒯 𝒩 d, ∀ g ∈ gradedHomF ℳ 𝒯 𝒩 d, g ≠ 0 →
        ∃ c : K, f = c • g := by
  rcases zmod2_cases d with hd0 | hd1
  · subst hd0
    have h1 : 1 ≤ Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 0) := Submodule.one_le_finrank_iff.mpr hd
    have h0 : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1) = 0 := by omega
    have hbot : gradedHomF ℳ 𝒯 𝒩 1 = ⊥ := Submodule.finrank_eq_zero.mp h0
    have heq : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 0) = 1 := by omega
    refine ⟨hbot, heq, fun f hf g hg hgne => ?_⟩
    exact spanning_of_finrank_le_one (S := gradedHomF ℳ 𝒯 𝒩 0) heq.le hg hgne f hf
  · subst hd1
    rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    have h1 : 1 ≤ Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1) := Submodule.one_le_finrank_iff.mpr hd
    have h0 : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 0) = 0 := by omega
    have hbot : gradedHomF ℳ 𝒯 𝒩 0 = ⊥ := Submodule.finrank_eq_zero.mp h0
    have heq : Module.finrank K ↥(gradedHomF ℳ 𝒯 𝒩 1) = 1 := by omega
    refine ⟨hbot, heq, fun f hf g hg hgne => ?_⟩
    exact spanning_of_finrank_le_one (S := gradedHomF ℳ 𝒯 𝒩 1) heq.le hg hgne f hf

end ParityConcentration

end Bimod

end Superfusion
