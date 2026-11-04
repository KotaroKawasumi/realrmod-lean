import Superfusion.Wedderburn.Density
import Superfusion.Gauge.SuperDivisionModule
import Superfusion.Super.BWPeriodicity
import Superfusion.Super.GradedTransfer
import Superfusion.Super.PlainOpposite

namespace Superfusion

open Module

/-! ### Deliverable 1: the `SetLike.GradedSMul` bridge -/

section Bridge

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- **The `SetLike.GradedSMul` bridge**: `E := Module.End A ↥I` acts on `↥I` by
application (mathlib's `Module.End.applyModule`), and this action is graded relative
to `endIdealGrading`/`idealGrading` — applying a degree-`i` endomorphism to a
degree-`j` element lands in degree `i + j`; exactly `mem_endIdealGrading`. -/
theorem gradedSMul_endIdealGrading_idealGrading (hI : I.IsHomogeneous 𝒜) :
    SetLike.GradedSMul (endIdealGrading 𝒜 hI) (idealGrading 𝒜 I) where
  smul_mem {i j} {f x} hf hx := by
    show f x ∈ idealGrading 𝒜 I (i +ᵥ j)
    rw [vadd_eq_add, add_comm]
    exact (mem_endIdealGrading 𝒜).mp hf j x hx

end Bridge

/-! ### Deliverable 2: parity-sorted reindex -/

section SortEquiv

/-- The equivalence splitting `Fin r` into its two parity fibers. -/
private def parityFiberEquiv {r : ℕ} (γ : Fin r → ZMod 2) :
    Fin r ≃ {i // γ i = 0} ⊕ {i // γ i = 1} :=
  (Equiv.sumCompl fun i => γ i = 0).symm.trans
    (Equiv.sumCongr (Equiv.refl _)
      (Equiv.subtypeEquivRight fun i => by
        constructor
        · intro h
          rcases zmod2_cases (γ i) with h0 | h1
          · exact absurd h0 h
          · exact h1
        · intro h h0
          rw [h] at h0
          exact absurd h0 (by decide)))

private theorem parityFiberEquiv_symm_inl {r : ℕ} (γ : Fin r → ZMod 2) (k' : {i // γ i = 0}) :
    (parityFiberEquiv γ).symm (Sum.inl k') = (k' : Fin r) := by
  simp [parityFiberEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Equiv.sumCompl_apply_inl]

private theorem parityFiberEquiv_symm_inr {r : ℕ} (γ : Fin r → ZMod 2) (k' : {i // γ i = 1}) :
    (parityFiberEquiv γ).symm (Sum.inr k') = (k' : Fin r) := by
  simp [parityFiberEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Equiv.sumCompl_apply_inr]

/-- **The parity-sorted reindex** (referee route): `Fin r ≃ Fin p ⊕ Fin q`, `p`/`q`
the sizes of the two parity fibers, via `Fintype.equivFin`. -/
noncomputable def sortEquiv {r : ℕ} (γ : Fin r → ZMod 2) :
    Fin r ≃ Fin (Fintype.card {i // γ i = 0}) ⊕ Fin (Fintype.card {i // γ i = 1}) :=
  (parityFiberEquiv γ).trans ((Fintype.equivFin _).sumCongr (Fintype.equivFin _))

/-- The reindex is parity-compatible: `γ` pulled back along `(sortEquiv γ).symm` is
exactly `sumParity p q` by construction. -/
theorem sortEquiv_symm_parity {r : ℕ} (γ : Fin r → ZMod 2)
    (x : Fin (Fintype.card {i // γ i = 0}) ⊕ Fin (Fintype.card {i // γ i = 1})) :
    γ ((sortEquiv γ).symm x) =
      sumParity (Fintype.card {i // γ i = 0}) (Fintype.card {i // γ i = 1}) x := by
  cases x with
  | inl k =>
      show γ ((parityFiberEquiv γ).symm (Sum.inl ((Fintype.equivFin _).symm k))) = 0
      rw [parityFiberEquiv_symm_inl]
      exact ((Fintype.equivFin {i // γ i = 0}).symm k).2
  | inr k =>
      show γ ((parityFiberEquiv γ).symm (Sum.inr ((Fintype.equivFin _).symm k))) = 1
      rw [parityFiberEquiv_symm_inr]
      exact ((Fintype.equivFin {i // γ i = 1}).symm k).2

end SortEquiv

/-! ### Existence of a parity-sorted homogeneous `E`-basis of `↥I` -/

section SortedBasis

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- **A parity-sorted homogeneous `Module.End A ↥I`-basis of `↥I`**: apply M9-1b's
`exists_homogeneous_basis` to the graded module `↥I` over the super division algebra
`E := Module.End A ↥I` (M10-2's `endIdeal_isSuperDivision`), extract `r ≠ 0` from
`Nontrivial ↥I`, and reindex the basis along `sortEquiv` to land on `Fin p ⊕ Fin q`
with parity function exactly `sumParity p q` by construction (the referee route:
reindex the basis, not the matrices). -/
theorem exists_sorted_homogeneous_basis [IsGradedSimple 𝒜] (hI : I.IsHomogeneous 𝒜)
    (hsimple : IsGradedSimpleIdeal 𝒜 I) (hne : I ≠ ⊥)
    [FiniteDimensional K A] [Invertible (2 : K)] :
    ∃ (p q : ℕ) (b : Basis (Fin p ⊕ Fin q) (Module.End A ↥I) ↥I),
      p + q ≠ 0 ∧ ∀ x : Fin p ⊕ Fin q, b x ∈ idealGrading 𝒜 I (sumParity p q x) := by
  haveI hIdec : DirectSum.Decomposition (idealGrading 𝒜 I) := idealDecomposition 𝒜 hI
  haveI hEalg : GradedAlgebra (endIdealGrading 𝒜 hI) := endIdealGradedAlgebra 𝒜 hI
  haveI hgsm : SetLike.GradedSMul (endIdealGrading 𝒜 hI) (idealGrading 𝒜 I) :=
    gradedSMul_endIdealGrading_idealGrading 𝒜 hI
  haveI : FiniteDimensional K ↥I :=
    FiniteDimensional.finiteDimensional_submodule (I.restrictScalars K)
  obtain ⟨r, γ, b, hb⟩ := Bimod.exists_homogeneous_basis (endIdealGrading 𝒜 hI)
    (idealGrading 𝒜 I) (endIdeal_isSuperDivision 𝒜 hI hsimple)
  haveI : Nontrivial ↥I := nontrivial_of_ne_bot hne
  have hr0 : r ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥I
    apply hxy
    exact Function.Injective.subsingleton b.equivFun.injective |>.elim x y
  set p := Fintype.card {i : Fin r // γ i = 0} with hp
  set q := Fintype.card {i : Fin r // γ i = 1} with hq
  refine ⟨p, q, b.reindex (sortEquiv γ), ?_, ?_⟩
  · have hple : p ≤ r := by
      rw [hp]
      simpa using Fintype.card_subtype_le (fun i : Fin r => γ i = 0)
    have hpq : p + q = r := by
      have hcard := Fintype.card_subtype_compl (fun i : Fin r => γ i = 0)
      simp only [Fintype.card_fin] at hcard
      have hcompl : {i : Fin r // ¬ γ i = 0} ≃ {i : Fin r // γ i = 1} :=
        Equiv.subtypeEquivRight fun i => by
          constructor
          · intro h; rcases zmod2_cases (γ i) with h0 | h1
            · exact absurd h0 h
            · exact h1
          · intro h h0; rw [h] at h0; exact absurd h0 (by decide)
      rw [hp, hq, ← Fintype.card_congr hcompl]
      omega
    rw [hpq]
    exact hr0
  · intro x
    rw [Basis.reindex_apply]
    have h := hb ((sortEquiv γ).symm x)
    have heq := sortEquiv_symm_parity γ x
    exact heq ▸ h

end SortedBasis

/-! ### Deliverable 3: the matrix identification -/

section MatrixEquiv

variable (K : Type*) [Field K] {E M ι : Type*} [Ring E] [Algebra K E]
  [AddCommGroup M] [Module K M] [Module E M] [IsScalarTower K E M]
  [Fintype ι] [DecidableEq ι]

/-- **The matrix identification**: given an `E`-basis `b` of `M`, `Module.End E M`
is `K`-algebra isomorphic to matrices with entries in the plain multiplicative
opposite `Eᵐᵒᵖ` — mathlib's `endVecAlgEquivMatrixEnd`/`AlgEquiv.moduleEndSelf`
composite (giant's shoulders, cf. `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`
in `Mathlib.RingTheory.SimpleModule.WedderburnArtin`): `LinearEquiv.conjAlgEquiv`
transports `g` along `b.equivFun : M ≃ₗ[E] (ι → E)` (`E`-linearity pulls scalars
out unsigned), `endVecAlgEquivMatrixEnd` turns a vector-endomorphism into a matrix
of scalar-endomorphisms, and `(AlgEquiv.moduleEndSelf K).symm` reads off each
scalar-endomorphism as the opposite of its value at `1`. -/
noncomputable def matrixEquiv (b : Basis ι E M) :
    Module.End E M ≃ₐ[K] Matrix ι ι Eᵐᵒᵖ :=
  (LinearEquiv.conjAlgEquiv K b.equivFun).trans
    ((endVecAlgEquivMatrixEnd ι K E E).trans
      (AlgEquiv.mapMatrix (AlgEquiv.moduleEndSelf K (A := E)).symm))

/-- **Entry formula**: `matrixEquiv b g r s = op (b.repr (g (b s)) r)` — the entry
`m_{rs}` defined by `g(b_s) = Σ_r m_{rs} • b_r`, in the plain opposite (design Step 4:
`E`-linearity pulls scalars out unsigned; composition reverses coefficient order). -/
theorem matrixEquiv_apply (b : Basis ι E M) (g : Module.End E M) (r s : ι) :
    matrixEquiv K b g r s = MulOpposite.op (b.repr (g (b s)) r) := by
  show MulOpposite.op ((((LinearEquiv.conjAlgEquiv K b.equivFun) g)
    (Pi.single s (1 : E))) r) = _
  congr 2
  rw [LinearEquiv.conjAlgEquiv_apply]
  show b.equivFun (g (b.equivFun.symm (Pi.single s (1 : E)))) r = _
  rw [show b.equivFun.symm (Pi.single s (1 : E)) = b s by
    rw [Basis.equivFun_symm_apply]
    simp [Pi.single_apply]]
  rw [Basis.equivFun_apply]

end MatrixEquiv

/-! Deliverable 4, preservation of super division by the ordinary
opposite, now lives in `Gauge.SuperDivisionBasic` because it is generic
module infrastructure rather than a Wedderburn result. -/

/-! ### `Module.End (Module.End A ↥I) ↥I` is a graded algebra

`densityEndGrading` (M10-3, `Density.lean`) is not built with a `GradedAlgebra`
instance — only directness and, via `densityEndGrading_spanning`, spanning are
proved there. Assemble the instance here: `IsCompl` from directness + spanning,
`DirectSum.Decomposition` via mathlib's `DirectSum.IsInternal.chooseDecomposition`
(the `ZMod 2`-two-index case of `DirectSum.isInternal_submodule_iff_isCompl`), and
`SetLike.GradedMonoid` by the same shift computation as `endIdealGrading`'s own
instance (`GradedSchur.lean`). -/

section DensityGraded

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A}

/-- **Build a `ZMod 2`-`DirectSum.Decomposition` from `IsCompl (ℬ 0) (ℬ 1)`** — the
mathlib-generic route absent upstream as a direct constructor, via
`DirectSum.isInternal_submodule_iff_isCompl` and `IsInternal.chooseDecomposition`. -/
@[implicit_reducible]
noncomputable def decompositionOfIsCompl {M : Type*} [AddCommGroup M] [Module K M]
    (ℬ : ZMod 2 → Submodule K M) (h : IsCompl (ℬ 0) (ℬ 1)) : DirectSum.Decomposition ℬ :=
  DirectSum.IsInternal.chooseDecomposition ℬ
    ((DirectSum.isInternal_submodule_iff_isCompl ℬ (by decide)
      (by
        ext x
        simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
        decide +revert)).mpr h)

/-- The spanning half of `IsCompl`, from `densityEndGrading_spanning`. -/
theorem densityEndGrading_sup_eq_top (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)] :
    densityEndGrading 𝒜 hI 0 ⊔ densityEndGrading 𝒜 hI 1 = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun g => ?_
  obtain ⟨g0, hg0, g1, hg1, heq⟩ := densityEndGrading_spanning 𝒜 hI hsimple hne g
  rw [heq]
  exact Submodule.add_mem_sup hg0 hg1

/-- `densityEndGrading 0` and `densityEndGrading 1` are complementary: directness
(`densityEndGrading_directness`, M10-3) plus spanning above. -/
theorem isCompl_densityEndGrading (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)] :
    IsCompl (densityEndGrading 𝒜 hI 0) (densityEndGrading 𝒜 hI 1) :=
  IsCompl.of_eq (densityEndGrading_directness 𝒜 hI) (densityEndGrading_sup_eq_top 𝒜 hI hsimple hne)

private theorem zmod2_density_mul : ∀ k j i : ZMod 2, (k + j) + i = k + (i + j) := by decide

/-- The `GradedMonoid` structure on `densityEndGrading`, mirroring `endIdealGrading`'s
own instance (`GradedSchur.lean`) verbatim (same shift computation, one level up). -/
theorem gradedMonoid_densityEndGrading (hI : I.IsHomogeneous 𝒜) :
    SetLike.GradedMonoid (densityEndGrading 𝒜 hI) where
  one_mem := fun j x hx => by
    rw [show ((1 : Module.End (Module.End A ↥I) ↥I) x) = x from rfl]
    rwa [show j + (0 : ZMod 2) = j from by rw [add_zero]]
  mul_mem {i j} f g hf hg := fun k x hx => by
    rw [show ((f * g) x) = f (g x) from rfl]
    have h := hf (k + j) (g x) (hg k x hx)
    rwa [zmod2_density_mul] at h

/-- **`Module.End (Module.End A ↥I) ↥I` is a graded algebra** under
`densityEndGrading`. -/
@[implicit_reducible]
noncomputable def densityEndGradedAlgebra (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
    (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)] :
    GradedAlgebra (densityEndGrading 𝒜 hI) where
  toGradedMonoid := gradedMonoid_densityEndGrading 𝒜 hI
  toDecomposition :=
    decompositionOfIsCompl (densityEndGrading 𝒜 hI) (isCompl_densityEndGrading 𝒜 hI hsimple hne)

end DensityGraded

/-! ### Deliverable 3 (continued): the matrix identification is graded -/

section MatrixGraded

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {I : Submodule A A} (hI : I.IsHomogeneous 𝒜) (hsimple : IsGradedSimpleIdeal 𝒜 I)
  (hne : I ≠ ⊥) [FiniteDimensional K A] [Invertible (2 : K)]
variable {p q : ℕ} (b : Basis (Fin p ⊕ Fin q) (Module.End A ↥I) ↥I)
  (hb : ∀ x, b x ∈ idealGrading 𝒜 I (sumParity p q x))

private theorem zmod2_matrix_shift (d x y : ZMod 2) : (x + d) + y = d + y + x := by
  decide +revert

omit [FiniteDimensional K A] [Invertible (2 : K)] in
/-- **The matrix identification is homogeneous**: entry `(r, s)` of the image of a
degree-`d` endomorphism lies in degree `d + π r + π s` — coordinate-homogeneity
(Section 0) applied to `g (b s)`, which the End-grading places in degree
`π s + d` where `π := sumParity p q`. -/
theorem matrixEquiv_mem_matrixGradingA (hb : ∀ x, b x ∈ idealGrading 𝒜 I (sumParity p q x))
    {d : ZMod 2} {g : Module.End (Module.End A ↥I) ↥I}
    (hg : g ∈ densityEndGrading 𝒜 hI d) :
    matrixEquiv K b g ∈ matrixGradingA (sumParity p q) (opGrading (endIdealGrading 𝒜 hI)) d := by
  haveI : GradedAlgebra (endIdealGrading 𝒜 hI) := endIdealGradedAlgebra 𝒜 hI
  haveI : DirectSum.Decomposition (idealGrading 𝒜 I) := idealDecomposition 𝒜 hI
  haveI : SetLike.GradedSMul (endIdealGrading 𝒜 hI) (idealGrading 𝒜 I) :=
    gradedSMul_endIdealGrading_idealGrading 𝒜 hI
  intro r s
  rw [matrixEquiv_apply, mem_opGrading_iff, MulOpposite.unop_op]
  have hgs : g (b s) ∈ idealGrading 𝒜 I (sumParity p q s + d) :=
    (mem_densityEndGrading 𝒜).mp hg (sumParity p q s) (b s) (hb s)
  have hcoord :=
    Bimod.basis_repr_mem_grading
      (endIdealGrading 𝒜 hI) (idealGrading 𝒜 I) b hb hgs r
  rwa [zmod2_matrix_shift] at hcoord

/-- **`matrixEquiv` carries the End grading onto the matrix grading**, via the
`map_grading_of_bijective` referee route (`Super/GradedTransfer.lean`): the reverse
inclusion needs no further coordinate work, only the forward homogeneity above plus
bijectivity of the `AlgEquiv`. -/
theorem matrixEquiv_map_grading (hsimple : IsGradedSimpleIdeal 𝒜 I) (hne : I ≠ ⊥)
    (hb : ∀ x, b x ∈ idealGrading 𝒜 I (sumParity p q x)) (d : ZMod 2) :
    (densityEndGrading 𝒜 hI d).map (matrixEquiv K b).toLinearMap
      = matrixGradingA (sumParity p q) (opGrading (endIdealGrading 𝒜 hI)) d := by
  haveI : GradedAlgebra (endIdealGrading 𝒜 hI) := endIdealGradedAlgebra 𝒜 hI
  haveI : GradedAlgebra (densityEndGrading 𝒜 hI) := densityEndGradedAlgebra 𝒜 hI hsimple hne
  exact map_grading_of_bijective (densityEndGrading 𝒜 hI)
    (matrixGradingA (sumParity p q) (opGrading (endIdealGrading 𝒜 hI)))
    (matrixEquiv K b).toAlgHom
    (fun d' g hg => matrixEquiv_mem_matrixGradingA 𝒜 hI b hb hg)
    (matrixEquiv K b).bijective d

end MatrixGraded

/-! ### Deliverable 5: `IsSuperDivision.isGradedSimple` (referee gap-fill) -/

section IsGradedSimpleOfDivision

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable {𝒜 : ZMod 2 → Submodule K A} [GradedAlgebra 𝒜]

/-- **A graded algebra whose grading is a super division algebra is graded-simple**
(referee gap-fill, needed for M10-6's `DBW.mulClosed` witness assembly): a nonzero
homogeneous two-sided ideal contains a nonzero homogeneous component of one of its
members — a unit by `IsSuperDivision` — hence equals `⊤`. No `Nontrivial` hypothesis
needed. -/
theorem IsSuperDivision.isGradedSimple (hdiv : Bimod.IsSuperDivision 𝒜) :
    IsGradedSimple 𝒜 := by
  constructor
  intro J hJ
  by_cases hJbot : J = ⊥
  · exact Or.inl hJbot
  refine Or.inr ?_
  obtain ⟨a, haJ, ha0⟩ : ∃ a ∈ J, a ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hJbot
    ext x
    rw [TwoSidedIdeal.mem_bot]
    constructor
    · intro hx
      by_contra hx0
      exact hx0 (hc x hx)
    · rintro rfl
      exact J.zero_mem
  have hcomp : ∃ i : ZMod 2, (DirectSum.decompose 𝒜 a i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    have h0 : evenPart 𝒜 a = 0 := hcon 0
    have h1 : oddPart 𝒜 a = 0 := hcon 1
    rw [← evenPart_add_oddPart 𝒜 a, h0, h1, add_zero]
  obtain ⟨i, hai⟩ := hcomp
  have haiJ : (DirectSum.decompose 𝒜 a i : A) ∈ J := hJ a haJ i
  have haimem : (DirectSum.decompose 𝒜 a i : A) ∈ 𝒜 i := SetLike.coe_mem _
  have hunit : IsUnit (DirectSum.decompose 𝒜 a i : A) := hdiv haimem hai
  obtain ⟨v, hv⟩ := hunit
  have h1 : (1 : A) ∈ J := by
    have h2 := J.mul_mem_left ((v⁻¹ : Aˣ) : A) _ haiJ
    rwa [← hv, Units.inv_mul] at h2
  ext x
  simp only [TwoSidedIdeal.mem_top, iff_true]
  have h3 := J.mul_mem_left x 1 h1
  rwa [mul_one] at h3

end IsGradedSimpleOfDivision

/-! ### `E = Module.End A ↥I` is finite-dimensional over `K` -/

section EndFinite

variable {K : Type*} [Field K] {A M : Type*} [Ring A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]

/-- The forgetful `K`-linear embedding `Module.End A M ↪ Module.End K M`. -/
private noncomputable def endRestrictToK : (M →ₗ[A] M) →ₗ[K] (M →ₗ[K] M) where
  toFun f := f.restrictScalars K
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

private theorem endRestrictToK_injective :
    Function.Injective (endRestrictToK (K := K) (A := A) (M := M)) := by
  intro f g hfg
  exact LinearMap.ext fun x => DFunLike.congr_fun hfg x

/-- **`E = Module.End A M` is finite-dimensional over `K`** whenever `M` is: `E`
embeds `K`-linearly (forgetting the `A`-linearity witness) into the finite-
dimensional `Module.End K M`. -/
theorem finiteDimensional_end_of_finiteDimensional [FiniteDimensional K M] :
    FiniteDimensional K (Module.End A M) :=
  FiniteDimensional.of_injective endRestrictToK endRestrictToK_injective

end EndFinite

/-! ### Deliverable 6: the graded Wedderburn theorem -/

universe u

/-- **The graded Wedderburn theorem** (the summit of the M10 arc): a finite-
dimensional, nontrivial, graded-simple superalgebra `A` over a field `K` with `2`
invertible is graded-isomorphic to a matrix stabilization `M_{p|q}(D)` of a super
division algebra `D`.

Assembly: a minimal homogeneous left ideal `I` (M10-1) with `E := Module.End A ↥I`
a super division algebra (M10-2); `densityRep` gives a bijective graded algebra
equivalence `A ≃ Module.End E ↥I` (M10-3); a parity-sorted homogeneous `E`-basis of
`↥I` (Deliverables 1–2 above) identifies `Module.End E ↥I` with matrices over `Eᵐᵒᵖ`
(Deliverable 3); `D := Eᵐᵒᵖ`, packaged as a super division algebra via the plain
opposite (Deliverable 4). -/
theorem graded_wedderburn {K : Type u} [Field K] (A : SuperAlgebra.{u, u} K)
    [IsGradedSimple A.grading] [FiniteDimensional K A.carrier] [Nontrivial A.carrier]
    [Invertible (2 : K)] :
    ∃ (D : SuperAlgebra.{u, u} K) (p q : ℕ), p + q ≠ 0 ∧ Bimod.IsSuperDivision D.grading ∧
      FiniteDimensional K D.carrier ∧ Nontrivial D.carrier ∧
      Nonempty (SuperAlgEquiv A (D.matrixSuper p q)) := by
  obtain ⟨I, hI, hne, hminimal⟩ := exists_minimal_homogeneous_leftIdeal A.grading
  have hsimple : IsGradedSimpleIdeal A.grading I := hminimal
  haveI : Nontrivial ↥I := nontrivial_of_ne_bot hne
  haveI hEalg : GradedAlgebra (endIdealGrading A.grading hI) := endIdealGradedAlgebra A.grading hI
  haveI hEnontriv : Nontrivial (Module.End A.carrier ↥I) := inferInstance
  haveI hEfin : FiniteDimensional K (Module.End A.carrier ↥I) :=
    finiteDimensional_end_of_finiteDimensional
  obtain ⟨p, q, b, hpq, hb⟩ := exists_sorted_homogeneous_basis A.grading hI hsimple hne
  set ρ := AlgEquiv.ofBijective (densityRep (K := K) (A := A.carrier) (I := I))
    (densityRep_bijective A.grading hI hsimple hne) with hρdef
  set Φ := matrixEquiv K b with hΦdef
  set θ := ρ.trans Φ with hθdef
  haveI hOp : GradedAlgebra (opGrading (endIdealGrading A.grading hI)) :=
    opGradedAlgebra (endIdealGrading A.grading hI)
  set D : SuperAlgebra K :=
    (⟨(Module.End A.carrier ↥I)ᵐᵒᵖ, opGrading (endIdealGrading A.grading hI)⟩ : SuperAlgebra K)
    with hDdef
  refine ⟨D, p, q, hpq,
    isSuperDivision_opGrading (endIdealGrading A.grading hI)
      (endIdeal_isSuperDivision A.grading hI hsimple),
    inferInstance, inferInstance, ⟨⟨θ, ?_⟩⟩⟩
  intro d
  show (A.grading d).map θ.toLinearMap = matrixGradingA (sumParity p q) D.grading d
  have hstep : (A.grading d).map θ.toLinearMap
      = (densityEndGrading A.grading hI d).map Φ.toLinearMap := by
    rw [hθdef, show (ρ.trans Φ).toLinearMap = Φ.toLinearMap ∘ₗ ρ.toLinearMap from rfl,
      Submodule.map_comp]
    congr 1
    show (A.grading d).map (densityRep (K := K) (A := A.carrier) (I := I)).toLinearMap = _
    exact densityRep_grading_eq A.grading hI hsimple hne d
  rw [hstep]
  exact matrixEquiv_map_grading A.grading hI b hsimple hne hb d

end Superfusion
