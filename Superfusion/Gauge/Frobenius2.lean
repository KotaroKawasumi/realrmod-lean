/-
Superfusion / Gauge / Frobenius2

Milestone C1b: the main body of a Lean formalization of **Frobenius' theorem** —
every finite-dimensional associative division algebra over `ℝ` is (isomorphic to)
`ℝ`, `ℂ`, or `ℍ`. Building on the setup stage `Superfusion.Gauge.Frobenius1`
(a square root of `-1` exists in any `D` not equal to `ℝ · 1`), this file carries
out the classification proper: the `i`-eigenspace decomposition of `D`, the
"`ℂ`-Schur lemma" (a finite-dimensional division algebra over `ℂ` is `ℂ` itself),
and the quaternion assembly in the remaining case. As with `Frobenius1`, this
material is (as of this writing) *absent from Mathlib*, so the file is written
as an upstream-candidate: Mathlib-only imports (plus `Frobenius1`), ordinary
Mathlib naming and generality, docstrings throughout.

## Main declarations

* `Superfusion.Frobenius.algebraMap_complex_surjective`: the **`ℂ`-Schur
  lemma** — for a finite-dimensional division algebra `E` over `ℂ`,
  `algebraMap ℂ E` is surjective (`ℂ` is algebraically closed, so a
  finite extension of it is trivial).
* `Superfusion.Frobenius.bijective_liftAux_of_central` /
  `nonempty_algEquiv_complex_of_central`: repackage the `ℂ`-Schur lemma for a
  ring `A` containing a **central** square root of `-1`: the associated map
  `ℂ →ₐ[ℝ] A` is then automatically bijective.
* `Superfusion.Frobenius.plus` / `Superfusion.Frobenius.minus`: for `i : D`,
  the `±1`-eigenspaces of conjugation by `i` (`plus i` is the centralizer of
  `i`, a subalgebra; `minus i` is the anti-centralizer, a submodule).
* `Superfusion.Frobenius.frobenius_trichotomy`: **the main theorem** — every
  finite-dimensional `ℝ`-division algebra is `ℝ`, `ℂ`, or `ℍ`.
* `Superfusion.Frobenius.frobenius_central`: the central refinement — a
  finite-dimensional *central* `ℝ`-division algebra is `ℝ` or `ℍ` (`ℂ` is
  excluded, having a strictly larger center).

## Implementation notes

The main theorem is stated for `D : Type` (universe `0`), matching `ℝ`, `ℂ`,
`ℍ[ℝ]`: this is what `Mathlib`'s `IsAlgClosed.of_ringEquiv` needs (`k` and `k'`
share a universe), and is no loss for the intended application (comparing `D`
against the fixed, universe-`0` targets `ℝ`, `ℂ`, `ℍ[ℝ]` already forces this).

The `ℂ`-Schur lemma is proved by reducing to Mathlib's
`IsAlgClosed.algebraMap_bijective_of_isIntegral`; the reduction from "`i`
central in `A`" to "`Algebra K A` with `K := (Complex.liftAux i hi).range`"
uses `RingHom.toAlgebra'` (an algebra structure from a homomorphism *into the
center*, avoiding a `CommRing K` hypothesis) together with `K`'s `IsField`
witness pulled back along a `MulEquiv` to `ℂ` (`MulEquiv.isField`), rather
than the (diamond-prone, since `K` is then quotiented against Mathlib's own
automatic `Module ℂ`-from-`Algebra ℂ` instances) more naive route through a
literal `Algebra ℂ A` instance.
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Superfusion.Gauge.Frobenius1

namespace Superfusion

namespace Frobenius

open Quaternion

/-! ## Stage 1: the `ℂ`-Schur lemma

A finite-dimensional division algebra over `ℂ` is trivial: `ℂ`, being
algebraically closed, has no proper finite (commutative or not) extension.
This is Mathlib's own `IsAlgClosed.algebraMap_bijective_of_isIntegral`,
specialized and repackaged. -/

section ComplexSchur

/-- **The `ℂ`-Schur lemma.** If `E` is a finite-dimensional division algebra
over `ℂ`, then `algebraMap ℂ E` is surjective (in fact bijective, injectivity
being automatic): every element of `E` is already a scalar. -/
theorem algebraMap_complex_surjective {E : Type} [DivisionRing E] [Algebra ℂ E]
    [FiniteDimensional ℂ E] : Function.Surjective (algebraMap ℂ E) :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral.2

end ComplexSchur

/-! ## Central complex embeddings

The form of the `ℂ`-Schur lemma actually needed below: given a ring `A` with
an `ℝ`-algebra structure and an element `I' : A` with `I' * I' = -1` that is
*central* (commutes with all of `A`, not just with itself), the associated
`ℝ`-algebra map `ℂ →ₐ[ℝ] A` (`Complex.liftAux`) is automatically bijective
once `A` is a finite-dimensional domain over `ℝ`. -/

section CentralComplex

/-- **Central complex embeddings are bijective.** If `A` is a finite
dimensional `ℝ`-algebra, a domain, and `I' : A` satisfies `I' * I' = -1` and
is central (commutes with all of `A`), then the associated map
`Complex.liftAux I' hI : ℂ →ₐ[ℝ] A` is bijective.

Proof sketch: `K := (Complex.liftAux I' hI).range` is (as the range of an
injective map out of a field) a copy of `ℂ`, hence a field, and — being
central by hypothesis — makes `A` into a finite-dimensional `K`-algebra via
`RingHom.toAlgebra'`; since `K` is algebraically closed (transported from
`ℂ`), the `ℂ`-Schur lemma (applied with base field `K`) forces `K = A`. -/
theorem bijective_liftAux_of_central {A : Type} [Ring A] [Algebra ℝ A] [IsDomain A]
    [FiniteDimensional ℝ A] (I' : A) (hI : I' * I' = -1)
    (hcen : ∀ x : A, I' * x = x * I') : Function.Bijective (Complex.liftAux I' hI) := by
  set f : ℂ →ₐ[ℝ] A := Complex.liftAux I' hI with hfdef
  set K : Subalgebra ℝ A := f.range with hKdef
  have e : ℂ ≃ₐ[ℝ] K := AlgEquiv.ofInjectiveField f
  have hIsField : IsField K := MulEquiv.isField (Field.toIsField ℂ) e.symm.toMulEquiv
  letI : Field K := hIsField.toField
  have hcenK : ∀ c : A, c ∈ K → ∀ x : A, c * x = x * c := by
    have hsub : K ≤ Subalgebra.centralizer ℝ (Set.univ : Set A) := by
      rw [hKdef]
      rintro _ ⟨c, rfl⟩
      rw [Subalgebra.mem_centralizer_iff ℝ]
      intro x _
      show x * f c = f c * x
      rw [hfdef, Complex.liftAux_apply]
      have h1 : algebraMap ℝ A c.re * x = x * algebraMap ℝ A c.re := Algebra.commutes _ _
      have h2 : (c.im • I') * x = x * (c.im • I') := by
        rw [smul_mul_assoc, mul_smul_comm, hcen]
      rw [add_mul, mul_add, h1, h2]
    intro c hc x
    exact ((Subalgebra.mem_centralizer_iff ℝ).mp (hsub hc) x (Set.mem_univ x)).symm
  letI : Algebra K A := (Subalgebra.val K).toAlgebra' (fun c x => hcenK (↑c) c.2 x)
  haveI hST : IsScalarTower ℝ K A := ⟨by
    intro r c x
    show (Subalgebra.val K) (r • c) * x = r • ((Subalgebra.val K) c * x)
    exact smul_mul_assoc r (Subalgebra.val K c) x⟩
  haveI hMF : Module.Finite K A := by
    have hRD : Module.Finite ℝ A := inferInstance
    rw [Module.finite_def, Submodule.fg_def] at hRD ⊢
    obtain ⟨S, hSfin, hSgen⟩ := hRD
    have hmemS : ∀ x : A, x ∈ Submodule.span ℝ S := fun x => hSgen.ge Submodule.mem_top
    exact ⟨S, hSfin, top_unique fun x _ => Submodule.span_le_restrictScalars ℝ K S (hmemS x)⟩
  haveI : IsAlgClosed (↥K) := IsAlgClosed.of_ringEquiv ℂ (↥K) e.toRingEquiv
  haveI hII : Algebra.IsIntegral (↥K) A := @Algebra.IsIntegral.of_finite (↥K) A _ _ _ hMF
  have hbij : Function.Bijective (algebraMap K A) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hKtop : K = ⊤ := by
    apply Algebra.eq_top_iff.mpr
    intro x
    obtain ⟨c, hc⟩ := hbij.2 x
    have hcx : (c : A) = x := hc
    exact hcx ▸ c.2
  refine ⟨f.toRingHom.injective, ?_⟩
  rw [← AlgHom.range_eq_top f]
  exact hKtop

/-- Bundled `AlgEquiv` form of `bijective_liftAux_of_central`. -/
theorem nonempty_algEquiv_complex_of_central {A : Type} [Ring A] [Algebra ℝ A] [IsDomain A]
    [FiniteDimensional ℝ A] (I' : A) (hI : I' * I' = -1) (hcen : ∀ x : A, I' * x = x * I') :
    Nonempty (ℂ ≃ₐ[ℝ] A) :=
  ⟨AlgEquiv.ofBijective (Complex.liftAux I' hI) (bijective_liftAux_of_central I' hI hcen)⟩

end CentralComplex

/-! ## Stage 2: the eigenspace decomposition

Fix `i : D` with `i * i = -1`. Conjugation `x ↦ i * x * i` is an `ℝ`-linear
involution of `D` (since `i * i = -1`), splitting `D` into its `-1` and `+1`
eigenspaces `plus i` (the centralizer of `i`, a subalgebra containing `i`)
and `minus i` (the anti-centralizer, a submodule). -/

section Eigenspace

variable {D : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

/-- The centralizer of `i`: elements of `D` commuting with `i`. A subalgebra,
containing `i` itself. -/
def plus (i : D) : Subalgebra ℝ D := Subalgebra.centralizer ℝ {i}

omit [FiniteDimensional ℝ D] in
theorem mem_plus_iff {i x : D} : x ∈ plus i ↔ i * x = x * i := by
  rw [plus, Subalgebra.mem_centralizer_iff]
  simp

omit [FiniteDimensional ℝ D] in
theorem i_mem_plus (i : D) : i ∈ plus i := mem_plus_iff.mpr rfl

omit [FiniteDimensional ℝ D] in
/-- The `ℝ`-linear map `x ↦ i * x + x * i`, whose kernel is `minus i`. -/
def antiCommLM (i : D) : D →ₗ[ℝ] D where
  toFun x := i * x + x * i
  map_add' x y := by
    show i * (x + y) + (x + y) * i = i * x + x * i + (i * y + y * i)
    rw [mul_add, add_mul]; abel
  map_smul' r x := by
    show i * (r • x) + (r • x) * i = r • (i * x + x * i)
    rw [mul_smul_comm, smul_mul_assoc, smul_add]

/-- The anti-centralizer of `i`: elements of `D` anticommuting with `i`.
An `ℝ`-submodule (not, in general, a subalgebra). -/
def minus (i : D) : Submodule ℝ D := LinearMap.ker (antiCommLM i)

omit [FiniteDimensional ℝ D] in
theorem mem_minus_iff {i x : D} : x ∈ minus i ↔ i * x = -(x * i) := by
  rw [minus, LinearMap.mem_ker]
  show i * x + x * i = 0 ↔ i * x = -(x * i)
  exact add_eq_zero_iff_eq_neg

omit [FiniteDimensional ℝ D] in
/-- The `+1`-projection `x ↦ (x - i*x*i)/2`, landing in `plus i`. -/
noncomputable def projPlus (i x : D) : D := (2 : ℝ)⁻¹ • (x - i * x * i)

omit [FiniteDimensional ℝ D] in
/-- The `-1`-projection `x ↦ (x + i*x*i)/2`, landing in `minus i`. -/
noncomputable def projMinus (i x : D) : D := (2 : ℝ)⁻¹ • (x + i * x * i)

omit [FiniteDimensional ℝ D] in
theorem projPlus_add_projMinus (i x : D) : projPlus i x + projMinus i x = x := by
  unfold projPlus projMinus
  rw [← smul_add, show (x - i * x * i) + (x + i * x * i) = (2 : ℝ) • x by rw [two_smul]; abel,
    smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

omit [FiniteDimensional ℝ D] in
theorem projPlus_mem_plus {i : D} (hi : i * i = -1) (x : D) : projPlus i x ∈ plus i := by
  rw [mem_plus_iff]
  unfold projPlus
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  linear_combination (norm := noncomm_ring) (i * x) * hi - hi * (x * i)

omit [FiniteDimensional ℝ D] in
theorem projMinus_mem_minus {i : D} (hi : i * i = -1) (x : D) : projMinus i x ∈ minus i := by
  rw [mem_minus_iff]
  unfold projMinus
  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg]
  congr 1
  linear_combination (norm := noncomm_ring) hi * (x * i) + (i * x) * hi

omit [FiniteDimensional ℝ D] in
/-- **Disjointness of the eigenspaces**: `plus i ⊓ minus i = ⊥`, since `i` is
invertible (a nonzero element of a division ring). -/
theorem eq_zero_of_mem_plus_of_mem_minus {i x : D} (hi0 : i ≠ 0) (hp : x ∈ plus i)
    (hm : x ∈ minus i) : x = 0 := by
  rw [mem_plus_iff] at hp
  rw [mem_minus_iff] at hm
  rw [hp] at hm
  have hxi : x * i = 0 := by
    have hsum : x * i + x * i = 0 := by nth_rewrite 1 [hm]; abel
    have h2 : (2 : ℝ) • (x * i) = 0 := by rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rcases mul_eq_zero.mp hxi with h | h
  · exact h
  · exact absurd h hi0

omit [FiniteDimensional ℝ D] in
theorem algebraMap_mem_plus (i : D) (r : ℝ) : algebraMap ℝ D r ∈ plus i :=
  mem_plus_iff.mpr (Algebra.commutes r i).symm

end Eigenspace

/-! ## Stage 2, continued: `plus i` is a division ring isomorphic to `ℂ`

`plus i` is closed under (ambient) inversion (hence a division ring, via
`divisionRingOfFiniteDimensional`), and — since `i` is central *in* `plus i`
by construction — is a copy of `ℂ`: every element of `plus i` is `a + b*i`
for `a b : ℝ`. -/

section PlusComplex

variable {D : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
/-- Inverses (computed in the ambient division ring `D`) of nonzero elements
of `plus i` remain in `plus i`. -/
theorem inv_mem_plus {i x : D} (hx : x ∈ plus i) : x⁻¹ ∈ plus i := by
  rw [mem_plus_iff] at hx ⊢
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have wayA : x⁻¹ * (i * x) * x⁻¹ = i * x⁻¹ := by
      rw [hx, ← mul_assoc x⁻¹ x i, inv_mul_cancel₀ hx0, one_mul]
    have wayB : x⁻¹ * (i * x) * x⁻¹ = x⁻¹ * i := by
      rw [← mul_assoc x⁻¹ i x, mul_assoc (x⁻¹ * i) x x⁻¹, mul_inv_cancel₀ hx0, mul_one]
    rw [← wayA, wayB]

/-- **`plus i` is a division ring** (kept as a `def`, not a global instance,
to avoid diamonds — assign it locally with `letI` at the use site, matching
`Superfusion.Frobenius.elementField`). -/
@[implicit_reducible]
noncomputable def plusDivisionRing (i : D) : DivisionRing (plus i) :=
  divisionRingOfFiniteDimensional ℝ (plus i)

/-- **`plus i` is a copy of `ℂ`**: every element is `a + b • i` for
`a b : ℝ`. The heart of the argument: `i`, viewed inside `plus i`, is
*central* there (`plus i` was built exactly as the things commuting with
`i`), so `bijective_liftAux_of_central` applies with `A := plus i`. -/
theorem exists_eq_add_smul_of_mem_plus {i : D} (hi : i * i = -1) {x : D} (hx : x ∈ plus i) :
    ∃ a b : ℝ, x = algebraMap ℝ D a + b • i := by
  set I' : plus i := ⟨i, i_mem_plus i⟩ with hI'def
  have hI' : I' * I' = -1 := Subtype.ext hi
  have hcen' : ∀ y : plus i, I' * y = y * I' := fun y => Subtype.ext (mem_plus_iff.mp y.2)
  obtain ⟨z, hz⟩ := (bijective_liftAux_of_central I' hI' hcen').2 (⟨x, hx⟩ : plus i)
  refine ⟨z.re, z.im, ?_⟩
  have hz' := congrArg (Subtype.val) hz
  rw [Complex.liftAux_apply] at hz'
  simpa using hz'.symm

end PlusComplex

/-! ## Stage 3: the quaternion branch

Assuming `minus i ≠ ⊥`, pick a nonzero `j₀ ∈ minus i`. Its square lands in
`plus i` (hence is `a + b*i`); conjugating `j₀²` by `j₀` shows `b = 0`, so
`j₀² = c` for some real `c`, and `c < 0` (else `j₀` would be a real multiple
of `1`, forcing `j₀ ∈ plus i ⊓ minus i = 0`). Normalizing
`j := (√(-c))⁻¹ • j₀` gives `j² = -1` and `i * j = -(j * i)`, from which
`D = ℝ-span {1, i, j, i*j}` and the quaternion embedding follows. -/

section Quaternion

variable {D : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
/-- `j₀²` commutes with `i`, i.e. lies in `plus i`. -/
theorem sq_mem_plus_of_mem_minus {i j0 : D} (hj0 : j0 ∈ minus i) : j0 * j0 ∈ plus i := by
  rw [mem_plus_iff]
  have hj := mem_minus_iff.mp hj0
  linear_combination (norm := noncomm_ring) hj * j0 - j0 * hj

/-- **`j₀² = c` for a real `c < 0`**, when `i * i = -1`, `j₀ ∈ minus i`,
`j₀ ≠ 0`: the "imaginary part" of `j₀² ∈ plus i` (w.r.t. `1, i`) vanishes by
conjugating `j₀ * j₀ = a + b • i` by `j₀` itself (trivial on the left,
picking up a sign flip on `i` on the right), and `c ≠ 0` since `j₀ ≠ 0`,
`c > 0` being excluded since it would force `j₀ = ± √c` into
`plus i ⊓ minus i = 0`. -/
theorem sq_eq_algebraMap_neg_of_mem_minus {i : D} (hi : i * i = -1) {j0 : D}
    (hj0 : j0 ∈ minus i) (hj0ne : j0 ≠ 0) (hi0 : i ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ j0 * j0 = algebraMap ℝ D c := by
  obtain ⟨a, b, hab⟩ := exists_eq_add_smul_of_mem_plus hi (sq_mem_plus_of_mem_minus hj0)
  have hj : i * j0 = -(j0 * i) := mem_minus_iff.mp hj0
  -- `b = 0`.
  have hb : b = 0 := by
    have key : j0 * (j0 * j0) = (j0 * j0) * j0 := (mul_assoc j0 j0 j0).symm
    rw [hab] at key
    have expand1 : j0 * (algebraMap ℝ D a + b • i) = algebraMap ℝ D a * j0 + b • (j0 * i) := by
      rw [mul_add, Algebra.commutes, mul_smul_comm]
    have expand2 : (algebraMap ℝ D a + b • i) * j0 = algebraMap ℝ D a * j0 + b • (i * j0) := by
      rw [add_mul, smul_mul_assoc]
    rw [expand1, expand2] at key
    have hcancel : b • (j0 * i) = b • (i * j0) := add_left_cancel key
    rw [hj, smul_neg] at hcancel
    have hb2 : ((2 : ℝ) * b) • (j0 * i) = 0 := by
      rw [mul_smul, two_smul]
      nth_rewrite 2 [hcancel]
      abel
    rcases smul_eq_zero.mp hb2 with h | h
    · linarith
    · exact absurd h (mul_ne_zero hj0ne hi0)
  rw [hb, zero_smul, add_zero] at hab
  -- `c := a < 0`.
  refine ⟨a, ?_, hab⟩
  rcases lt_trichotomy a 0 with h | h | h
  · exact h
  · exact absurd (h ▸ hab : j0 * j0 = algebraMap ℝ D (0 : ℝ)) (by
      rw [map_zero]
      exact fun hzero => hj0ne (mul_self_eq_zero.mp hzero))
  · exfalso
    have hsq' : (j0 - algebraMap ℝ D (Real.sqrt a)) * (j0 + algebraMap ℝ D (Real.sqrt a)) = 0 := by
      have hcomm : algebraMap ℝ D (Real.sqrt a) * j0 = j0 * algebraMap ℝ D (Real.sqrt a) :=
        Algebra.commutes _ _
      have heq : (j0 - algebraMap ℝ D (Real.sqrt a)) * (j0 + algebraMap ℝ D (Real.sqrt a))
          = j0 * j0 - algebraMap ℝ D (Real.sqrt a) * algebraMap ℝ D (Real.sqrt a) := by
        linear_combination (norm := noncomm_ring) -hcomm
      rw [heq, hab, ← map_mul, Real.mul_self_sqrt h.le, sub_self]
    rcases mul_eq_zero.mp hsq' with h' | h'
    · have heq2 : j0 = algebraMap ℝ D (Real.sqrt a) := sub_eq_zero.mp h'
      exact hj0ne (eq_zero_of_mem_plus_of_mem_minus hi0
        (heq2 ▸ algebraMap_mem_plus i (Real.sqrt a)) hj0)
    · have heq2 : j0 = -algebraMap ℝ D (Real.sqrt a) := eq_neg_of_add_eq_zero_left h'
      exact hj0ne (eq_zero_of_mem_plus_of_mem_minus hi0
        (heq2 ▸ neg_mem (algebraMap_mem_plus i (Real.sqrt a))) hj0)

/-- **Normalization**: from `i * i = -1` and a nonzero `j₀ ∈ minus i`,
produce `j` with `j * j = -1`, `i * j = -(j * i)`, `j ≠ 0`. -/
theorem exists_normalized_of_mem_minus {i : D} (hi : i * i = -1) {j0 : D}
    (hj0 : j0 ∈ minus i) (hj0ne : j0 ≠ 0) (hi0 : i ≠ 0) :
    ∃ j : D, j * j = -1 ∧ i * j = -(j * i) ∧ j ≠ 0 := by
  obtain ⟨c, hc0, hsq⟩ := sq_eq_algebraMap_neg_of_mem_minus hi hj0 hj0ne hi0
  have hj0i : i * j0 = -(j0 * i) := mem_minus_iff.mp hj0
  set r : ℝ := (Real.sqrt (-c))⁻¹ with hrdef
  have hrpos : 0 < Real.sqrt (-c) := Real.sqrt_pos.mpr (by linarith)
  have hrne : r ≠ 0 := inv_ne_zero hrpos.ne'
  refine ⟨r • j0, ?_, ?_, smul_ne_zero hrne hj0ne⟩
  · have hmul : (r • j0) * (r • j0) = (r * r) • (j0 * j0) := by rw [smul_mul_smul_comm]
    rw [hmul, hsq, Algebra.smul_def, ← map_mul]
    have hrr : r * r * c = -1 := by
      rw [hrdef]
      generalize hsdef : Real.sqrt (-c) = s at hrpos
      have hsne : s ≠ 0 := hrpos.ne'
      have hc' : c = -(s * s) := by
        rw [show s * s = -c from hsdef ▸ Real.mul_self_sqrt (by linarith)]; ring
      rw [hc']; field_simp
    rw [hrr, map_neg, map_one]
  · rw [smul_mul_assoc, mul_smul_comm, hj0i, smul_neg]

omit [FiniteDimensional ℝ D] in
/-- For `q ∈ minus i` and `j` with `i * j = -(j * i)`,
`q * (-j) ∈ plus i`: `minus i` is exactly `plus i` right-multiplied by `j`. -/
theorem mul_neg_mem_plus_of_mem_minus {i j q : D} (hij : i * j = -(j * i))
    (hq : q ∈ minus i) : q * (-j) ∈ plus i := by
  rw [mem_plus_iff]
  have hqi : i * q = -(q * i) := mem_minus_iff.mp hq
  linear_combination (norm := noncomm_ring) hqi * (-j) + q * hij

omit [FiniteDimensional ℝ D] [Algebra ℝ D] in
/-- Every `q ∈ minus i` factors as `(q * (-j)) * j` with `q * (-j) ∈ plus i`. -/
theorem eq_mul_of_mem_minus {j q : D} (hj : j * j = -1) :
    q = (q * (-j)) * j := by
  linear_combination (norm := noncomm_ring) q * hj

/-- **`D` is spanned over `ℝ` by `1, i, j, i*j`.** Combines the direct-sum
decomposition (`projPlus_add_projMinus`) with `exists_eq_add_smul_of_mem_plus`
applied twice (once to the `plus i`-part, once to the `plus i`-part of the
`minus i`-part, factored through `j`). -/
theorem span_eq_top {i j : D} (hi : i * i = -1) (hj : j * j = -1) (hij : i * j = -(j * i)) :
    Submodule.span ℝ (Set.range (![1, i, j, i * j] : Fin 4 → D)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, b, hab⟩ := exists_eq_add_smul_of_mem_plus hi (projPlus_mem_plus hi x)
  set p : D := (projMinus i x) * (-j) with hpdef
  have hpmem : p ∈ plus i := mul_neg_mem_plus_of_mem_minus hij (projMinus_mem_minus hi x)
  obtain ⟨c, d, hcd⟩ := exists_eq_add_smul_of_mem_plus hi hpmem
  have hmeq : projMinus i x = p * j := eq_mul_of_mem_minus hj
  have hx : x = algebraMap ℝ D a + b • i + (algebraMap ℝ D c + d • i) * j := by
    rw [← projPlus_add_projMinus i x, hab, hmeq, hcd]
  rw [hx]
  have h1 : (1 : D) ∈ Submodule.span ℝ (Set.range (![1, i, j, i * j] : Fin 4 → D)) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hi' : i ∈ Submodule.span ℝ (Set.range (![1, i, j, i * j] : Fin 4 → D)) :=
    Submodule.subset_span ⟨1, rfl⟩
  have hj' : j ∈ Submodule.span ℝ (Set.range (![1, i, j, i * j] : Fin 4 → D)) :=
    Submodule.subset_span ⟨2, rfl⟩
  have hij' : i * j ∈ Submodule.span ℝ (Set.range (![1, i, j, i * j] : Fin 4 → D)) :=
    Submodule.subset_span ⟨3, rfl⟩
  have haM : algebraMap ℝ D a = a • (1 : D) := by rw [Algebra.smul_def, mul_one]
  have hcM : algebraMap ℝ D c = c • (1 : D) := by rw [Algebra.smul_def, mul_one]
  have hexp : (algebraMap ℝ D c + d • i) * j = c • j + d • (i * j) := by
    rw [add_mul, smul_mul_assoc, hcM, smul_mul_assoc, one_mul]
  rw [haM, hexp]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b hi'))
    (Submodule.add_mem _ (Submodule.smul_mem _ c hj') (Submodule.smul_mem _ d hij'))

/-- **The quaternion embedding.** From `i * i = -1`, `j * j = -1`,
`i * j = -(j * i)`, and `D` spanned by `{1, i, j, i*j}`, build the
`ℍ[ℝ] →ₐ[ℝ] D` map via `QuaternionAlgebra.Basis`, and show it is bijective:
injective since `ℍ[ℝ]` is a division ring (hence simple) and `D` is
nontrivial, surjective (via a `finrank` count) since the span forces
`finrank ℝ D ≤ 4 = finrank ℝ ℍ[ℝ] ≤ finrank ℝ D`. -/
theorem nonempty_algEquiv_quaternion_of_relations {i j : D} (hi : i * i = -1)
    (hj : j * j = -1) (hij : i * j = -(j * i)) : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) := by
  let B : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1 : ℝ) :=
    { i := i, j := j, k := i * j,
      i_mul_i := by rw [hi]; simp,
      j_mul_j := by rw [hj]; simp,
      i_mul_j := rfl,
      j_mul_i := by simp only [zero_smul, zero_sub]; rw [hij, neg_neg] }
  let φ : ℍ[ℝ] →ₐ[ℝ] D := B.liftHom
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hle4 : Module.finrank ℝ D ≤ 4 := by
    have := finrank_le_of_span_eq_top (span_eq_top hi hj hij)
    simpa using this
  have heq : Module.finrank ℝ ℍ[ℝ] = Module.finrank ℝ D := by
    have hge4 : Module.finrank ℝ ℍ[ℝ] ≤ Module.finrank ℝ D :=
      LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
    rw [Quaternion.finrank_eq_four] at hge4 ⊢
    omega
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) heq).mp hinj⟩
  exact ⟨AlgEquiv.ofBijective φ hbij⟩

/-- **The quaternion branch, bundled.** If `i * i = -1` and `minus i ≠ ⊥`,
then `D ≅ ℍ[ℝ]` as `ℝ`-algebras. -/
theorem nonempty_algEquiv_quaternion_of_ne_bot {i : D} (hi : i * i = -1) (hi0 : i ≠ 0)
    (hne : minus i ≠ ⊥) : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) := by
  obtain ⟨j0, hj0, hj0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨j, hj, hij, -⟩ := exists_normalized_of_mem_minus hi hj0 hj0ne hi0
  exact nonempty_algEquiv_quaternion_of_relations hi hj hij

end Quaternion

/-! ## Stage 4: the trichotomy -/

section Trichotomy

variable {D : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
/-- If `minus i = ⊥`, then `plus i = ⊤`: every `x` decomposes as
`projPlus i x + projMinus i x` with the second summand `0`. -/
theorem plus_eq_top_of_minus_eq_bot {i : D} (hi : i * i = -1) (h : minus i = ⊥) :
    plus i = ⊤ := by
  apply Algebra.eq_top_iff.mpr
  intro x
  have hpm := projPlus_add_projMinus i x
  have hm0 : projMinus i x = 0 := by
    have hmem := projMinus_mem_minus hi x
    rw [h] at hmem
    exact hmem
  rw [hm0, add_zero] at hpm
  rw [← hpm]
  exact projPlus_mem_plus hi x

/-- **The trichotomy: Frobenius' theorem.** Every finite-dimensional
associative division algebra `D` over `ℝ` is `ℝ`-algebra isomorphic to
`ℝ`, `ℂ`, or `ℍ[ℝ]`. -/
theorem frobenius_trichotomy (D : Type) [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  by_cases htop : (⊥ : Subalgebra ℝ D) = ⊤
  · exact Or.inl ⟨(Subalgebra.topEquiv (R := ℝ) (A := D)).symm.trans
      ((Subalgebra.equivOfEq ⊤ ⊥ htop.symm).trans (Algebra.botEquiv ℝ D))⟩
  · obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_of_ne_top htop
    have hi0 : i ≠ 0 := fun h => by simp [h] at hi
    by_cases hbot : minus i = ⊥
    · refine Or.inr (Or.inl ?_)
      have hptop : plus i = ⊤ := plus_eq_top_of_minus_eq_bot hi hbot
      have hcen : ∀ x : D, i * x = x * i :=
        fun x => mem_plus_iff.mp (hptop ▸ Algebra.mem_top)
      exact ⟨(nonempty_algEquiv_complex_of_central i hi hcen).some.symm⟩
    · exact Or.inr (Or.inr ⟨(nonempty_algEquiv_quaternion_of_ne_bot hi hi0 hbot).some.symm⟩)

end Trichotomy

/-! ## The central refinement

`Algebra.IsCentral ℝ D` excludes the `ℂ` case: `ℂ`'s center (over `ℝ`) is all
of `ℂ`, not `ℝ · 1`. -/

section Central

/-- `ℂ` is not a central `ℝ`-algebra: its center is all of `ℂ`
(commutative), which is strictly bigger than `ℝ · 1` (witnessed by `I`). -/
theorem not_isCentral_complex : ¬ Algebra.IsCentral ℝ ℂ := by
  intro h
  have hI : Complex.I ∈ Subalgebra.center ℝ ℂ := by
    rw [Subalgebra.center_eq_top ℝ ℂ]; trivial
  rw [Algebra.IsCentral.center_eq_bot ℝ ℂ] at hI
  obtain ⟨r, hr⟩ := hI
  have him := congrArg Complex.im hr
  simp at him

/-- **Frobenius' theorem, central form.** A finite-dimensional *central*
`ℝ`-division algebra is `ℝ`-algebra isomorphic to `ℝ` or `ℍ[ℝ]` (`ℂ` is
excluded, not being central). -/
theorem frobenius_central (D : Type) [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] [Algebra.IsCentral ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  rcases frobenius_trichotomy D with h | h | h
  · exact Or.inl h
  · exact absurd (Algebra.IsCentral.of_algEquiv ℝ D ℂ h.some) not_isCentral_complex
  · exact Or.inr h

end Central

end Frobenius

end Superfusion
