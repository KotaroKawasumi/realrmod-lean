/-
Superfusion / Super / MatrixSuperTensor

Milestone M7f-4b (part i): **matrix stabilization commutes with the
graded tensor product** — the graded algebra map

  `matrixTensorSuperHom : (matrixGradingA π 𝒜) ᵍ⊗ ℬ
                            →ₐ Matrix n n (𝒜 ᵍ⊗ ℬ)`,
  `(M ᵍ⊗ b) ↦ (entries sgn(π s·|b|) · (M_{rs} ᵍ⊗ b))`,

with the **column-parity sign** forced by multiplicativity (the same
phenomenon as the sign-adjusted diagonal of M7d-4b-2): the naive
entrywise map fails because the Koszul sign of `b` against a matrix
sees the *matrix* degree, while entrywise it sees the *entry* degree
— they differ by the index parities.

Construction by the universal property: entrywise `includeLeft` on
matrices, and the signed diagonal embedding of `B` (multiplicative
because the sign is a character in `|b|`, per column).  Part ii:
bijectivity by an explicit entrywise inverse (`single` composed with
the column twist undoing the sign), the graded equivalence
`matrixTensorSuper`, and the bundled versions `matrixSuperGtensor`
and `matrixSuperGtensorRight` (`M_{p|q}(P) ᵍ⊗ Q ≅ M_{p|q}(P ᵍ⊗ Q)`,
both factors), which make the Brauer–Wall product well defined on
classes.
-/
import Superfusion.Super.MatrixSuperCoeff
import Superfusion.Super.TensorCoherence
import Superfusion.Super.BWTransitivity

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (π : n → ZMod 2)
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-! ### Sign and scalar helpers -/

private theorem sgn_mt_anti : ∀ j i r s : ZMod 2,
    ((sgn (j * i) : ℤˣ) : ℤ) * (((sgn (r * j) : ℤˣ) : ℤ)
        * ((sgn (j * (i + r + s)) : ℤˣ) : ℤ))
      = ((sgn (s * j) : ℤˣ) : ℤ) := by
  decide

private theorem sgn_mt_mul : ∀ j j' s : ZMod 2,
    ((sgn (s * j) : ℤˣ) : ℤ) * ((sgn (s * j') : ℤˣ) : ℤ)
      = ((sgn (s * (j + j')) : ℤˣ) : ℤ) := by
  decide

private theorem zmod2_mt_index : ∀ j s : ZMod 2, j + s + s = j := by
  decide

private theorem zmod2_mt_entry : ∀ i j r s : ZMod 2,
    (i + r + s) + j = (i + j) + r + s := by
  decide

private theorem gtmul_one_one :
    ((1 : A) ᵍ⊗ₜ[K] (1 : B) : 𝒜 ᵍ⊗[K] ℬ) = 1 := by
  rw [show ((1 : A) ᵍ⊗ₜ[K] (1 : B) : 𝒜 ᵍ⊗[K] ℬ)
      = of K 𝒜 ℬ ((1 : A) ⊗ₜ[K] (1 : B)) from rfl,
    show ((1 : A) ⊗ₜ[K] (1 : B) : A ⊗[K] B) = 1 from
      Algebra.TensorProduct.one_def.symm,
    of_one]

private theorem gtmul_ksmul' (c : K) (x : A) (y : B) :
    (x ᵍ⊗ₜ[K] (c • y) : 𝒜 ᵍ⊗[K] ℬ) = c • (x ᵍ⊗ₜ[K] y) := by
  rw [show ((x ᵍ⊗ₜ[K] (c • y) : 𝒜 ᵍ⊗[K] ℬ))
      = of K 𝒜 ℬ (x ⊗ₜ[K] (c • y)) from rfl,
    TensorProduct.tmul_smul, map_smul]

private theorem uzpow_to_sgn (e : ZMod 2) (z : 𝒜 ᵍ⊗[K] ℬ) :
    (-1 : ℤˣ) ^ e • z = ((sgn e : ℤˣ) : ℤ) • z := by
  rw [← sgn_eq_neg_one_uzpow, Units.smul_def]

/-! ### The two inclusions -/

/-- Entrywise `includeLeft`: `Matrix n n A →ₐ Matrix n n (A ᵍ⊗ B)`. -/
noncomputable def matrixInclLeft :
    Matrix n n A →ₐ[K] Matrix n n (𝒜 ᵍ⊗[K] ℬ) :=
  (includeLeft 𝒜 ℬ).mapMatrix

theorem matrixInclLeft_apply (M : Matrix n n A) (r s : n) :
    matrixInclLeft 𝒜 ℬ M r s = (M r s) ᵍ⊗ₜ[K] (1 : B) := rfl

theorem matrixInclLeft_mem {i : ZMod 2} {M : Matrix n n A}
    (hM : M ∈ matrixGradingA π 𝒜 i) :
    matrixInclLeft 𝒜 ℬ M
      ∈ matrixGradingA π (tensorGrading 𝒜 ℬ) i := by
  intro r s
  rw [matrixInclLeft_apply]
  have h := tmul_mem_tensorGrading 𝒜 ℬ (hM r s)
    (SetLike.one_mem_graded ℬ)
  rwa [add_zero] at h

/-- The signed diagonal value: for general `b`, the diagonal matrix
with `(s, s)` entry `1 ᵍ⊗ b₀ + sgn(π s)·(1 ᵍ⊗ b₁)`. -/
noncomputable def sdiag (b : B) : Matrix n n (𝒜 ᵍ⊗[K] ℬ) :=
  Matrix.diagonal fun s =>
    (1 : A) ᵍ⊗ₜ[K] (evenPart ℬ b)
      + ((sgn (π s) : ℤˣ) : ℤ) • ((1 : A) ᵍ⊗ₜ[K] (oddPart ℬ b))

omit [Fintype n] in
theorem sdiag_of_mem {j : ZMod 2} {b : B} (hb : b ∈ ℬ j) :
    sdiag π 𝒜 ℬ b = Matrix.diagonal fun s =>
      ((sgn (π s * j) : ℤˣ) : ℤ) • ((1 : A) ᵍ⊗ₜ[K] b) := by
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [sdiag]
    congr 1
    funext s
    rw [evenPart_of_mem_zero ℬ hb, oddPart_of_mem_zero ℬ hb,
      gtmul_zero, smul_zero, add_zero, mul_zero, sgn_zero,
      show (((1 : ℤˣ) : ℤ)) = 1 from rfl, one_smul]
  · rw [sdiag]
    congr 1
    funext s
    rw [evenPart_of_mem_one ℬ hb, oddPart_of_mem_one ℬ hb,
      gtmul_zero, zero_add, mul_one]

omit [Fintype n] in
private theorem sdiag_one : sdiag π 𝒜 ℬ (1 : B) = 1 := by
  rw [sdiag_of_mem π 𝒜 ℬ (SetLike.one_mem_graded ℬ),
    show (Matrix.diagonal fun s =>
        ((sgn (π s * 0) : ℤˣ) : ℤ) • ((1 : A) ᵍ⊗ₜ[K] (1 : B))
        : Matrix n n (𝒜 ᵍ⊗[K] ℬ))
      = Matrix.diagonal fun _ => (1 : 𝒜 ᵍ⊗[K] ℬ) from by
      congr 1
      funext s
      rw [mul_zero, sgn_zero, show (((1 : ℤˣ) : ℤ)) = 1 from rfl,
        one_smul, gtmul_one_one 𝒜 ℬ],
    Matrix.diagonal_one]

private theorem sdiag_mul_of_mem {j j' : ZMod 2} {b b' : B}
    (hb : b ∈ ℬ j) (hb' : b' ∈ ℬ j') :
    sdiag π 𝒜 ℬ (b * b') = sdiag π 𝒜 ℬ b * sdiag π 𝒜 ℬ b' := by
  rw [sdiag_of_mem π 𝒜 ℬ hb, sdiag_of_mem π 𝒜 ℬ hb',
    sdiag_of_mem π 𝒜 ℬ (SetLike.mul_mem_graded hb hb'),
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext s
  rw [smul_mul_smul_comm,
    show (((1 : A) ᵍ⊗ₜ[K] b) * ((1 : A) ᵍ⊗ₜ[K] b') : 𝒜 ᵍ⊗[K] ℬ)
      = (1 : A) ᵍ⊗ₜ[K] (b * b') from by
      rw [show ((1 : A) ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)
          = includeRight 𝒜 ℬ b from rfl,
        show ((1 : A) ᵍ⊗ₜ[K] b' : 𝒜 ᵍ⊗[K] ℬ)
          = includeRight 𝒜 ℬ b' from rfl,
        ← map_mul]
      rfl,
    sgn_mt_mul]

omit [Fintype n] in
private theorem sdiag_add (b b' : B) :
    sdiag π 𝒜 ℬ (b + b') = sdiag π 𝒜 ℬ b + sdiag π 𝒜 ℬ b' := by
  refine Matrix.ext fun r s => ?_
  rw [sdiag, sdiag, sdiag, Matrix.add_apply]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq, map_add, map_add, gtmul_add, gtmul_add,
      smul_add]
    abel
  · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs,
      Matrix.diagonal_apply_ne _ hrs, add_zero]

/-- The signed diagonal embedding `B →ₐ Matrix n n (A ᵍ⊗ B)`. -/
noncomputable def matrixInclRight :
    B →ₐ[K] Matrix n n (𝒜 ᵍ⊗[K] ℬ) :=
  AlgHom.ofLinearMap
    { toFun := sdiag π 𝒜 ℬ
      map_add' := sdiag_add π 𝒜 ℬ
      map_smul' := fun c b => by
        rw [RingHom.id_apply]
        refine Matrix.ext fun r s => ?_
        rw [sdiag, sdiag, Matrix.smul_apply]
        by_cases hrs : r = s
        · subst hrs
          rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
            map_smul, map_smul, gtmul_ksmul' 𝒜 ℬ, gtmul_ksmul' 𝒜 ℬ,
            smul_add, smul_comm ((sgn (π r) : ℤˣ) : ℤ) c]
        · rw [Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ hrs,
            smul_zero] }
    (sdiag_one π 𝒜 ℬ)
    (fun b b' => by
      show sdiag π 𝒜 ℬ (b * b') = sdiag π 𝒜 ℬ b * sdiag π 𝒜 ℬ b'
      have hb := evenPart_add_oddPart ℬ b
      have hb' := evenPart_add_oddPart ℬ b'
      conv_lhs => rw [← hb, ← hb']
      conv_rhs => rw [← hb, ← hb']
      rw [add_mul, mul_add, mul_add, sdiag_add, sdiag_add, sdiag_add,
        sdiag_mul_of_mem π 𝒜 ℬ (evenPart_mem ℬ b) (evenPart_mem ℬ b'),
        sdiag_mul_of_mem π 𝒜 ℬ (evenPart_mem ℬ b) (oddPart_mem ℬ b'),
        sdiag_mul_of_mem π 𝒜 ℬ (oddPart_mem ℬ b) (evenPart_mem ℬ b'),
        sdiag_mul_of_mem π 𝒜 ℬ (oddPart_mem ℬ b) (oddPart_mem ℬ b'),
        sdiag_add, sdiag_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add])

theorem matrixInclRight_apply (b : B) :
    matrixInclRight π 𝒜 ℬ b = sdiag π 𝒜 ℬ b := rfl

theorem matrixInclRight_mem {j : ZMod 2} {b : B} (hb : b ∈ ℬ j) :
    matrixInclRight π 𝒜 ℬ b
      ∈ matrixGradingA π (tensorGrading 𝒜 ℬ) j := by
  intro r s
  rw [matrixInclRight_apply, sdiag_of_mem π 𝒜 ℬ hb]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.diagonal_apply_eq]
    refine zsmul_mem ?_ _
    have h := tmul_mem_tensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜) hb
    rwa [zero_add, show j = j + π r + π r from (zmod2_mt_index j (π r)).symm]
      at h
  · rw [Matrix.diagonal_apply_ne _ hrs]
    exact zero_mem _

/-! ### Anticommutation and the lift -/

private theorem matrixTensor_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (M : matrixGradingA π 𝒜 i) (b : ℬ j),
      matrixInclLeft 𝒜 ℬ M * matrixInclRight π 𝒜 ℬ b
        = (-1 : ℤˣ) ^ (j * i) •
          (matrixInclRight π 𝒜 ℬ b * matrixInclLeft 𝒜 ℬ M) := by
  intro i j M b
  rw [matrixInclRight_apply, sdiag_of_mem π 𝒜 ℬ b.2]
  refine Matrix.ext fun r s => ?_
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    matrixInclLeft_apply, mul_smul_comm,
    show (((M : Matrix n n A) r s ᵍ⊗ₜ[K] (1 : B))
        * ((1 : A) ᵍ⊗ₜ[K] (b : B)) : 𝒜 ᵍ⊗[K] ℬ)
      = (M : Matrix n n A) r s ᵍ⊗ₜ[K] (b : B) from
      tmul_one_mul_one_tmul 𝒜 ℬ _ _,
    smul_mul_assoc,
    show ((((1 : A) ᵍ⊗ₜ[K] (b : B))
        * ((M : Matrix n n A) r s ᵍ⊗ₜ[K] (1 : B))) : 𝒜 ᵍ⊗[K] ℬ)
      = ((1 : A) ᵍ⊗ₜ[K] ((⟨(b : B), b.2⟩ : ℬ j) : B))
        * ((((⟨(M : Matrix n n A) r s, M.2 r s⟩
            : 𝒜 (i + π r + π s)) : A)) ᵍ⊗ₜ[K] (1 : B)) from rfl,
    tmul_coe_mul_coe_tmul, one_mul, mul_one, uzpow_to_sgn 𝒜 ℬ,
    smul_smul, ← Units.smul_def, uzpow_to_sgn 𝒜 ℬ, smul_smul, mul_assoc,
    sgn_mt_anti j i (π r) (π s), Units.smul_def]

/-- **Matrix stabilization commutes with `ᵍ⊗`** (M7f-4b, the map):
`(matrixGradingA π 𝒜) ᵍ⊗ ℬ →ₐ Matrix n n (𝒜 ᵍ⊗ ℬ)`. -/
noncomputable def matrixTensorSuperHom :
    ((matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) →ₐ[K]
      Matrix n n (𝒜 ᵍ⊗[K] ℬ) :=
  lift (matrixGradingA π 𝒜) ℬ (matrixInclLeft 𝒜 ℬ)
    (matrixInclRight π 𝒜 ℬ) (matrixTensor_anticommutes π 𝒜 ℬ)

theorem matrixTensorSuperHom_tmul (M : Matrix n n A) (b : B) :
    matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b)
      = matrixInclLeft 𝒜 ℬ M * matrixInclRight π 𝒜 ℬ b :=
  lift_tmul (matrixGradingA π 𝒜) ℬ (matrixInclLeft 𝒜 ℬ)
    (matrixInclRight π 𝒜 ℬ) (matrixTensor_anticommutes π 𝒜 ℬ) M b

/-! ### Homogeneity -/

theorem matrixTensorSuperHom_isHomogeneous :
    IsHomogeneousHom (tensorGrading (matrixGradingA π 𝒜) ℬ)
      (matrixGradingA π (tensorGrading 𝒜 ℬ))
      (matrixTensorSuperHom π 𝒜 ℬ) := by
  intro i z hz
  refine tensorGrading_induction (matrixGradingA π 𝒜) ℬ hz
    (p := fun w => matrixTensorSuperHom π 𝒜 ℬ w
      ∈ matrixGradingA π (tensorGrading 𝒜 ℬ) i)
    ?_ ?_ ?_ ?_
  · intro iM j M b hij hM hb
    rw [matrixTensorSuperHom_tmul]
    exact hij ▸ SetLike.mul_mem_graded (matrixInclLeft_mem π 𝒜 ℬ hM)
      (matrixInclRight_mem π 𝒜 ℬ hb)
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### Bijectivity: the entry formula and the explicit inverse

On a pure tensor `M ᵍ⊗ b` with `b` homogeneous, the map has entries
`sgn(π s·|b|) · (M_{rs} ᵍ⊗ b)`.  The inverse is therefore entrywise
`single`, with the column twist (identity on the even `B`-part,
`sgn (π s)` on the odd part) undoing the sign — no involution or
simplicity argument is needed. -/

theorem matrixTensorSuperHom_apply_of_mem {j : ZMod 2}
    (M : Matrix n n A) {b : B} (hb : b ∈ ℬ j) (r s : n) :
    matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b) r s
      = ((sgn (π s * j) : ℤˣ) : ℤ) • ((M r s) ᵍ⊗ₜ[K] b) := by
  rw [matrixTensorSuperHom_tmul, matrixInclRight_apply,
    sdiag_of_mem π 𝒜 ℬ hb, Matrix.mul_diagonal, matrixInclLeft_apply,
    mul_smul_comm,
    show (((M r s) ᵍ⊗ₜ[K] (1 : B)) * ((1 : A) ᵍ⊗ₜ[K] b) : 𝒜 ᵍ⊗[K] ℬ)
      = (M r s) ᵍ⊗ₜ[K] b from tmul_one_mul_one_tmul 𝒜 ℬ _ _]

/-- The column twist on `B`: identity on the even part, `sgn (π s)`
on the odd part. -/
private noncomputable def colTwistB (s : n) : B →ₗ[K] B :=
  evenPart ℬ + ((sgn (π s) : ℤˣ) : ℤ) • oddPart ℬ

omit [Fintype n] [DecidableEq n] in
private theorem colTwistB_of_mem {j : ZMod 2} {b : B} (hb : b ∈ ℬ j)
    (s : n) :
    colTwistB π ℬ s b = ((sgn (π s * j) : ℤˣ) : ℤ) • b := by
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [colTwistB, LinearMap.add_apply, LinearMap.smul_apply,
      evenPart_of_mem_zero ℬ hb, oddPart_of_mem_zero ℬ hb, smul_zero,
      add_zero, mul_zero, sgn_zero,
      show (((1 : ℤˣ) : ℤ)) = 1 from rfl, one_smul]
  · rw [colTwistB, LinearMap.add_apply, LinearMap.smul_apply,
      evenPart_of_mem_one ℬ hb, oddPart_of_mem_one ℬ hb, zero_add,
      mul_one]

private theorem sum_gtmul {ι : Type*} (t : Finset ι) (f : ι → A)
    (b : B) :
    ((∑ x ∈ t, f x) ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)
      = ∑ x ∈ t, ((f x) ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ) := by
  rw [show ((∑ x ∈ t, f x) ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)
      = of K 𝒜 ℬ ((∑ x ∈ t, f x) ⊗ₜ[K] b) from rfl,
    TensorProduct.sum_tmul, map_sum]

/-- The explicit linear inverse: entrywise `single` with the column
twist. -/
private noncomputable def matrixTensorInv :
    Matrix n n (𝒜 ᵍ⊗[K] ℬ) →ₗ[K] ((matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) :=
  ∑ r : n, ∑ s : n,
    (of K (matrixGradingA π 𝒜) ℬ).toLinearMap
      ∘ₗ TensorProduct.map (Matrix.singleLinearMap K r s)
          (colTwistB π ℬ s)
      ∘ₗ (of K 𝒜 ℬ).symm.toLinearMap
      ∘ₗ Matrix.entryLinearMap K (𝒜 ᵍ⊗[K] ℬ) r s

private theorem matrixTensorInv_term {j : ZMod 2} (M : Matrix n n A)
    {b : B} (hb : b ∈ ℬ j) (r s : n) :
    ((of K (matrixGradingA π 𝒜) ℬ).toLinearMap
        ∘ₗ TensorProduct.map (Matrix.singleLinearMap K r s)
            (colTwistB π ℬ s)
        ∘ₗ (of K 𝒜 ℬ).symm.toLinearMap
        ∘ₗ Matrix.entryLinearMap K (𝒜 ᵍ⊗[K] ℬ) r s)
        (matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b))
      = ((Matrix.single r s (M r s) : Matrix n n A) ᵍ⊗ₜ[K] b
          : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    show Matrix.entryLinearMap K (𝒜 ᵍ⊗[K] ℬ) r s
        (matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b))
      = matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b) r s from rfl,
    matrixTensorSuperHom_apply_of_mem π 𝒜 ℬ M hb r s,
    show (of K 𝒜 ℬ).symm.toLinearMap
        (((sgn (π s * j) : ℤˣ) : ℤ) • ((M r s) ᵍ⊗ₜ[K] b))
      = ((sgn (π s * j) : ℤˣ) : ℤ) • ((M r s) ⊗ₜ[K] b) from rfl,
    map_zsmul (TensorProduct.map (Matrix.singleLinearMap K r s)
      (colTwistB π ℬ s)),
    TensorProduct.map_tmul,
    show Matrix.singleLinearMap K r s (M r s)
      = Matrix.single r s (M r s) from rfl,
    colTwistB_of_mem π ℬ hb s, TensorProduct.tmul_smul]
  have hfinal : (of K (matrixGradingA π 𝒜) ℬ)
      (((sgn (π s * j) : ℤˣ) : ℤ) • (((sgn (π s * j) : ℤˣ) : ℤ)
        • ((Matrix.single r s (M r s) : Matrix n n A) ⊗ₜ[K] b)))
      = ((Matrix.single r s (M r s) : Matrix n n A) ᵍ⊗ₜ[K] b
          : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) := by
    rw [smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]
  exact hfinal

private theorem matrixTensorInv_tmul_of_mem {j : ZMod 2}
    (M : Matrix n n A) {b : B} (hb : b ∈ ℬ j) :
    matrixTensorInv π 𝒜 ℬ (matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b))
      = M ᵍ⊗ₜ[K] b :=
  calc matrixTensorInv π 𝒜 ℬ (matrixTensorSuperHom π 𝒜 ℬ (M ᵍ⊗ₜ[K] b))
      = ∑ r : n, ∑ s : n,
          ((Matrix.single r s (M r s) : Matrix n n A) ᵍ⊗ₜ[K] b
            : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) := by
        rw [matrixTensorInv]
        simp only [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun s _ =>
            matrixTensorInv_term π 𝒜 ℬ M hb r s
    _ = ((∑ r : n, ∑ s : n, Matrix.single r s (M r s)) ᵍ⊗ₜ[K] b
          : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) := by
        rw [sum_gtmul (matrixGradingA π 𝒜) ℬ]
        exact Finset.sum_congr rfl fun r _ =>
          (sum_gtmul (matrixGradingA π 𝒜) ℬ Finset.univ
            (fun s => Matrix.single r s (M r s)) b).symm
    _ = M ᵍ⊗ₜ[K] b := by rw [← Matrix.matrix_eq_sum_single M]

private theorem matrixTensorInv_leftInverse
    (z : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) :
    matrixTensorInv π 𝒜 ℬ (matrixTensorSuperHom π 𝒜 ℬ z) = z := by
  have key : ∀ t : Matrix n n A ⊗[K] B,
      matrixTensorInv π 𝒜 ℬ (matrixTensorSuperHom π 𝒜 ℬ
        (of K (matrixGradingA π 𝒜) ℬ t))
      = of K (matrixGradingA π 𝒜) ℬ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul M b =>
        rw [show of K (matrixGradingA π 𝒜) ℬ (M ⊗ₜ[K] b)
            = M ᵍ⊗ₜ[K] b from rfl]
        have hb := evenPart_add_oddPart ℬ b
        conv_lhs => rw [← hb]
        conv_rhs => rw [← hb]
        rw [gtmul_add, map_add, map_add,
          matrixTensorInv_tmul_of_mem π 𝒜 ℬ M (evenPart_mem ℬ b),
          matrixTensorInv_tmul_of_mem π 𝒜 ℬ M (oddPart_mem ℬ b)]
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  have h := key ((of K (matrixGradingA π 𝒜) ℬ).symm z)
  rwa [symm_of_of] at h

private theorem hom_single_tmul_of_mem (r s : n) (a : A) {j : ZMod 2}
    {b : B} (hb : b ∈ ℬ j) :
    matrixTensorSuperHom π 𝒜 ℬ
        ((Matrix.single r s a : Matrix n n A) ᵍ⊗ₜ[K] b)
      = ((sgn (π s * j) : ℤˣ) : ℤ)
          • Matrix.single r s ((a ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)) := by
  refine Matrix.ext fun u v => ?_
  rw [matrixTensorSuperHom_apply_of_mem π 𝒜 ℬ _ hb u v,
    Matrix.smul_apply]
  by_cases h : u = r ∧ v = s
  · obtain ⟨hu, hv⟩ := h
    subst hu; subst hv
    rw [Matrix.single_apply_same, Matrix.single_apply_same]
  · have h' : ¬(r = u ∧ s = v) := fun hc => h ⟨hc.1.symm, hc.2.symm⟩
    rw [Matrix.single_apply_of_ne r s a u v h',
      Matrix.single_apply_of_ne r s (a ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ) u v h',
      zero_gtmul, smul_zero, smul_zero]

private theorem hom_inv_tmul_of_mem (r s : n) (a : A) {j : ZMod 2}
    {b : B} (hb : b ∈ ℬ j) :
    matrixTensorSuperHom π 𝒜 ℬ
        ((of K (matrixGradingA π 𝒜) ℬ)
          (TensorProduct.map (Matrix.singleLinearMap K r s)
            (colTwistB π ℬ s) (a ⊗ₜ[K] b)))
      = Matrix.single r s ((a ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)) := by
  rw [TensorProduct.map_tmul,
    show Matrix.singleLinearMap K r s a = Matrix.single r s a from rfl,
    colTwistB_of_mem π ℬ hb s, TensorProduct.tmul_smul]
  change matrixTensorSuperHom π 𝒜 ℬ
      (((sgn (π s * j) : ℤˣ) : ℤ)
        • ((Matrix.single r s a : Matrix n n A) ᵍ⊗ₜ[K] b
            : (matrixGradingA π 𝒜) ᵍ⊗[K] ℬ))
    = Matrix.single r s (a ᵍ⊗ₜ[K] b)
  rw [map_zsmul (matrixTensorSuperHom π 𝒜 ℬ),
    hom_single_tmul_of_mem π 𝒜 ℬ r s a hb,
    smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]

private theorem hom_inv_single (r s : n) (x : 𝒜 ᵍ⊗[K] ℬ) :
    matrixTensorSuperHom π 𝒜 ℬ
        ((of K (matrixGradingA π 𝒜) ℬ)
          (TensorProduct.map (Matrix.singleLinearMap K r s)
            (colTwistB π ℬ s) ((of K 𝒜 ℬ).symm x)))
      = Matrix.single r s x := by
  have key : ∀ u : A ⊗[K] B,
      matrixTensorSuperHom π 𝒜 ℬ
          ((of K (matrixGradingA π 𝒜) ℬ)
            (TensorProduct.map (Matrix.singleLinearMap K r s)
              (colTwistB π ℬ s) u))
        = Matrix.single r s (of K 𝒜 ℬ u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero, map_zero, map_zero, Matrix.single_zero]
    | tmul a b =>
        rw [show of K 𝒜 ℬ (a ⊗ₜ[K] b) = a ᵍ⊗ₜ[K] b from rfl]
        have hb := evenPart_add_oddPart ℬ b
        conv_lhs => rw [← hb]
        conv_rhs => rw [← hb]
        rw [TensorProduct.tmul_add, gtmul_add, Matrix.single_add,
          map_add, map_add, map_add,
          hom_inv_tmul_of_mem π 𝒜 ℬ r s a (evenPart_mem ℬ b),
          hom_inv_tmul_of_mem π 𝒜 ℬ r s a (oddPart_mem ℬ b)]
    | add u v hu hv =>
        rw [map_add, map_add, map_add, map_add, Matrix.single_add,
          hu, hv]
  have h := key ((of K 𝒜 ℬ).symm x)
  rwa [symm_of_of] at h

private theorem matrixTensorInv_rightInverse
    (N : Matrix n n (𝒜 ᵍ⊗[K] ℬ)) :
    matrixTensorSuperHom π 𝒜 ℬ (matrixTensorInv π 𝒜 ℬ N) = N := by
  rw [matrixTensorInv]
  simp only [LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Matrix.entryLinearMap_apply]
  refine Eq.trans (Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => hom_inv_single π 𝒜 ℬ r s (N r s)) ?_
  exact (Matrix.matrix_eq_sum_single N).symm

theorem matrixTensorSuperHom_bijective :
    Function.Bijective (matrixTensorSuperHom π 𝒜 ℬ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨matrixTensorInv π 𝒜 ℬ, matrixTensorInv_leftInverse π 𝒜 ℬ,
      matrixTensorInv_rightInverse π 𝒜 ℬ⟩

/-- **Matrix stabilization commutes with `ᵍ⊗`** (M7f-4b):
`M_n(A) ᵍ⊗ B ≃ₐ M_n(A ᵍ⊗ B)`. -/
noncomputable def matrixTensorSuper :
    ((matrixGradingA π 𝒜) ᵍ⊗[K] ℬ) ≃ₐ[K] Matrix n n (𝒜 ᵍ⊗[K] ℬ) :=
  AlgEquiv.ofBijective (matrixTensorSuperHom π 𝒜 ℬ)
    (matrixTensorSuperHom_bijective π 𝒜 ℬ)

/-- The equivalence carries the tensor grading **onto** the matrix
grading of the tensor grading. -/
theorem matrixTensorSuper_map_grading (i : ZMod 2) :
    (tensorGrading (matrixGradingA π 𝒜) ℬ i).map
        (matrixTensorSuper π 𝒜 ℬ).toLinearMap
      = matrixGradingA π (tensorGrading 𝒜 ℬ) i :=
  map_grading_of_bijective (tensorGrading (matrixGradingA π 𝒜) ℬ)
    (matrixGradingA π (tensorGrading 𝒜 ℬ))
    (matrixTensorSuperHom π 𝒜 ℬ)
    (matrixTensorSuperHom_isHomogeneous π 𝒜 ℬ)
    (matrixTensorSuperHom_bijective π 𝒜 ℬ) i

/-! ### Bundled equivalences -/

section Bundled

variable {K : Type*} [CommRing K]

/-- **Matrix stabilization commutes with `ᵍ⊗`**, bundled (left):
`M_{p|q}(P) ᵍ⊗ Q ≅ M_{p|q}(P ᵍ⊗ Q)`. -/
noncomputable def matrixSuperGtensor (P Q : SuperAlgebra K) (p q : ℕ) :
    SuperAlgEquiv ((P.matrixSuper p q).gtensor Q)
      ((P.gtensor Q).matrixSuper p q) :=
  ⟨matrixTensorSuper (sumParity p q) P.grading Q.grading,
    matrixTensorSuper_map_grading (sumParity p q) P.grading Q.grading⟩

/-- Matrix stabilization commutes with `ᵍ⊗` on the right factor:
`P ᵍ⊗ M_{p|q}(Q) ≅ M_{p|q}(P ᵍ⊗ Q)`, via the braiding. -/
noncomputable def matrixSuperGtensorRight (P Q : SuperAlgebra K)
    (p q : ℕ) :
    SuperAlgEquiv (P.gtensor (Q.matrixSuper p q))
      ((P.gtensor Q).matrixSuper p q) :=
  (gtensorComm P (Q.matrixSuper p q)).trans
    ((matrixSuperGtensor Q P p q).trans
      ((gtensorComm Q P).matrixSuper p q))

end Bundled

end Superfusion
