/-
Superfusion / Super / PentagonMatrixTransport

Milestone M7d-5b-4-ii: **the signed-diagonal matrix transport of
intertwiners** — the second amplification of the transport kit.
If `t` intertwines `(φ, φ')` with parity `p`, then the naive
diagonal `diag(t, …, t)` does NOT intertwine the entrywise-mapped
pair (the matrix degree differs from the entry degrees by the index
parities — the same phenomenon as M7f-4b's column-parity sign);
the correct amplification is the **signed diagonal**

  `sdiagAmp π p t := diagonal (fun k => sgn(π k · p) • t)`,

which intertwines `(φ.mapMatrix, φ'.mapMatrix)` with the same
parity: entrywise the sign `sgn(π k p) · sgn((j+π i+π k) p)`
recombines to `sgn(j p) · sgn(π i p)`.  It is homogeneous of degree
`p` and invertible when `t` is (`sgn² = 1`).
-/
import Superfusion.Super.PentagonExtend

namespace Superfusion

open Module

section MatrixTransport

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable {n : Type*} [Fintype n] [DecidableEq n] (π : n → ZMod 2)

/-- The signed diagonal amplification of a homogeneous element. -/
noncomputable def sdiagAmp (p : ZMod 2) (t : B) : Matrix n n B :=
  Matrix.diagonal fun k => ((sgn (π k * p) : ℤˣ) : ℤ) • t

private theorem zmod2_two_mul' : ∀ p c : ZMod 2, p + c + c = p := by decide

omit [GradedAlgebra ℬ] [Fintype n] in
theorem sdiagAmp_mem {p : ZMod 2} {t : B} (htp : t ∈ ℬ p) :
    sdiagAmp π p t ∈ matrixGradingA π ℬ p := by
  intro i k
  by_cases h : i = k
  · subst h
    rw [sdiagAmp, Matrix.diagonal_apply_eq]
    refine zsmul_mem ?_ _
    rw [zmod2_two_mul' p (π i)]
    exact htp
  · rw [sdiagAmp, Matrix.diagonal_apply_ne _ h]
    exact zero_mem _

omit [GradedAlgebra ℬ] in
theorem sdiagAmp_isUnit {p : ZMod 2} {t : B} (ht : IsUnit t) :
    IsUnit (sdiagAmp π p t) := by
  obtain ⟨u, rfl⟩ := ht
  refine ⟨⟨sdiagAmp π p (u : B),
    sdiagAmp π p ((u⁻¹ : Bˣ) : B), ?_, ?_⟩, rfl⟩
  · have hfun : (fun k => (((sgn (π k * p) : ℤˣ) : ℤ) • (u : B))
          * (((sgn (π k * p) : ℤˣ) : ℤ) • ((u⁻¹ : Bˣ) : B)))
        = fun _ => (1 : B) := by
      funext k
      rw [smul_mul_smul_comm, Units.mul_inv]
      rw [← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]
    show sdiagAmp π p (u : B) * sdiagAmp π p ((u⁻¹ : Bˣ) : B) = 1
    rw [sdiagAmp, sdiagAmp, Matrix.diagonal_mul_diagonal, hfun, Matrix.diagonal_one]
  · have hfun : (fun k => (((sgn (π k * p) : ℤˣ) : ℤ) • ((u⁻¹ : Bˣ) : B))
          * (((sgn (π k * p) : ℤˣ) : ℤ) • (u : B)))
        = fun _ => (1 : B) := by
      funext k
      rw [smul_mul_smul_comm, Units.inv_mul]
      rw [← Units.val_mul, sgn_mul_self', Units.val_one, one_smul]
    show sdiagAmp π p ((u⁻¹ : Bˣ) : B) * sdiagAmp π p (u : B) = 1
    rw [sdiagAmp, sdiagAmp, Matrix.diagonal_mul_diagonal, hfun, Matrix.diagonal_one]

private theorem sgn_mapMatrix_recombine : ∀ j pi pk p : ZMod 2,
    ((sgn (pk * p) : ℤˣ) : ℤ) * ((sgn ((j + pi + pk) * p) : ℤˣ) : ℤ)
      = ((sgn (j * p) : ℤˣ) : ℤ) * ((sgn (pi * p) : ℤˣ) : ℤ) := by
  decide

omit [GradedAlgebra 𝒜] in
/-- **Signed-diagonal transport** (M7d-5b-4-ii): if `t` intertwines
`(φ, φ')` with parity `p`, the signed diagonal intertwines the
entrywise-mapped pair on matrix superalgebras, with the same
parity. -/
theorem intertwines_mapMatrix (φ φ' : A →ₐ[K] B)
    {p : ZMod 2} {t : B}
    (hint : ∀ ⦃j : ZMod 2⦄ ⦃x : A⦄, x ∈ 𝒜 j →
      φ' x * t = ((sgn (j * p) : ℤˣ) : ℤ) • (t * φ x)) :
    ∀ ⦃j : ZMod 2⦄ ⦃X : Matrix n n A⦄, X ∈ matrixGradingA π 𝒜 j →
      φ'.mapMatrix X * sdiagAmp π p t
        = ((sgn (j * p) : ℤˣ) : ℤ) •
          (sdiagAmp π p t * φ.mapMatrix X) := by
  intro j X hX
  refine Matrix.ext fun i k => ?_
  simp only [sdiagAmp, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  -- entry relation at degree j + π i + π k
  rw [mul_smul_comm]
  rw [show φ' (X i k) * t
      = ((sgn ((j + π i + π k) * p) : ℤˣ) : ℤ) • (t * φ (X i k))
      from hint (hX i k)]
  rw [smul_smul, sgn_mapMatrix_recombine j (π i) (π k) p, ← smul_smul,
    smul_mul_assoc]

end MatrixTransport

end Superfusion
