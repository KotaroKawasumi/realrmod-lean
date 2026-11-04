/-
Superfusion / Super / OddDoubleMatrix

Milestone M7d-4b-2: **the odd double commutes with matrix
stabilization** —

  `OddDouble (M_{p|q}(A)) ≅ M_{p|q}(OddDouble A)`

as graded algebras (`oddDoubleMatrixEquiv`).  This is the induction
step for Brauer–Wall mod-8 periodicity: iterating it identifies
`divisionTower ε (n+8)` with `M_{8|8}(divisionTower ε n)` starting from
the Bott certificate.

The map sends the adjoined odd generator `g` to the **sign-adjusted**
diagonal matrix `γ = diagonal (a ↦ sgn (π a) • g)`.  The signs are
forced: the parity involution of the coefficient matrix grading acts on
entries by `(J M)_{ab} = sgn (π a + π b) • J (M_{ab})`
(`parityMap_matrixGradingA_apply`), not entrywise, and the plain
diagonal would fail the conjugation law by exactly that sign.
-/
import Superfusion.Super.MatrixSuperCoeff
import Superfusion.Super.OddDoubleLift
import Superfusion.Super.OddDoubleTensor
import Superfusion.Super.GradedTransfer

namespace Superfusion

namespace OddDouble

open Matrix

variable {n : Type*}
variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K)

/-! ### Small `OddDouble` interface additions -/

theorem inl_mem_grading {j : ZMod 2} {x : A} (hx : x ∈ 𝒜 j) :
    inl 𝒜 ε x ∈ grading 𝒜 ε j :=
  mk_mem_grading 𝒜 ε hx (zero_mem _)

/-- Conjugation by `g` implements the parity involution on `A ⊕ 0`. -/
theorem gen_mul_inl (x : A) :
    gen 𝒜 ε * inl 𝒜 ε x = inl 𝒜 ε (parityMap 𝒜 x) * gen 𝒜 ε := by
  refine ext 𝒜 ε ?_ ?_ <;> simp

theorem inl_mul_gen (x : A) :
    inl 𝒜 ε x * gen 𝒜 ε = mk 𝒜 ε 0 x := by
  refine ext 𝒜 ε ?_ ?_ <;> simp [parityMap_one]

theorem zsmul_mk (m : ℤ) (a b : A) :
    m • mk 𝒜 ε a b = mk 𝒜 ε (m • a) (m • b) :=
  ext 𝒜 ε (by rw [map_zsmul, p1_mk, p1_mk]) (by rw [map_zsmul, p2_mk, p2_mk])

end OddDouble

/-! ### The parity involution of the coefficient matrix grading -/

section ParityMatrix

variable {n : Type*}
variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (π : n → ZMod 2) (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

private theorem sgn_cast_sq : ∀ x : ZMod 2,
    ((sgn x : ℤˣ) : ℤ) * ((sgn x : ℤˣ) : ℤ) = 1 := by decide

private theorem sgn_cast_split : ∀ x y : ZMod 2,
    ((sgn x : ℤˣ) : ℤ)
      = ((sgn y : ℤˣ) : ℤ) * ((sgn (x + y) : ℤˣ) : ℤ) := by decide

theorem decompose_matrixGradingA_zero_coe [Fintype n] [DecidableEq n]
    (M : Matrix n n A) :
    ((DirectSum.decompose (matrixGradingA π 𝒜) M 0 :
        matrixGradingA π 𝒜 0) : Matrix n n A) = matrixMaskA π 𝒜 0 M := by
  conv_lhs => rw [← matrixMaskA_add_matrixMaskA π 𝒜 M]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_same _ (matrixMaskA_mem π 𝒜 0 M),
    DirectSum.decompose_of_mem_ne _ (matrixMaskA_mem π 𝒜 1 M)
      (by decide : (1 : ZMod 2) ≠ 0),
    add_zero]

theorem decompose_matrixGradingA_one_coe [Fintype n] [DecidableEq n]
    (M : Matrix n n A) :
    ((DirectSum.decompose (matrixGradingA π 𝒜) M 1 :
        matrixGradingA π 𝒜 1) : Matrix n n A) = matrixMaskA π 𝒜 1 M := by
  conv_lhs => rw [← matrixMaskA_add_matrixMaskA π 𝒜 M]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_ne _ (matrixMaskA_mem π 𝒜 0 M)
      (by decide : (0 : ZMod 2) ≠ 1),
    DirectSum.decompose_of_mem_same _ (matrixMaskA_mem π 𝒜 1 M),
    zero_add]

/-- The parity involution of the coefficient matrix grading acts on
entries by the entrywise involution twisted by the index parity. -/
theorem parityMap_matrixGradingA_apply [Fintype n] [DecidableEq n]
    (M : Matrix n n A) (a b : n) :
    parityMap (matrixGradingA π 𝒜) M a b
      = ((sgn (π a + π b) : ℤˣ) : ℤ) • parityMap 𝒜 (M a b) := by
  have he : evenPart (matrixGradingA π 𝒜) M = matrixMaskA π 𝒜 0 M :=
    decompose_matrixGradingA_zero_coe π 𝒜 M
  have ho : oddPart (matrixGradingA π 𝒜) M = matrixMaskA π 𝒜 1 M :=
    decompose_matrixGradingA_one_coe π 𝒜 M
  rw [parityMap_apply, he, ho, Matrix.sub_apply, matrixMaskA_apply,
    matrixMaskA_apply, parityMap_apply]
  rcases zmod2_cases (π a + π b) with h | h
  · rw [show (0 : ZMod 2) + π a + π b = 0 from by rw [add_assoc, h]; decide,
      show (1 : ZMod 2) + π a + π b = 1 from by rw [add_assoc, h]; decide]
    rw [h, sgn_zero]
    simp only [Units.val_one, one_smul]
    rfl
  · rw [show (0 : ZMod 2) + π a + π b = 1 from by rw [add_assoc, h]; decide,
      show (1 : ZMod 2) + π a + π b = 0 from by rw [add_assoc, h]; decide]
    rw [h, sgn_one, units_sign_eq]
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_sub]
    rfl

end ParityMatrix

/-! ### The commutation equivalence -/

namespace OddDouble

open Matrix

section Commute

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (π : n → ZMod 2) (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ε : K)

/-- The entrywise inclusion `M_{p|q}(A) → M_{p|q}(OddDouble A)`. -/
noncomputable def matrixInl (_π : n → ZMod 2) (𝒜 : ZMod 2 → Submodule K A)
    [GradedAlgebra 𝒜] (ε : K) :
    Matrix n n A →ₐ[K] Matrix n n (OddDouble 𝒜 ε) :=
  (inl 𝒜 ε).mapMatrix

theorem matrixInl_apply (M : Matrix n n A) (a b : n) :
    matrixInl π 𝒜 ε M a b = inl 𝒜 ε (M a b) := rfl

/-- The sign-adjusted diagonal odd generator of the matrix
superalgebra. -/
noncomputable def gammaDiag : Matrix n n (OddDouble 𝒜 ε) :=
  Matrix.diagonal fun a => ((sgn (π a) : ℤˣ) : ℤ) • gen 𝒜 ε

theorem gammaDiag_sq :
    gammaDiag π 𝒜 ε * gammaDiag π 𝒜 ε
      = algebraMap K (Matrix n n (OddDouble 𝒜 ε)) ε := by
  rw [gammaDiag, Matrix.diagonal_mul_diagonal]
  rw [show (algebraMap K (Matrix n n (OddDouble 𝒜 ε)) ε)
      = Matrix.diagonal (fun _ => algebraMap K (OddDouble 𝒜 ε) ε) from by
    rw [Matrix.algebraMap_eq_diagonal]
    rfl]
  congr 1
  funext a
  rw [smul_mul_smul_comm, sgn_cast_sq, one_smul, gen_mul_gen]

omit [Fintype n] in
theorem gammaDiag_odd :
    gammaDiag π 𝒜 ε ∈ matrixGradingA π (grading 𝒜 ε) 1 := by
  intro a b
  by_cases hab : a = b
  · subst hab
    rw [gammaDiag, Matrix.diagonal_apply_eq]
    have h := gen_mem_grading 𝒜 ε
    have hmem : gen 𝒜 ε ∈ grading 𝒜 ε (1 + π a + π a) := by
      rw [show (1 : ZMod 2) + π a + π a = 1 from by
        rcases zmod2_cases (π a) with hpa | hpa <;> rw [hpa] <;> decide]
      exact h
    exact zsmul_mem hmem _
  · rw [gammaDiag, Matrix.diagonal_apply_ne _ hab]
    exact zero_mem _

theorem gammaDiag_conj (M : Matrix n n A) :
    gammaDiag π 𝒜 ε * matrixInl π 𝒜 ε M
      = matrixInl π 𝒜 ε (parityMap (matrixGradingA π 𝒜) M)
        * gammaDiag π 𝒜 ε := by
  ext a b
  rw [gammaDiag, Matrix.diagonal_mul, Matrix.mul_diagonal,
    matrixInl_apply, matrixInl_apply, smul_mul_assoc, gen_mul_inl,
    parityMap_matrixGradingA_apply, map_zsmul, smul_mul_assoc,
    mul_smul_comm,
    show ((sgn (π a) : ℤˣ) : ℤ)
        = ((sgn (π b) : ℤˣ) : ℤ) * ((sgn (π a + π b) : ℤˣ) : ℤ) from
      sgn_cast_split (π a) (π b),
    mul_comm, smul_smul]

/-- The lift `OddDouble (M_{p|q}(A)) → M_{p|q}(OddDouble A)`. -/
noncomputable def oddDoubleMatrixHom :
    OddDouble (matrixGradingA π 𝒜) ε →ₐ[K] Matrix n n (OddDouble 𝒜 ε) :=
  lift (matrixGradingA π 𝒜) ε (matrixInl π 𝒜 ε) (gammaDiag π 𝒜 ε)
    (gammaDiag_sq π 𝒜 ε) (gammaDiag_conj π 𝒜 ε)

theorem oddDoubleMatrixHom_mk (M N : Matrix n n A) (a b : n) :
    oddDoubleMatrixHom π 𝒜 ε (mk (matrixGradingA π 𝒜) ε M N) a b
      = mk 𝒜 ε (M a b) (((sgn (π b) : ℤˣ) : ℤ) • N a b) := by
  rw [oddDoubleMatrixHom, lift_mk, Matrix.add_apply, matrixInl_apply,
    gammaDiag, Matrix.mul_diagonal, matrixInl_apply, mul_smul_comm,
    inl_mul_gen, zsmul_mk, smul_zero]
  exact (ext 𝒜 ε (by simp) (by simp)).symm

/-- The explicit inverse. -/
noncomputable def oddDoubleMatrixInv
    (P : Matrix n n (OddDouble 𝒜 ε)) :
    OddDouble (matrixGradingA π 𝒜) ε :=
  mk (matrixGradingA π 𝒜) ε
    (Matrix.of fun a b => p1 𝒜 ε (P a b))
    (Matrix.of fun a b => ((sgn (π b) : ℤˣ) : ℤ) • p2 𝒜 ε (P a b))

theorem oddDoubleMatrixHom_bijective :
    Function.Bijective (oddDoubleMatrixHom π 𝒜 ε) := by
  have hR : Function.LeftInverse (oddDoubleMatrixInv π 𝒜 ε)
      (oddDoubleMatrixHom π 𝒜 ε) := by
    intro x
    set M := p1 (matrixGradingA π 𝒜) ε x with hM
    set N := p2 (matrixGradingA π 𝒜) ε x with hN
    have hx : x = mk (matrixGradingA π 𝒜) ε M N := (mk_p1_p2 (matrixGradingA π 𝒜) ε x).symm
    rw [hx, oddDoubleMatrixInv]
    refine congrArg₂ (mk (matrixGradingA π 𝒜) ε) ?_ ?_ <;> ext a b
    · rw [Matrix.of_apply, oddDoubleMatrixHom_mk, p1_mk]
    · rw [Matrix.of_apply, oddDoubleMatrixHom_mk, p2_mk, smul_smul,
        sgn_cast_sq, one_smul]
  have hL : Function.RightInverse (oddDoubleMatrixInv π 𝒜 ε)
      (oddDoubleMatrixHom π 𝒜 ε) := by
    intro P
    ext a b
    rw [oddDoubleMatrixInv, oddDoubleMatrixHom_mk, Matrix.of_apply,
      Matrix.of_apply, smul_smul, sgn_cast_sq, one_smul]
    exact mk_p1_p2 𝒜 ε (P a b)
  exact ⟨hR.injective, hL.surjective⟩

/-- The lift is grade-preserving. -/
theorem oddDoubleMatrixHom_isHomogeneous :
    IsHomogeneousHom (grading (matrixGradingA π 𝒜) ε)
      (matrixGradingA π (grading 𝒜 ε)) (oddDoubleMatrixHom π 𝒜 ε) := by
  refine lift_isHomogeneous (matrixGradingA π 𝒜) ε (matrixInl π 𝒜 ε)
    (gammaDiag π 𝒜 ε) (gammaDiag_sq π 𝒜 ε) (gammaDiag_conj π 𝒜 ε)
    (matrixGradingA π (grading 𝒜 ε)) ?_ (gammaDiag_odd π 𝒜 ε)
  intro j M hM a b
  rw [matrixInl_apply]
  exact OddDouble.inl_mem_grading 𝒜 ε (hM a b)

/-- **The odd double commutes with matrix stabilization** (M7d-4b-2):
`OddDouble (M_{p|q}(A)) ≅ M_{p|q}(OddDouble A)` as algebras. -/
noncomputable def oddDoubleMatrixEquiv :
    OddDouble (matrixGradingA π 𝒜) ε ≃ₐ[K] Matrix n n (OddDouble 𝒜 ε) :=
  AlgEquiv.ofBijective (oddDoubleMatrixHom π 𝒜 ε)
    (oddDoubleMatrixHom_bijective π 𝒜 ε)

/-- The commutation equivalence is graded. -/
theorem oddDoubleMatrixEquiv_map_grading (i : ZMod 2) :
    ((grading (matrixGradingA π 𝒜) ε) i).map
        (oddDoubleMatrixHom π 𝒜 ε).toLinearMap
      = matrixGradingA π (grading 𝒜 ε) i :=
  map_grading_of_bijective (grading (matrixGradingA π 𝒜) ε)
    (matrixGradingA π (grading 𝒜 ε)) (oddDoubleMatrixHom π 𝒜 ε)
    (oddDoubleMatrixHom_isHomogeneous π 𝒜 ε)
    (oddDoubleMatrixHom_bijective π 𝒜 ε) i

end Commute

end OddDouble

end Superfusion
