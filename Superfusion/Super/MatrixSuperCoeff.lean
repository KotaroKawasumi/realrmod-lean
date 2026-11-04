/-
Superfusion / Super / MatrixSuperCoeff

Milestone M7d-4b: **matrix superalgebras with coefficients**.

For an index parity `π : n → ZMod 2` and a superalgebra `(A, 𝒜)`, the
matrix algebra `Matrix n n A` is graded by

  `(matrixGradingA π 𝒜)ᵢ = {M | M a b ∈ 𝒜 (i + π a + π b)}`

— the explicit model of `M_{p|q}(A) = A ᵍ⊗ M_{p|q}(K)`, with no graded
tensor product needed.  Over the purely even base this recovers the
scalar matrix superalgebra of M7d-1
(`matrixGradingA_evenGrading`).

This is the stabilization device for the Brauer–Wall equivalence
(design record M7d-4b): `IsBWEquivalent P Q` will ask for a graded
isomorphism `M_{p|q}(P) ≅ M_{r|s}(Q)`, and the mod-8 periodicity
`D_{n+8} ∼ D_n` will follow from the Bott certificate together with
`OddDouble (M_{p|q}(A)) ≅ M_{p|q}(OddDouble A)`.
-/
import Superfusion.Super.MatrixSuper
import Superfusion.Super.EvenGrading

namespace Superfusion

section CoeffBase

variable {n : Type*}
variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]

private theorem zmod2_cancel : ∀ i j c : ZMod 2, i ≠ j → i + c ≠ j + c := by
  decide

private theorem zmod2_self : ∀ i : ZMod 2, i + i = 0 := by decide

private theorem zmod2_shift : ∀ i c : ZMod 2, c = i ↔ i + c = 0 := by decide

private theorem zmod2_two_mul (i c : ZMod 2) : i + c + c = i := by
  decide +revert

private theorem zmod2_mul_indices (i j x z y : ZMod 2) :
    (i + x + z) + (j + z + y) = (i + j) + x + y := by
  decide +revert

variable (π : n → ZMod 2) (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- The parity grading on a matrix algebra with superalgebra
coefficients: degree `i` matrices have their `(a, b)` entry in
`𝒜 (i + π a + π b)`. -/
def matrixGradingA (i : ZMod 2) : Submodule K (Matrix n n A) where
  carrier := {M | ∀ a b, M a b ∈ 𝒜 (i + π a + π b)}
  zero_mem' _ _ := zero_mem _
  add_mem' {M N} hM hN a b := by
    rw [Matrix.add_apply]
    exact add_mem (hM a b) (hN a b)
  smul_mem' c M hM a b := by
    rw [Matrix.smul_apply]
    exact Submodule.smul_mem _ _ (hM a b)

omit [GradedAlgebra 𝒜] in
theorem mem_matrixGradingA {i : ZMod 2} {M : Matrix n n A} :
    M ∈ matrixGradingA π 𝒜 i ↔ ∀ a b, M a b ∈ 𝒜 (i + π a + π b) :=
  Iff.rfl

/-- The degree-`i` mask: project every entry onto its relevant graded
component. -/
noncomputable def matrixMaskA (i : ZMod 2) :
    Matrix n n A →ₗ[K] Matrix n n A where
  toFun M := Matrix.of fun a b =>
    (DirectSum.decompose 𝒜 (M a b) (i + π a + π b) : A)
  map_add' M N := by
    ext a b
    show ((DirectSum.decompose 𝒜 ((M + N) a b) (i + π a + π b) : 𝒜 _) : A)
      = _
    rw [Matrix.add_apply, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add]
    rfl
  map_smul' c M := by
    ext a b
    show ((DirectSum.decompose 𝒜 ((c • M) a b) (i + π a + π b) : 𝒜 _) : A)
      = _
    rw [Matrix.smul_apply, DirectSum.decompose_smul, DirectSum.smul_apply,
      Submodule.coe_smul]
    rfl

theorem matrixMaskA_apply (i : ZMod 2) (M : Matrix n n A) (a b : n) :
    matrixMaskA π 𝒜 i M a b
      = (DirectSum.decompose 𝒜 (M a b) (i + π a + π b) : A) := rfl

theorem matrixMaskA_mem (i : ZMod 2) (M : Matrix n n A) :
    matrixMaskA π 𝒜 i M ∈ matrixGradingA π 𝒜 i := by
  intro a b
  rw [matrixMaskA_apply]
  exact SetLike.coe_mem _

theorem matrixMaskA_of_mem {i : ZMod 2} {M : Matrix n n A}
    (hM : M ∈ matrixGradingA π 𝒜 i) : matrixMaskA π 𝒜 i M = M := by
  ext a b
  rw [matrixMaskA_apply, DirectSum.decompose_of_mem_same 𝒜 (hM a b)]

theorem matrixMaskA_of_mem_ne {i j : ZMod 2} {M : Matrix n n A}
    (hM : M ∈ matrixGradingA π 𝒜 i) (hij : i ≠ j) :
    matrixMaskA π 𝒜 j M = 0 := by
  ext a b
  rw [matrixMaskA_apply, DirectSum.decompose_of_mem_ne 𝒜 (hM a b)
    (zmod2_cancel _ _ _ (zmod2_cancel _ _ _ hij))]
  rfl

theorem matrixMaskA_add_matrixMaskA (M : Matrix n n A) :
    matrixMaskA π 𝒜 0 M + matrixMaskA π 𝒜 1 M = M := by
  ext a b
  rw [Matrix.add_apply, matrixMaskA_apply, matrixMaskA_apply]
  rcases zmod2_cases (π a + π b) with h | h
  · rw [show (0 : ZMod 2) + π a + π b = 0 from by rw [add_assoc, h]; decide,
      show (1 : ZMod 2) + π a + π b = 1 from by rw [add_assoc, h]; decide]
    exact evenPart_add_oddPart 𝒜 (M a b)
  · rw [show (0 : ZMod 2) + π a + π b = 1 from by rw [add_assoc, h]; decide,
      show (1 : ZMod 2) + π a + π b = 0 from by rw [add_assoc, h]; decide]
    rw [add_comm]
    exact evenPart_add_oddPart 𝒜 (M a b)

variable [Fintype n] [DecidableEq n]

instance : SetLike.GradedMonoid (matrixGradingA π 𝒜) where
  one_mem a b := by
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have h1 : (1 : A) ∈ 𝒜 0 := SetLike.one_mem_graded 𝒜
      rwa [show (0 : ZMod 2) = 0 + π a + π a from
        by rw [add_assoc, zmod2_self]; decide] at h1
    · rw [Matrix.one_apply_ne hab]
      exact zero_mem _
  mul_mem {i j} M N hM hN := by
    intro a b
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h := SetLike.mul_mem_graded (hM a c) (hN c b)
    rwa [zmod2_mul_indices] at h

/-- The degree-`i` projection, corestricted to the layer. -/
noncomputable def matrixMaskAInto (i : ZMod 2) :
    Matrix n n A →ₗ[K] matrixGradingA π 𝒜 i :=
  LinearMap.codRestrict (matrixGradingA π 𝒜 i) (matrixMaskA π 𝒜 i)
    (matrixMaskA_mem π 𝒜 i)

noncomputable instance : DirectSum.Decomposition (matrixGradingA π 𝒜) where
  decompose' M :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(matrixGradingA π 𝒜 i)) 0
        (matrixMaskAInto π 𝒜 0 M)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(matrixGradingA π 𝒜 i)) 1
        (matrixMaskAInto π 𝒜 1 M)
  left_inv M := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact matrixMaskA_add_matrixMaskA π 𝒜 M
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        beta_reduce
        rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | of i b =>
        rcases zmod2_cases i with hi | hi <;> subst hi
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : matrixMaskAInto π 𝒜 0 (b : Matrix n n A) = b :=
            Subtype.ext (matrixMaskA_of_mem π 𝒜 b.2)
          have h2 : matrixMaskAInto π 𝒜 1 (b : Matrix n n A) = 0 :=
            Subtype.ext (matrixMaskA_of_mem_ne π 𝒜 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : matrixMaskAInto π 𝒜 0 (b : Matrix n n A) = 0 :=
            Subtype.ext (matrixMaskA_of_mem_ne π 𝒜 b.2 (by decide))
          have h2 : matrixMaskAInto π 𝒜 1 (b : Matrix n n A) = b :=
            Subtype.ext (matrixMaskA_of_mem π 𝒜 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-- Matrix algebras with superalgebra coefficients are superalgebras. -/
noncomputable instance matrixGradedAlgebraA :
    GradedAlgebra (matrixGradingA π 𝒜) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

end CoeffBase

/-! ### Sanity: over the purely even base this is M7d-1's grading -/

section Sanity

variable {n : Type*} {K : Type*} [CommRing K] (π : n → ZMod 2)

/-- Over the purely even base field, the coefficient grading is the
scalar matrix superalgebra grading of M7d-1. -/
theorem matrixGradingA_evenGrading :
    matrixGradingA π (evenGrading K K) = matrixGrading π K := by
  funext i
  ext M
  rw [mem_matrixGradingA, mem_matrixGrading]
  constructor
  · intro h a b hab
    have hM := h a b
    have hne : i + π a + π b ≠ 0 := by
      rw [add_assoc]
      exact fun h0 => hab ((zmod2_shift i (π a + π b)).mpr h0)
    rw [show evenGrading K K (i + π a + π b) = ⊥ from if_neg hne] at hM
    exact (Submodule.mem_bot K).mp hM
  · intro h a b
    by_cases hab : π a + π b = i
    · have h0 : i + π a + π b = 0 := by
        rw [add_assoc, hab, zmod2_self]
      rw [show evenGrading K K (i + π a + π b) = ⊤ from by
        rw [h0, evenGrading_zero]]
      exact Submodule.mem_top
    · rw [h a b hab]
      exact zero_mem _

end Sanity

end Superfusion
