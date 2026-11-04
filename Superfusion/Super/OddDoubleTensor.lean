/-
Superfusion / Super / OddDoubleTensor

Milestone M7c-3: the odd double **is** the graded tensor product
`A ᵍ⊗ D_ε`.

`equivGradedTensor : (𝒜 ᵍ⊗[K] AdjoinOdd.grading ε) ≃ₐ[K] OddDouble 𝒜 ε`
identifies M7c-1's explicit odd double with mathlib's Koszul-signed
tensor product against the rank-one Clifford superalgebra
`D_ε = AdjoinOdd ε` (M7a), over any commutative ring.  On homogeneous
tensors the identification is graded
(`equivGradedTensor_tmul_mem`) — in fact, since mathlib has no
`GradedAlgebra` instance on `ᵍ⊗` (an explicit TODO there), the grading
of `OddDouble` *is* the missing graded structure of `A ᵍ⊗ D_ε`,
transported through this equivalence.

Consequently the division tower (M7c-2) is the iterated graded tensor
product `D_ε ᵍ⊗ ⋯ ᵍ⊗ D_ε` in the precise mathlib sense, floor by
floor.

Construction: `ᵍ⊗ → OddDouble` by the universal property
(`GradedTensorProduct.lift`, with the Koszul sign checked on the four
parity cases); the inverse `(a, b) ↦ a ᵍ⊗ 1 + b ᵍ⊗ e` is linear, and
the two composites are the identity by a computation on pairs
resp. `TensorProduct.induction_on`.
-/
import Superfusion.Super.OddDouble
import Superfusion.Super.AdjoinOdd

namespace Superfusion

namespace OddDouble

open TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K)

/-- `A → OddDouble 𝒜 ε`, `a ↦ a + 0·g`. -/
noncomputable def inl : A →ₐ[K] OddDouble 𝒜 ε where
  toFun a := mk 𝒜 ε a 0
  map_one' := rfl
  map_mul' a b := ext 𝒜 ε (by simp) (by simp)
  map_zero' := rfl
  map_add' a b := ext 𝒜 ε (by simp) (by simp)
  commutes' r := rfl

@[simp] theorem inl_apply (a : A) : inl 𝒜 ε a = mk 𝒜 ε a 0 := rfl

/-- `D_ε → OddDouble 𝒜 ε`, `c + d·e ↦ c + d·g`. -/
noncomputable def inr : AdjoinOdd ε →ₐ[K] OddDouble 𝒜 ε where
  toFun x := mk 𝒜 ε (algebraMap K A (AdjoinOdd.ev ε x))
    (algebraMap K A (AdjoinOdd.od ε x))
  map_one' := ext 𝒜 ε (by simp) (by simp)
  map_mul' x y :=
    ext 𝒜 ε
      (by
        simp only [p1_mul, p1_mk, p2_mk, AdjoinOdd.ev_mul,
          parityMap_algebraMap, map_add, map_mul, Algebra.smul_def])
      (by
        simp only [p2_mul, p1_mk, p2_mk, AdjoinOdd.od_mul,
          parityMap_algebraMap, map_add, map_mul])
  map_zero' := ext 𝒜 ε (by simp) (by simp)
  map_add' x y := ext 𝒜 ε (by simp) (by simp)
  commutes' r := ext 𝒜 ε (by simp) (by simp)

@[simp] theorem inr_apply (x : AdjoinOdd ε) :
    inr 𝒜 ε x = mk 𝒜 ε (algebraMap K A (AdjoinOdd.ev ε x))
      (algebraMap K A (AdjoinOdd.od ε x)) := rfl

theorem inr_e : inr 𝒜 ε (AdjoinOdd.e ε) = gen 𝒜 ε :=
  ext 𝒜 ε (by simp) (by simp)

/-- The Koszul anticommutation between the two inclusions — the
hypothesis of `GradedTensorProduct.lift`. -/
theorem inl_inr_anticommutes ⦃i j : ZMod 2⦄ (a : 𝒜 i)
    (b : AdjoinOdd.grading ε j) :
    inl 𝒜 ε a * inr 𝒜 ε b =
      (-1 : ℤˣ) ^ (j * i) • (inr 𝒜 ε (b : AdjoinOdd ε) * inl 𝒜 ε a) := by
  have hb := b.2
  rw [Units.smul_def, ← sgn_eq_neg_one_uzpow]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · -- `b` even: everything commutes, sign `+1`
    rw [AdjoinOdd.mem_grading_zero] at hb
    rw [zero_mul, sgn_zero]
    refine ext 𝒜 ε ?_ ?_ <;>
      simp [hb, Algebra.commutes]
  · -- `b` odd: `inr b` is a multiple of `g`
    rw [AdjoinOdd.mem_grading_one] at hb
    rw [one_mul]
    rcases zmod2_cases i with hi | hi <;> subst hi
    · -- `a` even: `J a = a`, sign `+1`
      rw [sgn_zero]
      refine ext 𝒜 ε ?_ ?_ <;>
        simp [hb, parityMap_of_mem_zero 𝒜 a.2, Algebra.commutes]
    · -- `a` odd: `J a = -a`, sign `-1`
      rw [sgn_one, units_sign_eq]
      refine ext 𝒜 ε ?_ ?_ <;>
        simp [hb, parityMap_of_mem_one 𝒜 a.2, Algebra.commutes]

/-- `A ᵍ⊗ D_ε → OddDouble`, from the universal property of the graded
tensor product. -/
noncomputable def ofGradedTensor :
    (𝒜 ᵍ⊗[K] AdjoinOdd.grading ε) →ₐ[K] OddDouble 𝒜 ε :=
  GradedTensorProduct.lift 𝒜 (AdjoinOdd.grading ε) (inl 𝒜 ε) (inr 𝒜 ε)
    (inl_inr_anticommutes 𝒜 ε)

theorem ofGradedTensor_tmul (a : A) (b : AdjoinOdd ε) :
    ofGradedTensor 𝒜 ε (a ᵍ⊗ₜ[K] b) = inl 𝒜 ε a * inr 𝒜 ε b :=
  GradedTensorProduct.lift_tmul _ _ _ _ _ _ _

/-- The inverse, `a + b·g ↦ a ᵍ⊗ 1 + b ᵍ⊗ e`, as a linear map. -/
noncomputable def toGradedTensorLin :
    OddDouble 𝒜 ε →ₗ[K] (𝒜 ᵍ⊗[K] AdjoinOdd.grading ε) :=
  (GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε)).toLinearMap.comp
    (((TensorProduct.mk K A (AdjoinOdd ε)).flip 1).comp (p1 𝒜 ε)
      + ((TensorProduct.mk K A (AdjoinOdd ε)).flip
          (AdjoinOdd.e ε)).comp (p2 𝒜 ε))

theorem toGradedTensorLin_mk (a b : A) :
    toGradedTensorLin 𝒜 ε (mk 𝒜 ε a b) =
      a ᵍ⊗ₜ[K] (1 : AdjoinOdd ε) + b ᵍ⊗ₜ[K] AdjoinOdd.e ε := by
  rw [toGradedTensorLin, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, p1_mk, p2_mk,
    LinearMap.flip_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    TensorProduct.mk_apply, map_add]
  rfl

theorem ofGradedTensor_toGradedTensorLin (x : OddDouble 𝒜 ε) :
    ofGradedTensor 𝒜 ε (toGradedTensorLin 𝒜 ε x) = x := by
  conv_lhs => rw [← mk_p1_p2 𝒜 ε x]
  rw [toGradedTensorLin_mk, map_add, ofGradedTensor_tmul,
    ofGradedTensor_tmul, map_one, mul_one, inr_e]
  refine ext 𝒜 ε ?_ ?_ <;> simp [parityMap_one]

theorem toGradedTensorLin_ofGradedTensor
    (ξ : 𝒜 ᵍ⊗[K] AdjoinOdd.grading ε) :
    toGradedTensorLin 𝒜 ε (ofGradedTensor 𝒜 ε ξ) = ξ := by
  obtain ⟨z, rfl⟩ : ∃ z, GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε) z = ξ :=
    ⟨(GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε)).symm ξ,
      (GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε)).apply_symm_apply ξ⟩
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
      have hprod : inl 𝒜 ε a * inr 𝒜 ε b =
          mk 𝒜 ε (AdjoinOdd.ev ε b • a) (AdjoinOdd.od ε b • a) := by
        refine ext 𝒜 ε ?_ ?_ <;>
          simp [Algebra.smul_def, Algebra.commutes]
      show toGradedTensorLin 𝒜 ε (ofGradedTensor 𝒜 ε (a ᵍ⊗ₜ[K] b)) = _
      rw [ofGradedTensor_tmul, hprod, toGradedTensorLin_mk]
      show (GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε))
            ((AdjoinOdd.ev ε b • a) ⊗ₜ[K] (1 : AdjoinOdd ε))
          + (GradedTensorProduct.of K 𝒜 (AdjoinOdd.grading ε))
            ((AdjoinOdd.od ε b • a) ⊗ₜ[K] AdjoinOdd.e ε) = _
      rw [← map_add]
      congr 1
      have hb : b = AdjoinOdd.ev ε b • (1 : AdjoinOdd ε)
          + AdjoinOdd.od ε b • AdjoinOdd.e ε := by
        refine AdjoinOdd.ext ε ?_ ?_ <;> simp [smul_eq_mul]
      conv_rhs => rw [hb]
      rw [TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul']
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [hu, hv]

/-- **M7c-3**: the odd double is the graded tensor product `A ᵍ⊗ D_ε`,
over any commutative ring. -/
noncomputable def equivGradedTensor :
    (𝒜 ᵍ⊗[K] AdjoinOdd.grading ε) ≃ₐ[K] OddDouble 𝒜 ε :=
  AlgEquiv.ofBijective (ofGradedTensor 𝒜 ε)
    ⟨Function.LeftInverse.injective (toGradedTensorLin_ofGradedTensor 𝒜 ε),
      Function.RightInverse.surjective (ofGradedTensor_toGradedTensorLin 𝒜 ε)⟩

theorem equivGradedTensor_tmul (a : A) (b : AdjoinOdd ε) :
    equivGradedTensor 𝒜 ε (a ᵍ⊗ₜ[K] b) = inl 𝒜 ε a * inr 𝒜 ε b :=
  ofGradedTensor_tmul 𝒜 ε a b

/-- On homogeneous tensors the identification is graded: `OddDouble`'s
grading is the (missing in mathlib) graded structure of `A ᵍ⊗ D_ε`. -/
theorem equivGradedTensor_tmul_mem {i j : ZMod 2} {a : A}
    {b : AdjoinOdd ε} (ha : a ∈ 𝒜 i) (hb : b ∈ AdjoinOdd.grading ε j) :
    equivGradedTensor 𝒜 ε (a ᵍ⊗ₜ[K] b) ∈ grading 𝒜 ε (i + j) := by
  rw [equivGradedTensor_tmul]
  have h1 : inl 𝒜 ε a ∈ grading 𝒜 ε i :=
    mk_mem_grading 𝒜 ε ha (zero_mem _)
  have h2 : inr 𝒜 ε b ∈ grading 𝒜 ε j := by
    rcases zmod2_cases j with hj | hj <;> subst hj
    · rw [AdjoinOdd.mem_grading_zero] at hb
      exact mk_mem_grading 𝒜 ε (algebraMap_mem_grade_zero 𝒜 _)
        (by rw [hb, map_zero]; exact zero_mem _)
    · rw [AdjoinOdd.mem_grading_one] at hb
      exact mk_mem_grading 𝒜 ε (by rw [hb, map_zero]; exact zero_mem _)
        (algebraMap_mem_grade_zero 𝒜 _)
  exact SetLike.mul_mem_graded h1 h2

end OddDouble

end Superfusion
