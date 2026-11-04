/-
Superfusion / Gauge / RealFuse2

Milestone M9-4b-ii-2: **the second slice of the 64 fusion isomorphisms**:
**the hyperbolic core and the mixed-sign pairs**.

Three stages.

1. **The hyperbolic core** (`hypFuse`): `Cl_{0,1} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℝ)`, built
   explicitly from the universal property of the graded tensor product
   (`GradedTensorProduct.lift`, mirroring the odd-double-vs-graded-tensor
   identification of `Superfusion.Super.OddDoubleTensor`).  The two odd
   generators `e` (`e² = -1`) and `f` (`f² = 1`) are sent to the antidiagonal
   matrices `E = [[0,1],[-1,0]]`, `F = [[0,1],[1,0]]`; the Koszul
   anticommutation needed for `lift` reduces, on the four homogeneous cases,
   to `E·F = -(F·E)` (a direct `Matrix.fromBlocks_multiply` computation, the
   same idiom as `Superfusion.Super.QuaternionTower`/`BottCertificate`).
   Bijectivity is a dimension count (`4 = 4`) plus an explicit surjectivity
   formula (every `2×2` block matrix is `x·1 + y·E + z·F + w·EF`).

2. **Matrix absorption** (`gtensorMatrixAbsorb`): the reusable composite
   `A ≅ M_{p|q}(A')`, `B ≅ M_{r|s}(B')` `⟹` `A ᵍ⊗ B ≅ M_{rp+sq|rq+sp}(A' ᵍ⊗ B')`,
   assembled once from the landed `matrixSuperGtensor`/`matrixSuperGtensorRight`/
   `matrixSuperComp` kit (`Superfusion.Super.MatrixSuperTensor`,
   `Superfusion.Super.BWTransitivity`).

3. **Mixed-sign pairs via iterated peeling** (`peelFuse`): given a fusion
   result `Cl_{0,m} ᵍ⊗ Cl_{n,0} ≅ M_{p|q}(D)`, peeling one generator off each
   side (`towerSuccEquiv`), a four-fold interchange reassociation
   (`gtensorInterchange`), one `hypFuse` application on the two new
   generators, and matrix absorption produces
   `Cl_{0,m+1} ᵍ⊗ Cl_{n+1,0} ≅ M_{p+q|p+q}(D)`.  Starting from the unitor base
   cases (`baseFuseL`/`baseFuseR`, `M_{1|0}`) and iterating gives all nine
   `(m, n) ∈ {1,2,3}²` mixed-sign pairs; the nine transposes follow for free
   from the Koszul braiding (`realFuse_transpose`, generic, no new
   construction).

**Design relaxation (per task instructions): Table 2 agreement is a
cross-check only, not a requirement.**  Our `peelFuse` recursion always
produces *balanced* sizes `p = q` (`1|1`, `2|2`, `4|4`), since every step
multiplies through the *same* `M_{1|1}` hyperbolic factor; Table 2 sometimes
prefers an odd-target `p|0` split instead (documented as a solver
convention, not canonical, in `docs/paper-tables-extract.md`).  Our sizes
agree with Table 2 exactly on the "self-transpose" pairs `a + b ≡ 0`
(`(1,7) ↦ 1|1`, `(2,6) ↦ 2|2`, `(3,5) ↦ 4|4`) and diverge (but remain
dimensionally consistent) on the other six.

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealFuse1

namespace Superfusion

open TensorProduct
open GradedTensorProduct

/-! ### Stage 1: the hyperbolic core -/

section HypCore

/-! #### Membership helpers for the length-one towers (`OddDouble (evenGrading ℝ ℝ) ε`) -/

private theorem hyp_eq_mk_p_zero_of_mem_zero {ε : ℝ}
    {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 0) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε (OddDouble.p1 (evenGrading ℝ ℝ) ε x) 0 := by
  obtain ⟨-, h2⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [zero_add, evenGrading_one, Submodule.mem_bot] at h2
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h2]

private theorem hyp_eq_mk_zero_q_of_mem_one {ε : ℝ}
    {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 1) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε 0 (OddDouble.p2 (evenGrading ℝ ℝ) ε x) := by
  obtain ⟨h1, -⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [evenGrading_one, Submodule.mem_bot] at h1
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h1]

/-! #### The two antidiagonal matrices in `M_{1|1}(ℝ)` -/

/-- `E = [[0,1],[-1,0]]`: the image of `Cl_{0,1}`'s generator `e` (`e² = -1`). -/
private def hypE : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- `F = [[0,1],[1,0]]`: the image of `Cl_{1,0}`'s generator `f` (`f² = 1`). -/
private def hypF : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 0 1 1 0

private theorem hypE_sq :
    hypE * hypE = algebraMap ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (-1 : ℝ) := by
  show Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul]
  rw [map_neg, map_one, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

private theorem hypF_sq :
    hypF * hypF = algebraMap ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (1 : ℝ) := by
  show Matrix.fromBlocks 0 1 1 0 * Matrix.fromBlocks 0 1 1 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one]
  rw [map_one, Matrix.fromBlocks_one]

/-- `E · F = fromBlocks 1 0 0 (-1)` — the two odd generators' product, needed
both for the anticommutation check and for the surjectivity computation. -/
private theorem hypE_mul_hypF : hypE * hypF = Matrix.fromBlocks 1 0 0 (-1) := by
  show Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 1 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one]

private theorem hypF_mul_hypE : hypF * hypE = Matrix.fromBlocks (-1) 0 0 1 := by
  show Matrix.fromBlocks 0 1 1 0 * Matrix.fromBlocks 0 1 (-1) 0 = _
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_add, add_zero, mul_one, mul_neg, neg_zero]

/-- **The Koszul anticommutation on generators**: `E · F = -(F · E)`. -/
private theorem hypEF_anti : hypE * hypF = -(hypF * hypE) := by
  rw [hypE_mul_hypF, hypF_mul_hypE, Matrix.fromBlocks_neg, neg_neg, neg_zero]

/-! #### The two length-one algebra maps, via the universal property of the odd double -/

private theorem ofId_isHomogeneous {C : Type*} [Ring C] [Algebra ℝ C]
    (ℭ : ZMod 2 → Submodule ℝ C) [GradedAlgebra ℭ] :
    IsHomogeneousHom (evenGrading ℝ ℝ) ℭ (Algebra.ofId ℝ C) := by
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · rw [Algebra.ofId_apply]
    exact algebraMap_mem_grade_zero ℭ x
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    subst hx
    rw [map_zero]
    exact zero_mem _

private theorem hconjE (a : ℝ) :
    hypE * (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) a
      = (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))
          (parityMap (evenGrading ℝ ℝ) a) * hypE := by
  rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, Algebra.ofId_apply]
  exact (Algebra.commutes a hypE).symm

private theorem hconjF (a : ℝ) :
    hypF * (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) a
      = (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))
          (parityMap (evenGrading ℝ ℝ) a) * hypF := by
  rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, Algebra.ofId_apply]
  exact (Algebra.commutes a hypF).symm

/-- `φ : Cl_{0,1} → M_{1|1}(ℝ)`, `e ↦ E`. -/
private noncomputable def hypFusePhi :
    (divisionTower (-1 : ℝ) 1).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  OddDouble.lift (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE hypE_sq hconjE

/-- `ψ : Cl_{1,0} → M_{1|1}(ℝ)`, `f ↦ F`. -/
private noncomputable def hypFusePsi :
    (divisionTower (1 : ℝ) 1).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  OddDouble.lift (evenGrading ℝ ℝ) (1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypF hypF_sq hconjF

private theorem hypFusePhi_gen : hypFusePhi (OddDouble.gen (evenGrading ℝ ℝ) (-1 : ℝ)) = hypE :=
  OddDouble.lift_gen (evenGrading ℝ ℝ) (-1 : ℝ) _ hypE hypE_sq hconjE

private theorem hypFusePsi_gen : hypFusePsi (OddDouble.gen (evenGrading ℝ ℝ) (1 : ℝ)) = hypF :=
  OddDouble.lift_gen (evenGrading ℝ ℝ) (1 : ℝ) _ hypF hypF_sq hconjF

private theorem hypFusePhi_mk_p_zero (a : ℝ) :
    hypFusePhi (OddDouble.mk (evenGrading ℝ ℝ) (-1 : ℝ) a 0) = algebraMap ℝ _ a :=
  (OddDouble.lift_inl (evenGrading ℝ ℝ) (-1 : ℝ) _ hypE hypE_sq hconjE a).trans
    (Algebra.ofId_apply _ a)

private theorem hypFusePhi_mk_zero_q (a : ℝ) :
    hypFusePhi (OddDouble.mk (evenGrading ℝ ℝ) (-1 : ℝ) 0 a) = a • hypE := by
  rw [Algebra.smul_def]
  have h := OddDouble.lift_mk (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE hypE_sq hconjE 0 a
  rw [map_zero, zero_add, Algebra.ofId_apply _] at h
  exact h

private theorem hypFusePsi_mk_p_zero (a : ℝ) :
    hypFusePsi (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) a 0) = algebraMap ℝ _ a :=
  (OddDouble.lift_inl (evenGrading ℝ ℝ) (1 : ℝ) _ hypF hypF_sq hconjF a).trans
    (Algebra.ofId_apply _ a)

private theorem hypFusePsi_mk_zero_q (a : ℝ) :
    hypFusePsi (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 a) = a • hypF := by
  rw [Algebra.smul_def]
  have h := OddDouble.lift_mk (evenGrading ℝ ℝ) (1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypF hypF_sq hconjF 0 a
  rw [map_zero, zero_add, Algebra.ofId_apply _] at h
  exact h

/-! #### Homogeneity, into the scalar matrix grading -/

private theorem hypE_odd : hypE ∈ matrixGrading (sumParity 1 1) ℝ 1 := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [hypE, sumParity, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private theorem hypF_odd : hypF ∈ matrixGrading (sumParity 1 1) ℝ 1 := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [hypF, sumParity, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private theorem hypFusePhi_isHomogeneous :
    IsHomogeneousHom (divisionTower (-1 : ℝ) 1).grading (matrixGrading (sumParity 1 1) ℝ)
      hypFusePhi :=
  OddDouble.lift_isHomogeneous (evenGrading ℝ ℝ) (-1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypE hypE_sq hconjE
    (matrixGrading (sumParity 1 1) ℝ) (ofId_isHomogeneous _) hypE_odd

private theorem hypFusePsi_isHomogeneous :
    IsHomogeneousHom (divisionTower (1 : ℝ) 1).grading (matrixGrading (sumParity 1 1) ℝ)
      hypFusePsi :=
  OddDouble.lift_isHomogeneous (evenGrading ℝ ℝ) (1 : ℝ)
    (Algebra.ofId ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) hypF hypF_sq hconjF
    (matrixGrading (sumParity 1 1) ℝ) (ofId_isHomogeneous _) hypF_odd

/-! #### The anticommutation hypothesis of `GradedTensorProduct.lift` -/

private theorem hypFuse_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (a : (divisionTower (-1 : ℝ) 1).grading i)
      (b : (divisionTower (1 : ℝ) 1).grading j),
      hypFusePhi (a : (divisionTower (-1 : ℝ) 1).carrier)
          * hypFusePsi (b : (divisionTower (1 : ℝ) 1).carrier)
        = (-1 : ℤˣ) ^ (j * i) •
          (hypFusePsi (b : (divisionTower (1 : ℝ) 1).carrier)
            * hypFusePhi (a : (divisionTower (-1 : ℝ) 1).carrier)) := by
  intro i j a b
  rw [Units.smul_def, ← sgn_eq_neg_one_uzpow]
  rcases zmod2_cases i with hi | hi <;> subst hi
  · have ha := hyp_eq_mk_p_zero_of_mem_zero a.2
    rw [show (a : (divisionTower (-1 : ℝ) 1).carrier) = _ from ha, hypFusePhi_mk_p_zero,
      mul_zero, sgn_zero, Units.val_one, one_smul]
    exact Algebra.commutes _ _
  · rcases zmod2_cases j with hj | hj <;> subst hj
    · have hb := hyp_eq_mk_p_zero_of_mem_zero b.2
      rw [show (b : (divisionTower (1 : ℝ) 1).carrier) = _ from hb, hypFusePsi_mk_p_zero,
        zero_mul, sgn_zero, Units.val_one, one_smul]
      exact (Algebra.commutes _ _).symm
    · have ha := hyp_eq_mk_zero_q_of_mem_one a.2
      have hb := hyp_eq_mk_zero_q_of_mem_one b.2
      rw [show (a : (divisionTower (-1 : ℝ) 1).carrier) = _ from ha,
        show (b : (divisionTower (1 : ℝ) 1).carrier) = _ from hb,
        hypFusePhi_mk_zero_q, hypFusePsi_mk_zero_q, mul_one, sgn_one, units_sign_eq]
      rw [smul_mul_smul_comm, smul_mul_smul_comm, hypEF_anti,
        mul_comm (OddDouble.p2 (evenGrading ℝ ℝ) (1 : ℝ) (b : (divisionTower (1 : ℝ) 1).carrier))
          (OddDouble.p2 (evenGrading ℝ ℝ) (-1 : ℝ) (a : (divisionTower (-1 : ℝ) 1).carrier))]
      rw [zsmul_eq_mul]
      simp

end HypCore

/-! ### The graded algebra map, and bijectivity -/

section HypEquiv

/-- The algebra map `Cl_{0,1} ᵍ⊗ Cl_{1,0} → M_{1|1}(ℝ)` from the universal
property of the graded tensor product. -/
private noncomputable def hypFuseHom :
    ((divisionTower (-1 : ℝ) 1).grading ᵍ⊗[ℝ] (divisionTower (1 : ℝ) 1).grading) →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  GradedTensorProduct.lift (divisionTower (-1 : ℝ) 1).grading (divisionTower (1 : ℝ) 1).grading
    hypFusePhi hypFusePsi hypFuse_anticommutes

private theorem hypFuseHom_tmul (a : (divisionTower (-1 : ℝ) 1).carrier)
    (b : (divisionTower (1 : ℝ) 1).carrier) :
    hypFuseHom (a ᵍ⊗ₜ[ℝ] b) = hypFusePhi a * hypFusePsi b :=
  GradedTensorProduct.lift_tmul _ _ _ _ _ _ _

/-- **Surjectivity**: every block matrix `M` is `x·1 + y·E + z·F + w·EF`
with `x = (M_{LL}+M_{RR})/2`, `y = (M_{LR}-M_{RL})/2`, `z = (M_{LR}+M_{RL})/2`,
`w = (M_{LL}-M_{RR})/2`. -/
private theorem hypFuseHom_surjective : Function.Surjective hypFuseHom := by
  intro M
  set L : Fin 1 ⊕ Fin 1 := Sum.inl 0 with hL
  set R : Fin 1 ⊕ Fin 1 := Sum.inr 0 with hR
  set e1 : (divisionTower (-1 : ℝ) 1).carrier := OddDouble.gen (evenGrading ℝ ℝ) (-1 : ℝ) with he1
  set f1 : (divisionTower (1 : ℝ) 1).carrier := OddDouble.gen (evenGrading ℝ ℝ) (1 : ℝ) with hf1
  refine ⟨((M L L + M R R) / 2) •
        ((1 : (divisionTower (-1 : ℝ) 1).carrier) ᵍ⊗ₜ[ℝ] (1 : (divisionTower (1 : ℝ) 1).carrier))
      + ((M L R - M R L) / 2) • (e1 ᵍ⊗ₜ[ℝ] (1 : (divisionTower (1 : ℝ) 1).carrier))
      + ((M L R + M R L) / 2) • ((1 : (divisionTower (-1 : ℝ) 1).carrier) ᵍ⊗ₜ[ℝ] f1)
      + ((M L L - M R R) / 2) • (e1 ᵍ⊗ₜ[ℝ] f1), ?_⟩
  rw [he1, hf1] at *
  simp only [map_add, map_smul, hypFuseHom_tmul, map_one, hypFusePhi_gen, hypFusePsi_gen]
  refine Matrix.ext fun x y => ?_
  have hxy : x = L ∨ x = R := by rcases x with x | x <;> [left; right] <;>
    simp [hL, hR, Subsingleton.elim x 0]
  have hxy' : y = L ∨ y = R := by rcases y with y | y <;> [left; right] <;>
    simp [hL, hR, Subsingleton.elim y 0]
  rw [hypE_mul_hypF]
  rcases hxy with rfl | rfl <;> rcases hxy' with rfl | rfl <;>
    simp [hL, hR, Matrix.add_apply, Matrix.smul_apply, hypE, hypF,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, smul_eq_mul] <;>
    ring

private theorem hypFuseHom_finrank_eq :
    Module.finrank ℝ ((divisionTower (-1 : ℝ) 1).grading ᵍ⊗[ℝ] (divisionTower (1 : ℝ) 1).grading)
      = Module.finrank ℝ (Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) := by
  rw [← (GradedTensorProduct.of ℝ (divisionTower (-1 : ℝ) 1).grading
    (divisionTower (1 : ℝ) 1).grading).finrank_eq, Module.finrank_tensorProduct,
    divisionTower_finrank, divisionTower_finrank, Module.finrank_matrix]
  simp [Fintype.card_sum]

private theorem hypFuseHom_bijective : Function.Bijective hypFuseHom := by
  haveI := finite_gtensor (divisionTower (-1 : ℝ) 1).grading (divisionTower (1 : ℝ) 1).grading
  have hsurj := hypFuseHom_surjective
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := hypFuseHom.toLinearMap) hypFuseHom_finrank_eq).mpr hsurj
  exact ⟨hinj, hsurj⟩

private theorem hypFuseHom_isHomogeneous :
    IsHomogeneousHom
      (tensorGrading (divisionTower (-1 : ℝ) 1).grading (divisionTower (1 : ℝ) 1).grading)
      (matrixGrading (sumParity 1 1) ℝ) hypFuseHom := by
  intro i z hz
  refine tensorGrading_induction (divisionTower (-1 : ℝ) 1).grading
    (divisionTower (1 : ℝ) 1).grading hz
    (p := fun w => hypFuseHom w ∈ matrixGrading (sumParity 1 1) ℝ i) ?_ ?_ ?_ ?_
  · intro j k x y hjk hx hy
    rw [hypFuseHom_tmul]
    have h := SetLike.mul_mem_graded (hypFusePhi_isHomogeneous j x hx)
      (hypFusePsi_isHomogeneous k y hy)
    rwa [hjk] at h
  · rw [map_zero]; exact zero_mem _
  · intro u v hu hv; rw [map_add]; exact add_mem hu hv
  · intro c u hu; rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- The bundled `AlgEquiv`. -/
private noncomputable def hypFuseEquiv :
    ((divisionTower (-1 : ℝ) 1).gtensor (divisionTower (1 : ℝ) 1)).carrier ≃ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  AlgEquiv.ofBijective hypFuseHom hypFuseHom_bijective

private theorem hypFuseEquiv_map_grading (i : ZMod 2) :
    (tensorGrading (divisionTower (-1 : ℝ) 1).grading (divisionTower (1 : ℝ) 1).grading i).map
        hypFuseEquiv.toLinearMap
      = matrixGradingA (sumParity 1 1) (evenGrading ℝ ℝ) i := by
  rw [matrixGradingA_evenGrading]
  exact map_grading_of_bijective
    (tensorGrading (divisionTower (-1 : ℝ) 1).grading (divisionTower (1 : ℝ) 1).grading)
    (matrixGrading (sumParity 1 1) ℝ) hypFuseHom hypFuseHom_isHomogeneous
    hypFuseHom_bijective i

/-- **The hyperbolic core** (Stage 1): `Cl_{0,1} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℝ)`.
Table 2 cross-check: entry `(1,7)`, `1|1` — **matches**. -/
noncomputable def hypFuse :
    SuperAlgEquiv ((divisionTower (-1 : ℝ) 1).gtensor (divisionTower (1 : ℝ) 1))
      ((SuperAlgebra.base ℝ).matrixSuper 1 1) :=
  ⟨hypFuseEquiv, hypFuseEquiv_map_grading⟩

end HypEquiv

/-! ### Stage 2: matrix absorption composition -/

/-- **Matrix absorption composition** (Stage 2, reusable): if `A ≅ M_{p|q}(A')`
and `B ≅ M_{r|s}(B')`, then `A ᵍ⊗ B ≅ M_{rp+sq|rq+sp}(A' ᵍ⊗ B')` — assembled
once from `matrixSuperGtensorRight`, `matrixSuperGtensor` and
`matrixSuperComp`. -/
noncomputable def gtensorMatrixAbsorb {K : Type*} [CommRing K]
    {A B A' B' : SuperAlgebra K} (p q r s : ℕ)
    (eA : SuperAlgEquiv A (A'.matrixSuper p q)) (eB : SuperAlgEquiv B (B'.matrixSuper r s)) :
    SuperAlgEquiv (A.gtensor B) ((A'.gtensor B').matrixSuper (r * p + s * q) (r * q + s * p)) :=
  (eA.gtensorCongr eB).trans <|
    (matrixSuperGtensorRight (A'.matrixSuper p q) B' r s).trans <|
      ((matrixSuperGtensor A' B' p q).matrixSuper r s).trans
        (matrixSuperComp (A'.gtensor B') r s p q)

/-! ### Stage 3: mixed-sign pairs via iterated peeling -/

section Peel

/-- The four-fold interchange reassociation: `(A ᵍ⊗ B) ᵍ⊗ (C ᵍ⊗ D) ≅
(A ᵍ⊗ C) ᵍ⊗ (B ᵍ⊗ D)`, via associators and one braid on the middle two
factors. -/
noncomputable def gtensorInterchange {K : Type*} [CommRing K] (A B C D : SuperAlgebra K) :
    SuperAlgEquiv ((A.gtensor B).gtensor (C.gtensor D)) ((A.gtensor C).gtensor (B.gtensor D)) :=
  (gtensorAssoc A B (C.gtensor D)).trans <|
    ((SuperAlgEquiv.refl A).gtensorCongr (gtensorAssoc B C D).symm).trans <|
      ((SuperAlgEquiv.refl A).gtensorCongr
          ((gtensorComm B C).gtensorCongr (SuperAlgEquiv.refl D))).trans <|
        ((SuperAlgEquiv.refl A).gtensorCongr (gtensorAssoc C B D)).trans
          (gtensorAssoc A C (B.gtensor D)).symm

/-- **The peeling step** (Stage 3): given `Cl_{0,m} ᵍ⊗ Cl_{n,0} ≅ M_{p|q}(D)`,
peel one generator off each side, fuse the two new generators via `hypFuse`,
and absorb the resulting `M_{1|1}` into `M_{p|q}(D)` to get
`Cl_{0,m+1} ᵍ⊗ Cl_{n+1,0} ≅ M_{p+q|p+q}(D)`. -/
noncomputable def peelFuse {m n p q : ℕ} {D : SuperAlgebra ℝ}
    (e : SuperAlgEquiv ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) n))
      (D.matrixSuper p q)) :
    SuperAlgEquiv ((divisionTower (-1 : ℝ) (m + 1)).gtensor (divisionTower (1 : ℝ) (n + 1)))
      (D.matrixSuper (p + q) (p + q)) :=
  ((towerSuccEquiv (-1 : ℝ) m).gtensorCongr (towerSuccEquiv (1 : ℝ) n)).trans <|
    (gtensorInterchange (divisionTower (-1 : ℝ) m) (divisionTower (-1 : ℝ) 1)
        (divisionTower (1 : ℝ) n) (divisionTower (1 : ℝ) 1)).trans <|
      (e.gtensorCongr hypFuse).trans <|
        (gtensorMatrixAbsorb p q 1 1 (SuperAlgEquiv.refl (D.matrixSuper p q))
            (SuperAlgEquiv.refl ((SuperAlgebra.base ℝ).matrixSuper 1 1))).trans <|
          ((gtensorUnitorRight D).matrixSuper (1 * p + 1 * q) (1 * q + 1 * p)).trans
            (matrixSuperCast D (by ring) (by ring))

/-- Base case, `m = 0`: `Cl_{0,0} ᵍ⊗ Cl_{n,0} ≅ M_{1|0}(Cl_{n,0})`. -/
noncomputable def baseFuseL (n : ℕ) :
    SuperAlgEquiv ((divisionTower (-1 : ℝ) 0).gtensor (divisionTower (1 : ℝ) n))
      ((divisionTower (1 : ℝ) n).matrixSuper 1 0) :=
  (gtensorUnitorLeft (divisionTower (1 : ℝ) n)).trans (matrixSuperOne (divisionTower (1 : ℝ) n)).symm

/-- Base case, `n = 0`: `Cl_{0,m} ᵍ⊗ Cl_{0,0} ≅ M_{1|0}(Cl_{0,m})`. -/
noncomputable def baseFuseR (m : ℕ) :
    SuperAlgEquiv ((divisionTower (-1 : ℝ) m).gtensor (divisionTower (1 : ℝ) 0))
      ((divisionTower (-1 : ℝ) m).matrixSuper 1 0) :=
  (gtensorUnitorRight (divisionTower (-1 : ℝ) m)).trans
    (matrixSuperOne (divisionTower (-1 : ℝ) m)).symm

end Peel

/-! ### The nine forward pairs -/

/-- `(1, 7) ↦ 0`: `Cl_{0,1} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℝ)` — this **is** `hypFuse`.
Table 2 cross-check: `1|1`, **matches**. -/
noncomputable def realFuse_one_seven :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 7)) ((realRep (1 + 7)).matrixSuper 1 1) :=
  hypFuse

/-- `(1, 6) ↦ 7`: `Cl_{0,1} ᵍ⊗ Cl_{2,0} ≅ M_{1|1}(Cl_{1,0})`. Table 2 cross-check:
row 1, col 6 is `2|0` — our balanced `1|1` **deviates** (dimensionally
consistent: `2·4 = 4·2`; see the file docstring). -/
noncomputable def realFuse_one_six :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 6)) ((realRep (1 + 6)).matrixSuper 1 1) :=
  peelFuse (baseFuseL 1)

/-- `(1, 5) ↦ 6`: `Cl_{0,1} ᵍ⊗ Cl_{3,0} ≅ M_{1|1}(Cl_{2,0})`. Table 2
cross-check: row 1, col 5 is `2|0` — **deviates** (dimensionally consistent:
`2·8 = 4·4`). -/
noncomputable def realFuse_one_five :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 5)) ((realRep (1 + 5)).matrixSuper 1 1) :=
  peelFuse (baseFuseL 2)

/-- `(2, 7) ↦ 1`: `Cl_{0,2} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(Cl_{0,1})`. Table 2
cross-check: row 2, col 7 is `2|0` — **deviates** (dimensionally consistent:
`4·2 = 4·2`). -/
noncomputable def realFuse_two_seven :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 7)) ((realRep (2 + 7)).matrixSuper 1 1) :=
  peelFuse (baseFuseR 1)

/-- `(2, 6) ↦ 0`: `Cl_{0,2} ᵍ⊗ Cl_{2,0} ≅ M_{2|2}(ℝ)`. Table 2 cross-check:
row 2, col 6 is `2|2`, **matches**. -/
noncomputable def realFuse_two_six :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 6)) ((realRep (2 + 6)).matrixSuper 2 2) :=
  peelFuse hypFuse

/-- `(2, 5) ↦ 7`: `Cl_{0,2} ᵍ⊗ Cl_{3,0} ≅ M_{2|2}(Cl_{1,0})`. Table 2
cross-check: row 2, col 5 is `4|0` — **deviates** (dimensionally consistent:
`4·8 = 8·4`). -/
noncomputable def realFuse_two_five :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 5)) ((realRep (2 + 5)).matrixSuper 2 2) :=
  peelFuse realFuse_one_six

/-- `(3, 7) ↦ 2`: `Cl_{0,3} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(Cl_{0,2})`. Table 2
cross-check: row 3, col 7 is `2|0` — **deviates** (dimensionally consistent:
`8·2 = 4·4`). -/
noncomputable def realFuse_three_seven :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 7)) ((realRep (3 + 7)).matrixSuper 1 1) :=
  peelFuse (baseFuseR 2)

/-- `(3, 6) ↦ 1`: `Cl_{0,3} ᵍ⊗ Cl_{2,0} ≅ M_{2|2}(Cl_{0,1})`. Table 2
cross-check: row 3, col 6 is `4|0` — **deviates** (dimensionally consistent:
`8·4 = 16·2`). -/
noncomputable def realFuse_three_six :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 6)) ((realRep (3 + 6)).matrixSuper 2 2) :=
  peelFuse realFuse_two_seven

/-- `(3, 5) ↦ 0`: `Cl_{0,3} ᵍ⊗ Cl_{3,0} ≅ M_{4|4}(ℝ)`. Table 2 cross-check:
row 3, col 5 is `4|4`, **matches**. -/
noncomputable def realFuse_three_five :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 5)) ((realRep (3 + 5)).matrixSuper 4 4) :=
  peelFuse realFuse_two_six

/-! ### The nine transposes, for free from the Koszul braiding -/

/-- **The transpose pattern**: `realFuse b a` from `realFuse a b`, via the
Koszul braiding `gtensorComm` — no new construction (and no sign bookkeeping
needed: `gtensorComm` is already a verified `SuperAlgEquiv`). -/
noncomputable def realFuse_transpose {a b : ZMod 8} {p q : ℕ}
    (e : SuperAlgEquiv ((realRep a).gtensor (realRep b)) ((realRep (a + b)).matrixSuper p q)) :
    SuperAlgEquiv ((realRep b).gtensor (realRep a)) ((realRep (b + a)).matrixSuper p q) := by
  rw [add_comm b a]
  exact (gtensorComm (realRep b) (realRep a)).trans e

/-- `(7, 1) ↦ 0`. -/
noncomputable def realFuse_seven_one :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 1)) ((realRep (7 + 1)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_one_seven

/-- `(6, 1) ↦ 7`. -/
noncomputable def realFuse_six_one :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 1)) ((realRep (6 + 1)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_one_six

/-- `(5, 1) ↦ 6`. -/
noncomputable def realFuse_five_one :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 1)) ((realRep (5 + 1)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_one_five

/-- `(7, 2) ↦ 1`. -/
noncomputable def realFuse_seven_two :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 2)) ((realRep (7 + 2)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_two_seven

/-- `(6, 2) ↦ 0`. -/
noncomputable def realFuse_six_two :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 2)) ((realRep (6 + 2)).matrixSuper 2 2) :=
  realFuse_transpose realFuse_two_six

/-- `(5, 2) ↦ 7`. -/
noncomputable def realFuse_five_two :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 2)) ((realRep (5 + 2)).matrixSuper 2 2) :=
  realFuse_transpose realFuse_two_five

/-- `(7, 3) ↦ 2`. -/
noncomputable def realFuse_seven_three :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 3)) ((realRep (7 + 3)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_three_seven

/-- `(6, 3) ↦ 1`. -/
noncomputable def realFuse_six_three :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 3)) ((realRep (6 + 3)).matrixSuper 2 2) :=
  realFuse_transpose realFuse_three_six

/-- `(5, 3) ↦ 0`. -/
noncomputable def realFuse_five_three :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 3)) ((realRep (5 + 3)).matrixSuper 4 4) :=
  realFuse_transpose realFuse_three_five

end Superfusion
