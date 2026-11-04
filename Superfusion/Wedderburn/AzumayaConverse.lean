/-
Superfusion / Wedderburn / AzumayaConverse

Milestone M10-5: the converse half of Wall's criterion (classical fact:
Azumaya ⇒ central simple), independent of the Wedderburn realization
theorem itself.

Three results:

* `isGradedSimple_of_isSuperAzumaya` — a nonzero homogeneous two-sided
  ideal is stable under the image of the Wall map `superMulLeftRight`,
  which (super-Azumaya) is *all* of `End_K(A)`; a nonzero subspace
  stable under every `K`-linear endomorphism is `⊤`.
* `superMulLeftRight_exists_of_mem_endGrading` — the referee's
  degreewise-surjectivity helper: since the Wall map is graded
  (`superMulLeftRight_map_grading`, `Super/WallGraded.lean`) and
  bijective, its restriction to each graded piece is already onto the
  corresponding piece of `End_K(A)`.
* `isSuperCentral_of_isSuperAzumaya` — for `z` supercentral of degree
  `i`, left multiplication `L_z` supercommutes with every *signed*
  operator `T_{a,b} = superMulLeftRight (a ⊗ b)` with a sign uniform in
  `x` (`lmul_supercentral_commutes_tmul`); extended to every homogeneous
  endomorphism via the degreewise-surjectivity helper.  `End_K(A)`
  itself is transported to be supercentral from the matrix superalgebra
  `M_{p|q}(K)` (M7f-4c, `endMatrixSuper`) via `isSuperCentral_of_equiv`,
  so `L_z` is a scalar; reading off degree `0`/`1` recovers `z ∈ K·1`.

A fourth result, independent of the above, is the "P-twist" descent
used to unwind matrix stabilization in the Brauer–Wall group:

* `isSuperCentral_of_matrixSuper` — `IsSuperCentral (M_{p|q}(D))` implies
  `IsSuperCentral D` (`p + q ≠ 0`).  Even supercentral `z` gives the
  scalar diagonal matrix `z·1`; odd supercentral `z` gives the
  *P-twisted* diagonal matrix `z·P`, `P = diag((-1)^{π a})`, whose
  asymmetric contribution exactly cancels the Koszul cost of odd-degree
  supercommutation entrywise.  Reading a diagonal entry back out needs
  `p + q ≠ 0` (`Nonempty (Fin p ⊕ Fin q)`); the degenerate `p = q = 0`
  is a genuine counterexample (the zero ring is vacuously supercentral).
-/
import Superfusion.Super.GradedEndMatrix
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Superfusion

open Module TensorProduct GradedTensorProduct

/-! ### (a) super-Azumaya ⇒ graded-simple -/

section GradedSimple

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- **Azumaya ⇒ graded-simple** (M10-5a): a nonzero homogeneous
two-sided ideal is stable under the image of Wall's map, which is all
of `End_K(A)`; a nonzero subspace stable under every `K`-linear
endomorphism is `⊤`. -/
theorem isGradedSimple_of_isSuperAzumaya [IsSuperAzumaya 𝒜] :
    IsGradedSimple 𝒜 := by
  constructor
  intro J hJ
  by_cases hJbot : J = ⊥
  · exact Or.inl hJbot
  · right
    have hlt : (⊥ : TwoSidedIdeal A) < J := bot_lt_iff_ne_bot.mpr hJbot
    obtain ⟨-, v, hvJ, hv0'⟩ := SetLike.lt_iff_le_and_exists.mp hlt
    have hv0 : v ≠ 0 := by
      intro h
      exact hv0' (by rw [h]; exact TwoSidedIdeal.zero_mem _)
    -- `J` absorbs every `superMulLeftRight`-image.
    have hstable : ∀ w : SuperEnvelope 𝒜, ∀ x ∈ J,
        superMulLeftRight 𝒜 w x ∈ J := by
      intro w
      have key : ∀ t : A ⊗[K] SuperOp 𝒜, ∀ x ∈ J,
          superMulLeftRight 𝒜 (GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜) t) x
            ∈ J := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero =>
            intro x _
            simp only [map_zero, LinearMap.zero_apply]
            exact J.zero_mem
        | tmul a b =>
            intro x hx
            rw [show GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜) (a ⊗ₜ[K] b)
                = a ᵍ⊗ₜ[K] b from rfl, superMulLeftRight_tmul_apply, SuperOp.mulMap_apply]
            refine J.mul_mem_left a _ (J.sub_mem (J.mul_mem_right x (SuperOp.unop 𝒜 b) hx)
              (J.zsmul_mem 2 (J.mul_mem_right _ _ ?_)))
            rw [oddPart_apply]
            exact hJ x hx 1
        | add u v hu hv =>
            intro x hx
            simp only [map_add, LinearMap.add_apply]
            exact J.add_mem (hu x hx) (hv x hx)
      intro x hx
      have := key ((GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜)).symm w) x hx
      rwa [GradedTensorProduct.symm_of_of] at this
    have hall : ∀ (f : Module.End K A) (x : A), x ∈ J → f x ∈ J := by
      intro f x hx
      obtain ⟨w, hw⟩ := (IsSuperAzumaya.bij (𝒜 := 𝒜)).surjective f
      rw [← hw]
      exact hstable w x hx
    refine TwoSidedIdeal.ext fun y => ⟨fun _ => TwoSidedIdeal.mem_top A, fun _ => ?_⟩
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    have hfv : (LinearMap.toSpanSingleton K A y ∘ₗ φ) v = y := by
      rw [LinearMap.comp_apply, hφ, LinearMap.toSpanSingleton_apply, one_smul]
    rw [← hfv]
    exact hall (LinearMap.toSpanSingleton K A y ∘ₗ φ) v hvJ

end GradedSimple

/-! ### (b) degreewise surjectivity of Wall's map (referee helper) -/

section DegreewiseSurjective

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- **Degreewise surjectivity** (referee helper for M10-5b): for a
super-Azumaya algebra, every homogeneous endomorphism of degree `i` is
the image of a degree-`i` element of the envelope — immediate from the
graded map equality `superMulLeftRight_map_grading`. -/
theorem superMulLeftRight_exists_of_mem_endGrading [IsSuperAzumaya 𝒜]
    {i : ZMod 2} {φ : Module.End K A} (hφ : φ ∈ endGrading 𝒜 i) :
    ∃ w ∈ tensorGrading 𝒜 (SuperOp.grading 𝒜) i, superMulLeftRight 𝒜 w = φ := by
  have h := superMulLeftRight_map_grading 𝒜 i
  rw [← h] at hφ
  obtain ⟨w, hw, hwφ⟩ := Submodule.mem_map.mp hφ
  exact ⟨w, hw, hwφ⟩

end DegreewiseSurjective

/-! ### (c) super-Azumaya ⇒ supercentral -/

section SuperCentral

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

private theorem zmod2_lmul_supercentral (iz j1 j2 k : ZMod 2) :
    j2 * k + iz * j1 = iz * (j1 + j2) + j2 * (iz + k) := by decide +revert

/-- On a Wall generator, left multiplication by a supercentral element
supercommutes with the signed operator `T_{a,b}`, with sign uniform in
`x` (design record, referee-verified): `L_z T_{a,b} = (-1)^{i(|a|+|b|)}
T_{a,b} L_z`. -/
theorem lmul_supercentral_commutes_tmul
    {iz j1 j2 : ZMod 2} {z a : A} (hz : z ∈ 𝒜 iz) (hzc : IsSupercentral 𝒜 iz z)
    (ha : a ∈ 𝒜 j1) {b : SuperOp 𝒜} (hb : SuperOp.unop 𝒜 b ∈ 𝒜 j2) :
    Algebra.lmul K A z * superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b)
      = ((sgn (iz * (j1 + j2)) : ℤˣ) : ℤ) •
        (superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) * Algebra.lmul K A z) := by
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k m =>
      rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
        show Algebra.lmul K A z (superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) (m : A))
          = z * superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) (m : A) from rfl,
        superMulLeftRight_tmul_apply_of_mem 𝒜 a hb m.2,
        show Algebra.lmul K A z (m : A) = z * (m : A) from rfl,
        superMulLeftRight_tmul_apply_of_mem 𝒜 a hb (SetLike.mul_mem_graded hz m.2),
        mul_smul_comm]
      have hshift : z * (a * ((m : A) * SuperOp.unop 𝒜 b))
          = ((sgn (iz * j1) : ℤˣ) : ℤ) • (a * ((z * (m : A)) * SuperOp.unop 𝒜 b)) := by
        rw [show z * (a * ((m : A) * SuperOp.unop 𝒜 b))
            = z * a * ((m : A) * SuperOp.unop 𝒜 b) from (mul_assoc z a _).symm,
          hzc j1 a ha, smul_mul_assoc]
        congr 1
        simp only [mul_assoc]
      rw [hshift]
      simp only [smul_smul, ← Units.val_mul, ← sgn_add]
      rw [zmod2_lmul_supercentral iz j1 j2 k]
  | add u v hu hv =>
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_add] at hu hv ⊢
      rw [hu, hv]

/-- Extension of `lmul_supercentral_commutes_tmul` from generators to
the whole envelope, at a fixed tensor degree `j`. -/
theorem lmul_supercentral_commutes {iz : ZMod 2} {z : A} (hz : z ∈ 𝒜 iz)
    (hzc : IsSupercentral 𝒜 iz z) {j : ZMod 2} {w : SuperEnvelope 𝒜}
    (hw : w ∈ tensorGrading 𝒜 (SuperOp.grading 𝒜) j) :
    Algebra.lmul K A z * superMulLeftRight 𝒜 w
      = ((sgn (iz * j) : ℤˣ) : ℤ) • (superMulLeftRight 𝒜 w * Algebra.lmul K A z) := by
  refine tensorGrading_induction 𝒜 (SuperOp.grading 𝒜) hw
    (p := fun w => Algebra.lmul K A z * superMulLeftRight 𝒜 w
      = ((sgn (iz * j) : ℤˣ) : ℤ) • (superMulLeftRight 𝒜 w * Algebra.lmul K A z))
    ?_ ?_ ?_ ?_
  · intro j1 j2 a b hjk ha hb
    rw [← hjk]
    exact lmul_supercentral_commutes_tmul 𝒜 hz hzc ha ((SuperOp.mem_grading_iff 𝒜 j2 b).mp hb)
  · simp
  · intro u v hu hv
    simp only [map_add, mul_add, add_mul, hu, hv, smul_add]
  · intro c u hu
    rw [map_smul, mul_smul_comm, hu, smul_mul_assoc]
    exact smul_comm c _ _

/-- **The endomorphism algebra of a finite-dimensional superalgebra
over a field is supercentral** (transported from `M_{p|q}(K)`, M7f-4c,
along the graded equivalence `endMatrixSuper`). -/
theorem endGrading_isSuperCentral [FiniteDimensional K A] :
    IsSuperCentral (endGrading 𝒜) := by
  have heq : matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) (evenGrading K K)
      = matrixGrading (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) K :=
    matrixGradingA_evenGrading _
  haveI := isSuperCentral_matrix (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) K
  haveI hmatrix : IsSuperCentral
      (matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) (evenGrading K K)) := by
    constructor
    rw [heq]
    exact IsSuperCentral.superCenter_le_one
      (𝒜 := matrixGrading (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) K)
  have hφ : ∀ i, (matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)))
        (evenGrading K K) i).map (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).symm.toLinearMap
      = endGrading 𝒜 i := by
    intro i
    rw [← toMatrixAlgEquiv_homBasis_map_grading 𝒜 i, ← Submodule.map_comp]
    have hcomp : (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).symm.toLinearMap.comp
        (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).toLinearMap = LinearMap.id := by
      ext v; simp
    rw [hcomp, Submodule.map_id]
  exact isSuperCentral_of_equiv
    (matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))) (evenGrading K K))
    (endGrading 𝒜) (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).symm hφ

/-- **Azumaya ⇒ supercentral** (M10-5b): for `z` supercentral of degree
`i`, `L_z` is supercentral in the graded `End_K(A)` (which is itself
supercentral); reading off degree `0`/`1` recovers `z ∈ K·1`. -/
theorem isSuperCentral_of_isSuperAzumaya [FiniteDimensional K A] [IsSuperAzumaya 𝒜] :
    IsSuperCentral 𝒜 := by
  haveI hEndCentral : IsSuperCentral (endGrading 𝒜) := endGrading_isSuperCentral 𝒜
  constructor
  have layer : ∀ iz : ZMod 2, superCenterGrade 𝒜 iz ≤ (1 : Submodule K A) := by
    rintro iz z ⟨hz, hzc⟩
    have hLzc : IsSupercentral (endGrading 𝒜) iz (Algebra.lmul K A z) := by
      intro j φ hφ
      obtain ⟨w, hw, hwφ⟩ := superMulLeftRight_exists_of_mem_endGrading 𝒜 hφ
      rw [← hwφ]
      exact lmul_supercentral_commutes 𝒜 hz hzc hw
    have hLz1 : Algebra.lmul K A z ∈ (1 : Submodule K (Module.End K A)) :=
      mem_one_of_isSupercentral (endGrading 𝒜) (lmul_mem_endGrading 𝒜 hz) hLzc
    have hlmul1 : Algebra.lmul K A z (1 : A) = z := by
      show z * 1 = z; rw [mul_one]
    rcases zmod2_cases iz with hiz | hiz <;> subst hiz
    · obtain ⟨c, hc⟩ := Submodule.mem_one.mp hLz1
      refine Submodule.mem_one.mpr ⟨c, ?_⟩
      have h := DFunLike.congr_fun hc (1 : A)
      rw [Module.algebraMap_end_apply, hlmul1] at h
      rw [Algebra.algebraMap_eq_smul_one]
      exact h
    · have h0 : Algebra.lmul K A z ∈ endGrading 𝒜 0 := by
        obtain ⟨c, hc⟩ := Submodule.mem_one.mp hLz1
        rw [← hc]
        exact algebraMap_mem_grade_zero (endGrading 𝒜) c
      have h1 : Algebra.lmul K A z ∈ endGrading 𝒜 1 := lmul_mem_endGrading 𝒜 hz
      have hzero : Algebra.lmul K A z = 0 :=
        eq_zero_of_mem_zero_of_mem_one (endGrading 𝒜) h0 h1
      have h := DFunLike.congr_fun hzero (1 : A)
      rw [hlmul1, LinearMap.zero_apply] at h
      rw [h]
      exact Submodule.zero_mem _
  rw [superCenter, sup_le_iff]
  exact ⟨layer 0, layer 1⟩

end SuperCentral

/-! ### (d) the P-twist descent -/

section MatrixDescent

variable {K : Type*} [Field K] (D : SuperAlgebra K) (p q : ℕ)

private theorem zmod2_diag_index (e x : ZMod 2) : e + x + x = e := by decide +revert

private theorem zmod2_p_twist_odd (j x y : ZMod 2) :
    x + 1 * (j + x + y) = 1 * j + y := by decide +revert

/-- The scalar diagonal matrix `z · 1`, the even-degree witness of the
P-twist. -/
noncomputable def evenTwist (z : D.carrier) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier :=
  Matrix.diagonal fun _ => z

/-- The sign-twisted diagonal matrix `z · P`, `P = diag((-1)^{π a})`,
the odd-degree witness of the P-twist. -/
noncomputable def oddTwist (z : D.carrier) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier :=
  Matrix.diagonal fun a => ((sgn (sumParity p q a) : ℤˣ) : ℤ) • z

/-- The even case of the P-twist: `z · 1` is a homogeneous supercentral
degree-`0` element of `M_{p|q}(D)`. -/
theorem evenTwist_mem_and_isSupercentral {z : D.carrier} (hz : z ∈ D.grading 0)
    (hzc : IsSupercentral D.grading 0 z) :
    evenTwist D p q z ∈ matrixGradingA (sumParity p q) D.grading 0 ∧
      IsSupercentral (matrixGradingA (sumParity p q) D.grading) 0 (evenTwist D p q z) := by
  constructor
  · intro a b
    by_cases hab : a = b
    · subst hab
      rw [evenTwist, Matrix.diagonal_apply_eq, zmod2_diag_index]
      exact hz
    · rw [evenTwist, Matrix.diagonal_apply_ne _ hab]
      exact zero_mem _
  · intro j X hX
    ext a b
    rw [evenTwist, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hkey := hzc (j + sumParity p q a + sumParity p q b) (X a b) (hX a b)
    simpa using hkey

/-- The odd case of the P-twist: `z · P` is a homogeneous supercentral
degree-`1` element of `M_{p|q}(D)` (the Koszul-sign cancellation,
referee-recomputed). -/
theorem oddTwist_mem_and_isSupercentral {z : D.carrier} (hz : z ∈ D.grading 1)
    (hzc : IsSupercentral D.grading 1 z) :
    oddTwist D p q z ∈ matrixGradingA (sumParity p q) D.grading 1 ∧
      IsSupercentral (matrixGradingA (sumParity p q) D.grading) 1 (oddTwist D p q z) := by
  constructor
  · intro a b
    by_cases hab : a = b
    · subst hab
      rw [oddTwist, Matrix.diagonal_apply_eq,
        show (1 : ZMod 2) + sumParity p q a + sumParity p q a = 1 from
          zmod2_diag_index 1 (sumParity p q a)]
      exact zsmul_mem hz _
    · rw [oddTwist, Matrix.diagonal_apply_ne _ hab]
      exact zero_mem _
  · intro j X hX
    ext a b
    rw [oddTwist, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      smul_mul_assoc, mul_smul_comm]
    have hkey := hzc (j + sumParity p q a + sumParity p q b) (X a b) (hX a b)
    rw [hkey, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add,
      zmod2_p_twist_odd j (sumParity p q a) (sumParity p q b)]

/-- **The P-twist descent** (M10-5c): supercentrality of the matrix
stabilization `M_{p|q}(D)` descends to supercentrality of `D`, provided
`p + q ≠ 0` (the degenerate `p = q = 0` is a genuine counterexample:
the zero ring is vacuously supercentral). -/
theorem isSuperCentral_of_matrixSuper (hpq : p + q ≠ 0)
    [IsSuperCentral (D.matrixSuper p q).grading] : IsSuperCentral D.grading := by
  haveI hne : Nonempty (Fin p ⊕ Fin q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  obtain ⟨a0⟩ := hne
  haveI hSC : IsSuperCentral (matrixGradingA (sumParity p q) D.grading) :=
    ‹IsSuperCentral (D.matrixSuper p q).grading›
  constructor
  have layer : ∀ iz : ZMod 2, superCenterGrade D.grading iz ≤ (1 : Submodule K D.carrier) := by
    rintro iz z ⟨hz, hzc⟩
    rcases zmod2_cases iz with hiz | hiz <;> subst hiz
    · obtain ⟨hZmem, hZc⟩ := evenTwist_mem_and_isSupercentral D p q hz hzc
      have hZ1 : evenTwist D p q z
          ∈ (1 : Submodule K (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier)) :=
        IsSuperCentral.superCenter_le_one (𝒜 := matrixGradingA (sumParity p q) D.grading)
          (le_sup_left (α := Submodule K (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier))
            ⟨hZmem, hZc⟩)
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hZ1
      have hentry := congrFun (congrFun hc a0) a0
      rw [Matrix.algebraMap_matrix_apply, if_pos rfl, evenTwist, Matrix.diagonal_apply_eq]
        at hentry
      exact Submodule.mem_one.mpr ⟨c, hentry⟩
    · obtain ⟨hZmem, hZc⟩ := oddTwist_mem_and_isSupercentral D p q hz hzc
      have hZ1 : oddTwist D p q z
          ∈ (1 : Submodule K (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier)) :=
        IsSuperCentral.superCenter_le_one (𝒜 := matrixGradingA (sumParity p q) D.grading)
          (le_sup_right (α := Submodule K (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) D.carrier))
            ⟨hZmem, hZc⟩)
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hZ1
      have h0 : oddTwist D p q z ∈ matrixGradingA (sumParity p q) D.grading 0 := by
        rw [← hc]
        exact algebraMap_mem_grade_zero (matrixGradingA (sumParity p q) D.grading) c
      have hZ0 : oddTwist D p q z = 0 :=
        eq_zero_of_mem_zero_of_mem_one (matrixGradingA (sumParity p q) D.grading) h0 hZmem
      have hentry := congrFun (congrFun hZ0 a0) a0
      rw [oddTwist, Matrix.diagonal_apply_eq, Matrix.zero_apply] at hentry
      have hz0 : z = 0 := by
        have h := congrArg (fun v => ((sgn (sumParity p q a0) : ℤˣ) : ℤ) • v) hentry
        simp only [smul_smul, ← Units.val_mul, sgn_mul_self', Units.val_one, one_smul,
          smul_zero] at h
        exact h
      rw [hz0]
      exact Submodule.zero_mem _
  rw [superCenter, sup_le_iff]
  exact ⟨layer 0, layer 1⟩

end MatrixDescent

end Superfusion
