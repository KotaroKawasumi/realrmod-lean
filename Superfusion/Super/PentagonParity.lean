/-
Superfusion / Super / PentagonParity

Milestone M7d-5b-3-ii: **the route intertwiner and the parity
cochain** — super Skolem–Noether (M7d-5a) applied to the two fusion
routes (M7d-5b-3-i) yields, for each triple `(a,b,c) ∈ (ℤ/8)³`, an
invertible homogeneous intertwiner

  `pentagonT a b c : M_σ(T_{a+b+c})`,
  `routeR(x) · T = (-1)^{|x||T|} T · routeL(x)`,

whose parity defines the paper's parity 3-cochain

  `pentagonParity a b c := |T_{a,b,c}| ∈ ℤ/2`   (Table 5, tower
  gauge).

The hypotheses of Skolem–Noether are supplied by transferring
central simplicity from the matrix superalgebra target back along
`routeL` (M7b transfer + M7d-1 matrix-superalgebra results, extended
here from scalar to superalgebra coefficients:
`isSuperCentral_matrixGradingA` / `isGradedSimple_matrixGradingA`).
-/
import Superfusion.Super.PentagonRoutes
import Superfusion.Super.SkolemNoetherIso
import Superfusion.Super.OddDoubleMatrix
import Mathlib.LinearAlgebra.Matrix.Ideal

namespace Superfusion

open Module

/-! ### Central simplicity of matrix superalgebras with coefficients

`MatrixSuper.lean` (M7d-1) proves `IsSuperCentral`/`IsGradedSimple`
for the *scalar* matrix superalgebra `matrixGrading π K`.  The route
intertwiner lives inside a matrix superalgebra with coefficients in
a tower floor, `matrixGradingA π 𝒜`; we extend the two results to
this setting, entrywise, mirroring the scalar proofs. -/

section CentralSimpleCoeff

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (π : n → ZMod 2) (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- Matrix superalgebras with coefficients in a graded-simple superalgebra
are graded-simple: a homogeneous two-sided ideal of `Matrix n n A`
corresponds, via `TwoSidedIdeal.equivMatrix`, to a homogeneous two-sided
ideal of `A`. -/
theorem isGradedSimple_matrixGradingA [Nonempty n] [IsGradedSimple 𝒜] :
    IsGradedSimple (matrixGradingA π 𝒜) := by
  classical
  constructor
  intro I hI
  set J : TwoSidedIdeal A := TwoSidedIdeal.equivMatrix.symm I with hJdef
  have hIJ : I = J.matrix n := (TwoSidedIdeal.equivMatrix.apply_symm_apply I).symm
  have hJ : TwoSidedIdeal.IsHomogeneous 𝒜 J := by
    intro a ha i
    obtain ⟨c⟩ := ‹Nonempty n›
    have haI : (Matrix.single c c a : Matrix n n A) ∈ I := by
      rw [hIJ, TwoSidedIdeal.mem_matrix]
      intro i' j'
      by_cases h : c = i' ∧ c = j'
      · obtain ⟨rfl, rfl⟩ := h
        simpa [Matrix.single] using ha
      · simp [Matrix.single, h]
    have hde := hI _ haI i
    have hkey : ((DirectSum.decompose (matrixGradingA π 𝒜)
        (Matrix.single c c a) i : matrixGradingA π 𝒜 i) : Matrix n n A)
        = Matrix.single c c
          ((DirectSum.decompose 𝒜 a (i + π c + π c) : 𝒜 _) : A) := by
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [decompose_matrixGradingA_zero_coe]
        ext i' j'
        rw [matrixMaskA_apply]
        by_cases h : c = i' ∧ c = j'
        · obtain ⟨rfl, rfl⟩ := h
          simp [Matrix.single]
        · simp [Matrix.single, h]
      · rw [decompose_matrixGradingA_one_coe]
        ext i' j'
        rw [matrixMaskA_apply]
        by_cases h : c = i' ∧ c = j'
        · obtain ⟨rfl, rfl⟩ := h
          simp [Matrix.single]
        · simp [Matrix.single, h]
    rw [hkey] at hde
    have hzc : (i : ZMod 2) + π c + π c = i := by
      have : π c + π c = 0 := by
        rcases zmod2_cases (π c) with h | h <;> rw [h] <;> decide
      rw [add_assoc, this, add_zero]
    rw [hzc] at hde
    rw [hIJ, TwoSidedIdeal.mem_matrix] at hde
    have := hde c c
    simpa [Matrix.single] using this
  rcases IsGradedSimple.eq_bot_or_eq_top J hJ with h | h
  · left
    rw [hIJ, h, TwoSidedIdeal.matrix_bot]
  · right
    rw [hIJ, h, TwoSidedIdeal.matrix_top]

private theorem zmod2_i_add_self (i c : ZMod 2) : i + c + c = i := by
  decide +revert

/-- Matrix superalgebras with coefficients in a supercentral superalgebra
are supercentral. -/
theorem isSuperCentral_matrixGradingA [Nonempty n] [IsSuperCentral 𝒜] :
    IsSuperCentral (matrixGradingA π 𝒜) := by
  classical
  constructor
  obtain ⟨c⟩ := ‹Nonempty n›
  have layer : ∀ (i : ZMod 2) (z : Matrix n n A),
      z ∈ matrixGradingA π 𝒜 i →
      IsSupercentral (matrixGradingA π 𝒜) i z →
      z ∈ (1 : Submodule K (Matrix n n A)) := by
    intro i z hz hzc
    rcases zmod2_cases i with hi | hi <;> subst hi
    · -- even: z commutes with all of `Matrix n n A`, hence is a scalar
      -- matrix over the ordinary center of `A`
      have hcomm : ∀ X : Matrix n n A, X * z = z * X := by
        intro X
        have h0 := hzc 0 (evenPart (matrixGradingA π 𝒜) X)
          (evenPart_mem (matrixGradingA π 𝒜) X)
        have h1 := hzc 1 (oddPart (matrixGradingA π 𝒜) X)
          (oddPart_mem (matrixGradingA π 𝒜) X)
        simp only [mul_zero, zero_mul, sgn_zero, Units.val_one, one_smul]
          at h0 h1
        calc X * z
            = evenPart (matrixGradingA π 𝒜) X * z
              + oddPart (matrixGradingA π 𝒜) X * z := by
              rw [← add_mul, evenPart_add_oddPart]
          _ = z * evenPart (matrixGradingA π 𝒜) X
              + z * oddPart (matrixGradingA π 𝒜) X := by rw [← h0, ← h1]
          _ = z * X := by rw [← mul_add, evenPart_add_oddPart]
      have hcen : z ∈ Subalgebra.center K (Matrix n n A) :=
        Subalgebra.mem_center_iff.mpr hcomm
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map] at hcen
      obtain ⟨a, ha, rfl⟩ := hcen
      have haz0 : a ∈ 𝒜 0 := by
        have hzcc := hz c c
        change (Matrix.diagonal (fun _ => a) : Matrix n n A) c c
          ∈ 𝒜 (0 + π c + π c) at hzcc
        rwa [Matrix.diagonal_apply_eq, zmod2_i_add_self] at hzcc
      have hac : IsSupercentral 𝒜 0 a := by
        intro j b _
        have hcomm' := Subalgebra.mem_center_iff.mp ha b
        simpa using hcomm'.symm
      obtain ⟨d, hd⟩ := Submodule.mem_one.mp
        (mem_one_of_isSupercentral 𝒜 haz0 hac)
      refine Submodule.mem_one.mpr ⟨d, ?_⟩
      show (algebraMap K (Matrix n n A)) d = Matrix.scalarAlgHom n K a
      rw [← hd]
      exact ((Matrix.scalarAlgHom n K).commutes d).symm
    · -- odd: commuting with the even units forces diagonal support and
      -- supercentral diagonal entries, and odd supercentral scalars vanish
      have hdiag : ∀ (a x : n), x ≠ a → z x a = 0 := by
        intro a x hxa
        have hEmem : (Matrix.single a a (1 : A)) ∈ matrixGradingA π 𝒜 0 := by
          intro i' j'
          by_cases h : a = i' ∧ a = j'
          · obtain ⟨rfl, rfl⟩ := h
            simp only [Matrix.single_apply_same]
            rw [zmod2_i_add_self]
            exact SetLike.one_mem_graded 𝒜
          · rw [Matrix.single_apply_of_ne a a 1 i' j' h]
            exact zero_mem _
        have h := hzc 0 (Matrix.single a a 1) hEmem
        simp only [mul_zero, sgn_zero, Units.val_one, one_smul] at h
        have hentry : (z * Matrix.single a a (1 : A)) x a
            = (Matrix.single a a (1 : A) * z) x a := by rw [h]
        rw [Matrix.mul_single_apply_same, mul_one] at hentry
        rwa [Matrix.single_mul_apply_of_ne 1 a a x a hxa z] at hentry
      have hdiagzero : ∀ a : n, z a a = 0 := by
        intro a
        have hdc : z a a ∈ 𝒜 1 := by
          have := hz a a
          rwa [zmod2_i_add_self] at this
        have hac : IsSupercentral 𝒜 1 (z a a) := by
          intro j b hb
          have hbmem : (Matrix.single a a b) ∈ matrixGradingA π 𝒜 j := by
            intro i' j'
            by_cases h : a = i' ∧ a = j'
            · obtain ⟨rfl, rfl⟩ := h
              simp only [Matrix.single_apply_same]
              rwa [zmod2_i_add_self]
            · rw [Matrix.single_apply_of_ne a a b i' j' h]
              exact zero_mem _
          have h := hzc j (Matrix.single a a b) hbmem
          have hL : (z * Matrix.single a a b) a a = z a a * b := by
            rw [Matrix.mul_single_apply_same]
          have hR : (Matrix.single a a b * z) a a = b * z a a := by
            rw [Matrix.single_mul_apply_same]
          have hentry := congrArg (fun M : Matrix n n A => M a a) h
          simp only [Matrix.smul_apply] at hentry
          rwa [hL, hR] at hentry
        have hz1 : z a a ∈ (1 : Submodule K A) :=
          mem_one_of_isSupercentral 𝒜 hdc hac
        have hz0 : z a a ∈ 𝒜 0 := by
          obtain ⟨d, hd⟩ := Submodule.mem_one.mp hz1
          rw [← hd, Algebra.algebraMap_eq_smul_one]
          exact Submodule.smul_mem _ _ (SetLike.one_mem_graded 𝒜)
        have h0 := evenPart_of_mem_zero 𝒜 hz0
        have h1 := evenPart_of_mem_one 𝒜 hdc
        rw [h0] at h1
        exact h1
      have hzero : z = 0 := by
        ext x y
        by_cases hxy : x = y
        · subst hxy
          exact hdiagzero x
        · exact hdiag y x hxy
      rw [hzero]
      exact zero_mem _
  rw [superCenter, sup_le_iff]
  exact ⟨fun z hz => layer 0 z hz.1 hz.2, fun z hz => layer 1 z hz.1 hz.2⟩

end CentralSimpleCoeff

/-! ### Bundled: matrix superalgebras over a central simple floor -/

section Bundled

variable {K : Type*} [Field K]

/-- Bundled central simplicity of `P.matrixSuper p q` from central
simplicity of `P` (M7d-1, extended to superalgebra coefficients). -/
theorem matrixSuper_isSuperCentral (P : SuperAlgebra K) (p q : ℕ)
    [Nonempty (Fin p ⊕ Fin q)] (hP : IsSuperCentral P.grading) :
    IsSuperCentral (P.matrixSuper p q).grading :=
  isSuperCentral_matrixGradingA (sumParity p q) P.grading

/-- Bundled graded simplicity of `P.matrixSuper p q` from graded
simplicity of `P` (M7d-1, extended to superalgebra coefficients). -/
theorem matrixSuper_isGradedSimple (P : SuperAlgebra K) (p q : ℕ)
    [Nonempty (Fin p ⊕ Fin q)] (hP : IsGradedSimple P.grading) :
    IsGradedSimple (P.matrixSuper p q).grading :=
  isGradedSimple_matrixGradingA (sumParity p q) P.grading

end Bundled

section Parity

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- Forward homogeneity from a `map_grading` equality. -/
theorem isHomogeneousHom_of_map_grading {A B : Type*} [Ring A]
    [Algebra K A] [Ring B] [Algebra K B]
    {𝒜 : ZMod 2 → Submodule K A} {ℬ : ZMod 2 → Submodule K B}
    (e : A ≃ₐ[K] B) (he : ∀ i, (𝒜 i).map e.toLinearMap = ℬ i) :
    IsHomogeneousHom 𝒜 ℬ e.toAlgHom := by
  intro i x hx
  rw [← he i]
  exact Submodule.mem_map_of_mem hx

theorem stdTower_isSuperCentral (a : ZMod 8) :
    IsSuperCentral (stdTower (K := K) a).grading :=
  divisionTower_isSuperCentral one_ne_zero a.val

/-- The Skolem–Noether existence statement for the two fusion
routes: hypotheses transferred along `routeL` from the matrix
superalgebra target (M7d-1). -/
theorem pentagonT_exists (a b c : ZMod 8) :
    ∃ (p : ZMod 2)
      (t : ((stdTower (K := K) (a + b + c)).matrixSuper
        (sizeL a b c).1 (sizeL a b c).2).carrier),
      t ∈ ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2).grading p ∧ IsUnit t ∧
      ∀ ⦃j : ZMod 2⦄
        ⦃x : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
          (stdTower c)).carrier⦄,
        x ∈ (((stdTower a).gtensor (stdTower b)).gtensor
          (stdTower c)).grading j →
        (routeR a b c).toAlgEquiv x * t
          = ((sgn (j * p) : ℤˣ) : ℤ) • (t * (routeL a b c).toAlgEquiv x) := by
  classical
  set A : SuperAlgebra K :=
    ((stdTower a).gtensor (stdTower b)).gtensor (stdTower c) with hA
  set B : SuperAlgebra K :=
    (stdTower (a + b + c)).matrixSuper (sizeL a b c).1 (sizeL a b c).2
    with hB
  -- the target is a matrix superalgebra over a tower floor:
  -- finite-dimensional, nontrivial, supercentral, graded simple
  haveI hBfd : FiniteDimensional K B.carrier := by
    exact inferInstanceAs (Module.Finite K
      (Matrix _ _ (stdTower (K := K) (a + b + c)).carrier))
  haveI hBne : Nonempty (Fin (sizeL a b c).1 ⊕ Fin (sizeL a b c).2) := by
    have h := sizeL_ne_zero a b c
    by_cases h1 : (sizeL a b c).1 = 0
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, by omega⟩⟩
  haveI hBnt : Nontrivial B.carrier := by
    exact inferInstanceAs (Nontrivial
      (Matrix _ _ (stdTower (K := K) (a + b + c)).carrier))
  haveI hBsc : IsSuperCentral B.grading :=
    matrixSuper_isSuperCentral (stdTower (a + b + c)) _ _
      (stdTower_isSuperCentral (a + b + c))
  haveI hBgs : IsGradedSimple B.grading :=
    matrixSuper_isGradedSimple (stdTower (a + b + c)) _ _
      (stdTower_isGradedSimple (a + b + c))
  -- transfer back along routeL to the triple tensor source
  haveI hAfd : FiniteDimensional K A.carrier :=
    Module.Finite.equiv (routeL (K := K) a b c).toAlgEquiv.symm.toLinearEquiv
  haveI hAnt : Nontrivial A.carrier :=
    (routeL (K := K) a b c).toAlgEquiv.symm.injective.nontrivial
  haveI hAsc : IsSuperCentral A.grading :=
    isSuperCentral_of_equiv B.grading A.grading
      (routeL (K := K) a b c).toAlgEquiv.symm
      (routeL (K := K) a b c).symm.map_grading
  haveI hAgs : IsGradedSimple A.grading :=
    isGradedSimple_of_equiv B.grading A.grading
      (routeL (K := K) a b c).toAlgEquiv.symm
      (routeL (K := K) a b c).symm.map_grading
  exact superSkolemNoether_exists_of_surjective A.grading B.grading
    (routeL a b c).toAlgEquiv.toAlgHom (routeR a b c).toAlgEquiv.toAlgHom
    (isHomogeneousHom_of_map_grading _ (routeL a b c).map_grading)
    (isHomogeneousHom_of_map_grading _ (routeR a b c).map_grading)
    (routeL a b c).toAlgEquiv.surjective
    (routeR a b c).toAlgEquiv.surjective

/-- **The parity 3-cochain** (M7d-5b-3): the parity of the route
intertwiner — the paper's `p(a,b,c)` in the tower gauge. -/
noncomputable def pentagonParity (a b c : ZMod 8) : ZMod 2 :=
  (pentagonT_exists (K := K) a b c).choose

/-- **The route intertwiner** `T_{a,b,c}`. -/
noncomputable def pentagonT (a b c : ZMod 8) :
    ((stdTower (K := K) (a + b + c)).matrixSuper (sizeL a b c).1
      (sizeL a b c).2).carrier :=
  (pentagonT_exists (K := K) a b c).choose_spec.choose

theorem pentagonT_mem (a b c : ZMod 8) :
    pentagonT (K := K) a b c
      ∈ ((stdTower (a + b + c)).matrixSuper (sizeL a b c).1
        (sizeL a b c).2).grading (pentagonParity (K := K) a b c) :=
  (pentagonT_exists (K := K) a b c).choose_spec.choose_spec.1

theorem pentagonT_isUnit (a b c : ZMod 8) :
    IsUnit (pentagonT (K := K) a b c) :=
  (pentagonT_exists (K := K) a b c).choose_spec.choose_spec.2.1

theorem pentagonT_intertwines (a b c : ZMod 8) :
    ∀ ⦃j : ZMod 2⦄
      ⦃x : (((stdTower (K := K) a).gtensor (stdTower b)).gtensor
        (stdTower c)).carrier⦄,
      x ∈ (((stdTower a).gtensor (stdTower b)).gtensor
        (stdTower c)).grading j →
      (routeR a b c).toAlgEquiv x * pentagonT a b c
        = ((sgn (j * pentagonParity (K := K) a b c) : ℤˣ) : ℤ)
          • (pentagonT a b c * (routeL a b c).toAlgEquiv x) :=
  (pentagonT_exists (K := K) a b c).choose_spec.choose_spec.2.2

end Parity

end Superfusion
