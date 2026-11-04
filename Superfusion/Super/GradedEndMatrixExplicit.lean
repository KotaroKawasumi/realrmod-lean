/-
Superfusion / Super / GradedEndMatrixExplicit

**The basis-parameterized matrix realization of graded End** — the same
statement as `GradedEndMatrix.lean`'s `endMatrixSuper`, but along
USER-SUPPLIED homogeneous bases instead of the choice-produced
`Module.finBasis`.  This is the device that pins the matrix frames of the
`(4,4)` real fusion branch (and, downstream, of every coordinate
certificate) to explicit basis vectors: the anchor lemmas
`homBasisOf_inl`/`homBasisOf_inr` identify each frame vector with the
given basis vector, which `finBasis` cannot provide.

All proofs are verbatim adaptations of `GradedEndMatrix.lean`: nothing
there used any property of `finBasis` beyond being a basis of the even
and odd parts.
-/
import Superfusion.Super.GradedEndMatrix

namespace Superfusion

open Module

section HomBasisOf

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {p q : ℕ} (b₀ : Basis (Fin p) K (𝒜 0)) (b₁ : Basis (Fin q) K (𝒜 1))

/-- A homogeneous basis of a superalgebra glued from GIVEN bases of the
even and odd parts. -/
noncomputable def homBasisOf : Basis (Fin p ⊕ Fin q) K A :=
  (b₀.prod b₁).map (Submodule.prodEquivOfIsCompl _ _ (isCompl_grades 𝒜))

theorem homBasisOf_inl (k : Fin p) :
    homBasisOf 𝒜 b₀ b₁ (Sum.inl k) = (b₀ k : A) := by
  rw [homBasisOf, Basis.map_apply,
    show (b₀.prod b₁) (Sum.inl k) = (b₀ k, (0 : 𝒜 1)) from
      Prod.ext (Basis.prod_apply_inl_fst _ _ _) (Basis.prod_apply_inl_snd _ _ _),
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

theorem homBasisOf_inr (k : Fin q) :
    homBasisOf 𝒜 b₀ b₁ (Sum.inr k) = (b₁ k : A) := by
  rw [homBasisOf, Basis.map_apply,
    show (b₀.prod b₁) (Sum.inr k) = ((0 : 𝒜 0), b₁ k) from
      Prod.ext (Basis.prod_apply_inr_fst _ _ _) (Basis.prod_apply_inr_snd _ _ _),
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

/-- The glued basis is homogeneous of parity `sumParity`. -/
theorem homBasisOf_mem (r : Fin p ⊕ Fin q) :
    homBasisOf 𝒜 b₀ b₁ r ∈ 𝒜 (sumParity p q r) := by
  cases r with
  | inl k =>
      rw [show sumParity p q (Sum.inl k) = 0 from rfl, homBasisOf_inl]
      exact SetLike.coe_mem _
  | inr k =>
      rw [show sumParity p q (Sum.inr k) = 1 from rfl, homBasisOf_inr]
      exact SetLike.coe_mem _

/-- Coordinates of a homogeneous element vanish at the other parity. -/
theorem homBasisOf_repr_eq_zero {j : ZMod 2} {x : A} (hx : x ∈ 𝒜 j)
    {r : Fin p ⊕ Fin q} (hr : sumParity p q r ≠ j) :
    (homBasisOf 𝒜 b₀ b₁).repr x r = 0 := by
  have hrepr : ∀ y : A, (homBasisOf 𝒜 b₀ b₁).repr y
      = (b₀.prod b₁).repr
          ((Submodule.prodEquivOfIsCompl _ _ (isCompl_grades 𝒜)).symm y) := fun y => rfl
  cases r with
  | inl k =>
      rw [show sumParity p q (Sum.inl k) = 0 from rfl] at hr
      have hj : j = 1 := by
        rcases zmod2_cases j with h | h
        · exact absurd h.symm hr
        · exact h
      subst hj
      have hs := Submodule.prodEquivOfIsCompl_symm_apply_right
        (𝒜 0) (𝒜 1) (isCompl_grades 𝒜) (⟨x, hx⟩ : 𝒜 1)
      rw [show ((⟨x, hx⟩ : 𝒜 1) : A) = x from rfl] at hs
      rw [hrepr, hs, Basis.prod_repr_inl, map_zero, Finsupp.zero_apply]
  | inr k =>
      rw [show sumParity p q (Sum.inr k) = 1 from rfl] at hr
      have hj : j = 0 := by
        rcases zmod2_cases j with h | h
        · exact h
        · exact absurd h.symm hr
      subst hj
      have hs := Submodule.prodEquivOfIsCompl_symm_apply_left
        (𝒜 0) (𝒜 1) (isCompl_grades 𝒜) (⟨x, hx⟩ : 𝒜 0)
      rw [show ((⟨x, hx⟩ : 𝒜 0) : A) = x from rfl] at hs
      rw [hrepr, hs, Basis.prod_repr_inr, map_zero, Finsupp.zero_apply]

private theorem zmod2_endmat' : ∀ i a b : ZMod 2, i + a + b = 1 → a ≠ b + i := by
  decide

/-- In a given homogeneous basis, a homogeneous endomorphism of degree
`i` has matrix support on index pairs with `π r + π s = i`. -/
theorem toMatrixAlgEquiv_homBasisOf_isHomogeneous :
    IsHomogeneousHom (endGrading 𝒜)
      (matrixGradingA (sumParity p q) (evenGrading K K))
      (LinearMap.toMatrixAlgEquiv (homBasisOf 𝒜 b₀ b₁)).toAlgHom := by
  intro i f hf r s
  rw [show ((LinearMap.toMatrixAlgEquiv (homBasisOf 𝒜 b₀ b₁)).toAlgHom f) r s
      = (homBasisOf 𝒜 b₀ b₁).repr (f (homBasisOf 𝒜 b₀ b₁ s)) r from
      LinearMap.toMatrixAlgEquiv_apply _ f r s]
  have hfs : f (homBasisOf 𝒜 b₀ b₁ s) ∈ 𝒜 (sumParity p q s + i) :=
    (mem_endGrading 𝒜).mp hf _ _ (homBasisOf_mem 𝒜 b₀ b₁ s)
  rcases zmod2_cases (i + sumParity p q r + sumParity p q s) with hc | hc
  · rw [hc, evenGrading_zero]
    exact Submodule.mem_top
  · rw [hc, evenGrading_one, Submodule.mem_bot]
    exact homBasisOf_repr_eq_zero 𝒜 b₀ b₁ hfs (zmod2_endmat' i _ _ hc)

/-- The matrix realization along a given homogeneous basis carries the
End grading onto the matrix grading. -/
theorem toMatrixAlgEquiv_homBasisOf_map_grading (i : ZMod 2) :
    (endGrading 𝒜 i).map
        (LinearMap.toMatrixAlgEquiv (homBasisOf 𝒜 b₀ b₁)).toLinearMap
      = matrixGradingA (sumParity p q) (evenGrading K K) i :=
  map_grading_of_bijective (endGrading 𝒜)
    (matrixGradingA (sumParity p q) (evenGrading K K))
    (LinearMap.toMatrixAlgEquiv (homBasisOf 𝒜 b₀ b₁)).toAlgHom
    (toMatrixAlgEquiv_homBasisOf_isHomogeneous 𝒜 b₀ b₁)
    (LinearMap.toMatrixAlgEquiv (homBasisOf 𝒜 b₀ b₁)).bijective i

end HomBasisOf

section Bundled

variable {K : Type*} [Field K]

/-- **Graded End is a matrix superalgebra, along a given homogeneous
basis**: `End(P) ≅ M_{p|q}(K)` with the frame pinned to the supplied
basis vectors (`homBasisOf_inl`/`homBasisOf_inr`). -/
noncomputable def endMatrixSuperOf (P : SuperAlgebra K) {p q : ℕ}
    (b₀ : Basis (Fin p) K (P.grading 0)) (b₁ : Basis (Fin q) K (P.grading 1)) :
    SuperAlgEquiv P.gEnd ((SuperAlgebra.base K).matrixSuper p q) :=
  ⟨LinearMap.toMatrixAlgEquiv (homBasisOf P.grading b₀ b₁),
    toMatrixAlgEquiv_homBasisOf_map_grading P.grading b₀ b₁⟩

end Bundled

end Superfusion
