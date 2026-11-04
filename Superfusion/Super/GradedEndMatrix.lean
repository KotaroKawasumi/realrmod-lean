/-
Superfusion / Super / GradedEndMatrix

Milestone M7f-4c: **the graded endomorphism algebra of a
finite-dimensional superalgebra is a matrix superalgebra**:

  `End K A ≅ M_{p|q}(K)`,  `p = dim 𝒜₀`, `q = dim 𝒜₁`,

as graded algebras, via a homogeneous basis (bases of the even and
odd parts glued along the decomposition).  The point: in a
homogeneous basis, an endomorphism of degree `i` has matrix support
on the index pairs `(r, s)` with `π r + π s = i` — which is exactly
the matrix grading of `M_{p|q}(K)`.

Combined with Wall's isomorphism (M7f-2a) this yields the
Brauer–Wall inverse law: for a nontrivial finite-dimensional
super-Azumaya algebra `P` over a field,
`P ᵍ⊗ P^sop ≅ End(P) ~ 1` (BW-equivalent to the base field).
-/
import Superfusion.Super.WallGraded
import Superfusion.Super.BWTransitivity
import Superfusion.Super.TensorGradingUnitor

namespace Superfusion

open Module

/-! ### The homogeneous basis -/

section HomBasis

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- The even and odd parts are complementary. -/
theorem isCompl_grades : IsCompl (𝒜 0) (𝒜 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x h0 h1
    have h := evenPart_of_mem_zero 𝒜 h0
    rw [evenPart_of_mem_one 𝒜 h1] at h
    exact h.symm
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [show x = evenPart 𝒜 x + oddPart 𝒜 x from
      (evenPart_add_oddPart 𝒜 x).symm]
    exact Submodule.add_mem_sup (evenPart_mem 𝒜 x) (oddPart_mem 𝒜 x)

variable [FiniteDimensional K A]

/-- A homogeneous basis of a finite-dimensional superalgebra: bases
of the even and odd parts, glued along the decomposition.  The index
parity is `sumParity`. -/
noncomputable def homBasis :
    Basis (Fin (finrank K (𝒜 0)) ⊕ Fin (finrank K (𝒜 1))) K A :=
  ((finBasis K (𝒜 0)).prod (finBasis K (𝒜 1))).map
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_grades 𝒜))

private theorem homBasis_inl (k : Fin (finrank K (𝒜 0))) :
    homBasis 𝒜 (Sum.inl k) = ((finBasis K (𝒜 0)) k : A) := by
  rw [homBasis, Basis.map_apply,
    show ((finBasis K (𝒜 0)).prod (finBasis K (𝒜 1))) (Sum.inl k)
      = ((finBasis K (𝒜 0)) k, (0 : 𝒜 1)) from
      Prod.ext (Basis.prod_apply_inl_fst _ _ _)
        (Basis.prod_apply_inl_snd _ _ _),
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

private theorem homBasis_inr (k : Fin (finrank K (𝒜 1))) :
    homBasis 𝒜 (Sum.inr k) = ((finBasis K (𝒜 1)) k : A) := by
  rw [homBasis, Basis.map_apply,
    show ((finBasis K (𝒜 0)).prod (finBasis K (𝒜 1))) (Sum.inr k)
      = ((0 : 𝒜 0), (finBasis K (𝒜 1)) k) from
      Prod.ext (Basis.prod_apply_inr_fst _ _ _)
        (Basis.prod_apply_inr_snd _ _ _),
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

/-- The homogeneous basis is homogeneous: the vector at index `r`
lies in degree `sumParity r`. -/
theorem homBasis_mem
    (r : Fin (finrank K (𝒜 0)) ⊕ Fin (finrank K (𝒜 1))) :
    homBasis 𝒜 r
      ∈ 𝒜 (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)) r) := by
  cases r with
  | inl k =>
      rw [show sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))
          (Sum.inl k) = 0 from rfl, homBasis_inl]
      exact SetLike.coe_mem _
  | inr k =>
      rw [show sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))
          (Sum.inr k) = 1 from rfl, homBasis_inr]
      exact SetLike.coe_mem _

/-- **Support lemma**: the coordinates of a homogeneous element along
the homogeneous basis vanish at indices of the other parity. -/
theorem homBasis_repr_eq_zero {j : ZMod 2} {x : A} (hx : x ∈ 𝒜 j)
    {r : Fin (finrank K (𝒜 0)) ⊕ Fin (finrank K (𝒜 1))}
    (hr : sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)) r ≠ j) :
    (homBasis 𝒜).repr x r = 0 := by
  have hrepr : ∀ y : A, (homBasis 𝒜).repr y
      = ((finBasis K (𝒜 0)).prod (finBasis K (𝒜 1))).repr
          ((Submodule.prodEquivOfIsCompl _ _
            (isCompl_grades 𝒜)).symm y) := fun y => rfl
  cases r with
  | inl k =>
      rw [show sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))
          (Sum.inl k) = 0 from rfl] at hr
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
      rw [show sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1))
          (Sum.inr k) = 1 from rfl] at hr
      have hj : j = 0 := by
        rcases zmod2_cases j with h | h
        · exact h
        · exact absurd h.symm hr
      subst hj
      have hs := Submodule.prodEquivOfIsCompl_symm_apply_left
        (𝒜 0) (𝒜 1) (isCompl_grades 𝒜) (⟨x, hx⟩ : 𝒜 0)
      rw [show ((⟨x, hx⟩ : 𝒜 0) : A) = x from rfl] at hs
      rw [hrepr, hs, Basis.prod_repr_inr, map_zero, Finsupp.zero_apply]

/-! ### The matrix superalgebra structure of graded End -/

private theorem zmod2_endmat : ∀ i a b : ZMod 2,
    i + a + b = 1 → a ≠ b + i := by decide

/-- In the homogeneous basis, a homogeneous endomorphism of degree
`i` has matrix support on index pairs with `π r + π s = i`. -/
theorem toMatrixAlgEquiv_homBasis_isHomogeneous :
    IsHomogeneousHom (endGrading 𝒜)
      (matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)))
        (evenGrading K K))
      (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).toAlgHom := by
  intro i f hf r s
  rw [show ((LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).toAlgHom f) r s
      = (homBasis 𝒜).repr (f (homBasis 𝒜 s)) r from
      LinearMap.toMatrixAlgEquiv_apply _ f r s]
  have hfs : f (homBasis 𝒜 s)
      ∈ 𝒜 (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)) s + i) :=
    (mem_endGrading 𝒜).mp hf _ _ (homBasis_mem 𝒜 s)
  rcases zmod2_cases
      (i + sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)) r
        + sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)) s)
    with hc | hc
  · rw [hc, evenGrading_zero]
    exact Submodule.mem_top
  · rw [hc, evenGrading_one, Submodule.mem_bot]
    exact homBasis_repr_eq_zero 𝒜 hfs (zmod2_endmat i _ _ hc)

/-- The matrix realization carries the End grading **onto** the
matrix grading. -/
theorem toMatrixAlgEquiv_homBasis_map_grading (i : ZMod 2) :
    (endGrading 𝒜 i).map
        (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).toLinearMap
      = matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)))
          (evenGrading K K) i :=
  map_grading_of_bijective (endGrading 𝒜)
    (matrixGradingA (sumParity (finrank K (𝒜 0)) (finrank K (𝒜 1)))
      (evenGrading K K))
    (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).toAlgHom
    (toMatrixAlgEquiv_homBasis_isHomogeneous 𝒜)
    (LinearMap.toMatrixAlgEquiv (homBasis 𝒜)).bijective i

end HomBasis

/-! ### Bundled: graded End, Wall's isomorphism, and the inverse law -/

section Bundled

variable {K : Type*} [CommRing K]

/-- The graded endomorphism algebra, bundled. -/
noncomputable def SuperAlgebra.gEnd (P : SuperAlgebra K) :
    SuperAlgebra K where
  carrier := Module.End K P.carrier
  grading := endGrading P.grading

/-- **Wall's isomorphism, bundled** (M7f-2a): for a super-Azumaya
algebra, `P ᵍ⊗ P^sop ≅ End(P)` as superalgebras. -/
noncomputable def wallSuperEquiv (P : SuperAlgebra K)
    [IsSuperAzumaya P.grading] :
    SuperAlgEquiv (P.gtensor P.sop) P.gEnd :=
  ⟨AlgEquiv.ofBijective (superMulLeftRight P.grading) IsSuperAzumaya.bij,
    superMulLeftRight_map_grading P.grading⟩

end Bundled

section Field

variable {K : Type*} [Field K]

/-- **Graded End is a matrix superalgebra** (M7f-4c):
`End(P) ≅ M_{p|q}(K)`, `p = dim P₀`, `q = dim P₁`. -/
noncomputable def endMatrixSuper (P : SuperAlgebra K)
    [FiniteDimensional K P.carrier] :
    SuperAlgEquiv P.gEnd
      ((SuperAlgebra.base K).matrixSuper
        (finrank K (P.grading 0)) (finrank K (P.grading 1))) :=
  ⟨LinearMap.toMatrixAlgEquiv (homBasis P.grading),
    toMatrixAlgEquiv_homBasis_map_grading P.grading⟩

theorem finrank_grade_add_ne_zero (P : SuperAlgebra K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier] :
    finrank K (P.grading 0) + finrank K (P.grading 1) ≠ 0 := by
  intro h
  obtain ⟨h0, h1⟩ := Nat.add_eq_zero_iff.mp h
  rw [Submodule.finrank_eq_zero] at h0 h1
  obtain ⟨x, hx⟩ := exists_ne (0 : P.carrier)
  apply hx
  have e0 : evenPart P.grading x = 0 := by
    have h' := evenPart_mem P.grading x
    rwa [h0, Submodule.mem_bot] at h'
  have e1 : oddPart P.grading x = 0 := by
    have h' := oddPart_mem P.grading x
    rwa [h1, Submodule.mem_bot] at h'
  rw [← evenPart_add_oddPart P.grading x, e0, e1, add_zero]

/-- `[End P] = 1` in the Brauer–Wall relation. -/
theorem isBWEquivalent_gEnd_base (P : SuperAlgebra K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier] :
    IsBWEquivalent P.gEnd (SuperAlgebra.base K) :=
  IsBWEquivalent.of_matrixSuper (finrank_grade_add_ne_zero P)
    (endMatrixSuper P)

/-- **The Brauer–Wall inverse law** (M7f-4c): for a nontrivial
finite-dimensional super-Azumaya algebra over a field,
`[P]·[P^sop] = 1`. -/
theorem isBWEquivalent_gtensor_sop_base (P : SuperAlgebra K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [IsSuperAzumaya P.grading] :
    IsBWEquivalent (P.gtensor P.sop) (SuperAlgebra.base K) :=
  (IsBWEquivalent.of_superAlgEquiv (wallSuperEquiv P)).trans
    (isBWEquivalent_gEnd_base P)

end Field

end Superfusion
