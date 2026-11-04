import RMod.Classification.Proofs.TensorCenter

/-!
# Weak pointedness forces graded centrality

Even supercentral elements commute with all endomorphisms by the direct
sum grading, so the dual-product argument makes them real scalars. A
nonzero odd supercentral element would have a homogeneous inverse by
graded Schur; anticommuting with that inverse would give 1 = -1.
Consequently both layers of the supercenter lie in the scalar submodule.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X : LinearCategory C)

attribute [local implicit_reducible] CategoryTheory.End

theorem even_supercentral_mem_center (z : End X)
    (hz : IsSupercentral (endGrading (K := ℝ) X) 0 z) :
    z ∈ Subalgebra.center ℝ (End X) := by
  apply Subalgebra.mem_center_iff.mpr
  intro f
  obtain ⟨f₀, f₁, hf₀, hf₁, hf⟩ := C.laws.grade_decomposition f
  have h₀ := (isSupercentral_zero_iff _ z).mp hz 0 f₀ hf₀
  have h₁ := (isSupercentral_zero_iff _ z).mp hz 1 f₁ hf₁
  change C.data.comp z f = C.data.comp f z
  rw [← hf, C.laws.comp_add, C.laws.add_comp]
  exact congrArg₂ C.data.add h₀.symm h₁.symm

theorem odd_supercentral_eq_zero (hX : C.data.IsSimple X) (z : End X)
    (hz : z ∈ endGrading (K := ℝ) X 1)
    (hc : IsSupercentral (endGrading (K := ℝ) X) 1 z) : z = 0 := by
  by_contra hne
  obtain ⟨g, hzg, hgz⟩ := C.laws.graded_schur hX hX z hz hne
  have hg := homogeneous_inverse C.laws z g hzg hgz hz
  let g' : End X := g
  have hg' : g' ∈ endGrading (K := ℝ) X 1 := hg
  have hs : z * g' = -(g' * z) :=
    IsSupercentral.odd_anticomm (endGrading (K := ℝ) X) hc hg'
  change C.data.comp g z = C.data.neg (C.data.comp z g) at hs
  rw [hgz, hzg] at hs
  have htwo : (2 : ℝ) • (1 : End X) = 0 :=
    (two_smul ℝ (1 : End X)).trans (eq_neg_iff_add_eq_zero.mp hs)
  have hone : (1 : End X) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact simple_id_ne_zero C.laws hX hone

theorem end_isSuperCentral (hX : C.data.IsSimple X) :
    IsSuperCentral (endGrading (K := ℝ) X) := by
  constructor
  apply sup_le
  · intro z hz
    obtain ⟨r, hr⟩ := even_central_eq_scalar_of_weaklyInvertible C X
      (simple_id_ne_zero C.laws hX) (C.laws.weakly_pointed X hX) z hz.1
      (even_supercentral_mem_center C X z hz.2)
    exact Submodule.mem_one.mpr ⟨r, hr.symm⟩
  · intro z hz
    rw [odd_supercentral_eq_zero C X hX z hz.1 hz.2]
    exact zero_mem _

end RMod.Classification
