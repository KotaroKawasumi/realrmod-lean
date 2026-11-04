import Superfusion.Gauge.RealReps
import Superfusion.RMod.FromRawDCT.RealFinite

/-!
# Super-division for the real coordinate coefficients

This concrete proof layer identifies support in the stored coordinate basis
with the semantic grading of `realRep`.  It then transports the already proved
super-division theorem back to the executable coefficient vectors.  No inverse
operation is added to the candidate data: the inverse is chosen only inside a
proposition.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RModCoordinate

namespace RealDivision

/-! ## Coordinate grading and semantic grading -/

private theorem zmod2_eq_add_one_of_ne (p d : ZMod 2) (h : p ≠ d) :
    p = d + 1 := by
  rcases zmod2_cases p with hp | hp <;>
    rcases zmod2_cases d with hd | hd <;>
    subst p <;> subst d <;> simp_all [Coeff.add_self_eq_zero]

/-- Coordinate support in degree `d` gives semantic homogeneity. -/
theorem semantic_mem_of_memGrade (a : ZMod 8) (d : ZMod 2) (x : Coeff a)
    (hx : Coeff.MemGrade a d x) :
    Coeff.semantic a x ∈ (realRep a).grading d := by
  classical
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : realRepBasisParity a i = d
  · exact Submodule.smul_mem _ _ (hi ▸ realRepBasis_mem a i)
  · rw [hx i hi, zero_smul]
    exact Submodule.zero_mem _

/-- The canonical homogeneous basis detects coordinate support exactly. -/
theorem semantic_mem_iff_memGrade (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    Coeff.semantic a x ∈ (realRep a).grading d ↔
      Coeff.MemGrade a d x := by
  constructor
  · intro hx
    let xd : Coeff a := Coeff.component a d x
    let xo : Coeff a := Coeff.component a (d + 1) x
    have hxd : Coeff.semantic a xd ∈ (realRep a).grading d :=
      semantic_mem_of_memGrade a d xd (Coeff.component_memGrade a d x)
    have hxo' : Coeff.semantic a xo ∈ (realRep a).grading (d + 1) :=
      semantic_mem_of_memGrade a (d + 1) xo
        (Coeff.component_memGrade a (d + 1) x)
    have hsplit : Coeff.add a xd xo = x :=
      Coeff.component_complement a d x
    have hsem : Coeff.semantic a xd + Coeff.semantic a xo =
        Coeff.semantic a x := by
      rw [← Coeff.semantic_add, hsplit]
    have hxo : Coeff.semantic a xo ∈ (realRep a).grading d := by
      have heq : Coeff.semantic a xo =
          Coeff.semantic a x - Coeff.semantic a xd := by
        rw [← hsem]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hx hxd
    have hzero : Coeff.semantic a xo = 0 := by
      rcases zmod2_cases d with hd | hd <;> subst d
      · exact (isCompl_grades (realRep a).grading).disjoint.le_bot
          ⟨hxo, hxo'⟩
      · exact (isCompl_grades (realRep a).grading).disjoint.symm.le_bot
          ⟨hxo, hxo'⟩
    have hxo0 : xo = Coeff.zero a := by
      apply (Coeff.semantic a).injective
      rw [hzero, Coeff.semantic_zero]
    intro i hi
    have hp : realRepBasisParity a i = d + 1 :=
      zmod2_eq_add_one_of_ne _ _ hi
    have hcoord := congrFun hxo0 i
    simpa [xo, Coeff.component, hp, Coeff.zero] using hcoord
  · exact semantic_mem_of_memGrade a d x

/-! ## Transport of semantic super-division -/

/-- Every nonzero homogeneous real coordinate coefficient has a homogeneous
two-sided inverse of the same degree.  Equality of the degree with its inverse
uses that the grading group is `ZMod 2`. -/
theorem exists_homogeneous_inverse (a : ZMod 8) (d : ZMod 2) (x : Coeff a)
    (hx : Coeff.MemGrade a d x) (hx0 : x ≠ Coeff.zero a) :
    ∃ y : Coeff a,
      Coeff.MemGrade a d y ∧
        Coeff.mul a y x = Coeff.one a ∧
        Coeff.mul a x y = Coeff.one a := by
  classical
  have hsx : Coeff.semantic a x ∈ (realRep a).grading d :=
    semantic_mem_of_memGrade a d x hx
  have hsx0 : Coeff.semantic a x ≠ 0 := by
    intro hzero
    apply hx0
    apply (Coeff.semantic a).injective
    rw [hzero, Coeff.semantic_zero]
  obtain ⟨u, hu⟩ := realRep_isSuperDivision a hsx hsx0
  let y : Coeff a :=
    (Coeff.semantic a).symm
      (((u⁻¹ : (realRep a).carrierˣ) : (realRep a).carrier))
  have hsy : Coeff.semantic a y =
      ((u⁻¹ : (realRep a).carrierˣ) : (realRep a).carrier) :=
    (Coeff.semantic a).apply_symm_apply _
  have hsy_mem : Coeff.semantic a y ∈ (realRep a).grading d := by
    rw [hsy]
    exact Bimod.isUnit_inv_mem hsx u hu
  refine ⟨y, (semantic_mem_iff_memGrade a d y).mp hsy_mem, ?_, ?_⟩
  · apply (Coeff.semantic a).injective
    rw [Coeff.semantic_mul, Coeff.semantic_one, hsy, ← hu]
    exact u.inv_mul
  · apply (Coeff.semantic a).injective
    rw [Coeff.semantic_mul, Coeff.semantic_one, hsy, ← hu]
    exact u.mul_inv

end RealDivision

end Superfusion.RMod.FromRawDCT
