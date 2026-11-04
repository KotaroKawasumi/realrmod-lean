import RMod.Classification.Instances.HomogeneousStabilization
import RMod.Classification.Proofs.Endomorphisms
import RMod.Classification.Proofs.RealCliffordStabilization

/-!
# Connecting the intrinsic Clifford predicate to Brauer--Wall equivalence

The public predicate describes a concrete Clifford endomorphism algebra
on a finite sum. Homogeneous matrix units identify that sum with a
nonempty graded matrix stabilization. Consequently its generator has
the claimed Brauer--Wall class. No BW machinery enters Challenge.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

attribute [local implicit_reducible] CategoryTheory.End
  Category.endSuperAlgebra Category.endGrading

variable (C : WeaklyPointedSuperfusion.{0, 0})

/-- The existing tower realization can also be used to construct the
minimal Mathlib-Clifford predicate in the statement. -/
theorem hasCliffordEnd_of_towerEquiv {X : LinearCategory C} {n : ℕ}
    (e : SuperAlgEquiv (divisionTower (-1 : ℝ) n) (Category.endSuperAlgebra (K := ℝ) X)) :
    HasCliffordEnd C.data X n := by
  let t := towerCliffordEquiv (-1 : ℝ) n (by norm_num)
  apply (hasCliffordEnd_iff C X n).mpr
  refine ⟨t.symm.trans e.toAlgEquiv, ?_⟩
  intro a x
  have h₁ := mem_iff_map_mem (divisionTower (-1 : ℝ) n).grading
    (CliffordAlgebra.evenOdd (diagForm (-1 : ℝ) n)) t
    (fun b => towerCliffordHom_map_grading (-1 : ℝ) n (by norm_num) b)
    (i := a) (x := t.symm x)
  have h₂ := mem_iff_map_mem (divisionTower (-1 : ℝ) n).grading
    (Category.endSuperAlgebra (K := ℝ) X).grading e.toAlgEquiv e.map_grading
    (i := a) (x := t.symm x)
  rw [AlgEquiv.apply_symm_apply] at h₁
  exact h₁.symm.trans h₂

theorem HasCliffordEnd.exists_towerEquiv {X : LinearCategory C} {n : ℕ}
    (h : HasCliffordEnd C.data X n) :
    Nonempty (SuperAlgEquiv (divisionTower (-1 : ℝ) n)
      (Category.endSuperAlgebra (K := ℝ) X)) := by
  obtain ⟨e, he⟩ := (hasCliffordEnd_iff C X n).mp h
  let f := (towerCliffordEquiv (-1 : ℝ) n (by norm_num)).trans e
  letI : GradedAlgebra (Category.endSuperAlgebra (K := ℝ) X).grading :=
    (Category.endSuperAlgebra (K := ℝ) X).gradedAlgebra
  refine ⟨⟨f, ?_⟩⟩
  apply map_grading_of_bijective _ _ f.toAlgHom ?_ f.bijective
  intro a x hx
  apply (he a _).mp
  exact towerCliffordHom_isHomogeneous (-1 : ℝ) n a x hx

/-- The intrinsic type forces equality with the corresponding negative
Clifford tower in the existing graded Morita relation. -/
theorem HasBWType.isBWEquivalent {X : LinearCategory C} {r : ZMod 8}
    (h : HasBWType C.data X r) :
    IsBWEquivalent (Category.endSuperAlgebra (K := ℝ) X) (divisionTower (-1 : ℝ) r.val) := by
  obtain ⟨n, S, Y, hn, hS, hY, hcl⟩ := h
  obtain ⟨d, hd⟩ := exists_homogeneousSum C.laws hS hY
  obtain ⟨e⟩ := HasCliffordEnd.exists_towerEquiv C (X := Y) hcl
  exact (HomogeneousSum.isBWEquivalent (C := C) (X := X) (Y := Y) ⟨d, hd⟩ hn).symm.trans
    (IsBWEquivalent.of_superAlgEquiv e.symm)

/-- Uniqueness follows from the Clifford test itself, without assuming P. -/
theorem HasBWType.unique {X : LinearCategory C} {r s : ZMod 8}
    (hr : HasBWType C.data X r) (hs : HasBWType C.data X s) : r = s :=
  negativeTower_label_eq ((hr.isBWEquivalent C).symm.trans (hs.isBWEquivalent C))

end RMod.Classification
