import RMod.Classification.Instances.EndGrading
import RMod.Classification.Instances.RealPiLaws
import Superfusion.RMod.FromRawDCT.RealDivision

/-!
# The endomorphism algebra of a real singleton

Evaluating its sole matrix entry and interpreting the coefficient in the
existing real division representative gives an algebra equivalence.
The two endpoint parity shifts cancel, so this equivalence is graded.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.RMod.FromRawDCT
open Superfusion.RMod.RawDCT Superfusion.RModCoordinate

attribute [local implicit_reducible] CategoryTheory.End
  Category.endSuperAlgebra Category.endGrading Obj.singleton Obj.size Obj.atom
  realRModLegacy realRModData realEndpointCandidateData Candidate.dataWithAssociator

/-- The coefficient of the sole matrix entry of an endomorphism. -/
noncomputable def realSingletonEndLinearEquiv (a : ZMod 8) (s : ZMod 2) :
    End (C := LinearCategory realRModLegacy) (Obj.singleton (a, s)) ≃ₗ[ℝ] (realRep a).carrier where
  toFun f := Coeff.semantic a ((f 0 0).coeff rfl)
  invFun x := fun _ _ => AtomHom.ofLabelEq rfl ((Coeff.semantic a).symm x)
  left_inv f := by
    funext i j
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i; subst j
    apply AtomHom.ext_same_label
    rw [AtomHom.coeff_ofLabelEq, LinearEquiv.symm_apply_apply]
  right_inv x := by
    change Coeff.semantic a ((AtomHom.ofLabelEq (dD := realDData)
      (X := (a, s)) (Y := (a, s)) rfl ((Coeff.semantic a).symm x)).coeff rfl) = x
    rw [AtomHom.coeff_ofLabelEq, LinearEquiv.apply_symm_apply]
  map_add' f g := by
    change Coeff.semantic a ((AtomHom.add (f 0 0) (g 0 0)).coeff rfl) = _
    rw [AtomHom.coeff_add]
    exact Coeff.semantic_add a _ _
  map_smul' r f := by
    change Coeff.semantic a ((AtomHom.smul r (f 0 0)).coeff rfl) = _
    rw [AtomHom.coeff_smul]
    exact Coeff.semantic_smul a r _

/-- The categorical product has the correct order for the coefficient
algebra: f*g is g followed by f. -/
noncomputable def realSingletonEndAlgEquiv (a : ZMod 8) (s : ZMod 2) :
    End (C := LinearCategory realRModLegacy) (Obj.singleton (a, s)) ≃ₐ[ℝ] (realRep a).carrier :=
  AlgEquiv.ofLinearEquiv (realSingletonEndLinearEquiv a s)
    (by
      change Coeff.semantic a (((Hom.id realDData (Obj.singleton (a, s))) 0 0).coeff rfl) = 1
      simp only [Hom.id, dite_true, AtomHom.coeff_id]
      exact Coeff.semantic_one a)
    (fun f g => by
      change Coeff.semantic a ((Hom.comp g f 0 0).coeff rfl) = _
      have hc : Hom.comp g f 0 0 = AtomHom.comp (g 0 0) (f 0 0) := by
        change AtomHom.add (AtomHom.zero realDData (a, s) (a, s))
          (AtomHom.comp (g 0 0) (f 0 0)) = _
        exact AtomHom.zero_add realDLaws _
      rw [hc, AtomHom.coeff_comp_same_label]
      change Coeff.semantic a (Coeff.mul a ((f 0 0).coeff rfl) ((g 0 0).coeff rfl)) = _
      exact Coeff.semantic_mul a _ _)

theorem realSingletonEndAlgEquiv_grade_iff (a : ZMod 8) (s b : ZMod 2)
    (f : End (C := LinearCategory realRModLegacy) (Obj.singleton (a, s))) :
    realRModData.IsHomogeneous b f ↔ realSingletonEndAlgEquiv a s f ∈ (realRep a).grading b := by
  have hp : b + s + s = b := by simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  change Hom.MemGrade b f ↔ Coeff.semantic a ((f 0 0).coeff rfl) ∈ (realRep a).grading b
  rw [RealDivision.semantic_mem_iff_memGrade]
  constructor
  · intro hf
    have h := hf 0 0 rfl
    change Coeff.component a (b + s + s) ((f 0 0).coeff rfl) = (f 0 0).coeff rfl at h
    rw [hp] at h
    exact (Coeff.component_eq_self_iff a b _).mp h
  · intro hf i j h
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i; subst j
    change Coeff.component a (b + s + s) ((f 0 0).coeff h) = (f 0 0).coeff h
    rw [hp]
    apply (Coeff.component_eq_self_iff a b _).mpr
    simpa only [Subsingleton.elim h rfl] using hf

/-- The exact graded algebra comparison used in the reference proof. -/
noncomputable def realSingletonEndSuperEquiv (a : ZMod 8) (s : ZMod 2) :
    SuperAlgEquiv
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory realRModLegacy) (Obj.singleton (a, s)))
      (realRep a) where
  toAlgEquiv := realSingletonEndAlgEquiv a s
  map_grading b := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (realSingletonEndAlgEquiv_grade_iff a s b f).mp hf
    · intro hx
      refine ⟨(realSingletonEndAlgEquiv a s).symm x, ?_, AlgEquiv.apply_symm_apply _ x⟩
      apply (realSingletonEndAlgEquiv_grade_iff a s b _).mpr
      simpa only [AlgEquiv.apply_symm_apply] using hx

/-! The comparisons detect both a nonzero scalar and its sign. -/

example : realSingletonEndAlgEquiv 0 0 (2 : End
    (C := LinearCategory realRModLegacy) (Obj.singleton (0, 0))) ≠ 0 := by
  rw [map_ofNat]
  exact (by norm_num : (2 : ℝ) ≠ 0)

example : realSingletonEndAlgEquiv 0 1 (-1 : End
    (C := LinearCategory realRModLegacy) (Obj.singleton (0, 1))) ≠ 1 := by
  rw [map_neg, map_one]
  exact (by norm_num : (-1 : ℝ) ≠ 1)

end RMod.Classification
