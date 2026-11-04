import RMod.Classification.Instances.DualHomEquivalences
import RMod.Classification.Proofs.UnitPairing

/-!
# Dual representation of endomorphisms and their functionals

For a left dual L of X, the dual adjunction identifies End(X) with
Hom(1,L tensor X). The image of the identity is an even vector, and every
endomorphism is its postcomposition with id(L) tensor f. The perfect unit
pairing therefore represents every real functional on End(X) by a cap.
-/

set_option autoImplicit false

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {L X : C.data.Obj} (p : DualPairing C L X)

attribute [local implicit_reducible] CategoryTheory.End
  tensorLeftData tensorLeftSuperfunctor Superfunctor.toFunctor

def endHomLinearEquiv :
    End (C := LinearCategory C) X ≃ₗ[ℝ]
      @Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit (C.data.tensorObj L X) := by
  let e : @CategoryTheory.Iso (LinearCategory C) _ X (C.data.tensorObj X C.data.tensorUnit) :=
    ⟨C.data.rightUnitorInv X, C.data.rightUnitorHom X,
      C.laws.right_unitor_inv_hom X, C.laws.right_unitor_hom_inv X⟩
  exact (CategoryTheory.Linear.homCongr ℝ e (Iso.refl (C := LinearCategory C) X)).trans
    (p.leftHomLinearEquiv C.data.tensorUnit X)

def endUnitVector : C.data.Hom C.data.tensorUnit (C.data.tensorObj L X) :=
  p.endHomLinearEquiv (1 : End (C := LinearCategory C) X)

theorem endHomLinearEquiv_naturality (f : End (C := LinearCategory C) X) :
    p.endHomLinearEquiv f = C.data.comp p.endUnitVector (C.data.tensorHom (C.data.id L) f) := by
  change p.leftAdjunction.homEquiv C.data.tensorUnit X
      (C.data.comp (C.data.comp (C.data.rightUnitorHom X) f) (C.data.id X)) =
    C.data.comp
      (p.leftAdjunction.homEquiv C.data.tensorUnit X
        (C.data.comp (C.data.comp (C.data.rightUnitorHom X) (C.data.id X)) (C.data.id X)))
      (C.data.tensorHom (C.data.id L) f)
  simp only [C.laws.comp_id]
  exact p.leftAdjunction.homEquiv_naturality_right (C.data.rightUnitorHom X) f

theorem endHomLinearEquiv_grade_iff {a : ZMod 2} (f : End (C := LinearCategory C) X) :
    C.data.IsHomogeneous a (p.endHomLinearEquiv f) ↔ C.data.IsHomogeneous a f := by
  change C.data.IsHomogeneous a (p.leftHomLinearEquiv C.data.tensorUnit X
    (C.data.comp (C.data.comp (C.data.rightUnitorHom X) f) (C.data.id X))) ↔ _
  rw [p.leftHomLinearEquiv_grade_iff, C.laws.comp_id]
  constructor
  · intro h
    have hh := C.laws.comp_grade _ _ (C.laws.right_unitor_inv_even X) h
    rw [zero_add, ← C.laws.comp_assoc, C.laws.right_unitor_inv_hom, C.laws.id_comp] at hh
    exact hh
  · intro h
    have hh := C.laws.comp_grade _ _ (C.laws.right_unitor_hom_even X) h
    rw [zero_add] at hh
    exact hh

theorem endUnitVector_even : C.data.IsHomogeneous 0 p.endUnitVector :=
  (p.endHomLinearEquiv_grade_iff _).mpr (C.laws.id_even X)

/-- The cap is explicit data obtained by inverting the proved perfect pairing. -/
noncomputable def endCap (φ : Module.Dual ℝ (End (C := LinearCategory C) X)) :
    C.data.Hom (C.data.tensorObj L X) C.data.tensorUnit :=
  (unitPairing C (C.data.tensorObj L X)).toPerfPair.symm
    (φ.comp p.endHomLinearEquiv.symm.toLinearMap)

theorem endCap_evaluate (φ : Module.Dual ℝ (End (C := LinearCategory C) X))
    (f : End (C := LinearCategory C) X) :
    C.data.comp (C.data.comp p.endUnitVector (C.data.tensorHom (C.data.id L) f)) (p.endCap φ) =
      C.data.smul (φ f) (C.data.id C.data.tensorUnit) := by
  rw [← p.endHomLinearEquiv_naturality]
  have h := DFunLike.congr_fun ((unitPairing C (C.data.tensorObj L X)).apply_symm_toPerfPair_self
    (φ.comp p.endHomLinearEquiv.symm.toLinearMap)) (p.endHomLinearEquiv f)
  apply (unitEndEquiv C).symm.injective
  change unitPairing C (C.data.tensorObj L X) (p.endCap φ) (p.endHomLinearEquiv f) =
    (unitEndEquiv C).symm (unitEndEquiv C (φ f))
  rw [AlgEquiv.symm_apply_apply]
  change _ = φ (p.endHomLinearEquiv.symm (p.endHomLinearEquiv f)) at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end RMod.Classification.DualPairing
