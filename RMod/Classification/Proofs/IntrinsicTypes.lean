import RMod.Classification.Proofs.EndDivisionType
import RMod.Classification.Proofs.BrauerWallTypes
import RMod.Classification.Proofs.Pi

/-!
# Intrinsic Clifford types of all simple objects

The algebra classification assigns a real division representative to a
simple endomorphism algebra. Actual finite sums of the specified parity
shifts realize its Clifford stabilization, giving the public HasBWType
predicate. The previously proved Brauer-Wall uniqueness makes this type
unique in every completed Pi-superfusion category, without assuming P.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

variable (C : PiSuperfusion.{0, 0})

attribute [local implicit_reducible] PiSuperfusion.toWeaklyPointedSuperfusion
  CategoryTheory.End Category.endSuperAlgebra Category.endGrading SuperAlgebra.matrixSuper

theorem exists_homogeneous_shift (X : C.data.Obj) (a : ZMod 2) :
    ∃ Y, C.data.HasHomogeneousIso a X Y := by
  rcases parity_cases a with ha | ha <;> subst a
  · exact ⟨X, homogeneousIso_refl C.laws.toWeaklyPointedSuperfusionLaws X⟩
  · exact ⟨C.data.pi.shiftObj X, homogeneousIso_symm
      (C.laws.pi.has_odd_shift C.laws.toWeaklyPointedSuperfusionLaws X)⟩

theorem hasBWType_of_end_realRep (X : C.data.Obj) (r : ZMod 8)
    (eX : SuperAlgEquiv
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory C.toWeaklyPointedSuperfusion) X)
      (realRep r)) : HasBWType C.data.toWeaklyPointedSuperfusionData X r := by
  classical
  obtain ⟨p, q, hpq, ⟨e⟩⟩ := negativeTower_realRep_stabilization r.val
  rw [ZMod.natCast_zmod_val] at e
  let a : Fin (p + q) → ZMod 2 := fun i => sumParity p q (finSumFinEquiv.symm i)
  choose S hS using fun i : Fin (p + q) => exists_homogeneous_shift C X (a i)
  obtain ⟨Y, hY⟩ := C.laws.has_finite_biproducts S
  obtain ⟨d, hd, hda⟩ :=
    exists_homogeneousSum_of_degrees C.laws.toWeaklyPointedSuperfusionLaws a hS hY
  let b : HomogeneousSum C.data.toWeaklyPointedSuperfusionData X Y (p + q) := ⟨d, hd⟩
  let m := b.stabilizationEquivOfIndex (C := C.toWeaklyPointedSuperfusion)
    (finSumFinEquiv.symm : Fin (p + q) ≃ Fin p ⊕ Fin q) (fun i => congrFun hda i)
  let v := m.trans (eX.matrixSuper p q)
  refine ⟨p + q, S, Y, Nat.pos_of_ne_zero hpq, fun i => ⟨a i, hS i⟩, hY, ?_⟩
  exact hasCliffordEnd_of_towerEquiv C.toWeaklyPointedSuperfusion (e.trans v.symm)

theorem simple_has_unique_type (X : C.data.Obj) (hX : C.data.IsSimple X) :
    ∃! r : ZMod 8, HasBWType C.data.toWeaklyPointedSuperfusionData X r := by
  obtain ⟨r, ⟨e⟩⟩ := simple_end_realRep C.toWeaklyPointedSuperfusion X hX
  have hr := hasBWType_of_end_realRep C X r e
  exact ⟨r, hr, fun s hs => HasBWType.unique C.toWeaklyPointedSuperfusion hs hr⟩

end RMod.Classification
