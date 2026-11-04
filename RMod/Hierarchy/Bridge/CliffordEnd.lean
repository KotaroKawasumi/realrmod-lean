import RMod.Hierarchy.Bridge.Grading
import RMod.Classification.Proofs.Endomorphisms

/-!
# Clifford endomorphism types survive enrichment

The total endomorphism algebra equivalence preserves each parity. Composing
with it transports the existing graded Clifford algebra test without
changing the quadratic form or the multiplication convention.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem totalEndEquiv_grade (X : C.data.Obj)
    (f : End (totalObj (ofOldSupercategory C) X)) (a : ZMod 2) :
    f ∈ grade (ofOldSupercategory C) X X a ↔
      totalEndEquiv C X f ∈ Classification.LinearCategory.grade C X X a :=
  totalHomEquiv_grade C X X f a

theorem oldCliffordEnd_iff (X : C.data.Obj) (n : ℕ) :
    Classification.HasCliffordEnd C.data X n ↔
      ∃ e : CliffordAlgebra (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin n => (-1 : ℝ))) ≃ₐ[ℝ]
        End (totalObj (ofOldSupercategory C) X),
      ∀ a x, x ∈ CliffordAlgebra.evenOdd
        (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin n => (-1 : ℝ))) a ↔
        e x ∈ grade (ofOldSupercategory C) X X a := by
  rw [Classification.hasCliffordEnd_iff C X n]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (totalEndEquiv C X).symm, fun a x => ?_⟩
    erw [totalEndEquiv_grade, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    exact he a x
  · rintro ⟨e, he⟩
    refine ⟨e.trans (totalEndEquiv C X), fun a x => ?_⟩
    exact (he a x).trans (totalEndEquiv_grade C X (e x) a)

end RMod.Legacy.Hierarchy
