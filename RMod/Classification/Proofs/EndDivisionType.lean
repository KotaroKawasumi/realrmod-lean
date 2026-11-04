import RMod.Classification.Proofs.EndSuperCentral
import Superfusion.Gauge.RealClassification2

/-!
# The eight possible simple endomorphism superalgebras

Graded Schur supplies homogeneous units, while the dual-product argument
supplies graded centrality. The existing real central division theorem can
therefore be applied to any simple object, independently of P or any
chosen reference category. No new algebra-classification assumption is used.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X : LinearCategory C)

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

theorem end_isSuperDivision (hX : C.data.IsSimple X) :
    Bimod.IsSuperDivision (endGrading (K := ℝ) X) := by
  intro i f hf hne
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur hX hX f hf hne
  exact ⟨⟨f, g, hgf, hfg⟩, rfl⟩

theorem simple_end_realRep (hX : C.data.IsSimple X) :
    ∃ r : ZMod 8, Nonempty (SuperAlgEquiv (endSuperAlgebra (K := ℝ) X) (realRep r)) := by
  letI : IsSuperCentral (endSuperAlgebra (K := ℝ) X).grading := end_isSuperCentral C X hX
  letI : FiniteDimensional ℝ (endSuperAlgebra (K := ℝ) X).carrier :=
    LinearCategory.finiteDimensionalHom C X X
  letI : Nontrivial (endSuperAlgebra (K := ℝ) X).carrier :=
    ⟨⟨1, 0, simple_id_ne_zero C.laws hX⟩⟩
  exact real_superDivision_classification _ (end_isSuperDivision C X hX)

end RMod.Classification
