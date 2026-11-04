import RMod.Classification.Proofs.EndDivisionType
import RMod.Classification.Instances.TensorEndEquivalence
import Superfusion.Super.PentagonParity

/-!
# Central simple endomorphisms of products of simples

The intrinsic endomorphism classification and the tensor equivalence
reduce a product of simples to the existing binary fusion of real division
algebras. Its nonempty matrix stabilization has division label r+s. Both
graded centrality and graded simplicity then transport to the product.
These facts concern the abstract category and do not identify its objects
with objects of the concrete reference category.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : LinearCategory C)

noncomputable def tensorEnd_realRep {r s : ZMod 8} (hY : C.data.IsSimple Y)
    (eX : SuperAlgEquiv (endSuperAlgebra (K := ℝ) X) (realRep r))
    (eY : SuperAlgEquiv (endSuperAlgebra (K := ℝ) Y) (realRep s)) :
    SuperAlgEquiv (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y))
      ((realRep (r + s)).matrixSuper (realSize r s).1 (realSize r s).2) :=
  (tensorEndSuperEquiv C X Y hY).symm.trans ((eX.gtensorCongr eY).trans (realFuse r s))

theorem simple_tensor_end_stabilization (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) :
    ∃ r : ZMod 8, ∃ p q : ℕ, p + q ≠ 0 ∧
      Nonempty (SuperAlgEquiv
        (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y))
        ((realRep r).matrixSuper p q)) := by
  obtain ⟨r, ⟨eX⟩⟩ := simple_end_realRep C X hX
  obtain ⟨s, ⟨eY⟩⟩ := simple_end_realRep C Y hY
  exact ⟨r + s, (realSize r s).1, (realSize r s).2, realGauge.size_pos r s,
    ⟨tensorEnd_realRep C X Y hY eX eY⟩⟩

theorem simple_tensor_end_isSuperCentral (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) :
    IsSuperCentral (endGrading (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y)) := by
  obtain ⟨r, p, q, hpq, ⟨e⟩⟩ := simple_tensor_end_stabilization C X Y hX hY
  letI : Nonempty (Fin p ⊕ Fin q) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Nat.pos_of_ne_zero hpq)
  letI := matrixSuper_isSuperCentral (realRep r) p q (realRep_isSuperCentral r)
  exact isSuperCentral_of_equiv _ _ e.symm.toAlgEquiv e.symm.map_grading

theorem simple_tensor_end_isGradedSimple (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) :
    IsGradedSimple (endGrading (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y)) := by
  obtain ⟨r, p, q, hpq, ⟨e⟩⟩ := simple_tensor_end_stabilization C X Y hX hY
  letI : Nonempty (Fin p ⊕ Fin q) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Nat.pos_of_ne_zero hpq)
  letI := matrixSuper_isGradedSimple (realRep r) p q (realRep_isGradedSimple r)
  exact isGradedSimple_of_equiv _ _ e.symm.toAlgEquiv e.symm.map_grading

end RMod.Classification
