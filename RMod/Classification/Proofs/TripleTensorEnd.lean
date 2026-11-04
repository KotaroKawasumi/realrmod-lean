import RMod.Classification.Proofs.SimpleTensorEnd
import Superfusion.Super.MatrixSuperTensor

/-!
# The endomorphism algebra of a triple of simple objects

First stabilize the binary product. Tensoring its matrix superalgebra
with the third division algebra commutes with matrix stabilization.
Binary real fusion then gives a second nonempty stabilization. Repeated
matrix centrality proves that the original triple has real supercenter.
This does not assert that a tensor product of simples is simple.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y Z : LinearCategory C)

theorem simple_triple_tensor_end_stabilization
    (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) (hZ : C.data.IsSimple Z) :
    ∃ r : ZMod 8, ∃ p q m n : ℕ, p + q ≠ 0 ∧ m + n ≠ 0 ∧
      Nonempty (SuperAlgEquiv
        (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj (C.data.tensorObj X Y) Z))
        (((realRep r).matrixSuper p q).matrixSuper m n)) := by
  obtain ⟨r, m, n, hmn, ⟨eXY⟩⟩ := simple_tensor_end_stabilization C X Y hX hY
  obtain ⟨s, ⟨eZ⟩⟩ := simple_end_realRep C Z hZ
  let e := (tensorEndSuperEquiv C (C.data.tensorObj X Y) Z hZ).symm.trans
    ((eXY.gtensorCongr eZ).trans
      ((matrixSuperGtensor (realRep r) (realRep s) m n).trans ((realFuse r s).matrixSuper m n)))
  exact ⟨r + s, (realSize r s).1, (realSize r s).2, m, n, realGauge.size_pos r s, hmn, ⟨e⟩⟩

theorem simple_triple_tensor_end_isSuperCentral
    (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) (hZ : C.data.IsSimple Z) :
    IsSuperCentral (endGrading (K := ℝ) (C := LinearCategory C) (C.data.tensorObj (C.data.tensorObj X Y) Z)) := by
  obtain ⟨r, p, q, m, n, hpq, hmn, ⟨e⟩⟩ := simple_triple_tensor_end_stabilization C X Y Z hX hY hZ
  letI : Nonempty (Fin p ⊕ Fin q) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Nat.pos_of_ne_zero hpq)
  letI : Nonempty (Fin m ⊕ Fin n) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Nat.pos_of_ne_zero hmn)
  letI := matrixSuper_isSuperCentral ((realRep r).matrixSuper p q) m n
    (matrixSuper_isSuperCentral (realRep r) p q (realRep_isSuperCentral r))
  exact isSuperCentral_of_equiv _ _ e.symm.toAlgEquiv e.symm.map_grading

end RMod.Classification
