import RMod.Classification.Instances.HomogeneousSumTensorData
import RMod.Classification.Proofs.TensorSums
import RMod.Classification.Proofs.TensorCalculus
import RMod.Classification.Proofs.ParityPowers

/-!
# The tensor product of homogeneous sum presentations

The projection sign cancels the sign in super-interchange. The diagonal
and total equations thus have no remaining sign; off-diagonal entries
vanish in at least one factor. Bilinearity then turns the paired total
sum into the tensor of the two original identity sums.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomogeneousSum

variable {C : WeaklyPointedSuperfusion.{u, v}} {S T X Y : C.data.Obj} {n m : ℕ}
  (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data T Y m)

theorem tensor_projector (i : Fin n) (j : Fin m) :
    C.data.comp
      (C.data.smul ((-1 : ℝ) ^ (e.data.parity j * d.data.parity i).val)
        (C.data.tensorHom (d.data.projection i) (e.data.projection j)))
      (C.data.tensorHom (d.data.inclusion i) (e.data.inclusion j)) =
    C.data.tensorHom (C.data.comp (d.data.projection i) (d.data.inclusion i))
      (C.data.comp (e.data.projection j) (e.data.inclusion j)) := by
  rw [C.laws.smul_comp, C.laws.super_interchange _ _ _ _
    (e.laws.inclusion_grade j) (d.laws.projection_grade i),
    ← C.laws.mul_smul, parity_power_mul_self, C.laws.one_smul]

theorem tensorLaws : HomogeneousSumLaws (tensorData d.data e.data) where
  inclusion_grade k := C.laws.tensor_grade _ _ (d.laws.inclusion_grade _) (e.laws.inclusion_grade _)
  projection_grade k := C.laws.grade_smul _ _
    (C.laws.tensor_grade _ _ (d.laws.projection_grade _) (e.laws.projection_grade _))
  diagonal k := by
    dsimp only [tensorData]
    rw [C.laws.comp_smul, C.laws.super_interchange _ _ _ _
      (e.laws.projection_grade _) (d.laws.inclusion_grade _),
      ← C.laws.mul_smul, parity_power_mul_self, C.laws.one_smul,
      d.laws.diagonal, e.laws.diagonal, C.laws.tensor_id]
  off_diagonal i j hij := by
    dsimp only [tensorData]
    rw [C.laws.comp_smul, C.laws.super_interchange _ _ _ _
      (e.laws.projection_grade _) (d.laws.inclusion_grade _)]
    by_cases h : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
    · have h' : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
        intro he
        exact hij (finProdFinEquiv.symm.injective (Prod.ext h he))
      rw [e.laws.off_diagonal _ _ h', tensor_zero_right C.laws,
        C.laws.smul_zero, C.laws.smul_zero]
    · rw [d.laws.off_diagonal _ _ h, tensor_zero_left C.laws,
        C.laws.smul_zero, C.laws.smul_zero]
  total := by
    change C.data.finSum (n * m) (fun k =>
      C.data.comp
        (C.data.smul ((-1 : ℝ) ^
          (e.data.parity (finProdFinEquiv.symm k).2 * d.data.parity (finProdFinEquiv.symm k).1).val)
          (C.data.tensorHom (d.data.projection (finProdFinEquiv.symm k).1)
            (e.data.projection (finProdFinEquiv.symm k).2)))
        (C.data.tensorHom (d.data.inclusion (finProdFinEquiv.symm k).1)
          (e.data.inclusion (finProdFinEquiv.symm k).2))) = _
    simp only [tensor_projector d e]
    rw [finSum_finProd C n m (fun ij => C.data.tensorHom
      (C.data.comp (d.data.projection ij.1) (d.data.inclusion ij.1))
      (C.data.comp (e.data.projection ij.2) (e.data.inclusion ij.2)))]
    simp only [← tensor_finSum_right C]
    rw [← tensor_finSum_left C, d.laws.total, e.laws.total, C.laws.tensor_id]

end RMod.Classification.HomogeneousSum
