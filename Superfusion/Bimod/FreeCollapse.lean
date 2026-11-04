/-
Superfusion / Bimod / FreeCollapse

Milestone M8a-8b-1: **the free-column collapse**

  `(n → A) ⊗[A] N ≃ (n → N)`,   `v ⊗ w ↦ (j ↦ v_j • w)`,

for a finite index type `n`: the balanced tensor product of a free
right module of finite rank with any left module collapses to a
column of copies.  The inverse sends `g` to `∑ j, e_j ⊗ g j` (with
`e_j = Pi.single j 1`), and the round trips are the balancing relation
`e_j ⊗ (a • w) = (e_j · a) ⊗ w` plus `∑ j, single j (v j) = v`.

This is the engine of the paper's identification of
`B_L = C_{a,b} ⊗_{T_{a+b}} C_{a+b,c}` with the column bimodule of the
composite matrix superalgebra (§4.1): the first column is free over
the middle algebra, so the fusion is a column of copies of the second
column.  The transport of the graded/bimodule structure along the
collapse is the next step.
-/
import Superfusion.Bimod.RelTensorMap

namespace Superfusion

namespace Bimod

namespace RelTensor

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable [IsScalarTower K A N]

/-- The collapse bilinear map `(v, w) ↦ (j ↦ v_j • w)`. -/
private noncomputable def collapseBilin :
    (n → A) →ₗ[K] N →ₗ[K] (n → N) :=
  LinearMap.mk₂ K (fun v w => fun j => v j • w)
    (fun v v' w => funext fun j => by
      show (v + v') j • w = v j • w + v' j • w
      rw [Pi.add_apply, add_smul])
    (fun k v w => funext fun j => by
      show (k • v) j • w = k • (v j • w)
      rw [Pi.smul_apply, smul_assoc])
    (fun v w w' => funext fun j => by
      show v j • (w + w') = v j • w + v j • w'
      rw [smul_add])
    (fun k v w => funext fun j => by
      show v j • (k • w) = k • (v j • w)
      rw [smul_comm])

omit [Fintype n] [DecidableEq n] in
private theorem collapseBilin_apply (v : n → A) (w : N) :
    collapseBilin (K := K) v w = fun j => v j • w := rfl

omit [Fintype n] [DecidableEq n] in
private theorem collapseBilin_balanced :
    IsBalanced A (collapseBilin (K := K) (A := A) (n := n) (N := N)) := by
  intro a v w
  refine funext fun j => ?_
  show (MulOpposite.op a • v) j • w = v j • (a • w)
  rw [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    mul_smul]

/-- **The free-column collapse**: `(n → A) ⊗[A] N ≃ (n → N)`,
`v ⊗ w ↦ (j ↦ v_j • w)`. -/
noncomputable def freeCollapse :
    ((n → A) ⊗[A;K] N) ≃ₗ[K] (n → N) :=
  LinearEquiv.ofLinear
    (lift collapseBilin collapseBilin_balanced)
    (∑ j : n, (mk K A (n → A) N (Pi.single j 1)).comp (LinearMap.proj j))
    (by
      refine LinearMap.ext fun g => funext fun k => ?_
      rw [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.sum_apply,
        map_sum, Finset.sum_apply]
      have hterm : ∀ j : n,
          (lift collapseBilin collapseBilin_balanced
            (((mk K A (n → A) N (Pi.single j 1)).comp
              (LinearMap.proj j)) g)) k
          = (Pi.single j 1 : n → A) k • g j := fun j => by
        rw [LinearMap.comp_apply]
        show (lift collapseBilin collapseBilin_balanced
          (mk K A (n → A) N (Pi.single j 1) (g j))) k = _
        rw [lift_mk, collapseBilin_apply]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      rw [show (fun j => (Pi.single j 1 : n → A) k • g j)
          = fun j => if j = k then g j else 0 from funext fun j => by
        rcases eq_or_ne j k with hj | hj
        · subst hj
          rw [if_pos rfl, Pi.single_eq_same, one_smul]
        · rw [if_neg hj, Pi.single_eq_of_ne (Ne.symm hj), zero_smul]]
      rw [Finset.sum_ite_eq' Finset.univ k (fun j => g j),
        if_pos (Finset.mem_univ k)])
    (by
      refine hom_ext fun v w => ?_
      rw [LinearMap.comp_apply, LinearMap.id_apply, lift_mk]
      rw [LinearMap.sum_apply]
      have hterm : ∀ j : n,
          ((mk K A (n → A) N (Pi.single j 1)).comp (LinearMap.proj j))
            (collapseBilin (K := K) v w)
          = mk K A (n → A) N (Pi.single j (v j)) w := fun j => by
        rw [LinearMap.comp_apply]
        show mk K A (n → A) N (Pi.single j 1) (v j • w) = _
        have hsingle : MulOpposite.op (v j) • (Pi.single j 1 : n → A)
            = Pi.single j (v j) := by
          funext k
          show (Pi.single j 1 : n → A) k * v j = (Pi.single j (v j) : n → A) k
          rcases eq_or_ne k j with hk | hk
          · subst hk
            rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
          · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, zero_mul]
        rw [← mk_op_smul, hsingle]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      rw [show ∑ j : n, mk K A (n → A) N (Pi.single j (v j)) w
          = mk K A (n → A) N (∑ j : n, Pi.single j (v j)) w from by
        rw [map_sum, LinearMap.sum_apply]]
      rw [Finset.univ_sum_single])

theorem freeCollapse_mk (v : n → A) (w : N) :
    freeCollapse (mk K A (n → A) N v w) = fun j => v j • w := by
  show lift collapseBilin collapseBilin_balanced
    (mk K A (n → A) N v w) = _
  rw [lift_mk]
  rfl

theorem freeCollapse_symm_apply (g : n → N) :
    freeCollapse.symm g
      = ∑ j : n, mk K A (n → A) N (Pi.single j 1) (g j) := by
  show (∑ j : n, (mk K A (n → A) N (Pi.single j 1)).comp
    (LinearMap.proj j)) g = _
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

end RelTensor

end Bimod

end Superfusion
