import RMod.Classification.Instances.BiconeSelectGraph
import Mathlib.Data.Fintype.BigOperators

/-!
# Universality after removing zero component entries

If the retract inclusion has zero entries away from the selected graph,
the full total identity reduces to the graph sum. The retract identity
then proves that the selected bicone is again a bilimit.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C] {I J : Type*} [Fintype I] [Fintype J]
  {V : I × J → C}

noncomputable def biconeSelectGraph_isBilimit (b : Bicone V) (hb : b.IsBilimit)
    (s : I → J) {R : C} (incl : R ⟶ b.pt) (proj : b.pt ⟶ R)
    (hgraph : ∀ i, b.ι (i, s i) ≫ proj ≫ incl = b.ι (i, s i))
    (hzero : ∀ i j, j ≠ s i → incl ≫ b.π (i, j) = 0)
    (hretract : incl ≫ proj = 𝟙 R) : (biconeSelectGraph b s incl proj hgraph).IsBilimit := by
  classical
  apply isBilimitOfTotal
  change (∑ i, (incl ≫ b.π (i, s i)) ≫ (b.ι (i, s i) ≫ proj)) = 𝟙 R
  calc
    _ = ∑ i, ∑ j, (incl ≫ b.π (i, j)) ≫ (b.ι (i, j) ≫ proj) := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_eq_single (s i)
      · intro j _ hj
        rw [hzero i j hj, Limits.zero_comp]
      · intro hi
        exact False.elim (hi (Finset.mem_univ (s i)))
    _ = incl ≫ (∑ ij : I × J, b.π ij ≫ b.ι ij) ≫ proj := by
      simp only [Fintype.sum_prod_type, comp_sum, sum_comp, Category.assoc]
    _ = 𝟙 R := by rw [IsBilimit.total hb, Category.id_comp, hretract]

end RMod.Classification
