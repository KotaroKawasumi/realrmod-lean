import RMod.Classification.Instances.Decomposition
import RMod.Classification.Instances.EndGrading
import RMod.Classification.Proofs.TensorCalculus

/-!
# Central diagonal weights in a finite decomposition

Diagonal weights are even. If the two weights agree on every nonzero Hom
block, the resulting endomorphism is central. A scalar diagonal has that
same scalar on each nonzero summand. These statements use the specified
inclusions and projections, so no decomposition choices enter the laws.
-/

set_option autoImplicit false

namespace RMod.Classification.Decomposition

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C}
  {n : ℕ} {S : Fin n → LinearCategory C} (d : Decomposition C X S)

attribute [local implicit_reducible] CategoryTheory.End

theorem weightedDiagonal_even (w : Fin n → ℝ) :
    C.data.IsHomogeneous 0 (d.weightedDiagonal w) := by
  change (∑ i, w i • (d.data.projection i ≫ d.data.inclusion i : X ⟶ X)) ∈
    LinearCategory.grade C X X 0
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact comp_even C.laws (d.laws.projection_even i) (d.laws.inclusion_even i)

theorem weightedDiagonal_mem_center (w : Fin n → ℝ)
    (hw : ∀ i j, ∀ f : C.data.Hom (S i) (S j), C.data.smul (w i) f = C.data.smul (w j) f) :
    d.weightedDiagonal w ∈ Subalgebra.center ℝ (End X) := by
  apply Subalgebra.mem_center_iff.mpr
  intro T
  change C.data.comp (d.weightedDiagonal w) T = C.data.comp T (d.weightedDiagonal w)
  apply hom_ext_of_inclusions C.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  apply hom_ext_of_projections C.laws d.data.inclusion d.data.projection d.laws.total
  intro j
  have hi := d.inclusion_weightedDiagonal w i
  have hj := d.weightedDiagonal_projection w j
  change C.data.comp (d.data.inclusion i) (d.weightedDiagonal w) =
    C.data.smul (w i) (d.data.inclusion i) at hi
  change C.data.comp (d.weightedDiagonal w) (d.data.projection j) =
    C.data.smul (w j) (d.data.projection j) at hj
  calc
    _ = C.data.smul (w i)
        (C.data.comp (C.data.comp (d.data.inclusion i) T) (d.data.projection j)) := by
      rw [← C.laws.comp_assoc (d.data.inclusion i) (d.weightedDiagonal w) T,
        hi, C.laws.smul_comp, C.laws.smul_comp]
    _ = C.data.smul (w j)
        (C.data.comp (C.data.comp (d.data.inclusion i) T) (d.data.projection j)) := hw i j _
    _ = _ := by
      simp only [C.laws.comp_assoc]
      rw [hj, C.laws.comp_smul, C.laws.comp_smul]

theorem weight_eq_of_scalar (w : Fin n → ℝ) (r : ℝ)
    (h : d.weightedDiagonal w = r • (1 : End X))
    (i : Fin n) (hi : C.data.id (S i) ≠ C.data.zero) : w i = r := by
  have he := congrArg (fun f : End X =>
    C.data.comp (C.data.comp (d.data.inclusion i) f) (d.data.projection i)) h
  have hd := d.inclusion_weightedDiagonal w i
  change C.data.comp (d.data.inclusion i) (d.weightedDiagonal w) =
    C.data.smul (w i) (d.data.inclusion i) at hd
  rw [hd, C.laws.smul_comp, d.laws.diagonal] at he
  change C.data.smul (w i) (C.data.id (S i)) =
    C.data.comp (C.data.comp (d.data.inclusion i) (C.data.smul r (C.data.id X)))
      (d.data.projection i) at he
  rw [C.laws.comp_smul, C.laws.comp_id, C.laws.smul_comp, d.laws.diagonal] at he
  exact smul_left_injective ℝ (show (1 : End (C := LinearCategory C) (S i)) ≠ 0 from hi) he

end RMod.Classification.Decomposition
