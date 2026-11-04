import RMod.Classification.Instances.HomogeneousSumComparisonData
import RMod.Classification.Instances.HomogeneousMatrix
import RMod.Classification.Proofs.ParityPowers

/-!
# Homogeneous comparison of two presentations with the same parity list

The matrix-unit identities compute the comparison on each inclusion.
They also prove that the two specified sums are inverse whenever the
generator maps are inverse. Homogeneity follows term by term because
the two occurrences of the summand parity cancel.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory CategoryTheory.Preadditive

variable {C : WeaklyPointedSuperfusion.{0, 0}} {S T X Y : LinearCategory C} {n : ℕ}
  (a : ZMod 2) (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data T Y n)

theorem inclusion_comparison (f : S ⟶ T) (i : Fin n) :
    d.data.inclusion i ≫ comparisonHomData a d.data e.data f =
      ((-1 : ℝ) ^ (a * d.data.parity i).val) • (f ≫ e.data.inclusion i) := by
  change C.data.comp (d.data.inclusion i)
    (C.data.finSum n (fun j => C.data.smul ((-1 : ℝ) ^ (a * d.data.parity j).val)
      (C.data.comp (d.data.projection j) (C.data.comp f (e.data.inclusion j))))) = _
  rw [LinearCategory.finSum_eq_sum C]
  change d.data.inclusion i ≫
    (∑ j, ((-1 : ℝ) ^ (a * d.data.parity j).val) •
      (d.data.projection j ≫ f ≫ e.data.inclusion j) : X ⟶ Y) = _
  simp only [comp_sum, Linear.comp_smul, ← Category.assoc, inclusion_projection]
  simp [ite_comp, smul_ite]

theorem comparison_grade (hp : e.data.parity = d.data.parity) (f : S ⟶ T)
    (hf : C.data.IsHomogeneous a f) : C.data.IsHomogeneous a (comparisonHomData a d.data e.data f) := by
  change C.data.finSum n (fun i => C.data.smul ((-1 : ℝ) ^ (a * d.data.parity i).val)
    (C.data.comp (d.data.projection i) (C.data.comp f (e.data.inclusion i)))) ∈
      LinearCategory.grade C X Y a
  rw [LinearCategory.finSum_eq_sum C]
  change (∑ i, ((-1 : ℝ) ^ (a * d.data.parity i).val) •
    (d.data.projection i ≫ f ≫ e.data.inclusion i) : X ⟶ Y) ∈ LinearCategory.grade C X Y a
  apply Submodule.sum_mem
  intro i _
  apply C.laws.grade_smul
  have hg := C.laws.comp_grade _ _ (d.laws.projection_grade i)
    (C.laws.comp_grade _ _ hf (e.laws.inclusion_grade i))
  rw [hp, add_left_comm, CharTwo.add_self_eq_zero, add_zero] at hg
  exact hg

/-- Comparing every matrix coefficient determines the whole map. -/
theorem comparison_on_generator {b : ZMod 2} (f : S ⟶ T) (k : S ⟶ X) (l : T ⟶ Y)
    (h : ∀ i, (k ≫ d.data.projection i) ≫ f =
      ((-1 : ℝ) ^ (a * (b + d.data.parity i)).val) • ((f ≫ l) ≫ e.data.projection i)) :
    k ≫ comparisonHomData a d.data e.data f = ((-1 : ℝ) ^ (a * b).val) • (f ≫ l) := by
  change C.data.comp k (C.data.finSum n (fun i =>
    C.data.smul ((-1 : ℝ) ^ (a * d.data.parity i).val)
      (C.data.comp (d.data.projection i) (C.data.comp f (e.data.inclusion i))))) = _
  rw [LinearCategory.finSum_eq_sum C]
  change k ≫ (∑ i, ((-1 : ℝ) ^ (a * d.data.parity i).val) •
    (d.data.projection i ≫ f ≫ e.data.inclusion i) : X ⟶ Y) = _
  calc
    _ = ∑ i, ((-1 : ℝ) ^ (a * d.data.parity i).val) •
        (((k ≫ d.data.projection i) ≫ f) ≫ e.data.inclusion i) := by
      simp only [comp_sum, Linear.comp_smul, Category.assoc]
    _ = ∑ i, ((-1 : ℝ) ^ (a * b).val) •
        ((f ≫ l) ≫ (e.data.projection i ≫ e.data.inclusion i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h i, Linear.smul_comp, smul_smul, koszul_power_cancel, Category.assoc]
    _ = _ := by rw [← Finset.smul_sum, ← comp_sum, e.total, Category.comp_id]

theorem comparisonIsoLaws (hp : e.data.parity = d.data.parity) (t : IsoData C.data S T)
    (ht : IsoLaws C.data t) : IsoLaws C.data (comparisonIsoData a d.data e.data t) where
  hom_inv := by
    apply hom_ext_of_inclusions C.laws d.data.inclusion d.data.projection d.laws.total
    intro i
    change d.data.inclusion i ≫
      (comparisonHomData a d.data e.data t.hom ≫ comparisonHomData a e.data d.data t.inv) =
      d.data.inclusion i ≫ 𝟙 X
    rw [← Category.assoc, inclusion_comparison, Linear.smul_comp, Category.assoc,
      inclusion_comparison, Linear.comp_smul, hp, smul_smul, parity_power_mul_self,
      one_smul, ← Category.assoc]
    change (C.data.comp t.hom t.inv) ≫ d.data.inclusion i = d.data.inclusion i ≫ 𝟙 X
    rw [ht.hom_inv]
    exact (C.laws.id_comp _).trans (C.laws.comp_id _).symm
  inv_hom := by
    apply hom_ext_of_inclusions C.laws e.data.inclusion e.data.projection e.laws.total
    intro i
    change e.data.inclusion i ≫
      (comparisonHomData a e.data d.data t.inv ≫ comparisonHomData a d.data e.data t.hom) =
      e.data.inclusion i ≫ 𝟙 Y
    rw [← Category.assoc, inclusion_comparison, Linear.smul_comp, Category.assoc,
      inclusion_comparison, Linear.comp_smul, hp, smul_smul, parity_power_mul_self,
      one_smul, ← Category.assoc]
    change (C.data.comp t.inv t.hom) ≫ e.data.inclusion i = e.data.inclusion i ≫ 𝟙 Y
    rw [ht.inv_hom]
    exact (C.laws.id_comp _).trans (C.laws.comp_id _).symm

end RMod.Classification.HomogeneousSum
