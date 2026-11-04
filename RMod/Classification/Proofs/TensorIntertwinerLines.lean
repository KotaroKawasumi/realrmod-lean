import RMod.Classification.Proofs.TensorIntertwinerCenter

/-!
# Unique parity and invertible scalar ratios for tensor comparisons

The tensor of the two simple generator images is nonzero. Hence the
invertible ratio cannot be an odd scalar. Its real scalar is nonzero,
and cancelling one comparison makes that unit uniquely determined.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorIntertwiner

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  (E : SpanSuperequivalence C D S.data.object U.data.object)
  (H : SpanSuperequivalence C D T.data.object V.data.object)
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a b : ZMod 2}
  (η : TensorIntertwiner S T U V E.forwardFunctor H.forwardFunctor N a)
  (θ : TensorIntertwiner S T U V E.forwardFunctor H.forwardFunctor N b)

theorem target_id_ne_zero :
    D.data.id (D.data.tensorObj
      (E.forwardFunctor.data.obj (spanGenerator C S.data.object)).obj
      (H.forwardFunctor.data.obj (spanGenerator C T.data.object)).obj) ≠ D.data.zero :=
  tensor_id_ne_zero
    (simple_id_ne_zero D.laws (E.forwardFunctor.map_simple E.fullyFaithful E.map_grade_iff
      (spanGenerator C S.data.object) S.laws.simple))
    (simple_id_ne_zero D.laws (H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
      (spanGenerator C T.data.object) T.laws.simple))

theorem hom_ne_zero : η.data.hom ≠ D.data.zero := by
  intro hz
  apply target_id_ne_zero E H
  exact η.laws.inv_hom.symm.trans ((congrArg (D.data.comp η.data.inv) hz).trans
    (raw_comp_zero D.laws _))

theorem ratio_ne_zero : D.data.comp η.data.inv θ.data.hom ≠ D.data.zero := by
  let e := η.toIso.symm ≪≫ θ.toIso
  change e.hom ≠ 0
  intro hz
  apply target_id_ne_zero E H
  change 𝟙 _ = (0 : @Quiver.Hom (LinearCategory D) _ _ _)
  calc
    _ = e.hom ≫ e.inv := e.hom_inv_id.symm
    _ = 0 := by rw [hz]; simp

include E H η θ in
theorem parity_unique : a = b := by
  obtain ⟨r, hr⟩ := ratio_eq_scalar E H η θ
  have he : D.data.IsHomogeneous 0 (D.data.comp η.data.inv θ.data.hom) := by
    rw [hr]
    exact D.laws.grade_smul r _ (D.laws.id_even _)
  have hd : D.data.IsHomogeneous (a + b) (D.data.comp η.data.inv θ.data.hom) :=
    D.laws.comp_grade _ _ η.laws.inv_grade θ.laws.hom_grade
  have hab : a + b = 0 := by
    rcases parity_cases (a + b) with h | h
    · exact h
    · rw [h] at hd
      exact False.elim (ratio_ne_zero E H η θ (D.laws.grade_disjoint _ he hd))
  calc
    a = (a + b) + b := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = b := by rw [hab, zero_add]

theorem comparison_eq_scalar : ∃ r : ℝ,
    θ.data.hom = D.data.smul r η.data.hom := by
  obtain ⟨r, hr⟩ := ratio_eq_scalar E H η θ
  refine ⟨r, ?_⟩
  calc
    θ.data.hom = D.data.comp η.data.hom (D.data.comp η.data.inv θ.data.hom) := by
      rw [← D.laws.comp_assoc, η.laws.hom_inv, D.laws.id_comp]
    _ = D.data.smul r η.data.hom := by rw [hr, D.laws.comp_smul, D.laws.comp_id]

theorem comparison_eq_unique_unit_smul : ∃! r : ℝˣ,
    θ.data.hom = D.data.smul (r : ℝ) η.data.hom := by
  obtain ⟨r, hr⟩ := comparison_eq_scalar E H η θ
  have hr0 : r ≠ 0 := by
    intro hz
    apply hom_ne_zero E H θ
    rw [hz] at hr
    exact hr.trans (D.laws.zero_smul _)
  refine ⟨Units.mk0 r hr0, hr, ?_⟩
  intro s hs
  apply Units.ext
  exact smul_left_injective ℝ (show η.toIso.hom ≠ 0 from hom_ne_zero E H η) (hs.symm.trans hr)

end RMod.Classification.TensorIntertwiner
