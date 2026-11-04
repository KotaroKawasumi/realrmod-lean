import RMod.Classification.Proofs.TripleIntertwinerCenter

/-!
# Unique parity and scalar units for triple comparisons

The target triple is nonzero by repeated tensor nonvanishing. An
invertible ratio is therefore nonzero. Since that ratio is a real scalar,
it cannot have odd degree; the two comparison degrees agree. Cancelling
one comparison gives a unique nonzero real scalar between their maps.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleIntertwiner

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  (K : SpanSuperequivalence A C R.data.object W.data.object)
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a b : ZMod 2}
  (η : TripleIntertwiner S T R U V W E.forwardFunctor H.forwardFunctor K.forwardFunctor N a)
  (θ : TripleIntertwiner S T R U V W E.forwardFunctor H.forwardFunctor K.forwardFunctor N b)

theorem target_id_ne_zero :
    C.data.id (C.data.tensorObj
      (C.data.tensorObj (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj
        (H.forwardFunctor.data.obj (spanGenerator A T.data.object)).obj)
      (K.forwardFunctor.data.obj (spanGenerator A R.data.object)).obj) ≠ C.data.zero :=
  tensor_id_ne_zero
    (tensor_id_ne_zero
      (simple_id_ne_zero C.laws (E.forwardFunctor.map_simple E.fullyFaithful E.map_grade_iff
        (spanGenerator A S.data.object) S.laws.simple))
      (simple_id_ne_zero C.laws (H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
        (spanGenerator A T.data.object) T.laws.simple)))
    (simple_id_ne_zero C.laws (K.forwardFunctor.map_simple K.fullyFaithful K.map_grade_iff
      (spanGenerator A R.data.object) R.laws.simple))

theorem hom_ne_zero : η.data.hom ≠ C.data.zero := by
  intro hz
  apply target_id_ne_zero E H K
  exact η.laws.inv_hom.symm.trans ((congrArg (C.data.comp η.data.inv) hz).trans (raw_comp_zero C.laws _))

theorem ratio_ne_zero : C.data.comp η.data.inv θ.data.hom ≠ C.data.zero := by
  let e := η.toIso.symm ≪≫ θ.toIso
  change e.hom ≠ 0
  intro hz
  apply target_id_ne_zero E H K
  change 𝟙 _ = (0 : @Quiver.Hom (LinearCategory C) _ _ _)
  calc
    _ = e.hom ≫ e.inv := e.hom_inv_id.symm
    _ = 0 := by rw [hz]; simp

include E H K η θ in
theorem parity_unique : a = b := by
  obtain ⟨r, hr⟩ := ratio_eq_scalar E H K η θ
  have he : C.data.IsHomogeneous 0 (C.data.comp η.data.inv θ.data.hom) := by
    rw [hr]
    exact C.laws.grade_smul r _ (C.laws.id_even _)
  have hd : C.data.IsHomogeneous (a + b) (C.data.comp η.data.inv θ.data.hom) :=
    C.laws.comp_grade _ _ η.laws.inv_grade θ.laws.hom_grade
  have hab : a + b = 0 := by
    rcases parity_cases (a + b) with h | h
    · exact h
    · rw [h] at hd
      exact False.elim (ratio_ne_zero E H K η θ (C.laws.grade_disjoint _ he hd))
  calc
    a = (a + b) + b := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = b := by rw [hab, zero_add]

theorem comparison_eq_scalar : ∃ r : ℝ, θ.data.hom = C.data.smul r η.data.hom := by
  obtain ⟨r, hr⟩ := ratio_eq_scalar E H K η θ
  refine ⟨r, ?_⟩
  calc
    θ.data.hom = C.data.comp η.data.hom (C.data.comp η.data.inv θ.data.hom) := by
      rw [← C.laws.comp_assoc, η.laws.hom_inv, C.laws.id_comp]
    _ = C.data.smul r η.data.hom := by rw [hr, C.laws.comp_smul, C.laws.comp_id]

theorem comparison_eq_unique_unit_smul : ∃! r : ℝˣ, θ.data.hom = C.data.smul (r : ℝ) η.data.hom := by
  obtain ⟨r, hr⟩ := comparison_eq_scalar E H K η θ
  have hr0 : r ≠ 0 := by
    intro hz
    apply hom_ne_zero E H K θ
    rw [hz] at hr
    exact hr.trans (C.laws.zero_smul _)
  refine ⟨Units.mk0 r hr0, hr, ?_⟩
  intro s hs
  apply Units.ext
  exact smul_left_injective ℝ (show η.toIso.hom ≠ 0 from hom_ne_zero E H K η) (hs.symm.trans hr)

end RMod.Classification.TripleIntertwiner
