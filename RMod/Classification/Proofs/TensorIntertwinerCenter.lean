import RMod.Classification.Proofs.TensorIntertwinerRatio
import RMod.Classification.Proofs.TensorEndHomogeneousInduction
import RMod.Classification.Proofs.SimpleTensorEnd
import RMod.Classification.Proofs.SpanSimpleImages
import RMod.Classification.Proofs.SpanSuperequivalence

/-!
# Tensor comparison ratios are real scalars

Full faithfulness and grading reflection in each input let every
homogeneous pure target tensor be tested by source endomorphisms. Graded
tensor span induction then proves supercentrality against all target
endomorphisms. The previously proved centrality of the endomorphism
algebra of a product of simples makes the ratio a real scalar.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorIntertwiner

open CategoryTheory Superfusion Superfusion.Category

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  (E : SpanSuperequivalence C D S.data.object U.data.object)
  (H : SpanSuperequivalence C D T.data.object V.data.object)
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a b : ZMod 2}
  (η : TensorIntertwiner S T U V E.forwardFunctor H.forwardFunctor N a)
  (θ : TensorIntertwiner S T U V E.forwardFunctor H.forwardFunctor N b)

theorem ratio_supercentral :
    IsSupercentral (endGrading (K := ℝ) (C := LinearCategory D)
      (D.data.tensorObj
        (E.forwardFunctor.data.obj (spanGenerator C S.data.object)).obj
        (H.forwardFunctor.data.obj (spanGenerator C T.data.object)).obj))
      (a + b) (D.data.comp η.data.inv θ.data.hom) := by
  let X := (E.forwardFunctor.data.obj (spanGenerator C S.data.object)).obj
  let Y := (H.forwardFunctor.data.obj (spanGenerator C T.data.object)).obj
  have hY : D.data.IsSimple Y := H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
    (spanGenerator C T.data.object) T.laws.simple
  let e := E.forwardFunctor.endAlgEquiv E.fullyFaithful (spanGenerator C S.data.object)
  let h := H.forwardFunctor.endAlgEquiv H.fullyFaithful (spanGenerator C T.data.object)
  let z := D.data.comp η.data.inv θ.data.hom
  intro c k hk
  rw [← koszulSign_smul_eq_sgn_zsmul ℝ (a + b) c]
  change D.data.comp k z = D.data.smul ((-1 : ℝ) ^ ((a + b) * c).val) (D.data.comp z k)
  refine tensorEnd_homogeneous_induction D X Y hY
    (P := fun k => D.data.comp k z =
      D.data.smul ((-1 : ℝ) ^ ((a + b) * c).val) (D.data.comp z k)) k hk ?_ ?_ ?_ ?_
  · intro d f x y hdf hx hy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := h.surjective y
    have hx' := (E.map_grade_iff (ObjectProperty.homMk x :
      spanGenerator C S.data.object ⟶ spanGenerator C S.data.object)).mp hx
    have hy' := (H.map_grade_iff (ObjectProperty.homMk y :
      spanGenerator C T.data.object ⟶ spanGenerator C T.data.object)).mp hy
    have hn := ratio_intertwines_tensor η θ (ObjectProperty.homMk x) (ObjectProperty.homMk y) hx' hy'
    rw [hdf] at hn
    exact hn
  · change D.data.comp D.data.zero z = D.data.smul _ (D.data.comp z D.data.zero)
    rw [raw_zero_comp D.laws, raw_comp_zero D.laws, D.laws.smul_zero]
  · intro x y hx hy
    change D.data.comp (D.data.add x y) z = D.data.smul _ (D.data.comp z (D.data.add x y))
    rw [D.laws.add_comp, D.laws.comp_add, D.laws.smul_add, hx, hy]
  · intro r x hx
    change D.data.comp (D.data.smul r x) z = D.data.smul _ (D.data.comp z (D.data.smul r x))
    rw [D.laws.smul_comp, D.laws.comp_smul, hx, ← D.laws.mul_smul, ← D.laws.mul_smul,
      mul_comm r]

theorem ratio_eq_scalar : ∃ r : ℝ,
    D.data.comp η.data.inv θ.data.hom = D.data.smul r
      (D.data.id (D.data.tensorObj
        (E.forwardFunctor.data.obj (spanGenerator C S.data.object)).obj
        (H.forwardFunctor.data.obj (spanGenerator C T.data.object)).obj)) := by
  let X := (E.forwardFunctor.data.obj (spanGenerator C S.data.object)).obj
  let Y := (H.forwardFunctor.data.obj (spanGenerator C T.data.object)).obj
  have hX := E.forwardFunctor.map_simple E.fullyFaithful E.map_grade_iff
    (spanGenerator C S.data.object) S.laws.simple
  have hY := H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
    (spanGenerator C T.data.object) T.laws.simple
  letI := simple_tensor_end_isSuperCentral D X Y hX hY
  have hg : D.data.IsHomogeneous (a + b) (D.data.comp η.data.inv θ.data.hom) :=
    D.laws.comp_grade _ _ η.laws.inv_grade θ.laws.hom_grade
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp
    (mem_one_of_isSupercentral _ hg (ratio_supercentral E H η θ))
  exact ⟨r, hr.symm⟩

end RMod.Classification.TensorIntertwiner
