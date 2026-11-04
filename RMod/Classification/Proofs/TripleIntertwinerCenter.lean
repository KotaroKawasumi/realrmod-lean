import RMod.Classification.Proofs.TripleIntertwinerRatio
import RMod.Classification.Proofs.TripleTensorEndInduction
import RMod.Classification.Proofs.TripleTensorEnd
import RMod.Classification.Proofs.SpanSimpleImages
import RMod.Classification.Proofs.SpanSuperequivalence

/-!
# Triple comparison ratios are real scalars

Full faithfulness and grade reflection lift the three target factors to
source endomorphisms. Pure-triple intertwining and graded span induction
give supercentrality against every endomorphism of the target triple.
The proved centrality of its endomorphism algebra makes the ratio scalar.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleIntertwiner

open CategoryTheory Superfusion Superfusion.Category

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

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

theorem ratio_supercentral :
    IsSupercentral (endGrading (K := ℝ) (C := LinearCategory C)
      (C.data.tensorObj
        (C.data.tensorObj (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj
          (H.forwardFunctor.data.obj (spanGenerator A T.data.object)).obj)
        (K.forwardFunctor.data.obj (spanGenerator A R.data.object)).obj))
      (a + b) (C.data.comp η.data.inv θ.data.hom) := by
  let X := (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj
  let Y := (H.forwardFunctor.data.obj (spanGenerator A T.data.object)).obj
  let Z := (K.forwardFunctor.data.obj (spanGenerator A R.data.object)).obj
  have hY : C.data.IsSimple Y := H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
    (spanGenerator A T.data.object) T.laws.simple
  have hZ : C.data.IsSimple Z := K.forwardFunctor.map_simple K.fullyFaithful K.map_grade_iff
    (spanGenerator A R.data.object) R.laws.simple
  let e := E.forwardFunctor.endAlgEquiv E.fullyFaithful (spanGenerator A S.data.object)
  let j := H.forwardFunctor.endAlgEquiv H.fullyFaithful (spanGenerator A T.data.object)
  let k := K.forwardFunctor.endAlgEquiv K.fullyFaithful (spanGenerator A R.data.object)
  let z := C.data.comp η.data.inv θ.data.hom
  intro c f hf
  rw [← koszulSign_smul_eq_sgn_zsmul ℝ (a + b) c]
  change C.data.comp f z = C.data.smul ((-1 : ℝ) ^ ((a + b) * c).val) (C.data.comp z f)
  refine tripleTensorEnd_homogeneous_induction C X Y Z hY hZ
    (P := fun f => C.data.comp f z =
      C.data.smul ((-1 : ℝ) ^ ((a + b) * c).val) (C.data.comp z f)) f hf ?_ ?_ ?_ ?_
  · intro p q r x y w hpqr hx hy hw
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := j.surjective y
    obtain ⟨w, rfl⟩ := k.surjective w
    have hx' := (E.map_grade_iff (ObjectProperty.homMk x :
      spanGenerator A S.data.object ⟶ spanGenerator A S.data.object)).mp hx
    have hy' := (H.map_grade_iff (ObjectProperty.homMk y :
      spanGenerator A T.data.object ⟶ spanGenerator A T.data.object)).mp hy
    have hw' := (K.map_grade_iff (ObjectProperty.homMk w :
      spanGenerator A R.data.object ⟶ spanGenerator A R.data.object)).mp hw
    have hn := ratio_intertwines_triple η θ (ObjectProperty.homMk x) (ObjectProperty.homMk y)
      (ObjectProperty.homMk w) hx' hy' hw'
    rw [hpqr] at hn
    exact hn
  · change C.data.comp C.data.zero z = C.data.smul _ (C.data.comp z C.data.zero)
    rw [raw_zero_comp C.laws, raw_comp_zero C.laws, C.laws.smul_zero]
  · intro x y hx hy
    change C.data.comp (C.data.add x y) z = C.data.smul _ (C.data.comp z (C.data.add x y))
    rw [C.laws.add_comp, C.laws.comp_add, C.laws.smul_add, hx, hy]
  · intro r x hx
    change C.data.comp (C.data.smul r x) z = C.data.smul _ (C.data.comp z (C.data.smul r x))
    rw [C.laws.smul_comp, C.laws.comp_smul, hx, ← C.laws.mul_smul, ← C.laws.mul_smul, mul_comm r]

theorem ratio_eq_scalar : ∃ r : ℝ,
    C.data.comp η.data.inv θ.data.hom = C.data.smul r
      (C.data.id (C.data.tensorObj
        (C.data.tensorObj (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj
          (H.forwardFunctor.data.obj (spanGenerator A T.data.object)).obj)
        (K.forwardFunctor.data.obj (spanGenerator A R.data.object)).obj)) := by
  let X := (E.forwardFunctor.data.obj (spanGenerator A S.data.object)).obj
  let Y := (H.forwardFunctor.data.obj (spanGenerator A T.data.object)).obj
  let Z := (K.forwardFunctor.data.obj (spanGenerator A R.data.object)).obj
  have hX := E.forwardFunctor.map_simple E.fullyFaithful E.map_grade_iff
    (spanGenerator A S.data.object) S.laws.simple
  have hY := H.forwardFunctor.map_simple H.fullyFaithful H.map_grade_iff
    (spanGenerator A T.data.object) T.laws.simple
  have hZ := K.forwardFunctor.map_simple K.fullyFaithful K.map_grade_iff
    (spanGenerator A R.data.object) R.laws.simple
  letI := simple_triple_tensor_end_isSuperCentral C X Y Z hX hY hZ
  have hg : C.data.IsHomogeneous (a + b) (C.data.comp η.data.inv θ.data.hom) :=
    C.laws.comp_grade _ _ η.laws.inv_grade θ.laws.hom_grade
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp
    (mem_one_of_isSupercentral _ hg (ratio_supercentral E H K η θ))
  exact ⟨r, hr.symm⟩

end RMod.Classification.TripleIntertwiner
