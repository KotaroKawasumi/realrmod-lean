import RMod.Classification.Instances.TripleComparisonPresentations
import RMod.Classification.Proofs.Decompositions

/-!
# Triple comparisons are determined on the three generators

Signed naturality transports a generator scalar relation along every
triple of homogeneous inclusions. The mapped total matrix identity then
extends that same scalar to all objects of the three component categories.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleComparison

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}
  (η θ : TripleComparison S T R U V W E H K N a)

theorem hom_eq_smul_of_generator (r : ℝ)
    (h : η.evaluate.data.hom = C.data.smul r θ.evaluate.data.hom)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    (η.data.app X Y Z).hom = C.data.smul r (θ.data.app X Y Z).hom := by
  let d := tripleComparisonSourcePresentation S T R U V W N X Y Z
  apply hom_ext_of_inclusions C.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  let ij := (finProdFinEquiv.symm i).1
  let k := (finProdFinEquiv.symm i).2
  let j₁ := (finProdFinEquiv.symm ij).1
  let j₂ := (finProdFinEquiv.symm ij).2
  let p : spanGenerator A S.data.object ⟶ X := ObjectProperty.homMk ((spanPresentation X).data.inclusion j₁)
  let q : spanGenerator A T.data.object ⟶ Y := ObjectProperty.homMk ((spanPresentation Y).data.inclusion j₂)
  let t : spanGenerator A R.data.object ⟶ Z := ObjectProperty.homMk ((spanPresentation Z).data.inclusion k)
  let s := (-1 : ℝ) ^ (a * (((spanPresentation X).data.parity j₁ +
    (spanPresentation Y).data.parity j₂) + (spanPresentation Z).data.parity k)).val
  let l := C.data.tensorHom (C.data.tensorHom (E.data.map p).hom (H.data.map q).hom) (K.data.map t).hom
  let zη := (η.data.app (spanGenerator A S.data.object) (spanGenerator A T.data.object)
    (spanGenerator A R.data.object)).hom
  let zθ := (θ.data.app (spanGenerator A S.data.object) (spanGenerator A T.data.object)
    (spanGenerator A R.data.object)).hom
  change zη = C.data.smul r zθ at h
  have hleft := η.laws.naturality p q t ((spanPresentation X).laws.inclusion_grade j₁)
    ((spanPresentation Y).laws.inclusion_grade j₂) ((spanPresentation Z).laws.inclusion_grade k)
  have hright := θ.laws.naturality p q t ((spanPresentation X).laws.inclusion_grade j₁)
    ((spanPresentation Y).laws.inclusion_grade j₂) ((spanPresentation Z).laws.inclusion_grade k)
  change C.data.comp (N.data.map (tripleSpanHom A S T R p q t)).hom (η.data.app X Y Z).hom =
    C.data.comp (N.data.map (tripleSpanHom A S T R p q t)).hom (C.data.smul r (θ.data.app X Y Z).hom)
  calc
    _ = C.data.smul s (C.data.comp zη l) := hleft
    _ = C.data.smul s (C.data.comp (C.data.smul r zθ) l) :=
      congrArg (fun z => C.data.smul s (C.data.comp z l)) h
    _ = C.data.smul r (C.data.smul s (C.data.comp zθ l)) := by
      rw [C.laws.smul_comp, ← C.laws.mul_smul, ← C.laws.mul_smul, mul_comm]
    _ = C.data.smul r (C.data.comp (N.data.map (tripleSpanHom A S T R p q t)).hom (θ.data.app X Y Z).hom) :=
      congrArg (C.data.smul r) hright.symm
    _ = _ := (C.laws.comp_smul r _ _).symm

end RMod.Classification.TripleComparison
