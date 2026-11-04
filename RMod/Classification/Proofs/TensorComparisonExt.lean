import RMod.Classification.Instances.TensorComparisonEvaluation
import RMod.Classification.Instances.TensorComparisonPresentations
import RMod.Classification.Proofs.Decompositions

/-!
# Generator values determine the entire tensor comparison

Apply signed naturality to every paired inclusion in the source tensor
presentation. A scalar relation on the generator value then holds after
all mapped inclusions, and the total matrix identity proves it on every
pair of objects.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}
  (η θ : TensorComparison S T U V E H N a)

theorem hom_eq_smul_of_generator (r : ℝ)
    (h : η.evaluate.data.hom = D.data.smul r θ.evaluate.data.hom)
    (X : HomogeneousSpanCategory C S.data.object) (Y : HomogeneousSpanCategory C T.data.object) :
    (η.data.app X Y).hom = D.data.smul r (θ.data.app X Y).hom := by
  let d := tensorComparisonSourcePresentation S T U V N X Y
  apply hom_ext_of_inclusions D.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  let j := (finProdFinEquiv.symm i).1
  let k := (finProdFinEquiv.symm i).2
  let p : spanGenerator C S.data.object ⟶ X := ObjectProperty.homMk ((spanPresentation X).data.inclusion j)
  let q : spanGenerator C T.data.object ⟶ Y := ObjectProperty.homMk ((spanPresentation Y).data.inclusion k)
  let s := (-1 : ℝ) ^ (a * ((spanPresentation X).data.parity j + (spanPresentation Y).data.parity k)).val
  let l := D.data.tensorHom (E.data.map p).hom (H.data.map q).hom
  let zη := (η.data.app (spanGenerator C S.data.object) (spanGenerator C T.data.object)).hom
  let zθ := (θ.data.app (spanGenerator C S.data.object) (spanGenerator C T.data.object)).hom
  change zη = D.data.smul r zθ at h
  have hleft := η.laws.naturality p q
    ((spanPresentation X).laws.inclusion_grade j) ((spanPresentation Y).laws.inclusion_grade k)
  have hright := θ.laws.naturality p q
    ((spanPresentation X).laws.inclusion_grade j) ((spanPresentation Y).laws.inclusion_grade k)
  change D.data.comp (N.data.map (spanTensorHom C S T p q)).hom (η.data.app X Y).hom =
    D.data.comp (N.data.map (spanTensorHom C S T p q)).hom (D.data.smul r (θ.data.app X Y).hom)
  calc
    _ = D.data.smul s (D.data.comp zη l) := hleft
    _ = D.data.smul s (D.data.comp (D.data.smul r zθ) l) :=
      congrArg (fun z => D.data.smul s (D.data.comp z l)) h
    _ = D.data.smul r (D.data.smul s (D.data.comp zθ l)) := by
      rw [D.laws.smul_comp, ← D.laws.mul_smul, ← D.laws.mul_smul, mul_comm]
    _ = D.data.smul r (D.data.comp (N.data.map (spanTensorHom C S T p q)).hom (θ.data.app X Y).hom) :=
      congrArg (D.data.smul r) hright.symm
    _ = _ := (D.laws.comp_smul r _ _).symm

end RMod.Classification.TensorComparison
