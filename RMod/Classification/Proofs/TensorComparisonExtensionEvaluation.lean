import RMod.Classification.Instances.TensorComparisonExtension

/-!
# Extension recovers the specified generator comparison

Apply the proved formula on maps out of the generators to their identity
maps. Functoriality and tensor identities remove every surrounding map.
This retains the exact chosen comparison, including its scalar.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}

theorem tensorComparisonExtension_generator_hom (t : TensorIntertwiner S T U V E H N a) :
    ((tensorComparisonExtension t).data.app (spanGenerator A S.data.object)
      (spanGenerator A T.data.object)).hom = t.data.hom := by
  let X := spanGenerator A S.data.object
  let Y := spanGenerator A T.data.object
  let Z := spanTensorObj A S T X Y
  have ht : spanTensorHom A S T (𝟙 X) (𝟙 Y) = 𝟙 Z :=
    ObjectProperty.hom_ext _ (A.laws.tensor_id _ _)
  have hN : (N.data.map (spanTensorHom A S T (𝟙 X) (𝟙 Y))).hom = C.data.id (N.data.obj Z).obj :=
    congrArg (fun f : N.toFunctor.obj Z ⟶ N.toFunctor.obj Z => f.hom)
      ((congrArg N.data.map ht).trans (N.laws.map_id Z))
  have hE : (E.data.map (𝟙 X)).hom = C.data.id (E.data.obj X).obj :=
    congrArg (fun f : E.toFunctor.obj X ⟶ E.toFunctor.obj X => f.hom) (E.laws.map_id X)
  have hH : (H.data.map (𝟙 Y)).hom = C.data.id (H.data.obj Y).obj :=
    congrArg (fun f : H.toFunctor.obj Y ⟶ H.toFunctor.obj Y => f.hom) (H.laws.map_id Y)
  have h := tensorComparisonExtension_on_generator_hom t (𝟙 X) (𝟙 Y)
    (A.laws.id_even _) (A.laws.id_even _)
  rw [hN, hE, hH, C.laws.tensor_id] at h
  let q : C.data.Hom (N.data.obj Z).obj (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj) :=
    ((tensorComparisonExtension t).data.app X Y).hom
  let z : C.data.Hom (N.data.obj Z).obj (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj) := t.data.hom
  change C.data.comp (C.data.id (N.data.obj Z).obj) q =
    C.data.smul ((-1 : ℝ) ^ (a * (0 + 0)).val)
      (C.data.comp z (C.data.id (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj))) at h
  simpa only [zero_add, mul_zero, ZMod.val_zero, pow_zero, C.laws.one_smul,
    C.laws.id_comp, C.laws.comp_id] using h

end RMod.Classification
