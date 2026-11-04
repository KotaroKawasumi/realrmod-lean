import RMod.Classification.Proofs.TensorComparisonCoefficients

/-!
# Extended tensor comparisons on maps out of the generators

Project such a map onto every pair of summands. The rectangular
coefficient identity compares those coefficients, including the sign in
the tensor projection. Summing them with the target total identity
proves the required signed equation for the whole map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}
  (t : TensorIntertwiner S T U V E H N a)

theorem tensorComparisonExtension_on_generator_hom
    {X : HomogeneousSpanCategory C S.data.object} {Y : HomogeneousSpanCategory C T.data.object}
    {b c : ZMod 2}
    (f : spanGenerator C S.data.object ⟶ X) (g : spanGenerator C T.data.object ⟶ Y)
    (hf : C.data.IsHomogeneous b f.hom) (hg : C.data.IsHomogeneous c g.hom) :
    D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
      ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y).hom =
    D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
      (D.data.comp t.data.hom (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)) := by
  refine HomogeneousSum.comparison_on_generator a
    (tensorComparisonSourcePresentation S T U V N X Y)
    (tensorComparisonTargetPresentation S T U V E H X Y) t.data.hom
    (N.data.map (spanTensorHom C S T f g)).hom
    (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom) ?_
  intro i
  let j := (finProdFinEquiv.symm i).1
  let k := (finProdFinEquiv.symm i).2
  let p : X ⟶ spanGenerator C S.data.object := ObjectProperty.homMk ((spanPresentation X).data.projection j)
  let q : Y ⟶ spanGenerator C T.data.object := ObjectProperty.homMk ((spanPresentation Y).data.projection k)
  let r := (-1 : ℝ) ^ ((spanPresentation Y).data.parity k * (spanPresentation X).data.parity j).val
  let A := tensorSpanObject C S T
  let B := spanTensorObj C S T X Y
  have hm := congrArg (fun u : N.data.obj B ⟶ N.data.obj A => u.hom)
    (N.laws.map_smul r (spanTensorHom C S T p q))
  change (tensorComparisonSourcePresentation S T U V N X Y).data.projection i =
    D.data.smul r (N.data.map (spanTensorHom C S T p q)).hom at hm
  have hc := tensorIntertwiner_rectangular_coefficient t f g p q hf hg
    ((spanPresentation X).laws.projection_grade j) ((spanPresentation Y).laws.projection_grade k)
  change D.data.comp
    (D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
      ((tensorComparisonSourcePresentation S T U V N X Y).data.projection i)) t.data.hom =
    D.data.smul ((-1 : ℝ) ^ (a * ((b + c) +
      ((spanPresentation X).data.parity j + (spanPresentation Y).data.parity k))).val)
      (D.data.comp (D.data.comp t.data.hom (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom))
        (D.data.smul r (D.data.tensorHom (E.data.map p).hom (H.data.map q).hom)))
  rw [hm]
  let k₁ : D.data.Hom (N.data.obj A).obj (N.data.obj B).obj :=
    (N.data.map (spanTensorHom C S T f g)).hom
  let k₂ : D.data.Hom (N.data.obj B).obj (N.data.obj A).obj :=
    (N.data.map (spanTensorHom C S T p q)).hom
  let l₁ := D.data.tensorHom (E.data.map f).hom (H.data.map g).hom
  let l₂ := D.data.tensorHom (E.data.map p).hom (H.data.map q).hom
  let s := (-1 : ℝ) ^ (a * ((b + c) +
    ((spanPresentation X).data.parity j + (spanPresentation Y).data.parity k))).val
  change D.data.comp (D.data.comp k₁ k₂) t.data.hom =
    D.data.smul s (D.data.comp t.data.hom (D.data.comp l₁ l₂)) at hc
  change D.data.comp (D.data.comp k₁ (D.data.smul r k₂)) t.data.hom =
    D.data.smul s (D.data.comp (D.data.comp t.data.hom l₁) (D.data.smul r l₂))
  rw [D.laws.comp_smul, D.laws.smul_comp, hc, D.laws.comp_smul,
    D.laws.comp_assoc, ← D.laws.mul_smul, ← D.laws.mul_smul, mul_comm r]

end RMod.Classification
