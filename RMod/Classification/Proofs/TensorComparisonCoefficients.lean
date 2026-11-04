import RMod.Classification.Proofs.TensorComparisonExtensionObjects

/-!
# Signed comparison of rectangular tensor coefficients

Compose maps out of the two generators with maps back to them. Source
and target super-interchange contribute the same crossing sign. The
generator intertwining equation therefore compares the resulting
rectangular coefficients with the sign of their total degree.
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

theorem tensorIntertwiner_rectangular_coefficient
    {X : HomogeneousSpanCategory C S.data.object} {Y : HomogeneousSpanCategory C T.data.object}
    {b c d e : ZMod 2}
    (f : spanGenerator C S.data.object ⟶ X) (g : spanGenerator C T.data.object ⟶ Y)
    (p : X ⟶ spanGenerator C S.data.object) (q : Y ⟶ spanGenerator C T.data.object)
    (hf : C.data.IsHomogeneous b f.hom) (hg : C.data.IsHomogeneous c g.hom)
    (hp : C.data.IsHomogeneous d p.hom) (hq : C.data.IsHomogeneous e q.hom) :
    D.data.comp
      (D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
        (N.data.map (spanTensorHom C S T p q)).hom) t.data.hom =
    D.data.smul ((-1 : ℝ) ^ (a * ((b + c) + (d + e))).val)
      (D.data.comp t.data.hom
        (D.data.comp (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)
          (D.data.tensorHom (E.data.map p).hom (H.data.map q).hom))) := by
  let A := tensorSpanObject C S T
  let k : A ⟶ spanTensorObj C S T X Y := spanTensorHom C S T f g
  let l : spanTensorObj C S T X Y ⟶ A := spanTensorHom C S T p q
  let m : A ⟶ A := spanTensorHom C S T (f ≫ p) (g ≫ q)
  have hc : k ≫ l = ((-1 : ℝ) ^ (e * b).val) • m := by
    apply ObjectProperty.hom_ext
    exact C.laws.super_interchange p.hom q.hom f.hom g.hom hq hf
  have hn : N.data.map k ≫ N.data.map l = ((-1 : ℝ) ^ (e * b).val) • N.data.map m :=
    (N.laws.map_comp k l).symm.trans
      ((congrArg N.data.map hc).trans (N.laws.map_smul _ m))
  have hnraw := congrArg (fun u : N.data.obj A ⟶ N.data.obj A => u.hom) hn
  change D.data.comp (N.data.map k).hom (N.data.map l).hom =
    D.data.smul ((-1 : ℝ) ^ (e * b).val) (N.data.map m).hom at hnraw
  have ht := t.laws.intertwines (f ≫ p) (g ≫ q)
    (C.laws.comp_grade _ _ hf hp) (C.laws.comp_grade _ _ hg hq)
  have hdeg : (b + d) + (c + e) = (b + c) + (d + e) := by abel
  rw [hdeg] at ht
  change D.data.comp (N.data.map m).hom t.data.hom =
    D.data.smul ((-1 : ℝ) ^ (a * ((b + c) + (d + e))).val)
      (D.data.comp t.data.hom (D.data.tensorHom
        (E.data.map (f ≫ p)).hom (H.data.map (g ≫ q)).hom)) at ht
  have hemap := congrArg (fun u : E.data.obj (spanGenerator C S.data.object) ⟶
    E.data.obj (spanGenerator C S.data.object) => u.hom) (E.laws.map_comp f p)
  have hhmap := congrArg (fun u : H.data.obj (spanGenerator C T.data.object) ⟶
    H.data.obj (spanGenerator C T.data.object) => u.hom) (H.laws.map_comp g q)
  change (E.data.map (f ≫ p)).hom = D.data.comp (E.data.map f).hom (E.data.map p).hom at hemap
  change (H.data.map (g ≫ q)).hom = D.data.comp (H.data.map g).hom (H.data.map q).hom at hhmap
  change D.data.comp (D.data.comp (N.data.map k).hom (N.data.map l).hom) t.data.hom = _
  rw [hnraw, D.laws.smul_comp]
  rw [ht]
  rw [D.laws.super_interchange _ _ _ _ (H.laws.map_grade q hq) (E.laws.map_grade f hf),
    ← hemap, ← hhmap, D.laws.comp_smul, ← D.laws.mul_smul, ← D.laws.mul_smul, mul_comm]

end RMod.Classification
