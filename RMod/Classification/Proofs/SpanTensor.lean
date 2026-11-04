import RMod.Classification.Instances.SpanTensor
import RMod.Classification.Instances.SpanSuperfunctor

/-!
# Signed composition of tensor maps inside product components

The full-subcategory wrappers retain ambient super-interchange. A
component superfunctor preserves its equation by linearity, including
the crossing scalar, so no ordinary interchange law is imposed.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) {W : D.data.Obj}
  {X X' X'' : HomogeneousSpanCategory C S.data.object}
  {Y Y' Y'' : HomogeneousSpanCategory C T.data.object}

theorem spanTensorHom_comp {b c : ZMod 2}
    (f : X ⟶ X') (g : Y ⟶ Y') (p : X' ⟶ X'') (q : Y' ⟶ Y'')
    (hq : C.data.IsHomogeneous b q.hom) (hf : C.data.IsHomogeneous c f.hom) :
    spanTensorHom C S T f g ≫ spanTensorHom C S T p q =
      ((-1 : ℝ) ^ (b * c).val) • spanTensorHom C S T (f ≫ p) (g ≫ q) := by
  apply ObjectProperty.hom_ext
  exact C.laws.super_interchange p.hom q.hom f.hom g.hom hq hf

theorem map_spanTensorHom_comp
    (N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object W)
    {b c : ZMod 2} (f : X ⟶ X') (g : Y ⟶ Y') (p : X' ⟶ X'') (q : Y' ⟶ Y'')
    (hq : C.data.IsHomogeneous b q.hom) (hf : C.data.IsHomogeneous c f.hom) :
    D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
      (N.data.map (spanTensorHom C S T p q)).hom =
    D.data.smul ((-1 : ℝ) ^ (b * c).val)
      (N.data.map (spanTensorHom C S T (f ≫ p) (g ≫ q))).hom := by
  have h := (N.laws.map_comp (spanTensorHom C S T f g) (spanTensorHom C S T p q)).symm.trans
    ((congrArg N.data.map (spanTensorHom_comp S T f g p q hq hf)).trans
      (N.laws.map_smul _ (spanTensorHom C S T (f ≫ p) (g ≫ q))))
  exact congrArg (fun u : N.data.obj (spanTensorObj C S T X Y) ⟶
    N.data.obj (spanTensorObj C S T X'' Y'') => u.hom) h

end RMod.Classification
