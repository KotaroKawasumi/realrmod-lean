import RMod.Classification.Proofs.ParityTensorComparisonIsoTransport
import RMod.Classification.Instances.TensorFunctors

/-!
# Inserting a unit map before tensorator transport

A chosen comparison from the tensor unit can be composed with an actual
component isomorphism. Naturality and its retained inverse transport the
whole unit diagram, including the map out of its target component.
-/

set_option autoImplicit false

namespace RMod.Classification.ParityTensorComparison

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C} {p : Pi C.data} {a : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  (η : ParityTensorComparison S T U V p E H N a)

 theorem inserted_iso_transport_left {X X' : HomogeneousSpanCategory A S.data.object}
    (Y : HomogeneousSpanCategory A T.data.object) (e : IsoData A.data X.obj X'.obj)
    (he : EvenIsoLaws A.data e) (i : C.data.Hom C.data.tensorUnit (E.data.obj X).obj)
    {Z : C.data.Obj} (q : C.data.Hom (N.data.obj (spanTensorObj A S T X Y)).obj Z) :
    C.data.comp
      (C.data.comp (C.data.tensorHom (C.data.tensorHom (C.data.comp i (E.data.map (ObjectProperty.homMk e.hom : X ⟶ X')).hom) (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a))) (η.data.app X' Y).hom)
      (C.data.comp (N.data.map (spanTensorHom A S T (ObjectProperty.homMk e.inv : X' ⟶ X) (𝟙 Y))).hom q) =
      C.data.comp (C.data.comp (C.data.tensorHom (C.data.tensorHom i (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a))) (η.data.app X Y).hom) q := by
  have ht : C.data.tensorHom (C.data.tensorHom (C.data.comp i (E.data.map (ObjectProperty.homMk e.hom : X ⟶ X')).hom) (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a)) =
      C.data.comp (C.data.tensorHom (C.data.tensorHom i (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a))) (C.data.tensorHom (C.data.tensorHom (E.data.map (ObjectProperty.homMk e.hom : X ⟶ X')).hom (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a))) :=
    (congrArg (fun f => C.data.tensorHom f (C.data.id (p.data.factor a)))
      ((tensorRightLaws C (H.data.obj Y).obj).map_comp i (E.data.map (ObjectProperty.homMk e.hom : X ⟶ X')).hom)).trans
      ((tensorRightLaws C (p.data.factor a)).map_comp _ _)
  rw [ht]
  simp only [C.laws.comp_assoc]
  have hh := congrArg (fun f => C.data.comp f q) (η.iso_transport_left Y e he)
  simp only [C.laws.comp_assoc] at hh
  exact congrArg (C.data.comp (C.data.tensorHom (C.data.tensorHom i (C.data.id (H.data.obj Y).obj)) (C.data.id (p.data.factor a)))) hh

 theorem inserted_iso_transport_right (X : HomogeneousSpanCategory A S.data.object)
    {Y Y' : HomogeneousSpanCategory A T.data.object} (e : IsoData A.data Y.obj Y'.obj)
    (he : EvenIsoLaws A.data e) (i : C.data.Hom C.data.tensorUnit (H.data.obj Y).obj)
    {Z : C.data.Obj} (q : C.data.Hom (N.data.obj (spanTensorObj A S T X Y)).obj Z) :
    C.data.comp
      (C.data.comp (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) (C.data.comp i (H.data.map (ObjectProperty.homMk e.hom : Y ⟶ Y')).hom)) (C.data.id (p.data.factor a))) (η.data.app X Y').hom)
      (C.data.comp (N.data.map (spanTensorHom A S T (𝟙 X) (ObjectProperty.homMk e.inv : Y' ⟶ Y))).hom q) =
      C.data.comp (C.data.comp (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) i) (C.data.id (p.data.factor a))) (η.data.app X Y).hom) q := by
  have ht : C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) (C.data.comp i (H.data.map (ObjectProperty.homMk e.hom : Y ⟶ Y')).hom)) (C.data.id (p.data.factor a)) =
      C.data.comp (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) i) (C.data.id (p.data.factor a))) (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) (H.data.map (ObjectProperty.homMk e.hom : Y ⟶ Y')).hom) (C.data.id (p.data.factor a))) :=
    (congrArg (fun f => C.data.tensorHom f (C.data.id (p.data.factor a)))
      ((tensorLeftLaws C (E.data.obj X).obj).map_comp i (H.data.map (ObjectProperty.homMk e.hom : Y ⟶ Y')).hom)).trans
      ((tensorRightLaws C (p.data.factor a)).map_comp _ _)
  rw [ht]
  simp only [C.laws.comp_assoc]
  have hh := congrArg (fun f => C.data.comp f q) (η.iso_transport_right X e he)
  simp only [C.laws.comp_assoc] at hh
  exact congrArg (C.data.comp (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj) i) (C.data.id (p.data.factor a)))) hh

end RMod.Classification.ParityTensorComparison
