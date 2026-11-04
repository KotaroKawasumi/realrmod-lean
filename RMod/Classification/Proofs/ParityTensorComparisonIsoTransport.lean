import RMod.Classification.Proofs.ParityTensorComparisonNaturality
import RMod.Classification.Instances.SpanMapIso
import RMod.Classification.Proofs.IsoCalculus

/-!
# Tensorator transport through an actual component isomorphism

Naturality moves the chosen isomorphism across the tensorator. Mapping
its retained inverse cancels the resulting source comparison. This
allows the normalized unit generator to be replaced by the actual unit
component selected by the global reconstruction functor.
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

theorem iso_transport_left {X X' : HomogeneousSpanCategory A S.data.object}
    (Y : HomogeneousSpanCategory A T.data.object) (e : IsoData A.data X.obj X'.obj)
    (he : EvenIsoLaws A.data e) :
    C.data.comp
      (C.data.tensorHom (C.data.tensorHom
        (E.data.map (ObjectProperty.homMk e.hom : X ⟶ X')).hom (C.data.id (H.data.obj Y).obj))
        (C.data.id (p.data.factor a)))
      (C.data.comp (η.data.app X' Y).hom
        (N.data.map (spanTensorHom A S T (ObjectProperty.homMk e.inv : X' ⟶ X) (𝟙 Y))).hom) =
      (η.data.app X Y).hom := by
  have hn := η.naturality_all (ObjectProperty.homMk e.hom : X ⟶ X') (𝟙 Y)
  have hid : (H.data.map (𝟙 Y)).hom = C.data.id (H.data.obj Y).obj :=
    congrArg (fun m => m.hom) (H.laws.map_id Y)
  rw [hid] at hn
  have hm : C.data.comp
      (N.data.map (spanTensorHom A S T (ObjectProperty.homMk e.hom : X ⟶ X') (𝟙 Y))).hom
      (N.data.map (spanTensorHom A S T (ObjectProperty.homMk e.inv : X' ⟶ X) (𝟙 Y))).hom =
      C.data.id (N.data.obj (spanTensorObj A S T X Y)).obj :=
    (N.mapIsoLaws (X := spanTensorObj A S T X Y) (Y := spanTensorObj A S T X' Y)
      (he.tensor A.laws (EvenIsoLaws.refl A.laws Y.obj)).toIsoLaws).hom_inv
  exact (C.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => C.data.comp f
      (N.data.map (spanTensorHom A S T (ObjectProperty.homMk e.inv : X' ⟶ X) (𝟙 Y))).hom) hn).trans
      ((C.laws.comp_assoc _ _ _).trans
        ((congrArg (C.data.comp (η.data.app X Y).hom) hm).trans (C.laws.comp_id _))))

theorem iso_transport_right (X : HomogeneousSpanCategory A S.data.object)
    {Y Y' : HomogeneousSpanCategory A T.data.object} (e : IsoData A.data Y.obj Y'.obj)
    (he : EvenIsoLaws A.data e) :
    C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (E.data.obj X).obj)
        (H.data.map (ObjectProperty.homMk e.hom : Y ⟶ Y')).hom)
        (C.data.id (p.data.factor a)))
      (C.data.comp (η.data.app X Y').hom
        (N.data.map (spanTensorHom A S T (𝟙 X) (ObjectProperty.homMk e.inv : Y' ⟶ Y))).hom) =
      (η.data.app X Y).hom := by
  have hn := η.naturality_all (𝟙 X) (ObjectProperty.homMk e.hom : Y ⟶ Y')
  have hid : (E.data.map (𝟙 X)).hom = C.data.id (E.data.obj X).obj :=
    congrArg (fun m => m.hom) (E.laws.map_id X)
  rw [hid] at hn
  have hm : C.data.comp
      (N.data.map (spanTensorHom A S T (𝟙 X) (ObjectProperty.homMk e.hom : Y ⟶ Y'))).hom
      (N.data.map (spanTensorHom A S T (𝟙 X) (ObjectProperty.homMk e.inv : Y' ⟶ Y))).hom =
      C.data.id (N.data.obj (spanTensorObj A S T X Y)).obj :=
    (N.mapIsoLaws (X := spanTensorObj A S T X Y) (Y := spanTensorObj A S T X Y')
      ((EvenIsoLaws.refl A.laws X.obj).tensor A.laws he).toIsoLaws).hom_inv
  exact (C.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => C.data.comp f
      (N.data.map (spanTensorHom A S T (𝟙 X) (ObjectProperty.homMk e.inv : Y' ⟶ Y))).hom) hn).trans
      ((C.laws.comp_assoc _ _ _).trans
        ((congrArg (C.data.comp (η.data.app X Y).hom) hm).trans (C.laws.comp_id _))))

end RMod.Classification.ParityTensorComparison
