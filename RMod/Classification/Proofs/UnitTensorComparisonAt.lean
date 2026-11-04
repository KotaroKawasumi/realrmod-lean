import RMod.Classification.Instances.UnitTensorComparisonAt
import RMod.Classification.Proofs.IsoNaturality

/-!
# The canonical unit comparisons are even and natural on full Hom spaces

The naturality square is the composite of three squares: the mapped
source unitor, the inverse target unitor, and the fixed even insertion.
The other morphism may have any degree, or be inhomogeneous.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (T : SimpleObject A) {U V : C.data.Obj}
  (E : SpanSuperfunctor A C A.data.tensorUnit U) (H : SpanSuperfunctor A C T.data.object V)
  {i : IsoData C.data C.data.tensorUnit (E.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

include hi

theorem leftUnitTensorComparisonAt_even (Y : HomogeneousSpanCategory A T.data.object) :
    EvenIsoLaws C.data (leftUnitTensorComparisonAtData T E.data H.data i Y) :=
  ((H.mapEvenIsoLaws (X := leftUnitSpanObj A T Y) (Y := Y)
    (EvenIsoLaws.leftUnit A.laws _)).trans C.laws (EvenIsoLaws.leftUnit C.laws _).symm).trans C.laws
      (hi.tensor C.laws (EvenIsoLaws.refl C.laws _))

theorem rightUnitTensorComparisonAt_even (Y : HomogeneousSpanCategory A T.data.object) :
    EvenIsoLaws C.data (rightUnitTensorComparisonAtData T H.data E.data i Y) :=
  ((H.mapEvenIsoLaws (X := rightUnitSpanObj A T Y) (Y := Y)
    (EvenIsoLaws.rightUnit A.laws _)).trans C.laws (EvenIsoLaws.rightUnit C.laws _).symm).trans C.laws
      ((EvenIsoLaws.refl C.laws _).tensor C.laws hi)

theorem leftUnitTensorComparisonAt_naturality {Y Y' : HomogeneousSpanCategory A T.data.object}
    (g : Y ⟶ Y') :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom (A.data.id A.data.tensorUnit) g.hom) :
      leftUnitSpanObj A T Y ⟶ leftUnitSpanObj A T Y')).hom
        (leftUnitTensorComparisonAtData T E.data H.data i Y').hom =
      C.data.comp (leftUnitTensorComparisonAtData T E.data H.data i Y).hom
        (C.data.tensorHom (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj) (H.data.map g).hom) := by
  have h₁ := H.mapIso_naturality (X := leftUnitSpanObj A T Y) (Y := Y)
    (X' := leftUnitSpanObj A T Y') (Y' := Y')
    (i := IsoData.leftUnit A.data Y.obj) (j := IsoData.leftUnit A.data Y'.obj)
    (ObjectProperty.homMk (A.data.tensorHom (A.data.id A.data.tensorUnit) g.hom) :
      leftUnitSpanObj A T Y ⟶ leftUnitSpanObj A T Y') g (A.laws.left_unitor_naturality g.hom)
  have h₂ := iso_naturality_symm C.laws (EvenIsoLaws.leftUnit C.laws _).toIsoLaws
    (EvenIsoLaws.leftUnit C.laws _).toIsoLaws (C.laws.left_unitor_naturality (H.data.map g).hom)
  have h₃ := iso_naturality_tensor C.laws hi (EvenIsoLaws.refl C.laws _)
    (iso_naturality_constant C.laws i) (iso_naturality_refl C.laws (H.data.map g).hom)
  exact iso_naturality_trans C.laws (iso_naturality_trans C.laws h₁ h₂) h₃

theorem rightUnitTensorComparisonAt_naturality {Y Y' : HomogeneousSpanCategory A T.data.object}
    (g : Y ⟶ Y') :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom g.hom (A.data.id A.data.tensorUnit)) :
      rightUnitSpanObj A T Y ⟶ rightUnitSpanObj A T Y')).hom
        (rightUnitTensorComparisonAtData T H.data E.data i Y').hom =
      C.data.comp (rightUnitTensorComparisonAtData T H.data E.data i Y).hom
        (C.data.tensorHom (H.data.map g).hom (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj)) := by
  have h₁ := H.mapIso_naturality (X := rightUnitSpanObj A T Y) (Y := Y)
    (X' := rightUnitSpanObj A T Y') (Y' := Y')
    (i := IsoData.rightUnit A.data Y.obj) (j := IsoData.rightUnit A.data Y'.obj)
    (ObjectProperty.homMk (A.data.tensorHom g.hom (A.data.id A.data.tensorUnit)) :
      rightUnitSpanObj A T Y ⟶ rightUnitSpanObj A T Y') g (A.laws.right_unitor_naturality g.hom)
  have h₂ := iso_naturality_symm C.laws (EvenIsoLaws.rightUnit C.laws _).toIsoLaws
    (EvenIsoLaws.rightUnit C.laws _).toIsoLaws (C.laws.right_unitor_naturality (H.data.map g).hom)
  have h₃ := iso_naturality_tensor C.laws (EvenIsoLaws.refl C.laws _) hi
    (iso_naturality_refl C.laws (H.data.map g).hom) (iso_naturality_constant C.laws i)
  exact iso_naturality_trans C.laws (iso_naturality_trans C.laws h₁ h₂) h₃

end RMod.Classification
