import RMod.Classification.Instances.UnitTensorComparison
import RMod.Classification.Proofs.IsoNaturality
import RMod.Classification.Proofs.SpanMapRaw

/-!
# Naturality of the canonical unit tensor comparisons

The unitor squares and the even unit insertion commute with arbitrary
endomorphisms of the other generator. Every endomorphism of the tensor
unit is a real scalar, so linearity extends the identity-unit square to
all pairs of endomorphisms, including odd maps in the other factor.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} (T : SimpleObject A)
  {U V : C.data.Obj}
  (E : SpanSuperfunctor A C A.data.tensorUnit U)
  (H : SpanSuperfunctor A C T.data.object V)
  {i : IsoData C.data C.data.tensorUnit (E.data.obj (spanGenerator A A.data.tensorUnit)).obj}
  (hi : EvenIsoLaws C.data i)

include hi

theorem leftUnitTensorComparison_id_naturality
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object) :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom (A.data.id A.data.tensorUnit) g.hom) :
      leftUnitSpanObject A T ⟶ leftUnitSpanObject A T)).hom
        (leftUnitTensorComparisonData T E.data H.data i).hom =
      C.data.comp (leftUnitTensorComparisonData T E.data H.data i).hom
        (C.data.tensorHom (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj) (H.data.map g).hom) := by
  have h₁ := H.mapIso_naturality (X := leftUnitSpanObject A T) (Y := spanGenerator A T.data.object)
    (X' := leftUnitSpanObject A T) (Y' := spanGenerator A T.data.object)
    (i := IsoData.leftUnit A.data T.data.object) (j := IsoData.leftUnit A.data T.data.object)
    (ObjectProperty.homMk (A.data.tensorHom (A.data.id A.data.tensorUnit) g.hom) :
      leftUnitSpanObject A T ⟶ leftUnitSpanObject A T) g (A.laws.left_unitor_naturality g.hom)
  have h₂ := iso_naturality_symm C.laws (EvenIsoLaws.leftUnit C.laws _).toIsoLaws
    (EvenIsoLaws.leftUnit C.laws _).toIsoLaws (C.laws.left_unitor_naturality (H.data.map g).hom)
  have h₃ := iso_naturality_tensor C.laws hi (EvenIsoLaws.refl C.laws _)
    (iso_naturality_constant C.laws i) (iso_naturality_refl C.laws (H.data.map g).hom)
  exact iso_naturality_trans C.laws (iso_naturality_trans C.laws h₁ h₂) h₃

theorem leftUnitTensorComparison_naturality
    (f : spanGenerator A A.data.tensorUnit ⟶ spanGenerator A A.data.tensorUnit)
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object) :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom f.hom g.hom) :
      leftUnitSpanObject A T ⟶ leftUnitSpanObject A T)).hom
        (leftUnitTensorComparisonData T E.data H.data i).hom =
      C.data.comp (leftUnitTensorComparisonData T E.data H.data i).hom
        (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom) := by
  obtain ⟨r, hr⟩ := A.laws.unit_end_scalar_surjective f.hom
  have hf : f = ObjectProperty.homMk (A.data.smul r (A.data.id A.data.tensorUnit)) :=
    ObjectProperty.hom_ext _ hr.symm
  have hEf : (E.data.map f).hom = C.data.smul r
      (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj) := by
    rw [hf]
    exact (E.map_raw_smul (X := spanGenerator A A.data.tensorUnit)
      (Y := spanGenerator A A.data.tensorUnit) r _).trans
        (congrArg (C.data.smul r) (E.map_raw_id (spanGenerator A A.data.tensorUnit)))
  rw [hEf, C.laws.tensor_smul_left, C.laws.comp_smul]
  rw [← hr, A.laws.tensor_smul_left]
  have hm := H.map_raw_smul (X := leftUnitSpanObject A T) (Y := leftUnitSpanObject A T)
    r (A.data.tensorHom (A.data.id A.data.tensorUnit) g.hom)
  exact (congrArg (fun f => C.data.comp f (leftUnitTensorComparisonData T E.data H.data i).hom) hm).trans
    ((C.laws.smul_comp r _ _).trans
      (congrArg (C.data.smul r) (leftUnitTensorComparison_id_naturality T E H hi g)))

theorem rightUnitTensorComparison_id_naturality
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object) :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom g.hom (A.data.id A.data.tensorUnit)) :
      rightUnitSpanObject A T ⟶ rightUnitSpanObject A T)).hom
        (rightUnitTensorComparisonData T H.data E.data i).hom =
      C.data.comp (rightUnitTensorComparisonData T H.data E.data i).hom
        (C.data.tensorHom (H.data.map g).hom (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj)) := by
  have h₁ := H.mapIso_naturality (X := rightUnitSpanObject A T) (Y := spanGenerator A T.data.object)
    (X' := rightUnitSpanObject A T) (Y' := spanGenerator A T.data.object)
    (i := IsoData.rightUnit A.data T.data.object) (j := IsoData.rightUnit A.data T.data.object)
    (ObjectProperty.homMk (A.data.tensorHom g.hom (A.data.id A.data.tensorUnit)) :
      rightUnitSpanObject A T ⟶ rightUnitSpanObject A T) g (A.laws.right_unitor_naturality g.hom)
  have h₂ := iso_naturality_symm C.laws (EvenIsoLaws.rightUnit C.laws _).toIsoLaws
    (EvenIsoLaws.rightUnit C.laws _).toIsoLaws (C.laws.right_unitor_naturality (H.data.map g).hom)
  have h₃ := iso_naturality_tensor C.laws (EvenIsoLaws.refl C.laws _) hi
    (iso_naturality_refl C.laws (H.data.map g).hom) (iso_naturality_constant C.laws i)
  exact iso_naturality_trans C.laws (iso_naturality_trans C.laws h₁ h₂) h₃

theorem rightUnitTensorComparison_naturality
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object)
    (f : spanGenerator A A.data.tensorUnit ⟶ spanGenerator A A.data.tensorUnit) :
    C.data.comp (H.data.map (ObjectProperty.homMk (A.data.tensorHom g.hom f.hom) :
      rightUnitSpanObject A T ⟶ rightUnitSpanObject A T)).hom
        (rightUnitTensorComparisonData T H.data E.data i).hom =
      C.data.comp (rightUnitTensorComparisonData T H.data E.data i).hom
        (C.data.tensorHom (H.data.map g).hom (E.data.map f).hom) := by
  obtain ⟨r, hr⟩ := A.laws.unit_end_scalar_surjective f.hom
  have hf : f = ObjectProperty.homMk (A.data.smul r (A.data.id A.data.tensorUnit)) :=
    ObjectProperty.hom_ext _ hr.symm
  have hEf : (E.data.map f).hom = C.data.smul r
      (C.data.id (E.data.obj (spanGenerator A A.data.tensorUnit)).obj) := by
    rw [hf]
    exact (E.map_raw_smul (X := spanGenerator A A.data.tensorUnit)
      (Y := spanGenerator A A.data.tensorUnit) r _).trans
        (congrArg (C.data.smul r) (E.map_raw_id (spanGenerator A A.data.tensorUnit)))
  rw [hEf, C.laws.tensor_smul_right, C.laws.comp_smul]
  rw [← hr, A.laws.tensor_smul_right]
  have hm := H.map_raw_smul (X := rightUnitSpanObject A T) (Y := rightUnitSpanObject A T)
    r (A.data.tensorHom g.hom (A.data.id A.data.tensorUnit))
  exact (congrArg (fun f => C.data.comp f (rightUnitTensorComparisonData T H.data E.data i).hom) hm).trans
    ((C.laws.smul_comp r _ _).trans
      (congrArg (C.data.smul r) (rightUnitTensorComparison_id_naturality T E H hi g)))

end RMod.Classification
