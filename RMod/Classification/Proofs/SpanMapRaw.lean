import RMod.Classification.Instances.SpanSuperfunctor

/-! # The component functor laws on ambient morphisms -/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {S : A.data.Obj} {T : C.data.Obj}
  (F : SpanSuperfunctor A C S T)

theorem map_raw_id (X : HomogeneousSpanCategory A S) :
    (F.data.map (ObjectProperty.homMk (A.data.id X.obj) : X ⟶ X)).hom =
      C.data.id (F.data.obj X).obj :=
  congrArg (fun f : F.toFunctor.obj X ⟶ F.toFunctor.obj X => f.hom) (F.laws.map_id X)

theorem map_raw_smul {X Y : HomogeneousSpanCategory A S} (r : ℝ) (f : A.data.Hom X.obj Y.obj) :
    (F.data.map (ObjectProperty.homMk (A.data.smul r f) : X ⟶ Y)).hom =
      C.data.smul r (F.data.map (ObjectProperty.homMk f : X ⟶ Y)).hom :=
  congrArg (fun k : F.toFunctor.obj X ⟶ F.toFunctor.obj Y => k.hom)
    (F.laws.map_smul r (ObjectProperty.homMk f : X ⟶ Y))

theorem map_raw_add {X Y : HomogeneousSpanCategory A S} (f g : A.data.Hom X.obj Y.obj) :
    (F.data.map (ObjectProperty.homMk (A.data.add f g) : X ⟶ Y)).hom =
      C.data.add (F.data.map (ObjectProperty.homMk f : X ⟶ Y)).hom
        (F.data.map (ObjectProperty.homMk g : X ⟶ Y)).hom :=
  congrArg (fun k : F.toFunctor.obj X ⟶ F.toFunctor.obj Y => k.hom)
    (F.laws.map_add (ObjectProperty.homMk f : X ⟶ Y) (ObjectProperty.homMk g : X ⟶ Y))

theorem map_raw_comp {X Y Z : HomogeneousSpanCategory A S}
    (f : A.data.Hom X.obj Y.obj) (g : A.data.Hom Y.obj Z.obj) :
    (F.data.map (ObjectProperty.homMk (A.data.comp f g) : X ⟶ Z)).hom =
      C.data.comp (F.data.map (ObjectProperty.homMk f : X ⟶ Y)).hom
        (F.data.map (ObjectProperty.homMk g : Y ⟶ Z)).hom :=
  congrArg (fun k : F.toFunctor.obj X ⟶ F.toFunctor.obj Z => k.hom)
    (F.laws.map_comp (ObjectProperty.homMk f : X ⟶ Y) (ObjectProperty.homMk g : Y ⟶ Z))

end RMod.Classification.SpanSuperfunctor
