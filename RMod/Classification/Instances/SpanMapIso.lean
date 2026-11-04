import RMod.Classification.Instances.SpanSuperfunctor
import RMod.Classification.Abstract.Normalizers

/-!
# Mapping specified isomorphisms through a component functor

Both mapped arrows are taken from the supplied functor. Functoriality
proves their inverse identities, and preservation of grading proves
evenness without any new choice of an inverse.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {S : A.data.Obj} {T : C.data.Obj}
  {X Y : HomogeneousSpanCategory A S}

def mapIsoData (F : SpanSuperfunctorData A C S T) (i : IsoData A.data X.obj Y.obj) :
    IsoData C.data (F.obj X).obj (F.obj Y).obj where
  hom := (F.map (ObjectProperty.homMk i.hom : X ⟶ Y)).hom
  inv := (F.map (ObjectProperty.homMk i.inv : Y ⟶ X)).hom

theorem mapIsoLaws (F : SpanSuperfunctor A C S T) {i : IsoData A.data X.obj Y.obj}
    (hi : IsoLaws A.data i) : IsoLaws C.data (mapIsoData F.data i) where
  hom_inv := by
    let e : X ≅ Y := ⟨ObjectProperty.homMk i.hom, ObjectProperty.homMk i.inv,
      ObjectProperty.hom_ext _ hi.hom_inv, ObjectProperty.hom_ext _ hi.inv_hom⟩
    exact congrArg (fun f : F.toFunctor.obj X ⟶ F.toFunctor.obj X => f.hom)
      (F.toFunctor.mapIso e).hom_inv_id
  inv_hom := by
    let e : X ≅ Y := ⟨ObjectProperty.homMk i.hom, ObjectProperty.homMk i.inv,
      ObjectProperty.hom_ext _ hi.hom_inv, ObjectProperty.hom_ext _ hi.inv_hom⟩
    exact congrArg (fun f : F.toFunctor.obj Y ⟶ F.toFunctor.obj Y => f.hom)
      (F.toFunctor.mapIso e).inv_hom_id

theorem mapEvenIsoLaws (F : SpanSuperfunctor A C S T) {i : IsoData A.data X.obj Y.obj}
    (hi : EvenIsoLaws A.data i) : EvenIsoLaws C.data (mapIsoData F.data i) where
  toIsoLaws := mapIsoLaws F hi.toIsoLaws
  hom_even := F.laws.map_grade _ hi.hom_even
  inv_even := F.laws.map_grade _ hi.inv_even

/-- Mapping a commuting square keeps exactly its two mapped composites. -/
theorem mapIso_naturality (F : SpanSuperfunctor A C S T)
    {X' Y' : HomogeneousSpanCategory A S}
    {i : IsoData A.data X.obj Y.obj} {j : IsoData A.data X'.obj Y'.obj}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (h : A.data.comp f.hom j.hom = A.data.comp i.hom g.hom) :
    C.data.comp (F.data.map f).hom (mapIsoData F.data j).hom =
      C.data.comp (mapIsoData F.data i).hom (F.data.map g).hom := by
  have hh : f ≫ ObjectProperty.homMk j.hom = ObjectProperty.homMk i.hom ≫ g :=
    ObjectProperty.hom_ext _ h
  have hm := congrArg F.toFunctor.map hh
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact congrArg (fun k : F.toFunctor.obj X ⟶ F.toFunctor.obj Y' => k.hom) hm

end RMod.Classification.SpanSuperfunctor
