import RMod.Hierarchy.Abstract.Supercategory

/-! Superfunctors preserve the specified enriched identity and composition. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

structure SuperfunctorData (C D : SupercategoryData) where
  obj : C.Obj → D.Obj
  map : ∀ X Y, C.Hom X Y ⟶ D.Hom (obj X) (obj Y)
structure SuperfunctorLaws {C D : SupercategoryData} (F : SuperfunctorData C D) : Prop where
  map_id : ∀ X, C.id X ≫ F.map X X = D.id (F.obj X)
  map_comp : ∀ X Y Z, C.comp X Y Z ≫ F.map X Z =
    (F.map X Y ⊗ₘ F.map Y Z) ≫ D.comp (F.obj X) (F.obj Y) (F.obj Z)
structure Superfunctor (C D : Supercategory) where
  data : SuperfunctorData C.data D.data
  laws : SuperfunctorLaws data

def Superfunctor.enriched {C D : Supercategory} (F : Superfunctor C D) :
    EnrichedFunctor SuperVec C.data.Obj D.data.Obj where
  obj := F.data.obj
  map := F.data.map
  map_id := F.laws.map_id
  map_comp := F.laws.map_comp
def tMap {C D : SupercategoryData} (F : SuperfunctorData C D)
    {X Y : C.Obj} (f : THom C X Y) : THom D (F.obj X) (F.obj Y) :=
  fun a => F.map X Y a (f a)

end RMod.Legacy
