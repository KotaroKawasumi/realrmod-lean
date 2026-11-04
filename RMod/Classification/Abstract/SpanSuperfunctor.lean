import RMod.Classification.Abstract.HomogeneousSpan
import Mathlib.Combinatorics.Quiver.Prefunctor

/-!
# Superfunctors between homogeneous span components

Components need not themselves be monoidal categories. This separated
interface uses their completed ambient categories and Mathlib full
subcategories. Object and morphism maps are Prefunctor data; functor,
real-linearity and grading conditions are laws on precisely those maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C D : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj) (T : D.data.Obj)

abbrev SpanSuperfunctorData := Prefunctor (HomogeneousSpanCategory C S) (HomogeneousSpanCategory D T)

structure SpanSuperfunctorLaws (F : SpanSuperfunctorData C D S T) : Prop where
  map_id : ∀ X, F.map (𝟙 X) = 𝟙 (F.obj X)
  map_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g
  map_zero : ∀ X Y, F.map (0 : X ⟶ Y) = 0
  map_add : ∀ {X Y} (f g : X ⟶ Y), F.map (f + g) = F.map f + F.map g
  map_smul : ∀ {X Y} (r : ℝ) (f : X ⟶ Y), F.map (r • f) = r • F.map f
  map_grade : ∀ {X Y : HomogeneousSpanCategory C S} {a : ZMod 2} (f : X ⟶ Y),
    C.data.IsHomogeneous a f.hom → D.data.IsHomogeneous a (F.map f).hom

structure SpanSuperfunctor where
  data : SpanSuperfunctorData C D S T
  laws : SpanSuperfunctorLaws C D S T data

end RMod.Classification
