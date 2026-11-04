import RMod.Classification.Instances.SpanGenerator
import RMod.Classification.Instances.HomogeneousSpanPresentation
import RMod.Classification.Instances.HomogeneousMatrix
import RMod.Classification.Instances.SpanSuperfunctor

/-!
# Detecting morphisms from the image of a span generator

A superfunctor maps the total matrix identity of a homogeneous
presentation. Hence its mapped generator inclusions detect every map out
of the image object. This is the categorical density calculation behind
extension and uniqueness of homogeneous natural comparisons.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Preadditive

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  (F : SpanSuperfunctor C D S T)

theorem spanPresentation_total (X : HomogeneousSpanCategory C S) :
    ∑ i, (ObjectProperty.homMk ((spanPresentation X).data.projection i) :
      X ⟶ spanGenerator C S) ≫ ObjectProperty.homMk ((spanPresentation X).data.inclusion i) = 𝟙 X := by
  apply ObjectProperty.hom_ext
  have hh := map_sum (InducedCategory.homAddEquiv (C := LinearCategory C)
    (F := fun Y : HomogeneousSpanCategory C S => Y.obj) (X := X) (Y := X))
    (fun i => (ObjectProperty.homMk ((spanPresentation X).data.projection i) :
      X ⟶ spanGenerator C S) ≫ ObjectProperty.homMk ((spanPresentation X).data.inclusion i)) Finset.univ
  exact hh.trans (spanPresentation X).total

theorem SpanSuperfunctor.hom_ext_generator {X : HomogeneousSpanCategory C S}
    {Y : HomogeneousSpanCategory D T} (f g : F.toFunctor.obj X ⟶ Y)
    (h : ∀ i, F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) :
      spanGenerator C S ⟶ X) ≫ f =
        F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) :
          spanGenerator C S ⟶ X) ≫ g) : f = g := by
  have ht : ∑ i, F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.projection i) :
      X ⟶ spanGenerator C S) ≫
        F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) :
          spanGenerator C S ⟶ X) = 𝟙 (F.toFunctor.obj X) := by
    simp only [← F.toFunctor.map_comp, ← F.toFunctor.map_sum, spanPresentation_total, F.toFunctor.map_id]
  calc
    f = (∑ i, F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.projection i) :
      X ⟶ spanGenerator C S) ≫ F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) :
        spanGenerator C S ⟶ X)) ≫ f := by rw [ht, Category.id_comp]
    _ = (∑ i, F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.projection i) :
      X ⟶ spanGenerator C S) ≫ F.toFunctor.map (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) :
        spanGenerator C S ⟶ X)) ≫ g := by
      rw [sum_comp, sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      rw [Category.assoc, Category.assoc, h i]
    _ = g := by rw [ht, Category.id_comp]

end RMod.Classification
