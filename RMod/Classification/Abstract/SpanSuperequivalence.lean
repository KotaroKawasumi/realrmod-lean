import RMod.Classification.Abstract.SpanSuperfunctor
import Mathlib.CategoryTheory.Equivalence

/-!
# Superlinear equivalence of two homogeneous spans

Mathlib supplies the underlying ordinary equivalence, including its
actual inverse functor and natural isomorphisms. The additional linear,
grading and evenness conditions are separate laws on that exact external
bundle. Both ambient categories already carry their completed laws.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C D : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj) (T : D.data.Obj)

abbrev SpanSuperequivalenceData := HomogeneousSpanCategory C S ≌ HomogeneousSpanCategory D T

structure SpanSuperequivalenceLaws (d : SpanSuperequivalenceData C D S T) : Prop where
  forward : SpanSuperfunctorLaws C D S T d.functor.toPrefunctor
  backward : SpanSuperfunctorLaws D C T S d.inverse.toPrefunctor
  unit_hom_even : ∀ X, C.data.IsHomogeneous 0 (d.unitIso.hom.app X).hom
  unit_inv_even : ∀ X, C.data.IsHomogeneous 0 (d.unitIso.inv.app X).hom
  counit_hom_even : ∀ Y, D.data.IsHomogeneous 0 (d.counitIso.hom.app Y).hom
  counit_inv_even : ∀ Y, D.data.IsHomogeneous 0 (d.counitIso.inv.app Y).hom

structure SpanSuperequivalence where
  data : SpanSuperequivalenceData C D S T
  laws : SpanSuperequivalenceLaws C D S T data

end RMod.Classification
