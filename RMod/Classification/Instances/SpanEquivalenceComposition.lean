import RMod.Classification.Instances.SpanSuperequivalence
import RMod.Classification.Instances.SpanSuperfunctorComposition
import RMod.Classification.Proofs.EquivalenceComponents

/-!
# Composition of completed component equivalences

Mathlib composes the specified ordinary equivalences. The two component
superfunctors compose by their existing maps, and every component of the
new unit and counit is a composite of even maps. The extra superlinear
laws are proved separately for this exact ordinary equivalence data.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperequivalence

open CategoryTheory

variable {C D K : WeaklyPointedSuperfusion.{0, 0}}
  {S : C.data.Obj} {T : D.data.Obj} {U : K.data.Obj}

def transData (F : SpanSuperequivalenceData C D S T) (G : SpanSuperequivalenceData D K T U) :
    SpanSuperequivalenceData C K S U := F.trans G

theorem transLaws (F : SpanSuperequivalence C D S T) (G : SpanSuperequivalence D K T U) :
    SpanSuperequivalenceLaws C K S U (transData F.data G.data) where
  forward := SpanSuperfunctor.compLaws F.forwardFunctor G.forwardFunctor
  backward := SpanSuperfunctor.compLaws G.backwardFunctor F.backwardFunctor
  unit_hom_even X := by
    have h := C.laws.comp_grade _ _ (F.laws.unit_hom_even X)
      (F.laws.backward.map_grade _ (G.laws.unit_hom_even (F.data.functor.obj X)))
    rw [zero_add] at h
    have he := congrArg (fun f : X ⟶ _ => f.hom)
      (equivalence_trans_unit_hom F.data G.data X)
    exact he.symm ▸ h
  unit_inv_even X := by
    have h := C.laws.comp_grade _ _
      (F.laws.backward.map_grade _ (G.laws.unit_inv_even (F.data.functor.obj X)))
      (F.laws.unit_inv_even X)
    rw [zero_add] at h
    have he := congrArg (fun f : _ ⟶ X => f.hom)
      (equivalence_trans_unit_inv F.data G.data X)
    exact he.symm ▸ h
  counit_hom_even Y := by
    have h := K.laws.comp_grade _ _
      (G.laws.forward.map_grade _ (F.laws.counit_hom_even (G.data.inverse.obj Y)))
      (G.laws.counit_hom_even Y)
    rw [zero_add] at h
    have he := congrArg (fun f : _ ⟶ Y => f.hom)
      (equivalence_trans_counit_hom F.data G.data Y)
    exact he.symm ▸ h
  counit_inv_even Y := by
    have h := K.laws.comp_grade _ _ (G.laws.counit_inv_even Y)
      (G.laws.forward.map_grade _ (F.laws.counit_inv_even (G.data.inverse.obj Y)))
    rw [zero_add] at h
    have he := congrArg (fun f : Y ⟶ _ => f.hom)
      (equivalence_trans_counit_inv F.data G.data Y)
    exact he.symm ▸ h

def trans (F : SpanSuperequivalence C D S T) (G : SpanSuperequivalence D K T U) :
    SpanSuperequivalence C K S U := ⟨transData F.data G.data, transLaws F G⟩

end RMod.Classification.SpanSuperequivalence
