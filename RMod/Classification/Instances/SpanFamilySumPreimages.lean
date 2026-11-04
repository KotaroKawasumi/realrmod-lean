import RMod.Classification.Abstract.SpanFamilyPreimages
import RMod.Classification.Instances.GroupedSpanFamily
import RMod.Classification.Instances.SpanFamilySum
import RMod.Classification.Instances.EvenIsos

/-!
# Actual even preimages by grouping a simple decomposition

Choose a component label for each simple summand using the covering
hypothesis. The fiber sums and the even regrouping isomorphism give the
preimage data. Their inverse and parity laws then follow from the actual
Mathlib isomorphism, before bundling the completed preimage structure.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)
  (hS : ∀ i, C.data.IsSimple (S i))
  (cover : ∀ T, C.data.IsSimple T → ∃ i, SameParityOrbit C.data (S i) T)

noncomputable def simpleDecompositionComponentLabel (X : C.data.Obj)
    (j : Fin (simpleDecomposition C X).data.size) : I :=
  (cover ((simpleDecomposition C X).data.summand j) ((simpleDecomposition C X).laws.simple j)).choose

omit [Fintype I] in
theorem simpleDecompositionComponentLabel_spec (X : C.data.Obj)
    (j : Fin (simpleDecomposition C X).data.size) :
    SameParityOrbit C.data (S (simpleDecompositionComponentLabel C S cover X j))
      ((simpleDecomposition C X).data.summand j) :=
  (cover ((simpleDecomposition C X).data.summand j) ((simpleDecomposition C X).laws.simple j)).choose_spec

noncomputable def spanFamilySumPreimagesData : SpanFamilyPreimagesData C S (spanFamilySumData C S) where
  family X := groupedSpanFamily (simpleDecomposition C X) S hS (simpleDecompositionComponentLabel C S cover X)
    (simpleDecompositionComponentLabel_spec C S cover X)
  iso X := IsoData.ofEvenIso C (groupedSimpleIso (simpleDecomposition C X) (simpleDecompositionComponentLabel C S cover X))

theorem spanFamilySumPreimagesLaws : SpanFamilyPreimagesLaws C S (spanFamilySumPreimagesData C S hS cover) where
  evenIso X := evenIsoLaws_ofEvenIso C
    (groupedSimpleIso (simpleDecomposition C X) (simpleDecompositionComponentLabel C S cover X))

noncomputable def spanFamilySumPreimages : SpanFamilyPreimages C S (spanFamilySum C S) where
  data := spanFamilySumPreimagesData C S hS cover
  laws := spanFamilySumPreimagesLaws C S hS cover

end RMod.Classification
