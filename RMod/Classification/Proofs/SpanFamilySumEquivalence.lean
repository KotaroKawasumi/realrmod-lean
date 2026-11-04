import RMod.Classification.Instances.SpanFamilySumEquivalence
import RMod.Classification.Proofs.SpanFamilySumLinear
import RMod.Classification.Proofs.SpanFamilyInverse

/-!
# Superlinear laws of the actual component decomposition equivalence

The inverse is the one already constructed from grouped simple sums.
Mathlib derives its linearity from forward linearity. The even preimage
comparisons give even unit and counit in both directions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I]
  (S : I → C.data.Obj) (hS : ∀ i, C.data.IsSimple (S i))
  (hST : ∀ i j, i ≠ j → ¬ SameParityOrbit C.data (S i) (S j))
  (cover : ∀ T, C.data.IsSimple T → ∃ i, SameParityOrbit C.data (S i) T)

instance spanFamilySumEquivalence_forward_additive :
    (spanFamilySumEquivalence C S hS hST cover).functor.Additive :=
  spanFamilySum_additive C S

instance spanFamilySumEquivalence_forward_linear :
    (spanFamilySumEquivalence C S hS hST cover).functor.Linear ℝ :=
  spanFamilySum_linear C S

instance spanFamilySumEquivalence_backward_additive :
    (spanFamilySumEquivalence C S hS hST cover).inverse.Additive :=
  Equivalence.inverse_additive _

instance spanFamilySumEquivalence_backward_linear :
    (spanFamilySumEquivalence C S hS hST cover).inverse.Linear ℝ :=
  Equivalence.inverseLinear ℝ _

theorem spanFamilySumEquivalence_inverse_map_grade {X Y : LinearCategory C} {a : ZMod 2}
    (f : X ⟶ Y) (hf : C.data.IsHomogeneous a f) (i : I) :
    C.data.IsHomogeneous a ((spanFamilySumEquivalence C S hS hST cover).inverse.map f i).hom :=
  (spanFamilySumPreimages C S hS cover).inverseFunctor_map_grade
    (spanFamilySumFullyFaithful C S hS hST) (spanFamilySum_map_grade_iff C S) f hf i

theorem spanFamilySumEquivalence_unit_hom_even (X : SpanFamilyCategory C S) (i : I) :
    C.data.IsHomogeneous 0 ((spanFamilySumEquivalence C S hS hST cover).unitIso.hom.app X i).hom :=
  (spanFamilySumPreimages C S hS cover).inverseUnitIso_hom_even
    (spanFamilySumFullyFaithful C S hS hST) (spanFamilySum_map_grade_iff C S) X i

theorem spanFamilySumEquivalence_unit_inv_even (X : SpanFamilyCategory C S) (i : I) :
    C.data.IsHomogeneous 0 ((spanFamilySumEquivalence C S hS hST cover).unitIso.inv.app X i).hom :=
  (spanFamilySumPreimages C S hS cover).inverseUnitIso_inv_even
    (spanFamilySumFullyFaithful C S hS hST) (spanFamilySum_map_grade_iff C S) X i

theorem spanFamilySumEquivalence_counit_hom_even (X : LinearCategory C) :
    C.data.IsHomogeneous 0 ((spanFamilySumEquivalence C S hS hST cover).counitIso.hom.app X) :=
  ((spanFamilySumPreimages C S hS cover).laws.evenIso X).hom_even

theorem spanFamilySumEquivalence_counit_inv_even (X : LinearCategory C) :
    C.data.IsHomogeneous 0 ((spanFamilySumEquivalence C S hS hST cover).counitIso.inv.app X) :=
  ((spanFamilySumPreimages C S hS cover).laws.evenIso X).inv_even

end RMod.Classification
