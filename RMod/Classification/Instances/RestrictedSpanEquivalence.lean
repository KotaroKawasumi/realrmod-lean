import RMod.Classification.Instances.RestrictedSpanFunctor
import RMod.Classification.Instances.EquivalenceSimpleOrbits
import RMod.Classification.Proofs.HomogeneousSpanChange
import RMod.Classification.Proofs.SpanInverse

/-!
# Restriction of an arbitrary superequivalence to a simple component

The forward functor keeps the given maps. Its specified inverse sends
objects back into the source span, since the even unit identifies its
generator with the inverse image of the target generator. The original
counit supplies explicit even preimages. The existing inverse-functor
construction then gives a completed component superequivalence.
-/

set_option autoImplicit false

namespace RMod.Classification.MonoidalSuperequivalence

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (E : MonoidalSuperequivalence C D) (S : SimpleObject C)

theorem backward_mem_span (Y : HomogeneousSpanCategory D (E.data.forward.obj S.data.object)) :
    InHomogeneousSpan C S.data.object (E.data.backward.obj Y.obj) := by
  have hU : SameParityOrbit C.data S.data.object
      (E.data.backward.obj (E.data.forward.obj S.data.object)) :=
    ⟨0, E.data.unitHom S.data.object, E.data.unitInv S.data.object,
      E.laws.unit_hom_inv S.data.object, E.laws.unit_inv_hom S.data.object,
      E.laws.unit_hom_even S.data.object, E.laws.unit_inv_even S.data.object⟩
  exact (inHomogeneousSpan_congr_generator C S.laws.simple
    ((E.isSimple_backward_map_iff _).mpr (E.mapSimple S).laws.simple) hU _).mpr
      (E.backwardFunctor.map_homogeneousSpan Y.property)

def spanRestrictionPreimagesData :
    SpanPreimagesData (E.forwardFunctor.restrictSpan S.data.object).data where
  object Y := ⟨E.data.backward.obj Y.obj, E.backward_mem_span S Y⟩
  counit Y := ⟨E.data.counitHom Y.obj, E.data.counitInv Y.obj⟩

theorem spanRestrictionPreimagesLaws : SpanPreimagesLaws (E.spanRestrictionPreimagesData S) where
  counit Y :=
    { hom_inv := E.laws.counit_hom_inv Y.obj
      inv_hom := E.laws.counit_inv_hom Y.obj
      hom_even := E.laws.counit_hom_even Y.obj
      inv_even := E.laws.counit_inv_even Y.obj }

def spanRestrictionPreimages : SpanPreimages (E.forwardFunctor.restrictSpan S.data.object) :=
  ⟨E.spanRestrictionPreimagesData S, E.spanRestrictionPreimagesLaws S⟩

noncomputable def spanRestrictionFullyFaithful :
    (E.forwardFunctor.restrictSpan S.data.object).toFunctor.FullyFaithful where
  preimage f := ObjectProperty.homMk (E.underlyingEquivalence.fullyFaithfulFunctor.preimage f.hom)
  map_preimage f := ObjectProperty.hom_ext _
    (E.underlyingEquivalence.fullyFaithfulFunctor.map_preimage f.hom)
  preimage_map f := ObjectProperty.hom_ext _
    (E.underlyingEquivalence.fullyFaithfulFunctor.preimage_map f.hom)

noncomputable def spanRestrictionData :
    SpanSuperequivalenceData C D S.data.object (E.data.forward.obj S.data.object) :=
  (E.spanRestrictionPreimages S).underlyingEquivalence (E.spanRestrictionFullyFaithful S)

theorem spanRestrictionLaws :
    SpanSuperequivalenceLaws C D S.data.object (E.data.forward.obj S.data.object) (E.spanRestrictionData S) :=
  (E.spanRestrictionPreimages S).underlyingEquivalenceLaws (E.spanRestrictionFullyFaithful S)
    (fun f => E.map_grade_iff f.hom)

noncomputable def spanRestriction : SpanSuperequivalence C D S.data.object (E.data.forward.obj S.data.object) :=
  ⟨E.spanRestrictionData S, E.spanRestrictionLaws S⟩

end RMod.Classification.MonoidalSuperequivalence
