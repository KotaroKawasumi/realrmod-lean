import RMod.Classification.Instances.RestrictedSpanFunctor
import RMod.Classification.Instances.HomogeneousRealization
import RMod.Classification.Proofs.HomogeneousSumComparison
import RMod.Classification.Proofs.IsoCalculus

/-!
# A superfunctor covers the homogeneous span of its image generator

Realize the target presentation's parity list in the source category.
Its image has the same parity list, and the identity of the image
generator extends to an even isomorphism of the two presentations.
No full faithfulness hypothesis is needed for this existence statement.
-/

set_option autoImplicit false

namespace RMod.Classification.Superfunctor

variable {C : PiSuperfusion.{0, 0}} {D : WeaklyPointedSuperfusion.{0, 0}}
  (F : Superfunctor C.toWeaklyPointedSuperfusion D) (S : C.data.Obj)

theorem restrictSpan_even_essSurj (Y : HomogeneousSpanCategory D (F.data.obj S)) :
    ∃ X : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion S,
      D.data.HasHomogeneousIso 0 ((F.restrictSpan S).data.obj X).obj Y.obj := by
  obtain ⟨n, ⟨d⟩⟩ := Y.property
  let r := homogeneousRealization C S d.data.parity
  let X : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion S :=
    ⟨r.data.object, n, ⟨r.toHomogeneousSum⟩⟩
  let m := F.mapHomogeneousSum r.toHomogeneousSum
  let e := HomogeneousSum.comparisonIsoData 0 m.data d.data (IsoData.refl D.data (F.data.obj S))
  have hp : d.data.parity = m.data.parity := r.laws.parity.symm
  have hi := HomogeneousSum.comparisonIsoLaws (C := D) 0 m d hp
    (IsoData.refl D.data (F.data.obj S)) (EvenIsoLaws.refl D.laws _).toIsoLaws
  refine ⟨X, e.hom, e.inv, hi.hom_inv, hi.inv_hom, ?_, ?_⟩
  · exact HomogeneousSum.comparison_grade (C := D) 0 m d hp _ (D.laws.id_even _)
  · exact HomogeneousSum.comparison_grade (C := D) 0 d m hp.symm _ (D.laws.id_even _)

end RMod.Classification.Superfunctor
