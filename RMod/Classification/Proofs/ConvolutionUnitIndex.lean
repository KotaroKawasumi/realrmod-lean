import RMod.Classification.Proofs.ConvolutionUnitInsertions

/-!
# A unit-block inclusion with a propositionally equal group index

Keep the forced equality map before the surviving unit block. This is
needed when inverse group reindexing represents 1 by phi inverse(1).
-/

set_option autoImplicit false

namespace RMod.Classification

theorem convolutionLeftUnitor_inclusion_of_eq
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)
    (X : PullbackObj C t) (k g : t.group) (he : g = 1) :
    C.comp (convolutionInclusion C hC t (pullbackUnitObj C hC t) X k g)
      (convolutionLeftUnitorData C hC t ht X k).hom =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
      (congrArg (fun i => twistSummand C t (pullbackUnitObj C hC t) X i (i⁻¹ * k)) he)).hom
      (convolutionLeftUnitBlock C hC t ht X k).hom.hom := by
  subst g
  exact (convolutionLeftUnitor_inclusion C hC t ht X k).trans (hC.id_comp _).symm

end RMod.Classification
