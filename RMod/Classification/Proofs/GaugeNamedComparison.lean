import RMod.Classification.Instances.GaugeNamedComparison
import RMod.Classification.Proofs.IndexedMorphismEquality
import RMod.Classification.Proofs.HomogeneousIsoCalculus

/-!
# Inverse, parity, and signed naturality at the named coordinate

The support equality maps are even and natural in every indexed raw
morphism. Consequently the original selected component comparison keeps
its parity and signed naturality after naming the coordinate g.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : s.data.group)

theorem equivalenceNamedComparison_homogeneousIso
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData (equivalenceGaugeLambda C hC s t E g)
      (equivalenceNamedComparisonData C hC s t E g X) := by
  let η := equivalenceComponentComparison C hC s t E g
  have hi : HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData (equivalenceGaugeLambda C hC s t E g)
      (⟨(η.data.app X).hom, (η.data.inv.app X).hom⟩ : IsoData C.toWeaklyPointedSuperfusionData _ _) :=
    ⟨⟨congrArg (fun f => f.hom) (η.laws.hom_inv X), congrArg (fun f => f.hom) (η.laws.inv_hom X)⟩,
      η.laws.grade X, η.laws.inverse.grade X⟩
  have he := hi.trans hC.toWeaklyPointedSuperfusionLaws
    (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws
      (congrArg (fun j => (X.obj j).val) (pullbackSimpleDegree_placed C hC s g))).homogeneous
  rw [add_zero] at he
  exact he

theorem equivalenceNamedComparison_naturality
    {X Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object}
    {a : ZMod 2} (f : X ⟶ Y)
    (hf : (twistedPullback C hC s).data.IsHomogeneous a f.hom) :
    C.comp (E.data.forward.map f.hom (equivalenceGaugePhi C hC s t E g))
      (equivalenceNamedComparisonData C hC s t E g Y).hom =
      C.smul ((-1 : ℝ) ^ (equivalenceGaugeLambda C hC s t E g * a).val)
        (C.comp (equivalenceNamedComparisonData C hC s t E g X).hom (f.hom g)) := by
  let η := equivalenceComponentComparison C hC s t E g
  have hn := congrArg (fun q => q.hom) (η.laws.naturality f hf)
  change C.comp (E.data.forward.map f.hom (equivalenceGaugePhi C hC s t E g))
      (η.data.app Y).hom = C.smul ((-1 : ℝ) ^ (equivalenceGaugeLambda C hC s t E g * a).val)
        (C.comp (η.data.app X).hom
          (f.hom (pullbackSimpleDegree C hC s (pullbackDegreeSimple C hC s g)))) at hn
  have he := indexed_morphism_eq_naturality
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (fun j => (X.obj j).val) (fun j => (Y.obj j).val) f.hom
    (pullbackSimpleDegree_placed C hC s g)
    (congrArg (fun j => (X.obj j).val) (pullbackSimpleDegree_placed C hC s g))
    (congrArg (fun j => (Y.obj j).val) (pullbackSimpleDegree_placed C hC s g))
  dsimp only [equivalenceNamedComparisonData, IsoData.trans]
  refine (hC.comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun q => C.comp q _) hn).trans ?_
  rw [hC.smul_comp, hC.comp_assoc, he, ← hC.comp_assoc]

end RMod.Classification
