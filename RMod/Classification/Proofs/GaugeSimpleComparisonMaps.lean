import RMod.Classification.Instances.GaugeSimpleComparison
import RMod.Classification.Proofs.SpanNaturalIsoEquality

/-!
# The component comparison retains its selected maps under generator change

The construction at any simple of support g uses the original comparison
chosen at g. The two functor equalities only transport its endpoint types.
This makes the common choice on intermediate product components explicit.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)
  (g : s.data.group) (hg : pullbackSimpleDegree C hC s S = g)

theorem equivalenceSimpleComparison_heq :
    let P := pullbackDegreeSimple C hC s g
    let e := hg.trans (pullbackSimpleDegree_placed C hC s g).symm
    HEq (equivalenceSimpleComparison C hC s t E S g hg)
      (((equivalenceComponentComparison C hC s t E g).precompose
        (pullbackSourceSpanChange C hC s S P e).forwardFunctor).postcompose
          (pullbackReferenceSpanChange C hC s P S e.symm).forwardFunctor) := by
  unfold equivalenceSimpleComparison
  exact (cast_heq _ _).trans (cast_heq _ _)

theorem equivalenceSimpleComparison_app_heq
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object) :
    let P := pullbackDegreeSimple C hC s g
    let e := hg.trans (pullbackSimpleDegree_placed C hC s g).symm
    HEq ((equivalenceSimpleComparison C hC s t E S g hg).data.app X).hom
      ((equivalenceComponentComparison C hC s t E g).data.app
        ((pullbackSourceSpanChange C hC s S P e).forwardFunctor.data.obj X)).hom := by
  exact SpanHomogeneousNatIso.app_raw_heq
    (equivalenceEvaluation_change_generator C hC s S (pullbackDegreeSimple C hC s g)
      (hg.trans (pullbackSimpleDegree_placed C hC s g).symm) t E).symm
    (pullbackEvaluation_change_generator C hC s S (pullbackDegreeSimple C hC s g)
      (hg.trans (pullbackSimpleDegree_placed C hC s g).symm)).symm
    (equivalenceSimpleComparison_heq C hC s t E S g hg) X

theorem equivalenceSimpleComparison_inv_heq
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object) :
    let P := pullbackDegreeSimple C hC s g
    let e := hg.trans (pullbackSimpleDegree_placed C hC s g).symm
    HEq ((equivalenceSimpleComparison C hC s t E S g hg).data.inv.app X).hom
      ((equivalenceComponentComparison C hC s t E g).data.inv.app
        ((pullbackSourceSpanChange C hC s S P e).forwardFunctor.data.obj X)).hom := by
  exact SpanHomogeneousNatIso.inv_raw_heq
    (equivalenceEvaluation_change_generator C hC s S (pullbackDegreeSimple C hC s g)
      (hg.trans (pullbackSimpleDegree_placed C hC s g).symm) t E).symm
    (pullbackEvaluation_change_generator C hC s S (pullbackDegreeSimple C hC s g)
      (hg.trans (pullbackSimpleDegree_placed C hC s g).symm)).symm
    (equivalenceSimpleComparison_heq C hC s t E S g hg) X

/-- Renaming the same support does not change the selected map. -/
theorem equivalenceSimpleComparison_app_degree (g' : s.data.group)
    (hg' : pullbackSimpleDegree C hC s S = g') (he : g = g')
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object) :
    ((equivalenceSimpleComparison C hC s t E S g hg).data.app X).hom =
      ((equivalenceSimpleComparison C hC s t E S g' hg').data.app X).hom := by
  cases he
  rfl

theorem equivalenceSimpleComparison_inv_degree (g' : s.data.group)
    (hg' : pullbackSimpleDegree C hC s S = g') (he : g = g')
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object) :
    ((equivalenceSimpleComparison C hC s t E S g hg).data.inv.app X).hom =
      ((equivalenceSimpleComparison C hC s t E S g' hg').data.inv.app X).hom := by
  cases he
  rfl

end RMod.Classification
