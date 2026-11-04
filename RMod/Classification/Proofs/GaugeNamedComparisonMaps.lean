import RMod.Classification.Proofs.GaugeNamedComparison
import RMod.Classification.Proofs.GaugeSimpleComparisonMaps
import RMod.Classification.Proofs.RawHomEqualityMaps

/-!
# Naming a support retains both selected comparison maps

The added endpoint equality maps only transport morphism types. The same
heterogeneous map identities hold after changing the simple generator,
which allows composite tensor diagrams to be compared at common indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : s.data.group)

theorem equivalenceNamedComparison_hom_heq
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object) :
    HEq (equivalenceNamedComparisonData C hC s t E g X).hom
      ((equivalenceComponentComparison C hC s t E g).data.app X).hom :=
  rawHom_comp_ofEq_heq hC.toWeaklyPointedSuperfusionLaws _ _

theorem equivalenceNamedComparison_inv_heq
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object) :
    HEq (equivalenceNamedComparisonData C hC s t E g X).inv
      ((equivalenceComponentComparison C hC s t E g).data.inv.app X).hom := by
  dsimp only [equivalenceNamedComparisonData, IsoData.trans]
  rw [isoData_ofEq_inv_eq]
  exact rawHom_ofEq_comp_heq hC.toWeaklyPointedSuperfusionLaws _ _

variable (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)
  (hg : pullbackSimpleDegree C hC s S = g)
  (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion S.data.object)

theorem equivalenceSimpleComparison_named_hom_heq :
    let e := hg.trans (pullbackSimpleDegree_placed C hC s g).symm
    HEq ((equivalenceSimpleComparison C hC s t E S g hg).data.app X).hom
      (equivalenceNamedComparisonData C hC s t E g
        ((pullbackSourceSpanChange C hC s S (pullbackDegreeSimple C hC s g) e).forwardFunctor.data.obj X)).hom :=
  (equivalenceSimpleComparison_app_heq C hC s t E S g hg X).trans
    (equivalenceNamedComparison_hom_heq C hC s t E g _).symm

theorem equivalenceSimpleComparison_named_inv_heq :
    let e := hg.trans (pullbackSimpleDegree_placed C hC s g).symm
    HEq ((equivalenceSimpleComparison C hC s t E S g hg).data.inv.app X).hom
      (equivalenceNamedComparisonData C hC s t E g
        ((pullbackSourceSpanChange C hC s S (pullbackDegreeSimple C hC s g) e).forwardFunctor.data.obj X)).inv :=
  (equivalenceSimpleComparison_inv_heq C hC s t E S g hg X).trans
    (equivalenceNamedComparison_inv_heq C hC s t E g _).symm

end RMod.Classification
