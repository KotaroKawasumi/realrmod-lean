import RMod.Classification.Proofs.EquivalenceIndexedTripleEvaluation
import RMod.Classification.Proofs.ConvolutionRawAssociativity
import RMod.Classification.Proofs.InverseTensoratorAssociativity

/-!
# The raw triple scalar forced by an arbitrary monoidal equivalence

Factor out its given inverse tensorators, apply their actual associativity
law, and evaluate the target model's associator. The resulting scalar is
the target omega with its two deletion-order signs. Thus this equation
uses the given equivalence's coherence, rather than assuming a gauge form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

theorem equivalenceIndexedComparison_associator
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (X Y Z : PullbackObj C s.data) (g h k u v w : t.data.group)
    (eu : g * h = u) (ev : h * k = v) (ew : u * k = w) (ew' : g * v = w)
    (ep : t.data.nu g h + t.data.nu u k = t.data.nu h k + t.data.nu g v)
    (hX : ∀ l, l ≠ g → C.id (E.data.forward.obj X l).val = C.zero)
    (hY : ∀ l, l ≠ h → C.id (E.data.forward.obj Y l).val = C.zero) :
    C.comp (E.data.forward.map ((twistedPullback C hC s).data.associatorHom X Y Z) w)
      (equivalenceIndexedRightComparisonData C hC s t E X Y Z g h k v w ev ew').hom =
      C.smul ((t.data.omega g h k).val * (-1 : ℝ) ^
        (t.data.nu g h * t.data.nu u k + t.data.nu h k * t.data.nu g v).val)
        (equivalenceIndexedLeftComparisonData C hC s t E X Y Z g h k u w eu ew).hom := by
  let FL := C.comp (E.data.forward.tensorInv ((twistedPullback C hC s).data.tensorObj X Y) Z w)
    (convolutionHom C hC t.data (E.data.forward.tensorInv X Y)
      (fun j => C.id (E.data.forward.obj Z j).val) w)
  let FR := C.comp (E.data.forward.tensorInv X ((twistedPullback C hC s).data.tensorObj Y Z) w)
    (convolutionHom C hC t.data (fun j => C.id (E.data.forward.obj X j).val)
      (E.data.forward.tensorInv Y Z) w)
  let TL := (convolutionIndexedLeftComparisonData C hC t.data
    (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z) g h k u w eu ew).hom
  let TR := (convolutionIndexedRightComparisonData C hC t.data
    (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z) g h k v w ev ew').hom
  let a := (convolutionAssociatorDataOfParity C hC t.data t.laws.normalizer_parity
    (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z) w).hom
  let m := E.data.forward.map ((twistedPullback C hC s).data.associatorHom X Y Z) w
  let r := (t.data.omega g h k).val * (-1 : ℝ) ^
    (t.data.nu g h * t.data.nu u k + t.data.nu h k * t.data.nu g v).val
  have hl : (equivalenceIndexedLeftComparisonData C hC s t E X Y Z g h k u w eu ew).hom =
      C.comp FL TL := (equivalenceIndexedLeftComparison_factorization C hC s t E X Y Z g h k u w eu ew).trans
        (hC.comp_assoc _ _ _).symm
  have hr : (equivalenceIndexedRightComparisonData C hC s t E X Y Z g h k v w ev ew').hom =
      C.comp FR TR := (equivalenceIndexedRightComparison_factorization C hC s t E X Y Z g h k v w ev ew').trans
        (hC.comp_assoc _ _ _).symm
  have hc : C.comp FL a = C.comp m FR := by
    have he := congrFun (MonoidalSuperfunctor.inverseTensorator_associativity
      (⟨E.data.forward, E.laws.forward⟩ : MonoidalSuperfunctor
        (twistedPullback C hC s).toWeaklyPointedSuperfusion
        (twistedPullback C hC t).toWeaklyPointedSuperfusion) X Y Z) w
    exact (hC.comp_assoc _ _ _).trans he
  have ht : C.comp a TR = C.smul r TL := by
    have he := convolutionIndexedComparison_associator C hC t.data t.laws.normalizer_parity
      (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z)
      g h k u v w w eu ev ew ew' rfl ep hX hY
    simpa only [IsoData.ofEq, IsoData.refl, hC.comp_id] using he
  rw [hl, hr, ← hC.comp_assoc, ← hc, hC.comp_assoc, ht, hC.comp_smul]

end RMod.Classification
