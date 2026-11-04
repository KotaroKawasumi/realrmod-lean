import RMod.BrundanEllis.StackingExternalReversed
import RMod.BrundanEllis.StackingReferenceBinaryBlock

/-! The binary reference comparison has precisely the external twist's
parity.  Its target is the tensor of the two original convolution summands,
in the order used by the reversed exterior pairing. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- The external nu is the sum of the original parities and the middle exchange degree. -/
theorem exteriorTwist_nu (s t : Twist) (g g' : s.group) (h h' : t.group) :
    (exteriorTwist s t).val.nu (g, h) (g', h') =
      s.nu g g' + t.nu h h' + ReferenceCommutor.degree (s.rho g).toAdd (t.rho h').toAdd := by
  change fixedNu (externalTwist ⟨s, rfl⟩ ⟨t, rfl⟩) (g, h) (g', h') = _
  rw [externalTwist, fixedNu_mul]
  simp only [sumNu, cross, (baseChange_data _ _).1, (baseChange_data _ _).2.1]
  rfl

/-- Compare a single external convolution summand to the two original summands. -/
def exteriorBinaryBlockData (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    IsoData reference.data.toWeaklyPointedSuperfusionData
      (twistSummand reference.data (oldTwist (exteriorTwist s t).val).data
        ((reversedExteriorPairing s t).obj (X, Y)) ((reversedExteriorPairing s t).obj (X', Y'))
        (g, h) (g', h'))
      (reference.data.tensorObj
        (twistSummand reference.data (oldTwist t).data Y Y' h h')
        (twistSummand reference.data (oldTwist s).data X X' g g')) := by
  let e := referenceBinaryBlockData (s.rho g).toAdd (t.rho h').toAdd
    (Y h).val (X g).val (Y' h').val (X' g').val (X g).property (Y' h').property
    (s.nu g g') (t.nu h h')
  exact (IsoData.ofEq _ (congrArg (fun a => reference.data.tensorObj
    (reference.data.tensorObj (reference.data.tensorObj (Y h).val (X g).val)
      (reference.data.tensorObj (Y' h').val (X' g').val)) (reference.data.pi.factor a))
    (exteriorTwist_nu s t g g' h h'))).trans _ e

/-- The closed binary cochain makes the actual summand comparison even. -/
theorem exteriorBinaryBlockLaws (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    EvenIsoLaws reference.data.toWeaklyPointedSuperfusionData
      (exteriorBinaryBlockData s t X X' Y Y' g g' h h') := by
  apply EvenIsoLaws.trans referenceProperty.toWeaklyPointedSuperfusionLaws
    (EvenIsoLaws.ofEq referenceProperty.toWeaklyPointedSuperfusionLaws _)
  exact referenceBinaryBlockLaws _ _ _ _ _ _ _ _ _ _

end RMod.BrundanEllis.Stacking
