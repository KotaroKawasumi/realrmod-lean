import RMod.Classification.Proofs.ConvolutionComponents
import RMod.Classification.Proofs.FiniteSums
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Convolution objects in the abstract reference category

For output degree k, enumerate g in the given finite group and sum the
summands (X_g tensor Y_(g^-1 k)) tensor pi^nu(g,g^-1 k). The selected finite
sums come from C, and the proved component closure supplies their subtype
certificates. This is actual construction data, not an existence assertion.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def groupEnumeration (t : TwistData) : Fin (Nat.card t.group) ≃ t.group := by
  classical
  letI := Fintype.ofFinite t.group
  exact (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := t.group)).symm).symm

noncomputable def convolutionFamily (C : PiSuperfusionData.{0, 0}) (t : TwistData)
    (X Y : PullbackObj C t) (k : t.group) : Fin (Nat.card t.group) → C.Obj := fun i =>
  twistSummand C t X Y (groupEnumeration t i) ((groupEnumeration t i)⁻¹ * k)

noncomputable def convolutionObj (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)
    (t : TwistData) (X Y : PullbackObj C t) : PullbackObj C t := fun k =>
  ⟨((finiteSumsData C hC.toWeaklyPointedSuperfusionLaws).sum (convolutionFamily C t X Y k)).object,
    finiteSums_inComponent C hC (convolutionFamily C t X Y k)
      (Multiplicative.toAdd (t.rho k)) (fun i => by
        have h := twistSummand_inComponent C hC t X Y
          (groupEnumeration t i) ((groupEnumeration t i)⁻¹ * k)
        simpa only [convolutionFamily, mul_inv_cancel_left] using h)⟩

end RMod.Classification
