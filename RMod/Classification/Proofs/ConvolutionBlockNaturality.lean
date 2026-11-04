import RMod.Classification.Instances.ConvolutionAssociator
import RMod.Classification.Instances.ConvolutionTripleMaps
import RMod.Classification.Proofs.NormalizerNaturality
import Batteries.Tactic.GeneralizeProofs

/-!
# Naturality of the specified convolution block on all maps

The local normalizer is natural without a homogeneity hypothesis. The
only additional equalities here identify the same group coordinates in
the two expansion conventions; no quotient of group labels is used.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand convolutionLeftFamily convolutionRightFamily

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k)) {X X' Y Y' Z Z' : PullbackObj C t}

theorem convolutionBlockIsoOfParity_naturality (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.comp (convolutionLeftBlockHom C hC t f g h k (a * b) a)
      (convolutionBlockIsoOfParity C hC t hν X' Y' Z' k a b).hom.hom =
        C.comp (convolutionBlockIsoOfParity C hC t hν X Y Z k a b).hom.hom
          (convolutionRightBlockHom C hC t f g h k a b) := by
  dsimp only [convolutionBlockIsoOfParity, convolutionLeftBlockHom, convolutionRightBlockHom,
    twistSummandHom]
  -- Generalize the transport proofs before eliminating coordinate equalities.
  -- This also changes the endpoints hidden in dependent Hom arguments.
  generalize_proofs hC₀ hm₀ hm₁ hout' hin' he hlaw' hout hin hlaw
  revert hout' hin' he hlaw' hout hin hlaw
  dsimp only [convolutionLeftFamily, convolutionRightFamily, twistSummand]
  generalize hbb : a⁻¹ * (a * b) = bb
  have hbb' : bb = b := hbb.symm.trans (inv_mul_cancel_left a b)
  clear hbb
  subst bb
  generalize hcc : (a * b)⁻¹ * k = cc
  have hcc' : cc = b⁻¹ * (a⁻¹ * k) := by rw [← hcc, mul_inv_rev, mul_assoc]
  clear hcc
  subst cc
  generalize hdd : b * (b⁻¹ * (a⁻¹ * k)) = dd
  have hdd' : dd = a⁻¹ * k := hdd.symm.trans (mul_inv_cancel_left b (a⁻¹ * k))
  clear hdd
  subst dd
  intros
  exact hC.pi.localAssociator_naturality hC.toWeaklyPointedSuperfusionLaws
    (f a) (g b) (h (b⁻¹ * (a⁻¹ * k))) _ _ _ _ (by assumption) _

/-- The lawful-twist interface specializes the parity-only naturality law. -/
theorem convolutionBlockIso_naturality (ht : TwistLaws t)
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y')
    (h : PullbackHom C t Z Z') (k a b : t.group) :
    C.comp (convolutionLeftBlockHom C hC t f g h k (a * b) a)
      (convolutionBlockIso C hC t ht X' Y' Z' k a b).hom.hom =
        C.comp (convolutionBlockIso C hC t ht X Y Z k a b).hom.hom
          (convolutionRightBlockHom C hC t f g h k a b) :=
  convolutionBlockIsoOfParity_naturality C hC t ht.normalizer_parity f g h k a b

end RMod.Classification
