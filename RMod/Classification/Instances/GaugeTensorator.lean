import RMod.Classification.Proofs.GaugeTensorBlock
import RMod.Classification.Instances.ConvolutionBiproduct
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The actual tensorator of the gauge functor

Expand the target convolution into its chosen biproduct. Apply the local
gauge blocks while reindexing by the inverse group isomorphism, then
undo right tensor distribution and the source convolution comparison.
All maps act on the original chosen sum objects in the supplied category.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

noncomputable def gaugeTensorBlockEvenIso (X Y : PullbackObj C s.data) (k l : t.data.group) :
    convolutionEvenFamily C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k l ≅
    convolutionEvenFamily C hC s.data X Y (d.phi.symm k) (d.phi.symm l) ⊗
      referenceEvenObj C hC (C.pi.factor (d.lam (d.phi.symm k))) :=
  IsoData.toEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (gaugeTensorBlockData C hC s t d hρ hν X Y k l)
    (gaugeTensorBlock_evenIso C hC s t d hρ hν X Y k l)

noncomputable def gaugeTensoratorEvenIso (X Y : PullbackObj C s.data) (k : t.data.group) :
    referenceEvenObj C hC (convolutionObj C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k).val ≅
    referenceEvenObj C hC
      (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj
        (convolutionObj C hC s.data X Y)) k).val :=
  let P := referenceEvenObj C hC (C.pi.factor (d.lam (d.phi.symm k)))
  convolutionEvenIso C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k ≪≫
    biproduct.whiskerEquiv
      (g := fun g => convolutionEvenFamily C hC s.data X Y (d.phi.symm k) g ⊗ P)
      d.phi.symm.toEquiv (fun l => (gaugeTensorBlockEvenIso C hC s t d hρ hν X Y k l).symm) ≪≫
    (rightDistributor (convolutionEvenFamily C hC s.data X Y (d.phi.symm k)) P).symm ≪≫
    tensorIso (convolutionEvenIso C hC s.data X Y (d.phi.symm k)).symm (CategoryTheory.Iso.refl P)

noncomputable def gaugeTensoratorData (X Y : PullbackObj C s.data) (k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t.data
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) k).val
      (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj
        (convolutionObj C hC s.data X Y)) k).val :=
  IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (gaugeTensoratorEvenIso C hC s t d hρ hν X Y k)

end RMod.Classification
