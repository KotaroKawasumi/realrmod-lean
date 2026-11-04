import RMod.Classification.Instances.ConvolutionAssociatorOfParity
import RMod.Classification.Proofs.IsoEqualityMaps
import Batteries.Tactic.GeneralizeProofs

/-!
# The specified convolution block on a triple of input degrees

At output `(g*h)*k` all complementary degrees identify with the original
inputs. The actual block is the selected local associator, with the two
source and target equality comparisons retained explicitly. Only the
parity cocycle is used, never a scalar normalization or pentagon law.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionLeftFamily convolutionRightFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionBlockIsoOfParity_product_hom (X Y Z : PullbackObj C t) (g h k : t.group)
    (hs : (convolutionLeftFamily C hC t X Y Z ((g * h) * k) (g * h) g).obj =
      C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val) (C.pi.factor (t.nu (g * h) k)))
    (hr : C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k)) (C.pi.factor (t.nu g (h * k))) =
      (convolutionRightFamily C hC t X Y Z ((g * h) * k) g h).obj) :
    (convolutionBlockIsoOfParity C hC t hν X Y Z ((g * h) * k) g h).hom.hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (C.comp (C.pi.localAssociator (X g).val (Y h).val (Z k).val
          (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k))
          (hν g h k) (t.omega g h k)).hom
          (IsoData.ofEq C.toWeaklyPointedSuperfusionData hr).hom) := by
  dsimp only [convolutionBlockIsoOfParity]
  generalize_proofs hC₀ hm₀ hm₁ hout hin he hlaw hlocal
  revert hm₁ hout hin he hlaw hlocal hs hr
  dsimp only [convolutionLeftFamily, convolutionRightFamily, twistSummand]
  generalize hbb : g⁻¹ * (g * h) = bb
  have hbb' : bb = h := hbb.symm.trans (inv_mul_cancel_left g h)
  clear hbb
  subst bb
  generalize hcc : (g * h)⁻¹ * ((g * h) * k) = cc
  have hcc' : cc = k := hcc.symm.trans (inv_mul_cancel_left (g * h) k)
  clear hcc
  subst cc
  generalize hdd : g⁻¹ * ((g * h) * k) = dd
  have hdd' : dd = h * k := by rw [← hdd, mul_assoc, inv_mul_cancel_left]
  clear hdd
  subst dd
  generalize hee : h⁻¹ * (h * k) = ee
  have hee' : ee = k := hee.symm.trans (inv_mul_cancel_left h k)
  clear hee
  subst ee
  intros
  change (C.pi.localAssociator (X g).val (Y h).val (Z k).val
    (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k)) (hν g h k) (t.omega g h k)).hom =
    C.comp (C.id _) (C.comp (C.pi.localAssociator (X g).val (Y h).val (Z k).val
    (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k)) (hν g h k) (t.omega g h k)).hom (C.id _))
  rw [hC.comp_id, hC.id_comp]

end RMod.Classification
