import RMod.Classification.Proofs.RightFactorDeletion
import RMod.Classification.Proofs.HomogeneousTensorIso

/-! Redistribute a right parity factor across a homogeneous binary comparison.
Deletion, the given comparison, and the two insertions have total even degree
when the input parity is the sum of the two output parities and the comparison degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Delete the source parity factor and insert the two prescribed target factors. -/
def parityRedistributionData (C : WeaklyPointedSuperfusionData.{u, v}) (P : PiData C)
    (U V W : C.Obj) (p q c : ZMod 2) (e : IsoData C U (C.tensorObj V W)) :
    IsoData C (C.tensorObj U (P.factor (p + q + c)))
      (C.tensorObj (C.tensorObj V (P.factor q)) (C.tensorObj W (P.factor p))) :=
  ((P.rightFactorDeletion U (p + q + c)).trans C e).trans C
    (((P.rightFactorDeletion V q).symm C).homogeneousTensor C q p
      ((P.rightFactorDeletion W p).symm C))

/-- The Koszul-corrected tensor inverse makes the redistribution an even isomorphism. -/
theorem parityRedistributionLaws {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {P : PiData C} (hP : PiLaws C P)
    (U V W : C.Obj) (p q c : ZMod 2) (e : IsoData C U (C.tensorObj V W))
    (he : HomogeneousIsoLaws C c e) : EvenIsoLaws C (parityRedistributionData C P U V W p q c e) := by
  have h₁ := hP.rightFactorDeletion_homogeneousIso hC U (p + q + c)
  have h₂ := HomogeneousIsoLaws.tensor hC
    (hP.rightFactorDeletion_homogeneousIso hC V q).symm
    (hP.rightFactorDeletion_homogeneousIso hC W p).symm
  have h := HomogeneousIsoLaws.trans hC (HomogeneousIsoLaws.trans hC h₁ he) h₂
  have ha : ((p + q + c) + c) + (q + p) = 0 := by
    ring_nf
    simp [CharTwo.two_eq_zero]
  rw [ha] at h
  exact ⟨h.toIsoLaws, h.hom_grade, h.inv_grade⟩

end RMod.BrundanEllis.Stacking
