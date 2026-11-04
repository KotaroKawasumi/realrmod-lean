import RMod.Classification.Proofs.HomogeneousIsoCalculus

/-! A homogeneous interchange of the middle two factors.  Its maps are
explicit composites of the given associators and the specified middle
exchange.  Inverse and grading laws are proved separately from these data. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Reassociate four factors, exchange the middle pair, and reassociate back. -/
def interchangeIsoData (C : WeaklyPointedSuperfusionData.{u, v}) (X Y Z W : C.Obj)
    (e : IsoData C (C.tensorObj Y Z) (C.tensorObj Z Y)) :
    IsoData C (C.tensorObj (C.tensorObj X Y) (C.tensorObj Z W))
      (C.tensorObj (C.tensorObj X Z) (C.tensorObj Y W)) :=
  ((((IsoData.assoc C X Y (C.tensorObj Z W)).trans C
    ((IsoData.refl C X).tensor C ((IsoData.assoc C Y Z W).symm C))).trans C
    ((IsoData.refl C X).tensor C (e.tensor C (IsoData.refl C W)))).trans C
    ((IsoData.refl C X).tensor C (IsoData.assoc C Z Y W))).trans C
    ((IsoData.assoc C X Z (C.tensorObj Y W)).symm C)

/-- The four-factor interchange has the degree and invertibility of its middle exchange. -/
theorem interchangeIsoLaws {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) (X Y Z W : C.Obj) (a : ZMod 2)
    (e : IsoData C (C.tensorObj Y Z) (C.tensorObj Z Y)) (he : HomogeneousIsoLaws C a e) :
    HomogeneousIsoLaws C a (interchangeIsoData C X Y Z W e) := by
  have h₁ := (EvenIsoLaws.assoc hC X Y (C.tensorObj Z W)).homogeneous
  have h₂ := HomogeneousIsoLaws.whiskerLeft hC
    ((EvenIsoLaws.assoc hC Y Z W).symm.homogeneous) X
  have h₃ := HomogeneousIsoLaws.whiskerLeft hC (HomogeneousIsoLaws.whiskerRight hC he W) X
  have h₄ := HomogeneousIsoLaws.whiskerLeft hC (EvenIsoLaws.assoc hC Z Y W).homogeneous X
  have h₅ := ((EvenIsoLaws.assoc hC X Z (C.tensorObj Y W)).symm).homogeneous
  simpa only [interchangeIsoData, zero_add, add_zero] using
    HomogeneousIsoLaws.trans hC
      (HomogeneousIsoLaws.trans hC (HomogeneousIsoLaws.trans hC
        (HomogeneousIsoLaws.trans hC h₁ h₂) h₃) h₄) h₅

end RMod.BrundanEllis.Stacking
