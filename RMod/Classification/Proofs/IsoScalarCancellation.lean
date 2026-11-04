import RMod.Classification.Proofs.IsoCalculus

/-! # Cancel an invertible comparison from a scalar equation -/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem iso_cancel_right_smul {X Y Z : C.Obj} {d : IsoData C Y Z} (hd : IsoLaws C d)
    {f g : C.Hom X Y} {r : ℝ}
    (h : C.comp f d.hom = C.smul r (C.comp g d.hom)) : f = C.smul r g := by
  have hh := congrArg (fun q => C.comp q d.inv) h
  simpa only [hC.smul_comp, hC.comp_assoc, hd.hom_inv, hC.comp_id] using hh

theorem iso_comp_right_smul {X Y Z : C.Obj} (d : IsoData C Y Z)
    {f g : C.Hom X Y} {r : ℝ} (h : f = C.smul r g) :
    C.comp f d.hom = C.smul r (C.comp g d.hom) := by
  rw [h, hC.smul_comp]

end RMod.Classification
