import RMod.Classification.Proofs.IsoEqualityMaps

/-! # Cancellation of the specified equality comparison maps -/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem isoData_ofEq_cancel_left {X Y Z : C.data.Obj} (e : X = Y)
    (f g : C.data.Hom Y Z)
    (h : C.data.comp (IsoData.ofEq C.data e).hom f = C.data.comp (IsoData.ofEq C.data e).hom g) : f = g := by
  cases e
  exact (C.laws.id_comp f).symm.trans (h.trans (C.laws.id_comp g))

theorem isoData_ofEq_cancel_right {X Y Z : C.data.Obj} (e : Y = Z)
    (f g : C.data.Hom X Y)
    (h : C.data.comp f (IsoData.ofEq C.data e).hom = C.data.comp g (IsoData.ofEq C.data e).hom) : f = g := by
  cases e
  exact (C.laws.comp_id f).symm.trans (h.trans (C.laws.comp_id g))

end RMod.Classification
