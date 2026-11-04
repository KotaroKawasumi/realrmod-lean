import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Instances.LinearCategory

/-! # Equality of specified inverse data from equality of forward maps

Both inverse maps already satisfy the separate inverse laws. Mathlib's
uniqueness of inverses identifies them without making a new choice.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

theorem isoData_inv_eq_of_hom_eq (C : WeaklyPointedSuperfusion.{u, v})
    {X Y : C.data.Obj} {d e : IsoData C.data X Y}
    (hd : IsoLaws C.data d) (he : IsoLaws C.data e) (h : d.hom = e.hom) : d.inv = e.inv := by
  let α : @CategoryTheory.Iso (LinearCategory C) _ X Y := ⟨d.hom, d.inv, hd.hom_inv, hd.inv_hom⟩
  let β : @CategoryTheory.Iso (LinearCategory C) _ X Y := ⟨e.hom, e.inv, he.hom_inv, he.inv_hom⟩
  exact (CategoryTheory.Iso.inv_eq_inv α β).mpr h

theorem isoData_ext_of_hom_eq (C : WeaklyPointedSuperfusion.{u, v})
    {X Y : C.data.Obj} {d e : IsoData C.data X Y}
    (hd : IsoLaws C.data d) (he : IsoLaws C.data e) (h : d.hom = e.hom) : d = e := by
  have hi := isoData_inv_eq_of_hom_eq C hd he h
  cases d
  cases e
  cases h
  cases hi
  rfl

end RMod.Classification
