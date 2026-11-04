import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Proofs.TensorCalculus

/-!
# Even isomorphism calculus for structural normalizers

All maps and inverse maps were fixed in the data layer. The laws below
justify composition, tensoring and multiplication by an invertible real
scalar. Evenness removes the crossing sign when tensoring inverse pairs.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.EvenIsoLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem refl (X : C.Obj) : EvenIsoLaws C (IsoData.refl C X) where
  hom_inv := hC.id_comp _
  inv_hom := hC.id_comp _
  hom_even := hC.id_even X
  inv_even := hC.id_even X

theorem ofEq {X Y : C.Obj} (h : X = Y) : EvenIsoLaws C (IsoData.ofEq C h) := by
  subst Y
  exact refl hC X

omit hC in
theorem symm {X Y : C.Obj} {d : IsoData C X Y} (hd : EvenIsoLaws C d) :
    EvenIsoLaws C (d.symm C) where
  hom_inv := hd.inv_hom
  inv_hom := hd.hom_inv
  hom_even := hd.inv_even
  inv_even := hd.hom_even

theorem trans {X Y Z : C.Obj} {d : IsoData C X Y} {e : IsoData C Y Z}
    (hd : EvenIsoLaws C d) (he : EvenIsoLaws C e) : EvenIsoLaws C (d.trans C e) where
  hom_inv := by
    change C.comp (C.comp d.hom e.hom) (C.comp e.inv d.inv) = C.id X
    rw [hC.comp_assoc, ← hC.comp_assoc e.hom e.inv d.inv, he.hom_inv, hC.id_comp, hd.hom_inv]
  inv_hom := by
    change C.comp (C.comp e.inv d.inv) (C.comp d.hom e.hom) = C.id Z
    rw [hC.comp_assoc, ← hC.comp_assoc d.inv d.hom e.hom, hd.inv_hom, hC.id_comp, he.inv_hom]
  hom_even := comp_even hC hd.hom_even he.hom_even
  inv_even := comp_even hC he.inv_even hd.inv_even

theorem tensor {X X' Y Y' : C.Obj} {d : IsoData C X X'} {e : IsoData C Y Y'}
    (hd : EvenIsoLaws C d) (he : EvenIsoLaws C e) : EvenIsoLaws C (d.tensor C e) where
  hom_inv := by
    change C.comp (C.tensorHom d.hom e.hom) (C.tensorHom d.inv e.inv) = _
    rw [interchange_second_even hC _ _ _ _ he.inv_even, hd.hom_inv, he.hom_inv, hC.tensor_id]
  inv_hom := by
    change C.comp (C.tensorHom d.inv e.inv) (C.tensorHom d.hom e.hom) = _
    rw [interchange_second_even hC _ _ _ _ he.hom_even, hd.inv_hom, he.inv_hom, hC.tensor_id]
  hom_even := tensor_even hC hd.hom_even he.hom_even
  inv_even := tensor_even hC hd.inv_even he.inv_even

theorem scale {X Y : C.Obj} (r : ℝˣ) {d : IsoData C X Y} (hd : EvenIsoLaws C d) :
    EvenIsoLaws C (d.scale C r) where
  hom_inv := by
    change C.comp (C.smul r.val d.hom) (C.smul r⁻¹.val d.inv) = _
    simp only [hC.smul_comp, hC.comp_smul, ← hC.mul_smul, hd.hom_inv,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, hC.one_smul]
  inv_hom := by
    change C.comp (C.smul r⁻¹.val d.inv) (C.smul r.val d.hom) = _
    simp only [hC.smul_comp, hC.comp_smul, ← hC.mul_smul, hd.inv_hom,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, hC.one_smul]
  hom_even := hC.grade_smul _ _ hd.hom_even
  inv_even := hC.grade_smul _ _ hd.inv_even

theorem assoc (X Y Z : C.Obj) : EvenIsoLaws C (IsoData.assoc C X Y Z) where
  hom_inv := hC.associator_hom_inv X Y Z
  inv_hom := hC.associator_inv_hom X Y Z
  hom_even := hC.associator_hom_even X Y Z
  inv_even := hC.associator_inv_even X Y Z

theorem leftUnit (X : C.Obj) : EvenIsoLaws C (IsoData.leftUnit C X) where
  hom_inv := hC.left_unitor_hom_inv X
  inv_hom := hC.left_unitor_inv_hom X
  hom_even := hC.left_unitor_hom_even X
  inv_even := hC.left_unitor_inv_even X

theorem rightUnit (X : C.Obj) : EvenIsoLaws C (IsoData.rightUnit C X) where
  hom_inv := hC.right_unitor_hom_inv X
  inv_hom := hC.right_unitor_inv_hom X
  hom_even := hC.right_unitor_hom_even X
  inv_even := hC.right_unitor_inv_even X

end RMod.Classification.EvenIsoLaws
