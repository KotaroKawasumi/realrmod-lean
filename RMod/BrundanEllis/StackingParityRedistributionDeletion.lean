import RMod.BrundanEllis.StackingParityRedistribution

/-! Deleting the two target parity factors reduces the binary comparison
to the reference shuffle.  The retained product of the two parities is
one of the signs that enters the associator cochain calculation. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Ordered target deletions recover the original homogeneous comparison and its Koszul sign. -/
theorem parityRedistribution_deletion {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {P : PiData C} (hP : PiLaws C P)
    (U V W : C.Obj) (p q c : ZMod 2) (e : IsoData C U (C.tensorObj V W)) :
    C.comp (parityRedistributionData C P U V W p q c e).hom
      (C.tensorHom (P.rightFactorDeletion V q).hom (P.rightFactorDeletion W p).hom) =
    C.smul ((-1 : ℝ) ^ (p * q).val)
      (C.comp (P.rightFactorDeletion U (p + q + c)).hom e.hom) := by
  have hV := hP.rightFactorDeletion_homogeneousIso hC V q
  have hW := hP.rightFactorDeletion_homogeneousIso hC W p
  change C.comp (C.comp (C.comp (P.rightFactorDeletion U (p + q + c)).hom e.hom)
    (C.tensorHom (P.rightFactorDeletion V q).inv (P.rightFactorDeletion W p).inv)) _ = _
  rw [hC.comp_assoc, hC.super_interchange _ _ _ _ hW.hom_grade hV.inv_grade,
    hV.inv_hom, hW.inv_hom, hC.tensor_id, hC.comp_smul, hC.comp_id]

end RMod.BrundanEllis.Stacking
