import RMod.Classification.Instances.HomogeneousTensorIso
import RMod.Classification.Proofs.HomogeneousIsoCalculus
import RMod.Classification.Proofs.ParityPowers

/-!
# The Koszul-corrected tensor inverse has degree equal to the parity sum

Interchange contributes precisely the sign inserted in the inverse data.
Its square is one, so both composite maps are identities.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomogeneousIsoLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem tensor {X X' Y Y' : C.Obj} {a b : ZMod 2}
    {d : IsoData C X X'} {e : IsoData C Y Y'}
    (hd : HomogeneousIsoLaws C a d) (he : HomogeneousIsoLaws C b e) :
    HomogeneousIsoLaws C (a + b) (d.homogeneousTensor C a b e) where
  hom_inv := by
    change C.comp (C.tensorHom d.hom e.hom)
      (C.smul ((-1 : ℝ) ^ (b * a).val) (C.tensorHom d.inv e.inv)) = _
    rw [hC.comp_smul, hC.super_interchange _ _ _ _ he.inv_grade hd.hom_grade,
      ← hC.mul_smul, parity_power_mul_self, hC.one_smul, hd.hom_inv, he.hom_inv, hC.tensor_id]
  inv_hom := by
    change C.comp (C.smul ((-1 : ℝ) ^ (b * a).val) (C.tensorHom d.inv e.inv))
      (C.tensorHom d.hom e.hom) = _
    rw [hC.smul_comp, hC.super_interchange _ _ _ _ he.hom_grade hd.inv_grade,
      ← hC.mul_smul, parity_power_mul_self, hC.one_smul, hd.inv_hom, he.inv_hom, hC.tensor_id]
  hom_grade := hC.tensor_grade _ _ hd.hom_grade he.hom_grade
  inv_grade := hC.grade_smul _ _ (hC.tensor_grade _ _ hd.inv_grade he.inv_grade)

end RMod.Classification.HomogeneousIsoLaws
