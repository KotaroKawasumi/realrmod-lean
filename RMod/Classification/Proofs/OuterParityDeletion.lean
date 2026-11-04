import RMod.Classification.Proofs.NormalizerDeletion

/-!
# The associator with the outer tensor parity deleted first

Binary evaluation comparisons remove the outer parity factor before the
inner one. Interchanging those deletions on each side of the associator
produces the two signs below. This is the scalar convention of the raw
triple comparison, before conversion to the normalized beta convention.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem localAssociator_outerDeletion (X Y Z : C.Obj) (n m r s : ZMod 2)
    (e : n + m = r + s) (omega : ℝˣ) :
    C.comp (p.localAssociator X Y Z n m r s e omega).hom
      (C.comp (p.rightFactorDeletion
        (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor r))) s).hom
        (C.tensorHom (C.id X) (p.rightFactorDeletion (C.tensorObj Y Z) r).hom)) =
      C.smul (omega.val * (-1 : ℝ) ^ (n * m + r * s).val)
        (C.comp (p.rightFactorDeletion
          (C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor n)) Z) m).hom
          (C.comp (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id Z))
            (C.associatorHom X Y Z))) := by
  have hl := hp.rightFactorDeletion_naturality hC m
    (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id Z))
    ((hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj X Y) n).whiskerRight hC Z).hom_grade
  have hr := hp.rightFactorDeletion_naturality hC s
    (C.tensorHom (C.id X) (p.rightFactorDeletion (C.tensorObj Y Z) r).hom)
    ((hp.rightFactorDeletion_homogeneousIso hC (C.tensorObj Y Z) r).whiskerLeft hC X).hom_grade
  have he := hp.localAssociator_deletion hC X Y Z n m r s e omega
  rw [hr, hC.comp_smul, ← hC.comp_assoc _ _ (C.associatorHom X Y Z), hl,
    hC.smul_comp, ← hC.mul_smul] at he
  have hh := congrArg (C.smul ((-1 : ℝ) ^ (s * r).val)) he
  rw [← hC.mul_smul, parity_power_mul_self, hC.one_smul, ← hC.mul_smul] at hh
  refine hh.trans ?_
  rw [hC.comp_assoc]
  apply congrArg (fun z => C.smul z _)
  rw [parity_power_add, mul_comm n m, mul_comm r s]
  ring

end RMod.Classification.PiLaws
