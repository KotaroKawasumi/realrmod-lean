import RMod.Classification.Proofs.HomogeneousIsoCalculus
import RMod.Classification.Proofs.ParityPowers

/-!
# The signs when changed binary comparisons are composed

Cancel the intermediate component comparison in each triple route.
For the left route the crossing involves the original inner comparison;
for the right route it involves the changed inner comparison. These
orders follow the project's actual super-interchange convention.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem tensorComparisonChange_left
    {X X' Y Y' Z Z' : C.Obj} {a n : ZMod 2}
    (i : IsoData C X X') (hi : IsoLaws C i) (j : C.Hom Z Z')
    (k : C.Hom X Y) (l : C.Hom Y Y')
    (hj : C.IsHomogeneous a j) (hk : C.IsHomogeneous n k) :
    C.comp (C.tensorHom i.hom j)
      (C.tensorHom (C.comp i.inv (C.comp k l)) (C.id Z')) =
      C.smul ((-1 : ℝ) ^ (a * n).val)
        (C.comp (C.tensorHom k (C.id Z)) (C.tensorHom l j)) := by
  rw [interchange_second_even hC _ _ _ _ (hC.id_even Z'),
    ← hC.comp_assoc i.hom i.inv, hi.hom_inv, hC.id_comp, hC.comp_id,
    hC.super_interchange _ _ _ _ hj hk, hC.id_comp, ← hC.mul_smul,
    parity_power_mul_self, hC.one_smul]

theorem tensorComparisonChange_right
    {X X' Y Y' Z Z' : C.Obj} {a n : ZMod 2}
    (i : C.Hom X X') (j : IsoData C Y Y') (hj : IsoLaws C j)
    (k : C.Hom Y Z) (l : C.Hom Z Z')
    (hi : C.IsHomogeneous a i)
    (hk : C.IsHomogeneous n (C.comp j.inv (C.comp k l))) :
    C.comp (C.tensorHom i j.hom)
      (C.tensorHom (C.id X') (C.comp j.inv (C.comp k l))) =
      C.smul ((-1 : ℝ) ^ (a * n).val)
        (C.comp (C.tensorHom (C.id X) k) (C.tensorHom i l)) := by
  rw [hC.super_interchange _ _ _ _ hk hi, hC.comp_id,
    ← hC.comp_assoc j.hom j.inv, hj.hom_inv, hC.id_comp,
    interchange_first_even hC _ _ _ _ (hC.id_even X), hC.id_comp, mul_comm n a]

end RMod.Classification
