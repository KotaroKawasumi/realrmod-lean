import RMod.BrundanEllis.StackingInverse
import RMod.BrundanEllis.StackingGauge

/-! The cochain operations have the specified neutral element and right inverse.
These identities concern twists themselves and do not assume a quotient group. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis
open Stacking

theorem twistMul_unit {G : FiniteGrp.{0}} (s : TwistOn G) :
    twistMul s (twistUnit G) = s := by
  rcases s with ⟨s, hs⟩
  subst G
  apply Subtype.ext
  apply twistData_injective
  simp [twistMul, twistMulData, twistUnit, cupOne, realSign]

theorem twistUnit_mul {G : FiniteGrp.{0}} (s : TwistOn G) :
    twistMul (twistUnit G) s = s := by
  rcases s with ⟨s, hs⟩
  subst G
  apply Subtype.ext
  apply twistData_injective
  simp [twistMul, twistMulData, twistUnit, cupOne, realSign]

theorem twistMul_inv {G : FiniteGrp.{0}} (s : TwistOn G) :
    twistMul s (twistInv s) = twistUnit G := by
  rcases s with ⟨s, hs⟩
  subst G
  apply Subtype.ext
  apply twistData_injective
  simp only [twistMul, twistInv, twistUnit, twistMulData, twistInvData]
  simp only [mul_inv_cancel, MonoidHom.inv_apply, bwBit_inv]
  have hn (g h : s.group) : s.nu g h +
      (s.nu g h + bwBit (s.rho g) * bwBit (s.rho h)) +
        bwBit (s.rho g) * bwBit (s.rho h) = 0 := by
    simp [← add_assoc, CharTwo.add_self_eq_zero]
  simp only [hn]
  congr 1
  funext g h k
  have hc := inverse_correction s.rho s.nu g h k
  dsimp only [correction, typeCorrection, cross] at hc
  simp only [MonoidHom.inv_apply, bwBit_inv] at hc
  rw [hc]
  simp only [cupOne, cross, MonoidHom.inv_apply, bwBit_inv,
    ← add_assoc, mul_assoc, mul_inv_cancel_left, realSign_sq]

end RMod.BrundanEllis
