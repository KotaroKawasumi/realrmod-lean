import RMod.BrundanEllis.StackingOperations

/-! The explicit inverse twist is valid, with exactly the prescribed cochains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis
namespace Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

@[simp] theorem realSign_inv (a : ZMod 2) : (realSign a)⁻¹ = realSign a := by
  apply inv_eq_of_mul_eq_one_left
  exact realSign_sq a

@[simp] theorem bwBit_inv (a : Multiplicative (ZMod 8)) : bwBit a⁻¹ = bwBit a := by
  have h := bwBit_mul a a⁻¹
  rw [mul_inv_cancel, bwBit_one] at h
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -h

private theorem zmod2_square (a : ZMod 2) : a ^ 2 = a := by
  fin_cases a <;> rfl

/-- The cup-one square of a parity cup square vanishes as a cochain. -/
theorem cross_cupOne_self (r : G →* Multiplicative (ZMod 8)) (g h k : G) :
    cupOne (cross r r) (cross r r) g h k = 0 := by
  simp only [cupOne, cross, map_mul, bwBit_mul]
  ring_nf
  simp only [zmod2_square]
  ring_nf
  simp [show (4 : ZMod 2) = 0 from rfl]

/-- Substituting the inverse degree and binary cochain in the product correction
recovers the displayed closed inverse formula. -/
theorem inverse_correction (r : G →* Multiplicative (ZMod 8))
    (v : G → G → ZMod 2) (g h k : G) :
    cupOne (fun a b => v a b + bwBit (r a) * bwBit (r b)) v g h k +
      (bwPrimitive (r g) + bwBit (r g)) * bwBit (r h) * bwBit (r k) =
    correction r r⁻¹ v (fun a b => v a b + cross r r a b) g h k := by
  have hc : cross r r⁻¹ = cross r r := by
    funext a b; simp [cross]
  have hv : (fun a b => v a b + (v a b + cross r r a b)) = cross r r := by
    funext a b; simp [← add_assoc, CharTwo.add_self_eq_zero]
  simp only [correction, hc, hv, cross_cupOne_self, add_zero, typeCorrection,
    MonoidHom.inv_apply, bwBit_inv]
  dsimp [cross]
  ring_nf
  simp only [zmod2_square]

/-- A cochain correction with the required coboundary changes the pentagon parity. -/
theorem rescale_pentagon (v w : G → G → ZMod 2) (a : G → G → G → ℝˣ)
    (E : G → G → G → ZMod 2)
    (ha : ∀ g h k l, a h k l * a g (h * k) l * a g h k =
      realSign (v g h * v k l) * (a (g * h) k l * a g h (k * l)))
    (he : ∀ g h k l, E h k l + E g (h * k) l + E g h k + v g h * v k l =
      w g h * w k l + E (g * h) k l + E g h (k * l))
    (g h k l : G) :
    let o := fun x y z => a x y z * realSign (E x y z)
    o h k l * o g (h * k) l * o g h k =
      realSign (w g h * w k l) * (o (g * h) k l * o g h (k * l)) := by
  have hs := congrArg realSign (he g h k l)
  simp only [realSign_add] at hs
  dsimp only
  calc
    _ = (a h k l * a g (h * k) l * a g h k) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k)) := by ac_rfl
    _ = (a (g * h) k l * a g h (k * l)) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k) *
          realSign (v g h * v k l)) := by rw [ha]; ac_rfl
    _ = _ := by rw [hs]; ac_rfl

/-- Every field of the inverse data obeys the established twist laws. -/
theorem invLaws (s : Twist) :
    let d := twistInvData s
    RMod.Classification.TwistLaws ⟨d.group, d.rho, d.nu, d.omega⟩ := by
  dsimp only [twistInvData]
  let v := fun g h => s.nu g h + cross s.rho s.rho g h
  have hn : ∀ g h k, d₂ s.nu g h k = 0 := by
    simpa only [d₂, CharTwo.sub_eq_add] using s.cocycle
  have hv : ∀ g h k, d₂ v g h k = 0 := by
    intro g h k
    have h₁ := hn g h k
    have h₂ := cross_cocycle s.rho s.rho g h k
    dsimp [d₂, v] at *
    linear_combination h₁ + h₂
  let E := correction s.rho s.rho⁻¹ s.nu v
  have he : ∀ g h k l, E h k l + E g (h * k) l + E g h k + s.nu g h * s.nu k l =
      v g h * v k l + E (g * h) k l + E g h (k * l) := by
    intro g h k l
    have hc := correction_coboundary s.rho s.rho⁻¹ s.nu v hn hv g h k l
    have hz (a b : s.group) : sumNu s.rho s.rho⁻¹ s.nu v a b = 0 := by
      simp [sumNu, v, cross, ← add_assoc, CharTwo.add_self_eq_zero]
    rw [hz, hz, zero_mul, zero_add] at hc
    change E h k l - E (g * h) k l + E g (h * k) l - E g h (k * l) + E g h k = _ at hc
    simp only [CharTwo.sub_eq_add] at hc
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc
  have ho (g h k : s.group) :
      (twistInvData s).omega g h k = (s.omega g h k)⁻¹ * realSign (E g h k) := by
    dsimp [twistInvData, E, v]
    rw [inverse_correction]
  refine {
    nu_one_left := ?_, nu_one_right := ?_, omega_one₁ := ?_,
    omega_one₂ := ?_, omega_one₃ := ?_, cocycle := ?_, pentagon := ?_ }
  · intro g; simp [twistInvData, s.nu_one_left]
  · intro g; simp [twistInvData, s.nu_one_right]
  · intro g h; simp [twistInvData, cupOne, s.nu_one_left, s.omega_one₁, realSign]
  · intro g h; simp [twistInvData, cupOne, s.nu_one_left, s.nu_one_right, s.omega_one₂, realSign]
  · intro g h; simp [twistInvData, cupOne, s.nu_one_right, s.omega_one₃, realSign]
  · intro g h k
    simpa only [twistInvData, v, cross, d₂, CharTwo.sub_eq_add] using hv g h k
  · intro g h k l
    have ha : ∀ g h k l,
        (s.omega h k l)⁻¹ * (s.omega g (h * k) l)⁻¹ * (s.omega g h k)⁻¹ =
        realSign (s.nu g h * s.nu k l) * ((s.omega (g * h) k l)⁻¹ * (s.omega g h (k * l))⁻¹) := by
      intro a b c d
      simpa only [mul_inv_rev, realSign_inv, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun z : ℝˣ => z⁻¹) (s.pentagon a b c d)
    change (twistInvData s).omega h k l * (twistInvData s).omega g (h * k) l *
      (twistInvData s).omega g h k = realSign (v g h * v k l) *
        ((twistInvData s).omega (g * h) k l * (twistInvData s).omega g h (k * l))
    simpa only [ho] using
      rescale_pentagon s.nu v (fun a b c => (s.omega a b c)⁻¹) E ha he g h k l
end Stacking

def twistInv {G : FiniteGrp.{0}} (s : TwistOn G) : TwistOn G :=
  let d := twistInvData s.val
  let h := Stacking.invLaws s.val
  ⟨⟨d, h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂,
    h.omega_one₃, h.cocycle, h.pentagon⟩, s.property⟩
theorem twistInv_data {G : FiniteGrp.{0}} (s : TwistOn G) :
    (twistInv s).val.toTwistData = twistInvData s.val := rfl

end RMod.BrundanEllis
