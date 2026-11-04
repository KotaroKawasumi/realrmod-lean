import RMod.BrundanEllis.StackingCocycle

/-! Valid twists realizing the specified stacking operations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis

/-- The neutral cochains satisfy normalization, the cocycle equation and the pentagon. -/
def twistUnit (G : FiniteGrp.{0}) : TwistOn G :=
  ⟨{ group := G
     rho := 1
     nu := fun _ _ => 0
     omega := fun _ _ _ => 1
     nu_one_left := fun _ => rfl
     nu_one_right := fun _ => rfl
     omega_one₁ := fun _ _ => rfl
     omega_one₂ := fun _ _ => rfl
     omega_one₃ := fun _ _ => rfl
     cocycle := by intros; simp
     pentagon := by intros; simp [realSign] }, rfl⟩

theorem twistUnit_data (G : FiniteGrp.{0}) :
    (twistUnit G).val.toTwistData = ⟨G, 1, fun _ _ => 0, fun _ _ _ => 1⟩ := rfl


namespace Stacking
/-- The prescribed raw product satisfies all existing twist laws. -/
theorem mulLaws (s t : Twist) (hG : s.group = t.group) :
    let d := twistMulData s t hG
    RMod.Classification.TwistLaws ⟨d.group, d.rho, d.nu, d.omega⟩ := by
  rcases s with ⟨⟨S, r, v, a⟩, v1, v2, a1, a2, a3, hv, ha⟩
  rcases t with ⟨⟨T, q, w, b⟩, w1, w2, b1, b2, b3, hw, hb⟩
  change S = T at hG
  cases hG
  dsimp only [twistMulData]
  dsimp only at v1 v2 a1 a2 a3 hv ha w1 w2 b1 b2 b3 hw hb
  have hv' : ∀ g h k, Superfusion.d₂ v g h k = 0 := by
    simpa only [Superfusion.d₂, CharTwo.sub_eq_add] using hv
  have hw' : ∀ g h k, Superfusion.d₂ w g h k = 0 := by
    simpa only [Superfusion.d₂, CharTwo.sub_eq_add] using hw
  refine {
    nu_one_left := ?_, nu_one_right := ?_, omega_one₁ := ?_,
    omega_one₂ := ?_, omega_one₃ := ?_, cocycle := ?_, pentagon := ?_ }
  · intro g
    simp [twistMulData, v1, w1]
  · intro g
    simp [twistMulData, v2, w2]
  · intro g h
    simp [twistMulData, cupOne, v1, w1, a1, b1, realSign]
  · intro g h
    simp [twistMulData, cupOne, v1, v2, w1, w2, a2, b2, realSign]
  · intro g h
    simp [twistMulData, cupOne, v2, w2, a3, b3, realSign]
  · intro g h k
    simpa only [twistMulData, sumNu, cross, Superfusion.d₂, CharTwo.sub_eq_add] using
      sumNu_cocycle r q v w hv' hw' g h k
  · intro g h k l
    simpa only [twistMulData, sumNu, correction, typeCorrection, cupOne, cross, realSign, RMod.Classification.realSign, add_assoc] using
      mulOmega_pentagon r q v w hv' hw' a b ha hb g h k l
end Stacking

/-- Construct a valid twist with exactly the displayed data; closure is an output obligation. -/
def twistMul {G : FiniteGrp.{0}} (s t : TwistOn G) : TwistOn G :=
  let d := twistMulData s.val t.val (s.property.trans t.property.symm)
  let h := Stacking.mulLaws s.val t.val (s.property.trans t.property.symm)
  ⟨⟨d, h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂,
    h.omega_one₃, h.cocycle, h.pentagon⟩, s.property⟩
theorem twistMul_data {G : FiniteGrp.{0}} (s t : TwistOn G) :
    (twistMul s t).val.toTwistData =
      twistMulData s.val t.val (s.property.trans t.property.symm) := rfl

end RMod.BrundanEllis
