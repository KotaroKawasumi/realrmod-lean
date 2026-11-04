import RMod.BrundanEllis.Gauge

/-! Fixed stacking cochains and the label-preserving gauge relation.
These declarations are shared with Challenge, using its declaration-surface exception. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis

/-! A fixed group is a subtype of the existing Twist, not another twist structure.
The equality witnesses only transport indices; gauges must additionally have identity group map. -/
abbrev TwistOn (G : FiniteGrp.{0}) := {s : Twist // s.group = G}
abbrev GaugeEquivalentOn {G : FiniteGrp.{0}} (s t : TwistOn G) : Prop :=
  ∃ d : Gauge s.val.toTwistData, ∃ hd : d.targetGroup = s.val.group,
    (hd ▸ d.phi) = MulEquiv.refl s.val.group ∧
    (gaugeTransform s.val d).toTwistData = t.val.toTwistData

/-! Closed cochains of u. Multiplication in Multiplicative (ZMod 8) means addition mod 8. -/
def bwBit (a : Multiplicative (ZMod 8)) : ZMod 2 := (a.toAdd.val : ZMod 2)
def bwCarry (a b : Multiplicative (ZMod 8)) : ZMod 2 := if 8 ≤ a.toAdd.val + b.toAdd.val then 1 else 0
def bwPrimitive (a : Multiplicative (ZMod 8)) : ZMod 2 := ((a.toAdd.val * (a.toAdd.val + 1) / 2 : ℕ) : ZMod 2)
def cupOne {G : FiniteGrp.{0}} (v z : G → G → ZMod 2) (g h k : G) : ZMod 2 :=
  v (g * h) k * z g h + v g (h * k) * z h k

def twistMulData (s t : Twist) (hG : s.group = t.group) : TwistData :=
  let tRho : s.group →* Multiplicative (ZMod 8) := hG.symm ▸ t.rho
  let tNu : s.group → s.group → ZMod 2 := hG.symm ▸ t.nu
  let tOmega : s.group → s.group → s.group → ℝˣ := hG.symm ▸ t.omega
  let x := fun g => bwBit (s.rho g)
  let y := fun g => bwBit (tRho g)
  let c := fun g h => x g * y h
  { group := s.group
    rho := s.rho * tRho
    nu g h := s.nu g h + tNu g h + c g h
    omega g h k := s.omega g h k * tOmega g h k * realSign
      (cupOne tNu s.nu g h k + cupOne c (fun a b => s.nu a b + tNu a b) g h k +
       bwPrimitive (s.rho g) * y h * y k + x g * (x h * y h) * y k) }

/-- With these cochains, the displayed product of s with its inverse is the neutral twist. -/
def twistInvData (s : Twist) : TwistData :=
  let x := fun g => bwBit (s.rho g)
  let v := fun g h => s.nu g h + x g * x h
  { group := s.group
    rho := s.rho⁻¹
    nu := v
    omega g h k := (s.omega g h k)⁻¹ * realSign
      (cupOne v s.nu g h k + (bwPrimitive (s.rho g) + x g) * x h * x k) }

end RMod.BrundanEllis
