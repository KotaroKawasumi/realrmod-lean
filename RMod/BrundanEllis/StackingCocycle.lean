import RMod.BrundanEllis.StackingArithmetic

/-! The prescribed product preserves the binary cocycle and signed pentagon.
The cup-one identities are reused from the existing cochain library. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The parity cross-term in the binary cochain of the product. -/
def cross (r t : G →* Multiplicative (ZMod 8)) (g h : G) : ZMod 2 :=
  bwBit (r g) * bwBit (t h)

def sumNu (r t : G →* Multiplicative (ZMod 8)) (v w : G → G → ZMod 2)
    (g h : G) : ZMod 2 := v g h + w g h + cross r t g h

/-- The part of the scalar correction depending only on Brauer--Wall degrees. -/
def typeCorrection (r t : G →* Multiplicative (ZMod 8)) (g h k : G) : ZMod 2 :=
  bwPrimitive (r g) * bwBit (t h) * bwBit (t k) +
  bwBit (r g) * (bwBit (r h) * bwBit (t h)) * bwBit (t k)

def correction (r t : G →* Multiplicative (ZMod 8)) (v w : G → G → ZMod 2)
    (g h k : G) : ZMod 2 :=
  cupOne w v g h k + cupOne (cross r t) (fun a b => v a b + w a b) g h k +
    typeCorrection r t g h k

/-- Parity homomorphisms give a normalized binary cocycle by the cup product. -/
theorem cross_cocycle (r t : G →* Multiplicative (ZMod 8)) (g h k : G) :
    d₂ (cross r t) g h k = 0 := by
  simp only [d₂, cross, map_mul, bwBit_mul, CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem sumNu_cocycle (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    d₂ (sumNu r t v w) g h k = 0 := by
  have hc := cross_cocycle r t g h k
  dsimp [sumNu, d₂] at *
  linear_combination hv g h k + hw g h k + hc

/-- The primitive accounts for the square of the parity cross-term. -/
theorem typeCorrection_coboundary (r t : G →* Multiplicative (ZMod 8)) (g h k l : G) :
    d₃ (typeCorrection r t) g h k l = cross r t g h * cross r t k l := by
  simp only [d₃, typeCorrection, cross, map_mul, bwBit_mul, bwPrimitive_mul,
    CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The correction has exactly the coboundary required by the signed pentagon. -/
theorem correction_coboundary (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k l : G) :
    d₃ (correction r t v w) g h k l =
      sumNu r t v w g h * sumNu r t v w k l + v g h * v k l + w g h * w k l := by
  have hsum : ∀ g h k, d₂ (fun a b => v a b + w a b) g h k = 0 := by
    intro a b c
    have hv0 := hv a b c
    have hw0 := hw a b c
    dsimp [d₂] at hv0 hw0 ⊢
    linear_combination hv0 + hw0
  have h₁ := cup₂₂_add_swap_eq_d₃ hw hv g h k l
  have h₂ := cup₂₂_add_swap_eq_d₃ (cross_cocycle r t) hsum g h k l
  have h₃ := typeCorrection_coboundary r t g h k l
  change _ = d₃ (cupOne w v) g h k l at h₁
  change _ = d₃ (cupOne (cross r t) (fun a b => v a b + w a b)) g h k l at h₂
  simp only [d₃, correction, sumNu, cup₂₂, CharTwo.sub_eq_add] at h₁ h₂ h₃ ⊢
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -h₁ - h₂ + h₃


/-- Multiplying scalar cochains with this correction preserves the signed pentagon. -/
theorem mulOmega_pentagon (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (a b : G → G → G → ℝˣ)
    (ha : ∀ g h k l, a h k l * a g (h * k) l * a g h k =
      realSign (v g h * v k l) * (a (g * h) k l * a g h (k * l)))
    (hb : ∀ g h k l, b h k l * b g (h * k) l * b g h k =
      realSign (w g h * w k l) * (b (g * h) k l * b g h (k * l)))
    (g h k l : G) :
    let o := fun x y z => a x y z * b x y z * realSign (correction r t v w x y z)
    o h k l * o g (h * k) l * o g h k =
      realSign (sumNu r t v w g h * sumNu r t v w k l) *
        (o (g * h) k l * o g h (k * l)) := by
  let E := correction r t v w
  have hc := correction_coboundary r t v w hv hw g h k l
  change E h k l - E (g * h) k l + E g (h * k) l - E g h (k * l) + E g h k = _ at hc
  simp only [CharTwo.sub_eq_add] at hc
  have he : E h k l + E g (h * k) l + E g h k + v g h * v k l + w g h * w k l =
      sumNu r t v w g h * sumNu r t v w k l + E (g * h) k l + E g h (k * l) := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc
  have hs := congrArg realSign he
  simp only [realSign_add] at hs
  dsimp only
  calc
    _ = (a h k l * a g (h * k) l * a g h k) *
        (b h k l * b g (h * k) l * b g h k) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k)) := by
          dsimp [E]; ac_rfl
    _ = (a (g * h) k l * a g h (k * l)) * (b (g * h) k l * b g h (k * l)) *
        (realSign (E h k l) * realSign (E g (h * k) l) * realSign (E g h k) *
          realSign (v g h * v k l) * realSign (w g h * w k l)) := by
          rw [ha, hb]; ac_rfl
    _ = _ := by
      rw [hs]
      dsimp [E]
      ac_rfl

end RMod.BrundanEllis.Stacking
