import RMod.BrundanEllis.StackingCocycle

/-! The two placements of the quadratic primitive differ by an explicit
binary coboundary. This permits a reference comparison constructed in one
crossing orientation to be related to the specified cochain formula. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- Move the quadratic primitive between the first and last tensor factors. -/
theorem primitive_crossing_coboundary (r t : G →* Multiplicative (ZMod 8)) (g h k : G) :
    bwPrimitive (r g) * bwBit (t h) * bwBit (t k) +
      bwBit (r g) * bwBit (r h) * bwPrimitive (t k) =
        d₂ (fun a b => bwPrimitive (r a) * bwPrimitive (t b)) g h k := by
  simp only [d₂, CharTwo.sub_eq_add, map_mul, bwPrimitive_mul]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The quartic super-interchange term is unchanged by this scalar gauge. -/
theorem typeCorrection_other_primitive (r t : G →* Multiplicative (ZMod 8)) (g h k : G) :
    typeCorrection r t g h k +
      (bwBit (r g) * bwBit (r h) * bwPrimitive (t k) +
        bwBit (r g) * (bwBit (r h) * bwBit (t h)) * bwBit (t k)) =
      d₂ (fun a b => bwPrimitive (r a) * bwPrimitive (t b)) g h k := by
  rw [← primitive_crossing_coboundary]
  simp only [typeCorrection, cross]
  ring_nf
  simp [CharTwo.two_eq_zero]

end RMod.BrundanEllis.Stacking
