import RMod.Classification.Proofs.GaugeAssociativityScalars

/-!
# Converting the raw triple ratio sign to the gauge sign

The binary comparison contributes one sign at each of the four vertices.
Their sum equals the sign of the two outer-first deletion routes.
The component naturality crossings then give the prescribed gauge
exponent. The proof is polynomial algebra in Z/2, using the actual
binary parity equations and the source cocycle.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem gaugeComparisonRatio_sign (a b c d e f n m r s n' m' r' s' : ZMod 2)
    (hs : n + m = r + s)
    (h₁ : (a + b) + n' = n + d) (h₂ : (d + c) + m' = m + f)
    (h₃ : (b + c) + r' = r + e) (h₄ : (a + e) + s' = s + f) :
    (a * b + (a + b) * n' + d * n) + (d * c + (d + c) * m' + f * m) +
      (b * c + (b + c) * r' + e * r) + (a * e + (a + e) * s' + f * s) =
        n * m + r * s + n' * m' + r' * s' := by
  have cancel (x y z : ZMod 2) (h : x + y = z) : y = x + z := by
    rw [← h, CharTwo.add_cancel_left]
  rw [cancel _ _ _ h₁, cancel _ _ _ h₂, cancel _ _ _ h₃, cancel _ _ _ h₄,
    cancel _ _ _ hs.symm]
  have h3 : (3 : ZMod 2) = 1 := by
    change (2 : ZMod 2) + 1 = 1
    simp only [show (2 : ZMod 2) = 0 from CharTwo.two_eq_zero, zero_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, h3, mul_zero, mul_one, add_zero]

end RMod.Classification
