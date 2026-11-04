import RMod.BrundanEllis.StackingGaugeCalculus

/-! Explicit binary gauges for associativity, interchange and gauge compatibility
of the stacking product. These cochain identities precede the quotient construction. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion
variable {G : FiniteGrp.{0}}

/-- The binary carry is symmetric. -/
theorem bwCarry_comm (a b : Multiplicative (ZMod 8)) : bwCarry a b = bwCarry b a := by
  simp [bwCarry, add_comm]

/-- Compatibility of the carry with addition of two degree homomorphisms. -/
theorem bwCarry_mul_mul (a b c d : Multiplicative (ZMod 8)) :
    bwCarry (a * c) (b * d) = bwCarry a b + bwCarry c d +
      bwCarry a c + bwCarry b d + bwCarry (a * b) (c * d) := by
  have h₁ := bwCarry_cocycle a c (b * d)
  have h₂ := bwCarry_cocycle c b d
  have h₃ := bwCarry_cocycle a b (c * d)
  have h₄ := bwCarry_cocycle b c d
  rw [mul_comm c b, bwCarry_comm c b] at h₂
  rw [mul_left_comm c b d] at h₁
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h₁ + h₂ + h₃ + h₄

/-- Scalar gauge relating the two parenthesizations of the degree correction. -/
def typeAssociator (r t u : G →* Multiplicative (ZMod 8)) (g h : G) : ZMod 2 :=
  (bwPrimitive (r g) + bwBit (r g) * bwBit (t g)) * bwBit (t h) * bwBit (u h)

/-- Parity gauge interchanging two degree corrections. -/
def typeSwapParity (r t : G →* Multiplicative (ZMod 8)) (g : G) : ZMod 2 :=
  bwBit (r g) * bwBit (t g)

/-- Scalar gauge accompanying the interchange parity. -/
def typeSwapScalar (r t : G →* Multiplicative (ZMod 8)) (g h : G) : ZMod 2 :=
  bwPrimitive (t g) * bwPrimitive (r h) +
    (bwPrimitive (r g) + bwPrimitive (r h)) * bwBit (t g) * bwBit (t h)

theorem typeSwapParity_data (r t : G →* Multiplicative (ZMod 8)) :
    parityMove (cross r t) (typeSwapParity r t) = cross t r := by
  funext g h
  simp only [parityMove, cross, typeSwapParity, map_mul, bwBit_mul]
  ring_nf
  simp [CharTwo.two_eq_zero] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem typeAssociator_data (r t u : G →* Multiplicative (ZMod 8)) (g h k : G) :
    typeCorrection r t g h k + typeCorrection (r * t) u g h k +
      cupOne (cross (r * t) u) (cross r t) g h k +
      typeCorrection t u g h k + typeCorrection r (t * u) g h k +
      cupOne (cross r (t * u)) (cross t u) g h k =
        d₂ (typeAssociator r t u) g h k := by
  simp only [typeCorrection, typeAssociator, cross, cupOne, d₂, CharTwo.sub_eq_add,
    MonoidHom.mul_apply, map_mul, bwBit_mul, bwPrimitive_mul]
  ring_nf
  simp [CharTwo.two_eq_zero] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem typeSwapScalar_data (r t : G →* Multiplicative (ZMod 8)) (g h k : G) :
    typeCorrection r t g h k + typeCorrection t r g h k +
      parityFactor (cross r t) (typeSwapParity r t) g h k =
        d₂ (typeSwapScalar r t) g h k := by
  simp only [parityFactor, typeSwapParity_data, typeCorrection, typeSwapScalar, cross,
    typeSwapParity, d₂, CharTwo.sub_eq_add, map_mul, bwBit_mul, bwPrimitive_mul]
  ring_nf
  simp [CharTwo.two_eq_zero] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

def scalarProduct (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ)
    (g h k : G) : ℝˣ := a g h k * b g h k * realSign (cupOne w v g h k)

theorem cocycle_middle (v : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (g h k : G) : v (g * h) k = v h k + v g (h * k) + v g h := by
  have h := hv g h k
  simp only [d₂, CharTwo.sub_eq_add] at h
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h

theorem parityFactor_product_left (v w : G → G → ZMod 2) (l : G → ZMod 2)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    parityFactor v l g h k + cupOne w (parityMove v l) g h k =
      cupOne w v g h k + parityFactor (fun a b => v a b + w a b) l g h k +
        d₂ (fun a b => w a b * (l a + l b)) g h k := by
  simp only [parityFactor, parityMove, cupOne, d₂, CharTwo.sub_eq_add,
    cocycle_middle w hw g h k]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem parityFactor_product_right (v w : G → G → ZMod 2) (l : G → ZMod 2)
    (hv : ∀ g h k, d₂ v g h k = 0) (g h k : G) :
    parityFactor w l g h k + cupOne (parityMove w l) v g h k =
      cupOne w v g h k + parityFactor (fun a b => v a b + w a b) l g h k +
        d₂ (fun a b => v a b * l (a * b)) g h k := by
  simp only [parityFactor, parityMove, cupOne, d₂, CharTwo.sub_eq_add,
    cocycle_middle v hv g h k, mul_assoc]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem scalarMove_ratio (v : G → G → ZMod 2) (a : G → G → G → ℝˣ)
    (l : G → ZMod 2) (b : G → G → ℝˣ) (g h k : G) :
    scalarMove v a l b g h k =
      a g h k * scalarRatio b g h k * realSign (parityFactor v l g h k) := by
  dsimp [scalarMove, scalarRatio]
  ac_rfl

theorem scalarProduct_gauge_left (v w : G → G → ZMod 2)
    (a b : G → G → G → ℝˣ) (l : G → ZMod 2) (c : G → G → ℝˣ)
    (hw : ∀ g h k, d₂ w g h k = 0) :
    scalarProduct (parityMove v l) w (scalarMove v a l c) b =
      scalarMove (fun g h => v g h + w g h) (scalarProduct v w a b) l
        (fun g h => c g h * realSign (w g h * (l g + l h))) := by
  funext g h k
  have hs := congrArg realSign (parityFactor_product_left v w l hw g h k)
  simp only [realSign_add] at hs
  simp only [scalarProduct, scalarMove_ratio, scalarRatio_mul, scalarRatio_sign]
  calc
    _ = a g h k * b g h k * scalarRatio c g h k *
        (realSign (parityFactor v l g h k) * realSign (cupOne w (parityMove v l) g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

theorem scalarProduct_gauge_right (v w : G → G → ZMod 2)
    (a b : G → G → G → ℝˣ) (l : G → ZMod 2) (c : G → G → ℝˣ)
    (hv : ∀ g h k, d₂ v g h k = 0) :
    scalarProduct v (parityMove w l) a (scalarMove w b l c) =
      scalarMove (fun g h => v g h + w g h) (scalarProduct v w a b) l
        (fun g h => c g h * realSign (v g h * l (g * h))) := by
  funext g h k
  have hs := congrArg realSign (parityFactor_product_right v w l hv g h k)
  simp only [realSign_add] at hs
  simp only [scalarProduct, scalarMove_ratio, scalarRatio_mul, scalarRatio_sign]
  calc
    _ = a g h k * b g h k * scalarRatio c g h k *
        (realSign (parityFactor w l g h k) * realSign (cupOne (parityMove w l) v g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl


/-- Scalar correction for changing the first input by a parity gauge. -/
def gaugeLeftCorrection (r t : G →* Multiplicative (ZMod 8))
    (w : G → G → ZMod 2) (l : G → ZMod 2) (g h : G) : ZMod 2 :=
  (w g h + cross r t g h) * (l g + l h)

/-- Scalar correction for changing the second input by a parity gauge. -/
def gaugeRightCorrection (r t : G →* Multiplicative (ZMod 8))
    (v : G → G → ZMod 2) (l : G → ZMod 2) (g h : G) : ZMod 2 :=
  v g h * l (g * h) + cross r t g h * (l g + l h)

/-- Scalar gauge from (s t) u to s (t u). -/
def associatorCorrection (r t u : G →* Multiplicative (ZMod 8))
    (z : G → G → ZMod 2) (g h : G) : ZMod 2 :=
  cross r t g h * z g h + typeAssociator r t u g h

/-- Scalar gauge from s t to t s; its parity is typeSwapParity. -/
def swapCorrection (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (g h : G) : ZMod 2 :=
  v g h * w g h + typeSwapScalar r t g h +
    (v g h + w g h) * typeSwapParity r t (g * h)

theorem correction_gauge_left (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (l : G → ZMod 2)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    parityFactor v l g h k + correction r t (parityMove v l) w g h k =
      correction r t v w g h k + parityFactor (sumNu r t v w) l g h k +
        d₂ (gaugeLeftCorrection r t w l) g h k := by
  have h₁ := parityFactor_product_left v w l hw g h k
  have h₂ := parityFactor_product_left (fun a b => v a b + w a b) (cross r t) l
    (cross_cocycle r t) g h k
  simp only [correction, sumNu, gaugeLeftCorrection, parityFactor, parityMove,
    cupOne, d₂, CharTwo.sub_eq_add] at h₁ h₂ ⊢
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h₁ + h₂

theorem correction_gauge_right (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (l : G → ZMod 2)
    (hv : ∀ g h k, d₂ v g h k = 0) (g h k : G) :
    parityFactor w l g h k + correction r t v (parityMove w l) g h k =
      correction r t v w g h k + parityFactor (sumNu r t v w) l g h k +
        d₂ (gaugeRightCorrection r t v l) g h k := by
  have h₁ := parityFactor_product_right v w l hv g h k
  have h₂ := parityFactor_product_left (fun a b => v a b + w a b) (cross r t) l
    (cross_cocycle r t) g h k
  simp only [correction, sumNu, gaugeRightCorrection, parityFactor, parityMove,
    cupOne, d₂, CharTwo.sub_eq_add] at h₁ h₂ ⊢
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h₁ + h₂

theorem correction_assoc (r t u : G →* Multiplicative (ZMod 8))
    (v w z : G → G → ZMod 2) (hz : ∀ g h k, d₂ z g h k = 0) (g h k : G) :
    correction r t v w g h k + correction (r * t) u (sumNu r t v w) z g h k +
      correction t u w z g h k + correction r (t * u) v (sumNu t u w z) g h k =
        d₂ (associatorCorrection r t u z) g h k := by
  have h₁ := typeAssociator_data r t u g h k
  have h₂ := d₂_cupTwo₂₂ (cross_cocycle r t) hz g h k
  simp only [correction, sumNu, associatorCorrection, cupOne, cupOne₂₂, cupTwo₂₂,
    d₂, cross, MonoidHom.mul_apply, map_mul, bwBit_mul, CharTwo.sub_eq_add] at h₁ h₂ ⊢
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h₁ + h₂

theorem correction_swap (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (hv : ∀ g h k, d₂ v g h k = 0)
    (hw : ∀ g h k, d₂ w g h k = 0) (g h k : G) :
    correction r t v w g h k + correction t r w v g h k +
      parityFactor (sumNu r t v w) (typeSwapParity r t) g h k =
        d₂ (swapCorrection r t v w) g h k := by
  have hsum : ∀ g h k, d₂ (fun a b => v a b + w a b) g h k = 0 := by
    intro g h k
    rw [d₂_add, hv, hw, add_zero]
  have h₁ := typeSwapScalar_data r t g h k
  have h₂ := d₂_cupTwo₂₂ hv hw g h k
  have h₃ := parityFactor_product_right (fun a b => v a b + w a b) (cross r t)
    (typeSwapParity r t) hsum g h k
  rw [typeSwapParity_data] at h₃
  simp only [correction, sumNu, swapCorrection, cupOne, cupOne₂₂, cupTwo₂₂,
    d₂, parityFactor, parityMove, CharTwo.sub_eq_add] at h₁ h₂ h₃ ⊢
  linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h₁ + h₂ + h₃



/-- The scalar cochain in the specified stacking product. -/
def stackOmega (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ) (g h k : G) : ℝˣ :=
  a g h k * b g h k * realSign (correction r t v w g h k)

theorem stackOmega_gauge_left (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ)
    (l : G → ZMod 2) (c : G → G → ℝˣ) (hw : ∀ g h k, d₂ w g h k = 0) :
    stackOmega r t (parityMove v l) w (scalarMove v a l c) b =
      scalarMove (sumNu r t v w) (stackOmega r t v w a b) l
        (fun g h => c g h * realSign (gaugeLeftCorrection r t w l g h)) := by
  funext g h k
  have hs := congrArg realSign (correction_gauge_left r t v w l hw g h k)
  simp only [realSign_add] at hs
  simp only [stackOmega, scalarMove_ratio, scalarRatio_mul, scalarRatio_sign]
  calc
    _ = a g h k * b g h k * scalarRatio c g h k *
        (realSign (parityFactor v l g h k) * realSign (correction r t (parityMove v l) w g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

theorem stackOmega_gauge_right (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ)
    (l : G → ZMod 2) (c : G → G → ℝˣ) (hv : ∀ g h k, d₂ v g h k = 0) :
    stackOmega r t v (parityMove w l) a (scalarMove w b l c) =
      scalarMove (sumNu r t v w) (stackOmega r t v w a b) l
        (fun g h => c g h * realSign (gaugeRightCorrection r t v l g h)) := by
  funext g h k
  have hs := congrArg realSign (correction_gauge_right r t v w l hv g h k)
  simp only [realSign_add] at hs
  simp only [stackOmega, scalarMove_ratio, scalarRatio_mul, scalarRatio_sign]
  calc
    _ = a g h k * b g h k * scalarRatio c g h k *
        (realSign (parityFactor w l g h k) * realSign (correction r t v (parityMove w l) g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

theorem stackOmega_assoc (r t u : G →* Multiplicative (ZMod 8))
    (v w z : G → G → ZMod 2) (a b c : G → G → G → ℝˣ)
    (hz : ∀ g h k, d₂ z g h k = 0) :
    scalarMove (sumNu (r * t) u (sumNu r t v w) z)
      (stackOmega (r * t) u (sumNu r t v w) z (stackOmega r t v w a b) c)
      (fun _ => 0) (fun g h => realSign (associatorCorrection r t u z g h)) =
        stackOmega r (t * u) v (sumNu t u w z) a (stackOmega t u w z b c) := by
  funext g h k
  have hc := correction_assoc r t u v w z hz g h k
  have he : correction r t v w g h k + correction (r * t) u (sumNu r t v w) z g h k +
      d₂ (associatorCorrection r t u z) g h k =
        correction t u w z g h k + correction r (t * u) v (sumNu t u w z) g h k := by
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) hc
  have hs := congrArg realSign he
  simp only [realSign_add] at hs
  simp only [scalarMove_ratio, stackOmega, scalarRatio_sign, parityFactor, mul_zero,
    zero_mul, add_zero, realSign_zero, mul_one]
  calc
    _ = a g h k * b g h k * c g h k *
        (realSign (correction r t v w g h k) *
          realSign (correction (r * t) u (sumNu r t v w) z g h k) *
          realSign (d₂ (associatorCorrection r t u z) g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

theorem stackOmega_swap (r t : G →* Multiplicative (ZMod 8))
    (v w : G → G → ZMod 2) (a b : G → G → G → ℝˣ)
    (hv : ∀ g h k, d₂ v g h k = 0) (hw : ∀ g h k, d₂ w g h k = 0) :
    scalarMove (sumNu r t v w) (stackOmega r t v w a b) (typeSwapParity r t)
      (fun g h => realSign (swapCorrection r t v w g h)) = stackOmega t r w v b a := by
  funext g h k
  have hc := correction_swap r t v w hv hw g h k
  have he : correction r t v w g h k + d₂ (swapCorrection r t v w) g h k +
      parityFactor (sumNu r t v w) (typeSwapParity r t) g h k = correction t r w v g h k := by
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) hc
  have hs := congrArg realSign he
  simp only [realSign_add] at hs
  simp only [scalarMove_ratio, stackOmega, scalarRatio_sign]
  calc
    _ = a g h k * b g h k * (realSign (correction r t v w g h k) *
        realSign (d₂ (swapCorrection r t v w) g h k) *
        realSign (parityFactor (sumNu r t v w) (typeSwapParity r t) g h k)) := by ac_rfl
    _ = _ := by rw [hs]; ac_rfl

end RMod.BrundanEllis.Stacking
