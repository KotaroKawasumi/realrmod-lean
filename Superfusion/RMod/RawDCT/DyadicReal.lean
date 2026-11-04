import Superfusion.Cochain.DyadicCertificate

/-!
# Computable real realization of dyadic units

Dyadic certificate values are evaluated in `ℚ` first.  Their real units are
then obtained only by casting the rational value and the rational value of
the inverse certificate.  Thus the data stored in `ℝˣ` contain an explicit
inverse and never invoke inversion on real numbers.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Rational evaluation

The sign and the integral power of two are both computed in `ℚ`.  The group
law of `DyadicUnit` becomes ordinary multiplication of these rational
values.
-/

/-- Rational value of a dyadic certificate `(-1)^s 2^e`. -/
def dyadicRatValue (x : DyadicUnit) : ℚ :=
  ((sgn (Multiplicative.toAdd x).1 : ℚˣ) : ℚ) *
    (2 : ℚ) ^ (Multiplicative.toAdd x).2

@[simp]
theorem dyadicRatValue_dyadic (s : ZMod 2) (e : ℤ) :
    dyadicRatValue (dyadic s e) =
      ((sgn s : ℚˣ) : ℚ) * (2 : ℚ) ^ e :=
  rfl

@[simp]
theorem dyadicRatValue_one : dyadicRatValue 1 = 1 := by
  simp [dyadicRatValue]

/-- Rational evaluation respects multiplication of dyadic certificates. -/
theorem dyadicRatValue_mul (x y : DyadicUnit) :
    dyadicRatValue (x * y) = dyadicRatValue x * dyadicRatValue y := by
  unfold dyadicRatValue
  rw [toAdd_mul, Prod.fst_add, Prod.snd_add,
    sgn_add, Units.val_mul, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring

@[simp]
theorem dyadicRatValue_sign :
    dyadicRatValue (sign : DyadicUnit) = -1 := by
  show
    ((sgn ((((1 : ZMod 2), (0 : ℤ)) : ZMod 2 × ℤ)).1 : ℚˣ) : ℚ) *
      (2 : ℚ) ^ ((((1 : ZMod 2), (0 : ℤ)) : ZMod 2 × ℤ)).2 = -1
  simp

/-- The rational value and the value of the inverse certificate multiply to
one.  This is the inverse equation later stored in the real unit. -/
theorem dyadicRatValue_mul_inv (x : DyadicUnit) :
    dyadicRatValue x * dyadicRatValue x⁻¹ = 1 := by
  calc
    dyadicRatValue x * dyadicRatValue x⁻¹ =
        dyadicRatValue (x * x⁻¹) := (dyadicRatValue_mul x x⁻¹).symm
    _ = 1 := by rw [mul_inv_cancel, dyadicRatValue_one]

/-- The inverse certificate also gives the left inverse in `ℚ`. -/
theorem dyadicRatValue_inv_mul (x : DyadicUnit) :
    dyadicRatValue x⁻¹ * dyadicRatValue x = 1 := by
  calc
    dyadicRatValue x⁻¹ * dyadicRatValue x =
        dyadicRatValue (x⁻¹ * x) := (dyadicRatValue_mul x⁻¹ x).symm
    _ = 1 := by rw [inv_mul_cancel, dyadicRatValue_one]

@[simp]
theorem dyadicRatValue_inv (x : DyadicUnit) :
    dyadicRatValue x⁻¹ = (dyadicRatValue x)⁻¹ :=
  eq_inv_of_mul_eq_one_right (dyadicRatValue_mul_inv x)

/-! ## Real units with stored rational inverses

Both fields below are casts from `ℚ`: the value uses `x`, while the inverse
field uses `x⁻¹`.  The two unit equations are transported from the rational
identities above.
-/

/-- Computable real unit represented by a dyadic certificate. -/
def dyadicRealUnit (x : DyadicUnit) : ℝˣ where
  val := (dyadicRatValue x : ℝ)
  inv := (dyadicRatValue x⁻¹ : ℝ)
  val_inv := by
    calc
      (dyadicRatValue x : ℝ) * (dyadicRatValue x⁻¹ : ℝ) =
          ((dyadicRatValue x * dyadicRatValue x⁻¹ : ℚ) : ℝ) :=
        (Rat.cast_mul _ _).symm
      _ = 1 := by rw [dyadicRatValue_mul_inv, Rat.cast_one]
  inv_val := by
    calc
      (dyadicRatValue x⁻¹ : ℝ) * (dyadicRatValue x : ℝ) =
          ((dyadicRatValue x⁻¹ * dyadicRatValue x : ℚ) : ℝ) :=
        (Rat.cast_mul _ _).symm
      _ = 1 := by rw [dyadicRatValue_inv_mul, Rat.cast_one]

/-- Coercing the stored real unit exposes the cast of its rational value. -/
@[simp]
theorem dyadicRealUnit_val (x : DyadicUnit) :
    ((dyadicRealUnit x : ℝˣ) : ℝ) = (dyadicRatValue x : ℝ) :=
  rfl

/-- The value of the inverse real unit is the cast of the independently
evaluated inverse certificate. -/
@[simp]
theorem dyadicRealUnit_inv_val (x : DyadicUnit) :
    (((dyadicRealUnit x)⁻¹ : ℝˣ) : ℝ) =
      (dyadicRatValue x⁻¹ : ℝ) :=
  rfl

@[simp]
theorem dyadicRealUnit_one : dyadicRealUnit 1 = 1 := by
  apply Units.ext
  simp

/-- The explicit real units multiply according to their dyadic
certificates. -/
theorem dyadicRealUnit_mul (x y : DyadicUnit) :
    dyadicRealUnit (x * y) = dyadicRealUnit x * dyadicRealUnit y := by
  apply Units.ext
  change (dyadicRatValue (x * y) : ℝ) =
    (dyadicRatValue x : ℝ) * (dyadicRatValue y : ℝ)
  rw [dyadicRatValue_mul, Rat.cast_mul]

@[simp]
theorem dyadicRealUnit_inv (x : DyadicUnit) :
    dyadicRealUnit x⁻¹ = (dyadicRealUnit x)⁻¹ := by
  apply Units.ext
  rfl

@[simp]
theorem dyadicRealUnit_sign :
    dyadicRealUnit (sign : DyadicUnit) = (sign : ℝˣ) := by
  apply Units.ext
  simp

/-! ## Computable multiplicative realization

The monoid homomorphism only packages the explicit unit-valued function and
the rational multiplication theorem.  No additional realization mechanism
is used.
-/

/-- Computable realization of dyadic certificates as real units. -/
def dyadicRealHom : DyadicUnit →* ℝˣ where
  toFun := dyadicRealUnit
  map_one' := dyadicRealUnit_one
  map_mul' := dyadicRealUnit_mul

@[simp]
theorem dyadicRealHom_apply (x : DyadicUnit) :
    dyadicRealHom x = dyadicRealUnit x :=
  rfl

@[simp]
theorem dyadicRealHom_val (x : DyadicUnit) :
    ((dyadicRealHom x : ℝˣ) : ℝ) = (dyadicRatValue x : ℝ) :=
  rfl

@[simp]
theorem dyadicRealHom_one : dyadicRealHom 1 = 1 :=
  dyadicRealUnit_one

theorem dyadicRealHom_mul (x y : DyadicUnit) :
    dyadicRealHom (x * y) = dyadicRealHom x * dyadicRealHom y :=
  dyadicRealUnit_mul x y

@[simp]
theorem dyadicRealHom_inv (x : DyadicUnit) :
    dyadicRealHom x⁻¹ = (dyadicRealHom x)⁻¹ :=
  dyadicRealUnit_inv x

@[simp]
theorem dyadicRealHom_sign :
    dyadicRealHom (sign : DyadicUnit) = (sign : ℝˣ) :=
  dyadicRealUnit_sign

/-! ## Nontrivial closed evaluations -/

example :
    ((dyadicRealHom (dyadic 0 3) : ℝˣ) : ℝ) = 8 := by
  change ((dyadicRatValue (dyadic 0 3) : ℚ) : ℝ) = 8
  rw [dyadicRatValue_dyadic]
  norm_num

example :
    ((dyadicRealHom (dyadic 1 (-2)) : ℝˣ) : ℝ) = -(1 / 4) := by
  change ((dyadicRatValue (dyadic 1 (-2)) : ℚ) : ℝ) = -(1 / 4)
  rw [dyadicRatValue_dyadic]
  norm_num

end Superfusion.RMod.RawDCT

/-! ### Kernel dependency audit -/

#print axioms Superfusion.RMod.RawDCT.dyadicRatValue_mul
#print axioms Superfusion.RMod.RawDCT.dyadicRealUnit
#print axioms Superfusion.RMod.RawDCT.dyadicRealUnit_inv
#print axioms Superfusion.RMod.RawDCT.dyadicRealHom
#print axioms Superfusion.RMod.RawDCT.dyadicRealHom_sign
