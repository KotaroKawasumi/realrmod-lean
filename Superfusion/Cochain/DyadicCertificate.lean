/-
Superfusion / Cochain / DyadicCertificate

The discrete certificate group `± 2^ℤ`, realized as `Multiplicative
(ZMod 2 × ℤ)`, together with its realization homomorphism into the units of
any commutative ring with invertible `2`.

This is the certificate group announced in `Superfusion.Conventions`: scalar
identities whose two sides are dyadic units can be decided here by kernel
computation and then pushed forward to `Kˣ` along `dyadicHom`, which carries
the distinguished sign to the distinguished sign.
-/
import Superfusion.Cochain.Basic

namespace Superfusion

/-- The group `± 2^ℤ` in discrete form: the first component is the sign bit,
the second the dyadic exponent. -/
abbrev DyadicUnit : Type := Multiplicative (ZMod 2 × ℤ)

instance : GroupSign DyadicUnit where
  sign := Multiplicative.ofAdd (1, 0)
  sign_mul_self := by decide

/-- Build a dyadic unit from a sign bit and an exponent. -/
def dyadic (s : ZMod 2) (e : ℤ) : DyadicUnit := Multiplicative.ofAdd (s, e)

section Realization

variable (K : Type*) [CommRing K] [Invertible (2 : K)]

/-- `2` as a unit of a commutative ring with invertible `2`. -/
def twoUnit : Kˣ := unitOfInvertible (2 : K)

/-- The realization homomorphism `± 2^ℤ → Kˣ`, sending the sign bit to
`(-1)^s` and the exponent to the corresponding power of `2`. -/
def dyadicHom : DyadicUnit →* Kˣ where
  toFun x :=
    (sgn (Multiplicative.toAdd x).1 : Kˣ) * twoUnit K ^ (Multiplicative.toAdd x).2
  map_one' := by
    show (sgn ((0 : ZMod 2 × ℤ)).1 : Kˣ) * twoUnit K ^ ((0 : ZMod 2 × ℤ)).2 = 1
    simp
  map_mul' x y := by
    show (sgn (Multiplicative.toAdd x + Multiplicative.toAdd y).1 : Kˣ) *
          twoUnit K ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).2 = _
    rw [Prod.fst_add, Prod.snd_add, sgn_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

@[simp] theorem dyadicHom_apply (x : DyadicUnit) :
    dyadicHom K x =
      (sgn (Multiplicative.toAdd x).1 : Kˣ) * twoUnit K ^ (Multiplicative.toAdd x).2 :=
  rfl

@[simp] theorem dyadicHom_dyadic (s : ZMod 2) (e : ℤ) :
    dyadicHom K (dyadic s e) = (sgn s : Kˣ) * twoUnit K ^ e := rfl

/-- The realization homomorphism is sign-compatible: it carries the
distinguished sign of the certificate group to the distinguished sign of
`Kˣ`. -/
@[simp] theorem dyadicHom_sign : dyadicHom K (sign : DyadicUnit) = sign := by
  show (sgn ((((1 : ZMod 2), (0 : ℤ)) : ZMod 2 × ℤ)).1 : Kˣ) *
      twoUnit K ^ ((((1 : ZMod 2), (0 : ℤ)) : ZMod 2 × ℤ)).2 = _
  simp

end Realization

end Superfusion
