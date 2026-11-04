/-
Superfusion / Cochain / Basic

Normalized inhomogeneous group cochains with trivial coefficients, in the
low degrees used by the paper (§2.3), as curried computable functions.

Design (roadmap decision 1): we do NOT reuse mathlib's
`groupCohomology.inhomogeneousCochains` — it is noncomputable and carries no
cup products.  This project-local layer is computable and `decide`-friendly;
bridges to mathlib's `groupCohomology` will live in a separate file and only
at the level of cohomology classes.

Conventions: coboundaries follow the standard inhomogeneous formula with
trivial coefficients, e.g.
`(δf)(a,b) = f(b) - f(ab) + f(a)`,
`(δν)(a,b,c) = ν(b,c) - ν(ab,c) + ν(a,bc) - ν(a,b)`,
written additively (`d₁ … d₄`, for `ZMod 2`-valued parity cochains) and
multiplicatively (`dm₃`, `dm₄`, for `Kˣ`-valued scalar cochains).
-/
import Superfusion.Conventions

namespace Superfusion

variable {G : Type*} [Group G]

/-! ## Additive coboundaries (degrees 1–4) -/

section Additive

variable {A : Type*} [AddCommGroup A]

/-- Coboundary of a 1-cochain: `(d₁ f)(a,b) = f(b) - f(ab) + f(a)`. -/
def d₁ (f : G → A) : G → G → A :=
  fun a b => f b - f (a * b) + f a

/-- Coboundary of a 2-cochain:
`(d₂ ν)(a,b,c) = ν(b,c) - ν(ab,c) + ν(a,bc) - ν(a,b)`. -/
def d₂ (f : G → G → A) : G → G → G → A :=
  fun a b c => f b c - f (a * b) c + f a (b * c) - f a b

/-- Coboundary of a 3-cochain. -/
def d₃ (f : G → G → G → A) : G → G → G → G → A :=
  fun a b c d => f b c d - f (a * b) c d + f a (b * c) d - f a b (c * d) + f a b c

/-- Coboundary of a 4-cochain. -/
def d₄ (f : G → G → G → G → A) : G → G → G → G → G → A :=
  fun a b c d e =>
    f b c d e - f (a * b) c d e + f a (b * c) d e - f a b (c * d) e
      + f a b c (d * e) - f a b c d

theorem d₂_d₁ (f : G → A) (a b c : G) : d₂ (d₁ f) a b c = 0 := by
  simp only [d₁, d₂, mul_assoc]
  abel

theorem d₃_d₂ (f : G → G → A) (a b c d : G) : d₃ (d₂ f) a b c d = 0 := by
  simp only [d₂, d₃, mul_assoc]
  abel

theorem d₄_d₃ (f : G → G → G → A) (a b c d e : G) : d₄ (d₃ f) a b c d e = 0 := by
  simp only [d₃, d₄, mul_assoc]
  abel

/-- `d₂` is additive in the cochain. -/
theorem d₂_add (f g : G → G → A) (a b c : G) :
    d₂ (fun x y => f x y + g x y) a b c = d₂ f a b c + d₂ g a b c := by
  simp only [d₂]; abel

/-- `d₃` is additive in the cochain. -/
theorem d₃_add (f g : G → G → G → A) (a b c d : G) :
    d₃ (fun x y z => f x y z + g x y z) a b c d = d₃ f a b c d + d₃ g a b c d := by
  simp only [d₃]; abel

end Additive

/-! ## Normalization predicates -/

section Normalized

variable {A : Type*} [Zero A] {M : Type*} [One M]

/-- A 1-cochain is normalized if it kills the unit. -/
abbrev Normalized₁ (f : G → A) : Prop := f 1 = 0

/-- A 2-cochain is normalized if it vanishes whenever an argument is `1`. -/
abbrev Normalized₂ (f : G → G → A) : Prop := ∀ g, f 1 g = 0 ∧ f g 1 = 0

/-- A 3-cochain is normalized if it vanishes whenever an argument is `1`. -/
abbrev Normalized₃ (f : G → G → G → A) : Prop :=
  ∀ g h, f 1 g h = 0 ∧ f g 1 h = 0 ∧ f g h 1 = 0

/-- A 4-cochain is normalized if it vanishes whenever an argument is `1`. -/
abbrev Normalized₄ (f : G → G → G → G → A) : Prop :=
  ∀ g h k,
    f 1 g h k = 0 ∧ f g 1 h k = 0 ∧ f g h 1 k = 0 ∧ f g h k 1 = 0

/-- Multiplicative normalization for 2-cochains. -/
abbrev MulNormalized₂ (f : G → G → M) : Prop := ∀ g, f 1 g = 1 ∧ f g 1 = 1

/-- Multiplicative normalization for 3-cochains. -/
abbrev MulNormalized₃ (f : G → G → G → M) : Prop :=
  ∀ g h, f 1 g h = 1 ∧ f g 1 h = 1 ∧ f g h 1 = 1

/-- Multiplicative normalization for 4-cochains. -/
abbrev MulNormalized₄ (f : G → G → G → G → M) : Prop :=
  ∀ g h k,
    f 1 g h k = 1 ∧ f g 1 h k = 1 ∧ f g h 1 k = 1 ∧ f g h k 1 = 1

end Normalized

/-! ## Multiplicative coboundaries (degrees 2–4)

Used for scalar-valued cochains (`ω`, `χ`, values in `Kˣ` or a discrete
certificate group). -/

section Multiplicative

variable {M : Type*} [CommGroup M]

/-- Multiplicative coboundary of a 2-cochain. -/
def dm₂ (f : G → G → M) : G → G → G → M :=
  fun a b c => f b c * (f (a * b) c)⁻¹ * f a (b * c) * (f a b)⁻¹

/-- Multiplicative coboundary of a 3-cochain:
`(δω)(a,b,c,d) = ω(b,c,d) ω(ab,c,d)⁻¹ ω(a,bc,d) ω(a,b,cd)⁻¹ ω(a,b,c)`. -/
def dm₃ (f : G → G → G → M) : G → G → G → G → M :=
  fun a b c d =>
    f b c d * (f (a * b) c d)⁻¹ * f a (b * c) d * (f a b (c * d))⁻¹ * f a b c

/-- Multiplicative coboundary of a 4-cochain. -/
def dm₄ (f : G → G → G → G → M) : G → G → G → G → G → M :=
  fun a b c d e =>
    f b c d e * (f (a * b) c d e)⁻¹ * f a (b * c) d e * (f a b (c * d) e)⁻¹
      * f a b c (d * e) * (f a b c d)⁻¹

/-- `dm₃` of a pointwise product is the pointwise product of `dm₃`s. -/
theorem dm₃_mul (f g : G → G → G → M) (a b c d : G) :
    dm₃ (fun x y z => f x y z * g x y z) a b c d = dm₃ f a b c d * dm₃ g a b c d := by
  simp only [dm₃, mul_inv]
  group
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- `dm₃` of a pointwise inverse is the pointwise inverse of `dm₃`. -/
theorem dm₃_inv (f : G → G → G → M) (a b c d : G) :
    dm₃ (fun x y z => (f x y z)⁻¹) a b c d = (dm₃ f a b c d)⁻¹ := by
  simp only [dm₃, mul_inv, inv_inv]

/-- Bridge: `dm₂` is the additive `d₂` transported along `Additive`. -/
theorem dm₂_eq_toMul_d₂ (f : G → G → M) (a b c : G) :
    dm₂ f a b c =
      Additive.toMul (d₂ (fun x y => Additive.ofMul (f x y)) a b c) := by
  simp only [dm₂, d₂, toMul_sub, toMul_add, div_eq_mul_inv]
  rfl

/-- Bridge: `dm₃` is the additive `d₃` transported along `Additive`. -/
theorem dm₃_eq_toMul_d₃ (f : G → G → G → M) (a b c d : G) :
    dm₃ f a b c d =
      Additive.toMul (d₃ (fun x y z => Additive.ofMul (f x y z)) a b c d) := by
  simp only [dm₃, d₃, toMul_sub, toMul_add, div_eq_mul_inv]
  rfl

/-- `δδ = 1` multiplicatively: coboundaries of 2-cochains are 3-cocycles. -/
theorem dm₃_dm₂ (f : G → G → M) (a b c d : G) : dm₃ (dm₂ f) a b c d = 1 := by
  rw [dm₃_eq_toMul_d₃]
  have h : (fun x y z => Additive.ofMul (dm₂ f x y z)) =
      d₂ (fun x y => Additive.ofMul (f x y)) := by
    funext x y z
    rw [dm₂_eq_toMul_d₂]
    simp
  rw [h, d₃_d₂]
  simp

end Multiplicative

end Superfusion
