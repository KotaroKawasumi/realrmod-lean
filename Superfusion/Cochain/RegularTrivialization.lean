/-
Superfusion / Cochain / RegularTrivialization

The cochain data which kills the degree-four obstruction of a regular
weakly pointed construction.  This file is independent of fusion gauges:
it records the exact low-degree formula and its normalization consequences.

Only the parity shift `ν` is normalized here.  The scalar cochain `β` is
unit-valued, hence pointwise nonzero, but need not be normalized.  This is
essential for a raw canonical connector chosen by `Exists.choose`: its unit
comparison scalars need not be one.  Normalization of `β` is a separate
predicate, appropriate only after the connector family has itself been
normalized at the unit.
-/
import Superfusion.Cochain.Cup

namespace Superfusion

universe u v

variable {H : Type u} [Group H]
variable {M : Type v} [CommGroup M] [GroupSign M]

/-- The quadratic four-cochain introduced by shifting binary fusion columns
by a parity two-cochain `ν`:
`q(ν,p) = ν ∪ ν + ν ∪₁ p`. -/
def regularQuadratic
    (ν : H → H → ZMod 2) (p : H → H → H → ZMod 2) :
    H → H → H → H → ZMod 2 :=
  fun a b c d => cup₂₂ ν ν a b c d + cupOne₂₃ ν p a b c d

/-- The quadratic correction has exactly the boundary required by the
degree-four supercocycle equation.  No separate cocycle hypothesis is
needed: `p = d₂ ν` already implies it. -/
theorem d₄_regularQuadratic
    (ν : H → H → ZMod 2) (p : H → H → H → ZMod 2)
    (hν : ∀ a b c, d₂ ν a b c = p a b c) (a b c d e : H) :
    d₄ (regularQuadratic ν p) a b c d e = cupOne₃₃ p p a b c d e := by
  have hp : p = d₂ ν := by
    funext x y z
    exact (hν x y z).symm
  subst p
  have sub_eq_add : ∀ x y : ZMod 2, x - y = x + y := by decide
  simp only [regularQuadratic, d₄, d₂, cup₂₂, cupOne₂₃, cupOne₃₃, mul_assoc,
    sub_eq_add]
  ring_nf
  have two_eq_zero : (2 : ZMod 2) = 0 := by decide
  simp only [two_eq_zero, mul_zero, add_zero]

/-- A cochain-level trivialization of a degree-four supercohomology pair.

The equations use the convention in which the uncorrected pentagon is
`TOP = χ · BOTTOM`; the final associator is the shifted connector scaled
by `β⁻¹`.  Consequently the scalar equation is
` χ * sgn (q(ν,p)) = dm₃ β` rather than its inverse. -/
structure RegularTrivialization
    (p : H → H → H → ZMod 2) (χ : H → H → H → H → M) where
  /-- Parity shifts of the binary fusion columns. -/
  ν : H → H → ZMod 2
  /-- Nonzero scalar rescaling of the ternary connectors. -/
  β : H → H → H → M
  /-- Unit fusion columns are not parity shifted. -/
  ν_normalized : Normalized₂ ν
  /-- Shifting cancels the parity of every ternary connector. -/
  parity : ∀ a b c, d₂ ν a b c = p a b c
  /-- Scaling the shifted connectors by `β⁻¹` cancels their pentagon scalar. -/
  pentagon : ∀ a b c d,
    χ a b c d * sgn (regularQuadratic ν p a b c d) = dm₃ β a b c d

namespace RegularTrivialization

variable {p : H → H → H → ZMod 2} {χ : H → H → H → H → M}

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by decide +revert

@[simp] theorem ν_one_left (t : RegularTrivialization p χ) (g : H) :
    t.ν 1 g = 0 := (t.ν_normalized g).1

@[simp] theorem ν_one_right (t : RegularTrivialization p χ) (g : H) :
    t.ν g 1 = 0 := (t.ν_normalized g).2

/-- A regular trivialization forces its parity cochain to be normalized. -/
theorem p_normalized (t : RegularTrivialization p χ) : Normalized₃ p := by
  intro g h
  constructor
  · rw [← t.parity]
    simp [d₂]
  constructor
  · rw [← t.parity]
    simp [d₂, zmod2_add_self]
  · rw [← t.parity]
    simp [d₂]

theorem p_one_first (t : RegularTrivialization p χ) (g h : H) :
    p 1 g h = 0 := (t.p_normalized g h).1

theorem p_one_second (t : RegularTrivialization p χ) (g h : H) :
    p g 1 h = 0 := (t.p_normalized g h).2.1

theorem p_one_third (t : RegularTrivialization p χ) (g h : H) :
    p g h 1 = 0 := (t.p_normalized g h).2.2

/-- A coboundary parity is automatically a three-cocycle. -/
theorem p_isCocycle (t : RegularTrivialization p χ) (a b c d : H) :
    d₃ p a b c d = 0 := by
  calc
    d₃ p a b c d = d₃ (d₂ t.ν) a b c d := by
      congr 1
      funext x y z
      exact (t.parity x y z).symm
    _ = 0 := d₃_d₂ t.ν a b c d

/-- The scalar cancellation used by the regular pentagon.

The three factors on the left are the `β⁻¹` rescalings of the three-edge
route, while the two factors on the right are the rescalings of the
two-edge route.  Thus an unscaled shifted pentagon with scalar
`χ * sgn (regularQuadratic ν p)` becomes a strict pentagon after every
connector is rescaled by `β⁻¹`. -/
theorem rescaledPentagon (t : RegularTrivialization p χ)
    (a b c d : H) :
    (t.β a b c)⁻¹ * (t.β a (b * c) d)⁻¹ * (t.β b c d)⁻¹ *
        (χ a b c d * sgn (regularQuadratic t.ν p a b c d)) =
      (t.β (a * b) c d)⁻¹ * (t.β a b (c * d))⁻¹ := by
  rw [t.pentagon]
  simp [dm₃, mul_assoc, mul_comm, mul_left_comm]

/-- Unit normalization of the scalar rescaling is extra data, not part of a
trivialization relative to an arbitrary raw connector family. -/
def IsUnitNormalized (t : RegularTrivialization p χ) : Prop :=
  MulNormalized₃ t.β

@[simp] theorem β_one_first (t : RegularTrivialization p χ)
    (ht : t.IsUnitNormalized) (g h : H) : t.β 1 g h = 1 :=
  (ht g h).1

@[simp] theorem β_one_second (t : RegularTrivialization p χ)
    (ht : t.IsUnitNormalized) (g h : H) : t.β g 1 h = 1 :=
  (ht g h).2.1

@[simp] theorem β_one_third (t : RegularTrivialization p χ)
    (ht : t.IsUnitNormalized) (g h : H) : t.β g h 1 = 1 :=
  (ht g h).2.2

/-- After the connector and `β` have both been normalized at the unit, the
four-cochain `χ` is normalized as a consequence, not an independent axiom. -/
theorem χ_normalized (t : RegularTrivialization p χ)
    (ht : t.IsUnitNormalized) : MulNormalized₄ χ := by
  intro g h k
  constructor
  · simpa [regularQuadratic, cup₂₂, cupOne₂₃, dm₃,
      p_one_first t, p_one_second t, p_one_third t,
      β_one_first t ht, β_one_second t ht, β_one_third t ht] using
      t.pentagon 1 g h k
  constructor
  · simpa [regularQuadratic, cup₂₂, cupOne₂₃, dm₃,
      p_one_first t, p_one_second t, p_one_third t,
      β_one_first t ht, β_one_second t ht, β_one_third t ht] using
      t.pentagon g 1 h k
  constructor
  · simpa [regularQuadratic, cup₂₂, cupOne₂₃, dm₃,
      p_one_first t, p_one_second t, p_one_third t,
      β_one_first t ht, β_one_second t ht, β_one_third t ht] using
      t.pentagon g h 1 k
  · simpa [regularQuadratic, cup₂₂, cupOne₂₃, dm₃,
      p_one_first t, p_one_second t, p_one_third t,
      β_one_first t ht, β_one_second t ht, β_one_third t ht] using
      t.pentagon g h k 1

end RegularTrivialization

end Superfusion
