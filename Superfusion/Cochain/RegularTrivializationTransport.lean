/-
Superfusion / Cochain / RegularTrivializationTransport

Transport principles for `RegularTrivialization`:

* `map` pushes a trivialization forward along a sign-compatible group
  homomorphism (e.g. from a discrete certificate group into `Kˣ`);
* `ofCoboundary` transports it across a change of the four-cochain `χ` by an
  explicit coboundary — the exact freedom left by the canonical connector
  normalizations (`gChiCanon` is pinned only up to a coboundary);
* `copy` replaces `p` and `χ` by pointwise-equal cochains.

Together these reduce a trivialization of a choice-produced pair `(p, χ)` to
a trivialization of an explicitly tabulated pair together with a class-level
identification of the two.
-/
import Superfusion.Cochain.RegularTrivialization

namespace Superfusion

universe u v w

variable {H : Type u} [Group H]
variable {M : Type v} [CommGroup M] [GroupSign M]
variable {N : Type w} [CommGroup N] [GroupSign N]

/-- A sign-compatible monoid homomorphism intertwines the `sgn` maps. -/
theorem map_sgn (f : M →* N) (hf : f sign = sign) (i : ZMod 2) :
    f (sgn i) = sgn i := by
  rcases zmod2_cases i with hi | hi <;> simp [hi, sgn, hf]

omit [GroupSign M] [GroupSign N] in
/-- Monoid homomorphisms commute with the multiplicative coboundary `dm₃`. -/
theorem map_dm₃ (f : M →* N) (β : H → H → H → M) (a b c d : H) :
    f (dm₃ β a b c d) = dm₃ (fun x y z => f (β x y z)) a b c d := by
  simp [dm₃, map_mul, map_inv]

namespace RegularTrivialization

variable {p : H → H → H → ZMod 2} {χ : H → H → H → H → M}

/-- Push a trivialization forward along a sign-compatible homomorphism. -/
def map (t : RegularTrivialization p χ) (f : M →* N) (hf : f sign = sign) :
    RegularTrivialization p (fun a b c d => f (χ a b c d)) where
  ν := t.ν
  β := fun a b c => f (t.β a b c)
  ν_normalized := t.ν_normalized
  parity := t.parity
  pentagon := by
    intro a b c d
    have h := congrArg f (t.pentagon a b c d)
    rw [map_mul, map_sgn f hf, map_dm₃] at h
    exact h

/-- Transport a trivialization across a coboundary change of the
four-cochain: if `χ' = χ · δγ` pointwise, a trivialization of `(p, χ)`
yields one of `(p, χ')` with rescaling `β · γ`. -/
def ofCoboundary (t : RegularTrivialization p χ)
    (χ' : H → H → H → H → M) (γ : H → H → H → M)
    (hχ : ∀ a b c d, χ' a b c d = χ a b c d * dm₃ γ a b c d) :
    RegularTrivialization p χ' where
  ν := t.ν
  β := fun a b c => t.β a b c * γ a b c
  ν_normalized := t.ν_normalized
  parity := t.parity
  pentagon := by
    intro a b c d
    rw [dm₃_mul, hχ, ← t.pentagon a b c d]
    exact mul_right_comm _ _ _

/-- Replace `p` and `χ` by pointwise-equal cochains. -/
def copy (t : RegularTrivialization p χ)
    (p' : H → H → H → ZMod 2) (χ' : H → H → H → H → M)
    (hp : ∀ a b c, p' a b c = p a b c)
    (hχ : ∀ a b c d, χ' a b c d = χ a b c d) :
    RegularTrivialization p' χ' where
  ν := t.ν
  β := t.β
  ν_normalized := t.ν_normalized
  parity := fun a b c => by rw [hp]; exact t.parity a b c
  pentagon := by
    intro a b c d
    have hq : regularQuadratic t.ν p' a b c d = regularQuadratic t.ν p a b c d := by
      simp only [regularQuadratic, cup₂₂, cupOne₂₃, hp]
    rw [hχ, hq]
    exact t.pentagon a b c d

end RegularTrivialization

end Superfusion
