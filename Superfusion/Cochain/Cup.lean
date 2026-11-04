/-
Superfusion / Cochain / Cup

The cup and cup-1/cup-2 products of §2.3, defined exactly in the bidegrees
the paper uses (roadmap decision: no general Steenrod theory).

Paper formulas (§2.3), normalized inhomogeneous cochains:
  (u ∪ v)(g₁,…,g_{m+n}) = u(g₁,…,g_m) v(g_{m+1},…,g_{m+n})
  (u ∪₁ v)(a,b,c)     = u(ab,c)v(a,b) + u(a,bc)v(b,c)                 (2,2)
  (u ∪₁ v)(a,b,c,d)   = u(abc,d)v(a,b,c) + u(a,bcd)v(b,c,d)           (2,3)
  (u ∪₁ v)(a,b,c,d,e) = u(abc,d,e)v(a,b,c) + u(a,bcd,e)v(b,c,d)
                        + u(a,b,cde)v(c,d,e)                           (3,3)
  (u ∪₂ v)(a,b)       = u(a,b)v(a,b)                                   (2,2)
The bidegree-(3,2) cup-1, needed on the right side of the coboundary rule
(3) and forced by Steenrod's general formula, is
  (u ∪₁ v)(a,b,c,d)   = u(ab,c,d)v(a,b) + u(a,bc,d)v(b,c) + u(a,b,cd)v(c,d).

Main theorem: equation (3) in bidegree (2,2),
  δ(u ∪₁ v) = u ∪ v + v ∪ u + δu ∪₁ v + u ∪₁ δv   (mod 2),
for an arbitrary group `G` — the engine behind the Gu–Wen product (6).
-/
import Superfusion.Cochain.Basic

namespace Superfusion

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

/-! ## Cup products (values in a commutative ring, used with `R = ZMod 2`) -/

/-- Cup product in bidegree (1,1). -/
def cup₁₁ (u v : G → R) : G → G → R := fun a b => u a * v b

/-- Cup product in bidegree (1,2). -/
def cup₁₂ (u : G → R) (v : G → G → R) : G → G → G → R := fun a b c => u a * v b c

/-- Cup product in bidegree (1,3). -/
def cup₁₃ (u : G → R) (v : G → G → G → R) : G → G → G → G → R :=
  fun a b c d => u a * v b c d

/-- Cup product in bidegree (2,2), e.g. `(ν ∪ ν)(g,h,k,l) = ν(g,h)ν(k,l)`. -/
def cup₂₂ (u v : G → G → R) : G → G → G → G → R := fun a b c d => u a b * v c d

/-! ## Cup-1 products in the paper's bidegrees -/

/-- Cup-1 in bidegree (2,2). -/
def cupOne₂₂ (u v : G → G → R) : G → G → G → R :=
  fun a b c => u (a * b) c * v a b + u a (b * c) * v b c

/-- Cup-1 in bidegree (2,3). -/
def cupOne₂₃ (u : G → G → R) (v : G → G → G → R) : G → G → G → G → R :=
  fun a b c d => u (a * b * c) d * v a b c + u a (b * c * d) * v b c d

/-- Cup-1 in bidegree (3,2) (forced by equation (3)). -/
def cupOne₃₂ (u : G → G → G → R) (v : G → G → R) : G → G → G → G → R :=
  fun a b c d => u (a * b) c d * v a b + u a (b * c) d * v b c + u a b (c * d) * v c d

/-- Cup-1 in bidegree (3,3). -/
def cupOne₃₃ (u v : G → G → G → R) : G → G → G → G → G → R :=
  fun a b c d e =>
    u (a * b * c) d e * v a b c + u a (b * c * d) e * v b c d
      + u a b (c * d * e) * v c d e

/-- Cup-2 in bidegree (2,2). -/
def cupTwo₂₂ (u v : G → G → R) : G → G → R := fun a b => u a b * v a b

/-! ## The coboundary rule (3) -/

private theorem zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

private theorem zmod2_sub_eq_add : ∀ x y : ZMod 2, x - y = x + y := by decide

/-- **Equation (3)** in bidegree (2,2):
`δ(u ∪₁ v) = u ∪ v + v ∪ u + δu ∪₁ v + u ∪₁ δv` (mod 2), pointwise. -/
theorem d₃_cupOne₂₂ (u v : G → G → ZMod 2) (a b c d : G) :
    d₃ (cupOne₂₂ u v) a b c d =
      cup₂₂ u v a b c d + cup₂₂ v u a b c d
        + cupOne₃₂ (d₂ u) v a b c d + cupOne₂₃ u (d₂ v) a b c d := by
  simp only [d₃, d₂, cupOne₂₂, cupOne₃₂, cupOne₂₃, cup₂₂, mul_assoc,
    zmod2_sub_eq_add]
  ring_nf
  simp only [zmod2_two_eq_zero, mul_zero, add_zero]

/-- For 2-cocycles, `u ∪ v + v ∪ u` is the coboundary of `u ∪₁ v`
(the consequence of (3) used repeatedly in §2.3). -/
theorem cup₂₂_add_swap_eq_d₃ {u v : G → G → ZMod 2}
    (hu : ∀ a b c, d₂ u a b c = 0) (hv : ∀ a b c, d₂ v a b c = 0) (a b c d : G) :
    cup₂₂ u v a b c d + cup₂₂ v u a b c d = d₃ (cupOne₂₂ u v) a b c d := by
  rw [d₃_cupOne₂₂]
  simp [cupOne₃₂, cupOne₂₃, hu, hv]

/-- Leibniz rule for the cup product in bidegree (1,2):
`δ(u ∪ v) = δu ∪ v + u ∪ δv` (mod 2). -/
theorem d₃_cup₁₂ (u : G → ZMod 2) (v : G → G → ZMod 2) (a b c d : G) :
    d₃ (cup₁₂ u v) a b c d =
      cup₂₂ (d₁ u) v a b c d + cup₁₃ u (d₂ v) a b c d := by
  simp only [d₃, d₂, d₁, cup₁₂, cup₂₂, cup₁₃, zmod2_sub_eq_add]
  ring_nf
  simp only [zmod2_two_eq_zero, mul_zero, add_zero]

/-- A 2-cocycle in solved form: `u(ab, c) = u(b,c) + u(a,bc) + u(a,b)`. -/
theorem cocycle_solved {u : G → G → ZMod 2} (hu : ∀ a b c, d₂ u a b c = 0)
    (a b c : G) : u (a * b) c = u b c + u a (b * c) + u a b := by
  have key : ∀ x₁ x₂ x₃ x₄ : ZMod 2, x₁ - x₂ + x₃ - x₄ = 0 → x₂ = x₁ + x₃ + x₄ := by
    decide
  exact key _ _ _ _ (hu a b c)

/-- The Steenrod relation one degree up, for 2-cocycles:
`δ(u ∪₂ v) = u ∪₁ v + v ∪₁ u` (mod 2).  This is what makes the Gu–Wen
product (6) commutative up to a supercoboundary (Proposition 2.5). -/
theorem d₂_cupTwo₂₂ {u v : G → G → ZMod 2}
    (hu : ∀ a b c, d₂ u a b c = 0) (hv : ∀ a b c, d₂ v a b c = 0) (a b c : G) :
    d₂ (cupTwo₂₂ u v) a b c =
      cupOne₂₂ u v a b c + cupOne₂₂ v u a b c := by
  simp only [d₂, cupTwo₂₂, cupOne₂₂, cocycle_solved hu, cocycle_solved hv,
    zmod2_sub_eq_add]
  ring_nf
  simp only [zmod2_two_eq_zero, mul_zero, add_zero, zero_add]

/-! ## Bilinearity of the cup and cup-1 products (pointwise) -/

omit [Group G] in
theorem cup₂₂_add_left (u u' v : G → G → R) (a b c d : G) :
    cup₂₂ (fun x y => u x y + u' x y) v a b c d =
      cup₂₂ u v a b c d + cup₂₂ u' v a b c d := by
  simp [cup₂₂, add_mul]

omit [Group G] in
theorem cup₂₂_add_right (u v v' : G → G → R) (a b c d : G) :
    cup₂₂ u (fun x y => v x y + v' x y) a b c d =
      cup₂₂ u v a b c d + cup₂₂ u v' a b c d := by
  simp [cup₂₂, mul_add]

theorem cupOne₂₂_add_left (u u' v : G → G → R) (a b c : G) :
    cupOne₂₂ (fun x y => u x y + u' x y) v a b c =
      cupOne₂₂ u v a b c + cupOne₂₂ u' v a b c := by
  simp only [cupOne₂₂, add_mul]; ring

theorem cupOne₂₂_add_right (u v v' : G → G → R) (a b c : G) :
    cupOne₂₂ u (fun x y => v x y + v' x y) a b c =
      cupOne₂₂ u v a b c + cupOne₂₂ u v' a b c := by
  simp only [cupOne₂₂, mul_add]; ring

theorem cupOne₂₂_zero_left (v : G → G → R) (a b c : G) :
    cupOne₂₂ (fun _ _ => (0 : R)) v a b c = 0 := by
  simp [cupOne₂₂]

theorem cupOne₂₂_zero_right (u : G → G → R) (a b c : G) :
    cupOne₂₂ u (fun _ _ => (0 : R)) a b c = 0 := by
  simp [cupOne₂₂]

end Superfusion
