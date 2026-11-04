/-
Superfusion / Bimod / QuadEdge4

Milestone M8a-8c′-1b-v (roadmap v3): **the fourth pentagon edge** (the
first leg of the bottom route).  Right-associating `Q1` exposes the
canonical `B_L(a{+}b,c,d)` as the inner factor:

  `Q1r = C_{a,b} ⊗_{T_{a+b}} (C_{a+b,c} ⊗_{T_{(a+b)+c}} C_{(a+b)+c,d})
       = C_{a,b} ⊗_{T_{a+b}} B_L(a{+}b,c,d)`

(all balancings canonical — no recasts), and the fourth edge is the
signed amplification of a canonical triple intertwiner
`t₄ : B_L(a{+}b,c,d) → B_R(a{+}b,c,d)`:

  `E4 t₄ = (id ⊗_signed t₄) ∘ assoc : Q1 → Q5`,

landing in the `(ab)(cd)`-vertex

  `Q5 = C_{a,b} ⊗_{T_{a+b}} B_R(a{+}b,c,d)
      = C_{a,b} ⊗_{T_{a+b}} (C_{c,d} ⊗_{T_{c+d}} C_{a+b,c+d})`

— the two-sided fusion, with no external tensor product needed.  The
`T_{a+b}`-equivariance datum of `t₄` is its `(a{+}b)`-slot
super-equivariance: on the source the slot action of `B_L`, on the
target the signed middle action of `B_R`.
-/
import Superfusion.Bimod.QuadEdge3

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-- Pentagon vertex `(ab)(cd)`: the two-sided fusion
`C_{a,b} ⊗ B_R(a+b,c,d) = C_{a,b} ⊗ (C_{c,d} ⊗ C_{a+b,c+d})`. -/
def Q5 : Type _ :=
  RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
    (BR K (a + b) c d)

noncomputable instance : AddCommGroup (Q5 K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d)))

noncomputable instance : Module K (Q5 K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (BR K (a + b) c d)))

/-- The associator at the `((ab)c)d`-vertex: the right-associated form
exposes the canonical `B_L(a+b,c,d)` (all balancings canonical). -/
noncomputable def q1Assoc :
    Q1 K a b c d ≃ₗ[K]
      RelTensor K (stdTower (K := K) (a + b)).carrier
        (TowerColumn K a b) (BL K (a + b) c d) :=
  RelTensor.assoc K (stdTower (K := K) (a + b)).carrier
    (stdTower (K := K) ((a + b) + c)).carrier
    (TowerColumn K a b) (TowerColumn K (a + b) c)
    (TowerColumn K ((a + b) + c) d)

theorem q1Assoc_mk (u : TowerColumn K a b) (v : TowerColumn K (a + b) c)
    (w : TowerColumn K ((a + b) + c) d) :
    q1Assoc K a b c d
        (RelTensor.mk K (stdTower (K := K) ((a + b) + c)).carrier
          (BL K a b c) (TowerColumn K ((a + b) + c) d)
          (BL.mk K a b c u v) w)
      = RelTensor.mk K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (BL K (a + b) c d) u
          (BL.mk K (a + b) c d v w) :=
  RelTensor.assoc_mk K (stdTower (K := K) (a + b)).carrier
    (stdTower (K := K) ((a + b) + c)).carrier
    (TowerColumn K a b) (TowerColumn K (a + b) c)
    (TowerColumn K ((a + b) + c) d) u v w

/-- **The fourth pentagon edge** `E4 t₄ = (id ⊗_signed t₄) ∘ assoc`,
for a canonical triple intertwiner `t₄ : B_L(a+b,c,d) → B_R(a+b,c,d)`
of parity `e`, super-equivariant for the `(a+b)`-slot. -/
noncomputable def E4 (e : ZMod 2)
    (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i →
      ∀ n : BL K (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n)) :
    Q1 K a b c d →ₗ[K] Q5 K a b c d :=
  (smap (stdTower (K := K) (a + b)).grading (TowerColumn.grading K a b)
    t₄ e ht₄).comp (q1Assoc K a b c d).toLinearMap

/-- The generator formula of the fourth edge, on homogeneous first
slots. -/
theorem E4_mk_of_mem (e : ZMod 2)
    (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i →
      ∀ n : BL K (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))
    {j : ZMod 2} {u : TowerColumn K a b}
    (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄
        (RelTensor.mk K (stdTower (K := K) ((a + b) + c)).carrier
          (BL K a b c) (TowerColumn K ((a + b) + c) d)
          (BL.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (stdTower (K := K) (a + b)).carrier
            (TowerColumn K a b) (BR K (a + b) c d) u
            (t₄ (BL.mk K (a + b) c d v w)) := by
  show (smap (stdTower (K := K) (a + b)).grading
      (TowerColumn.grading K a b) t₄ e ht₄)
      (q1Assoc K a b c d
        (RelTensor.mk K (stdTower (K := K) ((a + b) + c)).carrier
          (BL K a b c) (TowerColumn K ((a + b) + c) d)
          (BL.mk K a b c u v) w)) = _
  rw [q1Assoc_mk, smap_mk_of_mem (stdTower (K := K) (a + b)).grading
    (TowerColumn.grading K a b) t₄ e ht₄ hu]

end PentagonB

end Bimod

end Superfusion
