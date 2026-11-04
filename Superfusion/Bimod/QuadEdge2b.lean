/-
Superfusion / Bimod / QuadEdge2b

Milestone M8a-8c′-1b-iii (roadmap v3): **the second pentagon edge**.
With the associator `q2Assoc` (1b-i) and the signed amplification
`smap` (1b-ii) in hand, the second edge is

  `E2 t₂ = (id_{C_{b,c}} ⊗_signed t₂) ∘ q2Assoc : Q2 → Q3`,

where `t₂` is a generator *at the vertex spelling* (no index casts —
the design decision of 1b-ii): a map from the middle factor of `Q2r`
(the spelled `B_L(a,b{+}c,d)`) to the spelled `B_R(a,b{+}c,d)`
(`Q3Inner`, which happens to need no recast at all), super-equivariant
of its parity `e` for the `(b+c)`-slot.  The vertex

  `Q3 = C_{b,c} ⊗_{T_{b+c}} (C_{b+c,d} ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d})`

is the right-associated form of the `a((bc)d)`-bracketing.
-/
import Superfusion.Bimod.QuadEdge2
import Superfusion.Bimod.SignedMap

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-- The middle factor of `Q2r`: the spelled `B_L(a,b+c,d)`. -/
abbrev Q2rInner : Type _ :=
  RelTensor K (stdTower (K := K) (a + b + c)).carrier
    (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d)

/-- The spelled `B_R(a,b+c,d)` (no recast is needed at this
spelling). -/
def Q3Inner : Type _ :=
  RelTensor K (stdTower (K := K) ((b + c) + d)).carrier
    (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))

noncomputable instance : AddCommGroup (Q3Inner K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) ((b + c) + d)).carrier
      (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))))

noncomputable instance : Module K (Q3Inner K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) ((b + c) + d)).carrier
      (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))))

/-- The outer-left `T_{b+c}`-action on `Q3Inner` (through the
`(b+c)`-slot of its first column). -/
noncomputable instance : Module (stdTower (K := K) (b + c)).carrier
    (Q3Inner K a b c d) :=
  leftModule K (stdTower (K := K) ((b + c) + d)).carrier
    (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))
    (B := (stdTower (K := K) (b + c)).carrier)

/-- Pentagon vertex `a((bc)d)`, in right-associated form. -/
def Q3 : Type _ :=
  RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
    (Q3Inner K a b c d)

noncomputable instance : AddCommGroup (Q3 K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d)))

noncomputable instance : Module K (Q3 K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (Q3Inner K a b c d)))

/-- **The second pentagon edge** `E2 t₂ = (id ⊗_signed t₂) ∘ assoc`,
for a spelled generator `t₂` of parity `e`, super-equivariant for the
`(b+c)`-slot. -/
noncomputable def E2 (e : ZMod 2)
    (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
      y ∈ (stdTower (K := K) (b + c)).grading i →
      ∀ n : Q2rInner K a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n)) :
    Q2 K a b c d →ₗ[K] Q3 K a b c d :=
  (smap (stdTower (K := K) (b + c)).grading (TowerColumn.grading K b c)
    t₂ e ht₂).comp (q2Assoc K a b c d).toLinearMap

/-- The generator formula of the second edge, on homogeneous first
slots. -/
theorem E2_mk_of_mem (e : ZMod 2)
    (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
      y ∈ (stdTower (K := K) (b + c)).grading i →
      ∀ n : Q2rInner K a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))
    {j : ZMod 2} {u : TowerColumn K b c}
    (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂
        (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (BR K a b c) (TowerColumn K (a + b + c) d)
          (BR.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (stdTower (K := K) (b + c)).carrier
            (TowerColumn K b c) (Q3Inner K a b c d) u
            (t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d)
              v w)) := by
  show (smap (stdTower (K := K) (b + c)).grading
      (TowerColumn.grading K b c) t₂ e ht₂)
      (q2Assoc K a b c d
        (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (BR K a b c) (TowerColumn K (a + b + c) d)
          (BR.mk K a b c u v) w)) = _
  rw [q2Assoc_mk, smap_mk_of_mem (stdTower (K := K) (b + c)).grading
    (TowerColumn.grading K b c) t₂ e ht₂ hu]

end PentagonB

end Bimod

end Superfusion
