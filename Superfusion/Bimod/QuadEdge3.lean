/-
Superfusion / Bimod / QuadEdge3

Milestone M8a-8c′-1b-iv (roadmap v3): **the third pentagon edge**.
The left-associated form of `Q3` is

  `Q3l = (C_{b,c} ⊗_{T_{b+c}} C_{b+c,d}) ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}
       = B_L(b,c,d) ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}`

— the first factor is *literally* the canonical `B_L(b,c,d)`, and all
balancings are canonical (no recasts!).  So the third edge is the
`Q1 → Q2` pattern shifted by one slot:

  `E3 t₃ = (t₃ ⊗ id) ∘ assoc⁻¹ : Q3 → Q4`,

with `t₃ : B_L(b,c,d) → B_R(b,c,d)` a canonical triple intertwiner
(its right-equivariance over `T_{(b+c)+d}` through the generic recast
of M8a-8c′-0 at the indices `(b,c,d)`), landing in the
`a(b(cd))`-vertex

  `Q4 = B_R(b,c,d) ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}`.
-/
import Superfusion.Bimod.QuadEdge2b

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-- Pentagon vertex `a(b(cd))` (spelled form: `B_R(b,c,d)` balanced
through its recast right action). -/
def Q4 : Type _ :=
  RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d))

noncomputable instance : AddCommGroup (Q4 K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d))))

noncomputable instance : Module K (Q4 K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
      (TowerColumn K a ((b + c) + d))))

/-- The associator at the `a((bc)d)`-vertex: the left-associated form
`B_L(b,c,d) ⊗ C_{a,(b+c)+d}` re-associates to `Q3` (all balancings
canonical). -/
noncomputable def q3Assoc :
    (RelTensor K (stdTower (K := K) ((b + c) + d)).carrier
      (BL K b c d) (TowerColumn K a ((b + c) + d)))
      ≃ₗ[K] Q3 K a b c d :=
  RelTensor.assoc K (stdTower (K := K) (b + c)).carrier
    (stdTower (K := K) ((b + c) + d)).carrier
    (TowerColumn K b c) (TowerColumn K (b + c) d)
    (TowerColumn K a ((b + c) + d))

theorem q3Assoc_mk (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    q3Assoc K a b c d
        (RelTensor.mk K (stdTower (K := K) ((b + c) + d)).carrier
          (BL K b c d) (TowerColumn K a ((b + c) + d))
          (BL.mk K b c d u v) w)
      = RelTensor.mk K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (Q3Inner K a b c d) u
          (RelTensor.mk K (stdTower (K := K) ((b + c) + d)).carrier
            (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))
            v w) :=
  RelTensor.assoc_mk K (stdTower (K := K) (b + c)).carrier
    (stdTower (K := K) ((b + c) + d)).carrier
    (TowerColumn K b c) (TowerColumn K (b + c) d)
    (TowerColumn K a ((b + c) + d)) u v w

/-- **The third pentagon edge** `E3 t₃ = (t₃ ⊗ id) ∘ assoc⁻¹`, for a
right-equivariant `t₃ : B_L(b,c,d) → B_R(b,c,d)`. -/
noncomputable def E3 (t₃ : BL K b c d →ₗ[K] BR K b c d)
    (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
      (m : BL K b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m) :
    Q3 K a b c d →ₗ[K] Q4 K a b c d :=
  (RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl)).comp
    (q3Assoc K a b c d).symm.toLinearMap

theorem E3_mk (t₃ : BL K b c d →ₗ[K] BR K b c d)
    (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
      (m : BL K b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃
        (RelTensor.mk K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (Q3Inner K a b c d) u
          (RelTensor.mk K (stdTower (K := K) ((b + c) + d)).carrier
            (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))
            v w))
      = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d))
          (t₃ (BL.mk K b c d u v)) w := by
  show (RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl))
      ((q3Assoc K a b c d).symm
        (RelTensor.mk K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c) (Q3Inner K a b c d) u
          (RelTensor.mk K (stdTower (K := K) ((b + c) + d)).carrier
            (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d))
            v w))) = _
  rw [← q3Assoc_mk, LinearEquiv.symm_apply_apply, RelTensor.map_mk]
  rfl

end PentagonB

end Bimod

end Superfusion
