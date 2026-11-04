/-
Superfusion / Bimod / QuadEdge2

Milestone M8a-8c′-1b-i (roadmap v3): **the associator at the
`(a(bc))d`-vertex**.  The second pentagon edge is
`assoc⁻¹ ∘ (id ⊗ t_{a,b+c,d}) ∘ assoc`; this file realizes the first
leg: the right-associated form

  `Q2r = C_{b,c} ⊗_{T_{b+c}} (C_{a,b+c} ⊗_{T_{(a+b)+c}} C_{a+b+c,d})`

and the associator `q2Assoc : Q2 ≃ Q2r`, instantiating the abstract
`RelTensor.assoc` of M8a-5 with the column-level recast kit of
M8a-8c′-1b-prep (the inner balancing over `T_{(a+b)+c}` runs through
the recast coefficients of `C_{a,b+c}`; the outer `T_{b+c}`-action on
the inner product is the outer-left action through the `(b+c)`-slot).
The middle factor of `Q2r` is `B_L(a, b+c, d)` up to the recast — the
target of `t_{a,b+c,d}` — so the second edge continues from here.
-/
import Superfusion.Bimod.QuadRoutes
import Superfusion.Bimod.RelTensorAssoc

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-- The right-associated form of the `(a(bc))d`-vertex. -/
def Q2r : Type _ :=
  RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier
      (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d))

noncomputable instance : AddCommGroup (Q2r K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (RelTensor K (stdTower (K := K) (a + b + c)).carrier
        (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d))))

noncomputable instance : Module K (Q2r K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (b + c)).carrier (TowerColumn K b c)
      (RelTensor K (stdTower (K := K) (a + b + c)).carrier
        (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d))))

/-- **The associator at the `(a(bc))d`-vertex**: the abstract
`RelTensor.assoc`, instantiated through the recast kit. -/
noncomputable def q2Assoc : Q2 K a b c d ≃ₗ[K] Q2r K a b c d :=
  RelTensor.assoc K (stdTower (K := K) (b + c)).carrier
    (stdTower (K := K) (a + b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c))
    (TowerColumn K (a + b + c) d)

theorem q2Assoc_mk (u : TowerColumn K b c) (v : TowerColumn K a (b + c))
    (w : TowerColumn K (a + b + c) d) :
    q2Assoc K a b c d
        (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (BR K a b c) (TowerColumn K (a + b + c) d)
          (BR.mk K a b c u v) w)
      = RelTensor.mk K (stdTower (K := K) (b + c)).carrier
          (TowerColumn K b c)
          (RelTensor K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d)) u
          (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w) :=
  RelTensor.assoc_mk K (stdTower (K := K) (b + c)).carrier
    (stdTower (K := K) (a + b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c))
    (TowerColumn K (a + b + c) d) u v w

end PentagonB

end Bimod

end Superfusion
