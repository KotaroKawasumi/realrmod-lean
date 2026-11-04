/-
Superfusion / Bimod / QuadRoutes

Milestone M8a-8c′-1 (roadmap v3, first block): **the first two
pentagon vertices and the first edge**.  On a quadruple `(a,b,c,d)`
the pentagon compares five iterated fusions; this file constructs

* `Q1 = B_L(a,b,c) ⊗_{T_{a+b+c}} C_{a+b+c,d}`  (bracketing `((ab)c)d`),
* `Q2 = B_R(a,b,c) ⊗_{T_{a+b+c}} C_{a+b+c,d}`  (bracketing `(a(bc))d`),

— `Q2` is balanced through the *recast* right action of M8a-8c′-0,
so both quadruples are balanced over literally the same tower fiber —
and the first pentagon edge

* `E1 t = t ⊗ id : Q1 → Q2`

for any right-equivariant `t : B_L → B_R` (in particular any member
of the intertwiner space, via
`rightSemilinear_iff_recast_equivariant`).  The remaining vertices,
edges, and the definition of `χ` continue in the next blocks.
-/
import Superfusion.Bimod.RouteRecast
import Superfusion.Bimod.MapEquivariance

namespace Superfusion

namespace Bimod

namespace PentagonB

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-- Pentagon vertex `((ab)c)d`. -/
def Q1 : Type _ :=
  RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
    (TowerColumn K (a + b + c) d)

noncomputable instance : AddCommGroup (Q1 K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d)))

noncomputable instance : Module K (Q1 K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BL K a b c)
      (TowerColumn K (a + b + c) d)))

/-- Pentagon vertex `(a(bc))d` (balanced through the recast right
action of `B_R`). -/
def Q2 : Type _ :=
  RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
    (TowerColumn K (a + b + c) d)

noncomputable instance : AddCommGroup (Q2 K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d)))

noncomputable instance : Module K (Q2 K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier (BR K a b c)
      (TowerColumn K (a + b + c) d)))

/-- **The first pentagon edge** `E1 t = t ⊗ id : Q1 → Q2`, for a
right-equivariant `t : B_L → B_R`. -/
noncomputable def E1 (t : BL K a b c →ₗ[K] BR K a b c)
    (ht : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier)
      (m : BL K a b c),
      t (MulOpposite.op τ • m) = MulOpposite.op τ • t m) :
    Q1 K a b c d →ₗ[K] Q2 K a b c d :=
  RelTensor.map t LinearMap.id ht (fun _ _ => rfl)

theorem E1_mk (t : BL K a b c →ₗ[K] BR K a b c)
    (ht : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier)
      (m : BL K a b c),
      t (MulOpposite.op τ • m) = MulOpposite.op τ • t m)
    (u : BL K a b c) (v : TowerColumn K (a + b + c) d) :
    E1 K a b c d t ht
        (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (BL K a b c) (TowerColumn K (a + b + c) d) u v)
      = RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (BR K a b c) (TowerColumn K (a + b + c) d) (t u) v := by
  show RelTensor.map t LinearMap.id ht (fun _ _ => rfl)
      (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
        (BL K a b c) (TowerColumn K (a + b + c) d) u v) = _
  rw [RelTensor.map_mk]
  rfl

end PentagonB

end Bimod

end Superfusion
