/-
Superfusion / Bimod / QuadClose

Milestone M8a-8c′-1b-viii (roadmap v3): **closing the bottom route**
— the connector `q4Close : Q4r ≃ Q4` between the two presentations of
the `a(b(cd))`-vertex, so that both pentagon routes land in literally
the same space:

  `Q4r = C_{c,d} ⊗_{T_{c+d}} (C_{b,c+d} ⊗_{T_{b+(c+d)}} C_{a,b+(c+d)})`
  (right-associated, natural coefficients — the landing of `E5`),

  `Q4  = (C_{c,d} ⊗_{T_{c+d}} C_{b,c+d}) ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}`
  (left-associated, recast coefficients — the landing of `E3`).

Two legs, no signs:

* the associator: `Q4l = B_R(b,c,d) ⊗_{T_{b+(c+d)}} C_{a,b+(c+d)}
  ≃ Q4r` (`q4lAssoc` — all balancings canonical, the first factor is
  literally the canonical `B_R(b,c,d)`);
* the coefficient recast `q4Recast : Q4l ≃ Q4`: identity on
  `B_R(b,c,d)`, the column cast `C_{a,b+(c+d)} ≃ C_{a,(b+c)+d}` on
  the second factor.  Balancedness on the `Q4` side is the defining
  property of the recast right action (M8a-8c′-0), on the `Q4l` side
  the cast-compatibility of the column's second-slot action
  (`columnCast_symm_rslot` — a `subst`-`refl` fact).
-/
import Superfusion.Bimod.QuadEdge5

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-- The left-associated, natural-coefficient presentation of the
`a(b(cd))`-vertex: `B_R(b,c,d) ⊗_{T_{b+(c+d)}} C_{a,b+(c+d)}` (all
balancings canonical). -/
def Q4l : Type _ :=
  RelTensor K (stdTower (K := K) (b + (c + d))).carrier (BR K b c d)
    (TowerColumn K a (b + (c + d)))

noncomputable instance : AddCommGroup (Q4l K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (b + (c + d))).carrier (BR K b c d)
      (TowerColumn K a (b + (c + d)))))

noncomputable instance : Module K (Q4l K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (b + (c + d))).carrier (BR K b c d)
      (TowerColumn K a (b + (c + d)))))

/-! ### The associator leg -/

/-- The associator at the `a(b(cd))`-vertex: the left-associated
natural form re-associates to `Q4r`. -/
noncomputable def q4lAssoc : Q4l K a b c d ≃ₗ[K] Q4r K a b c d :=
  RelTensor.assoc K (stdTower (K := K) (c + d)).carrier
    (stdTower (K := K) (b + (c + d))).carrier
    (TowerColumn K c d) (TowerColumn K b (c + d))
    (TowerColumn K a (b + (c + d)))

theorem q4lAssoc_mk (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d))) :
    q4lAssoc K a b c d
        (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (BR K b c d) (TowerColumn K a (b + (c + d)))
          (BR.mk K b c d v u) w)
      = RelTensor.mk K (stdTower (K := K) (c + d)).carrier
          (TowerColumn K c d) (BR K a b (c + d)) v
          (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
            (TowerColumn K b (c + d)) (TowerColumn K a (b + (c + d)))
            u w) :=
  RelTensor.assoc_mk K (stdTower (K := K) (c + d)).carrier
    (stdTower (K := K) (b + (c + d))).carrier
    (TowerColumn K c d) (TowerColumn K b (c + d))
    (TowerColumn K a (b + (c + d))) v u w

/-! ### The recast leg -/

/-- The forward bilinear of the recast leg:
`(m, v) ↦ m ⊗ (columnCast v)`. -/
private noncomputable def closeFwdBilin :
    BR K b c d →ₗ[K] TowerColumn K a (b + (c + d)) →ₗ[K] Q4 K a b c d :=
  (RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier (BR K b c d)
    (TowerColumn K a ((b + c) + d))).compl₂
    (columnCast K a (add_assoc b c d).symm).toLinearMap

private theorem closeFwdBilin_apply (m : BR K b c d)
    (v : TowerColumn K a (b + (c + d))) :
    closeFwdBilin K a b c d m v
      = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d)) m
          (columnCast K a (add_assoc b c d).symm v) :=
  rfl

/-- Balancedness of the forward leg: the natural balancing of `Q4l`
maps to the recast balancing of `Q4` through the tower cast. -/
private theorem closeFwd_balanced :
    RelTensor.IsBalanced (stdTower (K := K) (b + (c + d))).carrier
      (closeFwdBilin K a b c d) := by
  intro β m v
  rw [closeFwdBilin_apply, closeFwdBilin_apply, columnCast_symm_rslot,
    show (MulOpposite.op β • m : BR K b c d)
        = MulOpposite.op ((stdTowerCast (K := K)
            (add_assoc b c d)).toAlgEquiv.symm β) • m from by
      rw [BR.recast_op_smul_def, AlgEquiv.apply_symm_apply],
    RelTensor.mk_op_smul]

/-- The backward bilinear of the recast leg:
`(m, w) ↦ m ⊗ (columnCast⁻¹ w)`. -/
private noncomputable def closeBwdBilin :
    BR K b c d →ₗ[K] TowerColumn K a ((b + c) + d) →ₗ[K]
      Q4l K a b c d :=
  (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
    (BR K b c d) (TowerColumn K a (b + (c + d)))).compl₂
    (columnCast K a (add_assoc b c d).symm).symm.toLinearMap

private theorem closeBwdBilin_apply (m : BR K b c d)
    (w : TowerColumn K a ((b + c) + d)) :
    closeBwdBilin K a b c d m w
      = RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (BR K b c d) (TowerColumn K a (b + (c + d))) m
          ((columnCast K a (add_assoc b c d).symm).symm w) :=
  rfl

/-- Balancedness of the backward leg: the recast balancing of `Q4`
maps to the natural balancing of `Q4l` through the tower cast. -/
private theorem closeBwd_balanced :
    RelTensor.IsBalanced (stdTower (K := K) (b + c + d)).carrier
      (closeBwdBilin K a b c d) := by
  intro t m w
  rw [closeBwdBilin_apply, closeBwdBilin_apply,
    columnCast_symm_symm_rslot, BR.recast_op_smul_def,
    RelTensor.mk_op_smul]

private noncomputable def closeFwd : Q4l K a b c d →ₗ[K] Q4 K a b c d :=
  RelTensor.lift (closeFwdBilin K a b c d) (closeFwd_balanced K a b c d)

private noncomputable def closeBwd : Q4 K a b c d →ₗ[K] Q4l K a b c d :=
  RelTensor.lift (closeBwdBilin K a b c d) (closeBwd_balanced K a b c d)

private theorem closeFwd_mk (m : BR K b c d)
    (v : TowerColumn K a (b + (c + d))) :
    closeFwd K a b c d
        (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (BR K b c d) (TowerColumn K a (b + (c + d))) m v)
      = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d)) m
          (columnCast K a (add_assoc b c d).symm v) := by
  show RelTensor.lift (closeFwdBilin K a b c d)
      (closeFwd_balanced K a b c d)
      (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
        (BR K b c d) (TowerColumn K a (b + (c + d))) m v) = _
  rw [RelTensor.lift_mk, closeFwdBilin_apply]

private theorem closeBwd_mk (m : BR K b c d)
    (w : TowerColumn K a ((b + c) + d)) :
    closeBwd K a b c d
        (RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d)) m w)
      = RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (BR K b c d) (TowerColumn K a (b + (c + d))) m
          ((columnCast K a (add_assoc b c d).symm).symm w) := by
  show RelTensor.lift (closeBwdBilin K a b c d)
      (closeBwd_balanced K a b c d)
      (RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
        (BR K b c d) (TowerColumn K a ((b + c) + d)) m w) = _
  rw [RelTensor.lift_mk, closeBwdBilin_apply]

private theorem closeFwd_closeBwd :
    (closeFwd K a b c d).comp (closeBwd K a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun m w => ?_
  show closeFwd K a b c d (closeBwd K a b c d
      (RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
        (BR K b c d) (TowerColumn K a ((b + c) + d)) m w))
    = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
        (BR K b c d) (TowerColumn K a ((b + c) + d)) m w
  rw [closeBwd_mk, closeFwd_mk, LinearEquiv.apply_symm_apply]

private theorem closeBwd_closeFwd :
    (closeBwd K a b c d).comp (closeFwd K a b c d) = LinearMap.id := by
  refine RelTensor.hom_ext fun m v => ?_
  show closeBwd K a b c d (closeFwd K a b c d
      (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
        (BR K b c d) (TowerColumn K a (b + (c + d))) m v))
    = RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
        (BR K b c d) (TowerColumn K a (b + (c + d))) m v
  rw [closeFwd_mk, closeBwd_mk, LinearEquiv.symm_apply_apply]

/-- **The coefficient recast** `Q4l ≃ Q4`: identity on `B_R(b,c,d)`,
the column cast on the second factor. -/
noncomputable def q4Recast : Q4l K a b c d ≃ₗ[K] Q4 K a b c d :=
  LinearEquiv.ofLinear (closeFwd K a b c d) (closeBwd K a b c d)
    (closeFwd_closeBwd K a b c d) (closeBwd_closeFwd K a b c d)

theorem q4Recast_mk (m : BR K b c d)
    (v : TowerColumn K a (b + (c + d))) :
    q4Recast K a b c d
        (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (BR K b c d) (TowerColumn K a (b + (c + d))) m v)
      = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d)) m
          (columnCast K a (add_assoc b c d).symm v) := by
  exact closeFwd_mk K a b c d m v

/-! ### The connector -/

/-- **Closing the bottom route**: the connector between the two
presentations of the `a(b(cd))`-vertex — the associator followed by
the coefficient recast.  Both pentagon routes now land in `Q4`. -/
noncomputable def q4Close : Q4r K a b c d ≃ₗ[K] Q4 K a b c d :=
  (q4lAssoc K a b c d).symm.trans (q4Recast K a b c d)

/-- The generator formula of the connector (no signs). -/
theorem q4Close_mk (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d))) :
    q4Close K a b c d
        (RelTensor.mk K (stdTower (K := K) (c + d)).carrier
          (TowerColumn K c d) (BR K a b (c + d)) v
          (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
            (TowerColumn K b (c + d)) (TowerColumn K a (b + (c + d)))
            u w))
      = RelTensor.mk K (stdTower (K := K) (b + c + d)).carrier
          (BR K b c d) (TowerColumn K a ((b + c) + d))
          (BR.mk K b c d v u)
          (columnCast K a (add_assoc b c d).symm w) := by
  show q4Recast K a b c d ((q4lAssoc K a b c d).symm
      (RelTensor.mk K (stdTower (K := K) (c + d)).carrier
        (TowerColumn K c d) (BR K a b (c + d)) v
        (RelTensor.mk K (stdTower (K := K) (b + (c + d))).carrier
          (TowerColumn K b (c + d)) (TowerColumn K a (b + (c + d)))
          u w))) = _
  rw [← q4lAssoc_mk, LinearEquiv.symm_apply_apply, q4Recast_mk]

end PentagonB

end Bimod

end Superfusion
