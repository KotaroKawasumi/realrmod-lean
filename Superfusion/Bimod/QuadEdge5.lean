/-
Superfusion / Bimod / QuadEdge5

Milestone M8a-8c′-1b-vii (roadmap v3): **the fifth pentagon edge**
(the second leg of the bottom route).  The middle swap (1b-vi)
applied to the two-sided fusion `Q5` exposes the canonical
`B_L(a,b,c{+}d)` as the inner factor:

  `Q5 = C_{a,b} ⊗_{T_{a+b}} (C_{c,d} ⊗_{T_{c+d}} C_{a+b,c+d})
      ≃ C_{c,d} ⊗_{T_{c+d}} (C_{a,b} ⊗_{T_{a+b}} C_{a+b,c+d})
      = C_{c,d} ⊗_{T_{c+d}} B_L(a,b,c{+}d)`      (`q5Swap`),

with the sign `(-1)^{|u||v|}` on generators.  The `MidSignLaw`
hypotheses of the swap are discharged by the generator sign laws of
the route bimodules (`BR.aslot_smul_mk_of_mem` for the source
balancing, `BL.cslot_smul_mk_of_mem` for the target), carried across
the synonym boundary by `inferInstanceAs` bridges.  The fifth edge is
then the signed amplification of a canonical triple intertwiner
`t₅ : B_L(a,b,c{+}d) → B_R(a,b,c{+}d)`:

  `E5 t₅ = (id ⊗_signed t₅) ∘ q5Swap : Q5 → Q4r`,

landing in `Q4r = C_{c,d} ⊗_{T_{c+d}} B_R(a,b,c{+}d)` — the
right-associated presentation of the `a(b(cd))`-vertex (its
reconciliation with `Q4` belongs to the χ-milestone, where the common
Hom space of the two routes is fixed).  The `T_{c+d}`-equivariance
datum of `t₅`: on the source the signed middle action of `B_L` (its
`(c{+}d)`-slot), on the target the outer slot action of `B_R`.
-/
import Superfusion.Bimod.QuadEdge4
import Superfusion.Bimod.MiddleSwap

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### Synonym bridges for the middle swap -/

/-- `inferInstanceAs` bridge: the signed middle `T_{a+b}`-action of
`B_R(a{+}b,c,d)` in the raw `RelTensor` spelling (the inner factor of
`Q5` as the middle swap sees it). -/
noncomputable instance : Module (stdTower (K := K) (a + b)).carrier
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (TowerColumn K (a + b) (c + d))) :=
  inferInstanceAs
    (Module (stdTower (K := K) (a + b)).carrier (BR K (a + b) c d))

/-- `inferInstanceAs` bridge: the signed middle `T_{c+d}`-action of
`B_L(a,b,c{+}d)` in the raw `RelTensor` spelling (the inner factor of
the swapped vertex). -/
noncomputable instance : Module (stdTower (K := K) (c + d)).carrier
    (RelTensor K (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) (c + d))) :=
  inferInstanceAs
    (Module (stdTower (K := K) (c + d)).carrier (BL K a b (c + d)))

/-- The sign law of the `Q5`-side balancing: the `T_{a+b}`-slot of
`B_R(a{+}b,c,d)` is a signed middle action. -/
private theorem q5LawA :
    MidSignLaw K (stdTower (K := K) (a + b)).carrier
      (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (TowerColumn K (a + b) (c + d))
      (stdTower (K := K) (a + b)).grading (TowerColumn.grading K c d) := by
  intro l i x hx n hn p
  exact BR.aslot_smul_mk_of_mem K (a + b) c d hx hn p

/-- The sign law of the swapped-side balancing: the `T_{c+d}`-slot of
`B_L(a,b,c{+}d)` is a signed middle action. -/
private theorem q5LawB :
    MidSignLaw K (stdTower (K := K) (c + d)).carrier
      (stdTower (K := K) (a + b)).carrier (TowerColumn K a b)
      (TowerColumn K (a + b) (c + d))
      (stdTower (K := K) (c + d)).grading (TowerColumn.grading K a b) := by
  intro l i z hz m hm p
  exact BL.cslot_smul_mk_of_mem K a b (c + d) hz hm p

/-! ### The swapped vertex and the swap -/

/-- The swapped presentation of the `(ab)(cd)`-vertex: the middle
swap exposes the canonical `B_L(a,b,c{+}d)`. -/
def Q5s : Type _ :=
  RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
    (BL K a b (c + d))

noncomputable instance : AddCommGroup (Q5s K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BL K a b (c + d))))

noncomputable instance : Module K (Q5s K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BL K a b (c + d))))

/-- **The middle swap at the `(ab)(cd)`-vertex**: the direct
instantiation of `midSwap` at the tower columns. -/
noncomputable def q5Swap : Q5 K a b c d ≃ₗ[K] Q5s K a b c d :=
  midSwap K (stdTower (K := K) (a + b)).carrier
    (stdTower (K := K) (c + d)).carrier (TowerColumn K a b)
    (TowerColumn K c d) (TowerColumn K (a + b) (c + d))
    (stdTower (K := K) (a + b)).grading
    (stdTower (K := K) (c + d)).grading
    (TowerColumn.grading K a b) (TowerColumn.grading K c d)
    (q5LawA K a b c d) (q5LawB K a b c d)

/-- The sign law of the swap on homogeneous generators:
`u ⊗ (v ⊗ w) ↦ (-1)^{|u||v|} v ⊗ (u ⊗ w)`. -/
theorem q5Swap_mk_of_mem {i j : ZMod 2} {v : TowerColumn K c d}
    {u : TowerColumn K a b} (hv : v ∈ TowerColumn.grading K c d i)
    (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    q5Swap K a b c d
        (RelTensor.mk K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (BR K (a + b) c d) u
          (BR.mk K (a + b) c d v w))
      = ((sgn (i * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (stdTower (K := K) (c + d)).carrier
            (TowerColumn K c d) (BL K a b (c + d)) v
            (BL.mk K a b (c + d) u w) :=
  midSwap_mk_of_mem K (stdTower (K := K) (a + b)).carrier
    (stdTower (K := K) (c + d)).carrier (TowerColumn K a b)
    (TowerColumn K c d) (TowerColumn K (a + b) (c + d))
    (stdTower (K := K) (a + b)).grading
    (stdTower (K := K) (c + d)).grading
    (TowerColumn.grading K a b) (TowerColumn.grading K c d)
    (q5LawA K a b c d) (q5LawB K a b c d) hv hu w

/-! ### The fifth edge -/

/-- The landing of the fifth edge: the right-associated presentation
`C_{c,d} ⊗_{T_{c+d}} B_R(a,b,c{+}d)` of the `a(b(cd))`-vertex.  Its
reconciliation with `Q4` belongs to the χ-milestone. -/
def Q4r : Type _ :=
  RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
    (BR K a b (c + d))

noncomputable instance : AddCommGroup (Q4r K a b c d) :=
  inferInstanceAs (AddCommGroup
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d))))

noncomputable instance : Module K (Q4r K a b c d) :=
  inferInstanceAs (Module K
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d))))

/-- **The fifth pentagon edge** `E5 t₅ = (id ⊗_signed t₅) ∘ q5Swap`,
for a canonical triple intertwiner `t₅ : B_L(a,b,c+d) → B_R(a,b,c+d)`
of parity `e`, super-equivariant for the `(c+d)`-slot (the signed
middle action on the source, the outer slot action on the target). -/
noncomputable def E5 (e : ZMod 2)
    (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i →
      ∀ n : BL K a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n)) :
    Q5 K a b c d →ₗ[K] Q4r K a b c d :=
  (smap (stdTower (K := K) (c + d)).grading (TowerColumn.grading K c d)
    t₅ e ht₅).comp (q5Swap K a b c d).toLinearMap

/-- The generator formula of the fifth edge, on homogeneous first and
second slots: `u ⊗ (v ⊗ w) ↦ (-1)^{|v|(e+|u|)} v ⊗ t₅(u ⊗ w)`. -/
theorem E5_mk_of_mem (e : ZMod 2)
    (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i →
      ∀ n : BL K a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))
    {i j : ZMod 2} {v : TowerColumn K c d} {u : TowerColumn K a b}
    (hv : v ∈ TowerColumn.grading K c d i)
    (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅
        (RelTensor.mk K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (BR K (a + b) c d) u
          (BR.mk K (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          RelTensor.mk K (stdTower (K := K) (c + d)).carrier
            (TowerColumn K c d) (BR K a b (c + d)) v
            (t₅ (BL.mk K a b (c + d) u w)) := by
  show (smap (stdTower (K := K) (c + d)).grading
      (TowerColumn.grading K c d) t₅ e ht₅)
      (q5Swap K a b c d
        (RelTensor.mk K (stdTower (K := K) (a + b)).carrier
          (TowerColumn K a b) (BR K (a + b) c d) u
          (BR.mk K (a + b) c d v w))) = _
  have sign_id : ∀ e i j : ZMod 2, i * j + e * i = i * (e + j) := by
    decide
  rw [q5Swap_mk_of_mem K a b c d hv hu w, map_zsmul,
    smap_mk_of_mem (stdTower (K := K) (c + d)).grading
      (TowerColumn.grading K c d) t₅ e ht₅ hv,
    smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

end PentagonB

end Bimod

end Superfusion
