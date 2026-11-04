/-
Superfusion / Bimod / EdgeEquiv4

Milestone M8a-8c′-2b-ii (roadmap v3, fourth block): **equivariance of
the fourth pentagon edge** `E4 t₄ = (id ⊗_signed t₄) ∘ q1Assoc : Q1 →
Q5`, for a canonical triple intertwiner `t₄ : B_L(a{+}b,c,d) →
B_R(a{+}b,c,d)` of parity `e`, `(a{+}b)`-slot super-equivariant
(`ht₄`, folded into `E4`'s own construction via `smap`).  As with `E2`
(second block, `EdgeEquiv2.lean`) and `E3` (third block,
`EdgeEquiv3.lean`), the associator `q1Assoc` is folded into `E4`'s
generator formula (`E4_mk_of_mem`), so `End`-descent does not apply;
every transport below is closed at the generator level
`Q1.mk (BL.mk u v) w`, `u` homogeneous, by unfolding through `Q1`'s
and `Q5`'s own slot laws (M8a-8c′-2a″) together with the slot laws of
`B_L(a,b,c)` and of `t₄`'s own domain/codomain `B_L(a{+}b,c,d)`,
`B_R(a{+}b,c,d)` (M8a-7c-3) — unlike `E3`, no `Q3Inner`-style synonym
bridging is needed here, since `Q1`'s and `Q5`'s factor types are
literally `B_L(a,b,c)` and `B_R(a{+}b,c,d)`, matching `t₄`'s own
domain/codomain exactly:

* the `a`, `b`-slots (through the exposed `TowerColumn K a b` factor,
  after `q1Assoc`): `B_L(a{+}b,c,d)`/`B_R(a{+}b,c,d)` carry no direct
  `T_a`- or `T_b`-action at all (only the *combined* `(a{+}b)`-slot
  does — the *spectator* pattern), and `Q1`'s own `a`, `b`-slots (via
  `B_L(a,b,c)`'s outer left action) and `Q5`'s own `a`, `b`-slots (via
  the exposed column's outer left action) are both *direct*, so the
  only sign is the amplification's own `(-1)^{ek}` (mirroring `E2`'s
  `b`, `c`-slot pattern / `E3`'s `comp_aslot`, `comp_bslot`);
* the `c`-slot (`t₄`'s own domain/codomain: the *direct* outer
  `b`-position of `B_L(a{+}b,c,d)`/`B_R(a{+}b,c,d)`, but the *signed*
  middle slot of both `Q1` — through `B_L(a,b,c)`'s own `c`-slot — and
  of `Q5` — its own `c`-slot, mid-of-mid): the two Koszul signs, both
  keyed to the *same* pair `(k,j)` for the amplification's `c`-degree
  `k` against `u`'s degree `j`, cancel exactly, leaving only `t₄`'s own
  equivariance scalar (`comp_cslot`, `ht₄C`-conditional — a clean
  cancellation with no residual, mirroring `E3`'s `comp_dslot`);
* the `d`-slot (`t₄`'s own domain/codomain: the *signed* middle
  `c`-position of `B_L(a{+}b,c,d)`/`B_R(a{+}b,c,d)`, keyed to `v`'s
  degree `jv`; on `Q1` it is the *outer* mid-of-mid sign keyed to the
  *full* `B_L(a,b,c)`-degree `j+jv`; on `Q5` it is the *outer*
  mid-of-mid sign keyed to `u`'s degree `j` alone): the three Koszul
  signs `(-1)^{m(j+jv)}`, `(-1)^{mjv}`, `(-1)^{mj}` combine to
  `(-1)^{2m(j+jv)} = 1` and cancel exactly, leaving only `t₄`'s own
  equivariance scalar (`comp_dslot`, `ht₄D`-conditional — again a
  clean cancellation, mirroring `E3`'s `comp_dslot` but with a
  three-fold rather than two-fold sign combination);
* the right action: along the recast `T_{a+b+c+d} ≅ T_{a+b+(c+d)}` of
  the total coefficient algebra (`stdTowerCast`, M8a-8c′-0's device) —
  `B_L(a{+}b,c,d)`'s own right-coefficient tower is literally
  `T_{a+b+c+d}` (matching `Q1`'s outer right action exactly, no cast
  needed *there*), while `B_R(a{+}b,c,d)`'s is `T_{a+b+(c+d)}`
  (matching `Q5`'s), so the cast lands on `t₄`'s own right-equivariance
  (`ht₄R`), exactly mirroring `E2`'s `comp_right` pattern (deviating
  from `E3`, whose right-coefficient towers matched syntactically on
  both ends with no cast at all);
* the grading: `t₄`'s own degree-`e` homogeneity (`ht₄deg`) threading
  through `E4_mk_of_mem` exactly as `E3`'s `ht₃deg` did.
-/
import Superfusion.Bimod.QuadEdge4
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

namespace E4

variable (e : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
  x ∈ (stdTower (K := K) (a + b)).grading i →
  ∀ n : BL K (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- `E4_mk_of_mem`, restated through the synonym-valued `mk`s of `Q1`
and `Q5` (the track's discipline) — bridges the raw `RelTensor.mk`
spelling of `E4_mk_of_mem` to the generator lemmas of `Q1` and `Q5`,
by `rfl` (`Q1.mk`, `Q5.mk` unfold to `RelTensor.mk`). -/
private theorem E4_mk_of_mem' {j : ZMod 2} {u : TowerColumn K a b}
    (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄ (Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          Q5.mk K a b c d u (t₄ (BL.mk K (a + b) c d v w)) :=
  E4_mk_of_mem K a b c d e t₄ ht₄ hu v w

/-- The `ZMod 2`-arithmetic fact behind the exact squared-sign
cancellations (`comp_cslot`'s single cancellation, `comp_dslot`'s two
intermediate ones): doubling a product of degrees is always `0`. -/
private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

/-- The `ZMod 2`-arithmetic fact behind `comp_dslot`'s three-fold sign
cancellation: `Q1`'s outer sign (keyed to the full `j+jv`) combines
with `B_L(a{+}b,c,d)`'s own sign (keyed to `jv`) and `Q5`'s own sign
(keyed to `j`) to `0`. -/
private theorem zmod2_dslot_deg : ∀ m j jv : ZMod 2,
    m * (j + jv) + m * jv + m * j = 0 := by decide

/-- `E4` transports the `a`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot: `B_L(a{+}b,c,d)`/`B_R(a{+}b,c,d)`
carry no `T_a`-action at all (only the *combined* `(a{+}b)`-slot
does), and `Q1`'s, `B_L(a,b,c)`'s and `Q5`'s own `a`-slots are all
*direct*, so the only sign is the amplification's own `(-1)^{ek}`
(mirroring `E2`'s `b`, `c`-slot pattern). -/
theorem comp_aslot {k j : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄ (x • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (x • E4 K a b c d e t₄ ht₄
            (Q1.mk K a b c d (BL.mk K a b c u v) w)) := by
  have hL : E4 K a b c d e t₄ ht₄ (x • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * (k + j)) : ℤˣ) : ℤ) •
          Q5.mk K a b c d (x • u) (t₄ (BL.mk K (a + b) c d v w)) := by
    rw [Q1.aslot_smul_mk, BL.aslot_smul_mk]
    exact E4_mk_of_mem' K a b c d e t₄ ht₄
      ((vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hx hu) v w
  rw [hL, E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w, smul_comm x, Q5.aslot_smul_mk,
    smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `E4` transports the `b`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot, exactly parallel to `comp_aslot`
(neither `B_L(a{+}b,c,d)` nor `B_R(a{+}b,c,d)` carries a direct
`T_b`-action, and `Q1`'s, `B_L(a,b,c)`'s and `Q5`'s own `b`-slots are
all *direct*). -/
theorem comp_bslot {k j : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄ (y • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (y • E4 K a b c d e t₄ ht₄
            (Q1.mk K a b c d (BL.mk K a b c u v) w)) := by
  have hL : E4 K a b c d e t₄ ht₄ (y • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * (k + j)) : ℤˣ) : ℤ) •
          Q5.mk K a b c d (y • u) (t₄ (BL.mk K (a + b) c d v w)) := by
    rw [Q1.bslot_smul_mk, BL.bslot_smul_mk]
    exact E4_mk_of_mem' K a b c d e t₄ ht₄
      ((vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hy hu) v w
  rw [hL, E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w, smul_comm y, Q5.bslot_smul_mk,
    smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `E4` transports the `c`-slot up to `t₄`'s own equivariance scalar
`s` for it — `T_c` is the *direct* outer `b`-position of both
`B_L(a{+}b,c,d)` and `B_R(a{+}b,c,d)`, but the *signed* middle slot of
`Q1` (through `B_L(a,b,c)`'s own `c`-slot) and of `Q5` (its own
`c`-slot), both keyed to the *same* pair `(k,j)`: the two Koszul signs
cancel exactly, leaving only `t₄`'s own equivariance scalar (a clean
cancellation with no residual, mirroring `E3`'s `comp_dslot`). -/
theorem comp_cslot {s : ℤ} {k j : ZMod 2}
    {z : (stdTower (K := K) c).carrier}
    (hz : z ∈ (stdTower (K := K) c).grading k)
    (ht₄C : ∀ n : BL K (a + b) c d, t₄ (z • n) = s • (z • t₄ n))
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄ (z • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = s • (z • E4 K a b c d e t₄ ht₄
          (Q1.mk K a b c d (BL.mk K a b c u v) w)) := by
  have h1 : z • Q1.mk K a b c d (BL.mk K a b c u v) w
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          Q1.mk K a b c d (BL.mk K a b c u (z • v)) w := by
    rw [Q1.cslot_smul_mk, BL.cslot_smul_mk_of_mem K a b c hz hu]
    simp only [map_zsmul, LinearMap.smul_apply]
  have h2 : E4 K a b c d e t₄ ht₄
      (Q1.mk K a b c d (BL.mk K a b c u (z • v)) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          (s • Q5.mk K a b c d u (z • t₄ (BL.mk K (a + b) c d v w))) := by
    rw [E4_mk_of_mem' K a b c d e t₄ ht₄ hu (z • v) w, ← BL.bslot_smul_mk, ht₄C]
    simp only [map_zsmul]
  have h3 : Q5.mk K a b c d u (z • t₄ (BL.mk K (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (z • Q5.mk K a b c d u (t₄ (BL.mk K (a + b) c d v w))) := by
    rw [Q5.cslot_smul_mk_of_mem K a b c d hz hu, smul_smul, ← Units.val_mul, ← sgn_add,
      zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have hkey : ((sgn (k * j) : ℤˣ) : ℤ) * ((sgn (k * j) : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one]
  rw [h1, map_zsmul, h2, h3, E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w, smul_comm z]
  simp only [smul_smul]
  congr 1
  linear_combination (s * ((sgn (e * j) : ℤˣ) : ℤ)) * hkey

/-- `E4` transports the `d`-slot up to `t₄`'s own equivariance scalar
`s'` for it — `T_d` is the *signed* middle `c`-position of both
`B_L(a{+}b,c,d)` and `B_R(a{+}b,c,d)`: the three Koszul signs of `Q1`
(keyed to the *full* `B_L(a,b,c)`-degree `j+jv`), of `B_L(a{+}b,c,d)`'s
own `d`-slot (keyed to `v`'s degree `jv`) and of `Q5` (keyed to `u`'s
degree `j`) combine to `(-1)^{2m(j+jv)} = 1` and cancel exactly,
leaving only `t₄`'s own equivariance scalar (a clean cancellation with
no residual, mirroring `E3`'s `comp_dslot`). -/
theorem comp_dslot {s' : ℤ} {m j jv : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₄D : ∀ n : BL K (a + b) c d, t₄ (τ • n) = s' • (τ • t₄ n))
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    {v : TowerColumn K (a + b) c} (hv : v ∈ TowerColumn.grading K (a + b) c jv)
    (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄ (τ • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = s' • (τ • E4 K a b c d e t₄ ht₄
          (Q1.mk K a b c d (BL.mk K a b c u v) w)) := by
  have h1 : τ • Q1.mk K a b c d (BL.mk K a b c u v) w
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) •
          Q1.mk K a b c d (BL.mk K a b c u v) (τ • w) :=
    Q1.dslot_smul_mk_of_mem K a b c d hτ (BL.mk_mem_grading K a b c hu hv) w
  have h2 : BL.mk K (a + b) c d v (τ • w)
      = ((sgn (m * jv) : ℤˣ) : ℤ) • (τ • BL.mk K (a + b) c d v w) := by
    rw [BL.cslot_smul_mk_of_mem K (a + b) c d hτ hv, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have h3 : Q5.mk K a b c d u (τ • t₄ (BL.mk K (a + b) c d v w))
      = ((sgn (m * j) : ℤˣ) : ℤ) •
          (τ • Q5.mk K a b c d u (t₄ (BL.mk K (a + b) c d v w))) := by
    rw [Q5.dslot_smul_mk_of_mem K a b c d hτ hu, smul_smul, ← Units.val_mul, ← sgn_add,
      zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have h4 : E4 K a b c d e t₄ ht₄
      (Q1.mk K a b c d (BL.mk K a b c u v) (τ • w))
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          (((sgn (m * jv) : ℤˣ) : ℤ) •
            (s' • Q5.mk K a b c d u (τ • t₄ (BL.mk K (a + b) c d v w)))) := by
    rw [E4_mk_of_mem' K a b c d e t₄ ht₄ hu v (τ • w), h2]
    simp only [map_zsmul]
    rw [ht₄D]
    simp only [map_zsmul]
  have hkey3 : ((sgn (m * (j + jv)) : ℤˣ) : ℤ) * ((sgn (m * jv) : ℤˣ) : ℤ) *
      ((sgn (m * j) : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_dslot_deg,
      sgn_zero, Units.val_one]
  rw [h1, map_zsmul, h4, h3, E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w, smul_comm τ]
  simp only [smul_smul]
  congr 1
  linear_combination (s' * ((sgn (e * j) : ℤˣ) : ℤ)) * hkey3

/-- The associativity recast of the total coefficient algebra used by
`comp_right`: `B_L(a{+}b,c,d)`'s own right-coefficient tower is
literally `T_{a+b+c+d}` (matching `Q1`'s outer right action exactly),
while `B_R(a{+}b,c,d)`'s is `T_{a+b+(c+d)}` (matching `Q5`'s), so the
cast lands on `t₄`'s own right-equivariance (`ht₄R`). -/
private theorem right_recast_eq : a + b + c + d = a + b + (c + d) := by ring

/-- `E4` transports the right action along the recast
`T_{a+b+c+d} ≅ T_{a+b+(c+d)}` (`stdTowerCast`, M8a-8c′-0's device) —
conditional on `t₄`'s own right-equivariance for it (its domain's
right tower already matches `Q1`'s outer one exactly, so no cast is
needed on the source side of `ht₄R`). -/
theorem comp_right {j : ZMod 2}
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht₄R : ∀ n : BL K (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((stdTowerCast (K := K)
              (right_recast_eq a b c d)).toAlgEquiv τ) • t₄ n)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (v : TowerColumn K (a + b) c) (w : TowerColumn K ((a + b) + c) d) :
    E4 K a b c d e t₄ ht₄
        (MulOpposite.op τ • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = MulOpposite.op ((stdTowerCast (K := K)
            (right_recast_eq a b c d)).toAlgEquiv τ)
          • E4 K a b c d e t₄ ht₄
              (Q1.mk K a b c d (BL.mk K a b c u v) w) := by
  have hL : E4 K a b c d e t₄ ht₄
      (MulOpposite.op τ • Q1.mk K a b c d (BL.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          Q5.mk K a b c d u
            (MulOpposite.op ((stdTowerCast (K := K)
                  (right_recast_eq a b c d)).toAlgEquiv τ)
              • t₄ (BL.mk K (a + b) c d v w)) := by
    rw [Q1.right_smul_mk,
      E4_mk_of_mem' K a b c d e t₄ ht₄ hu v (MulOpposite.op τ • w),
      ← BL.right_smul_mk, ht₄R]
  rw [hL, E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w, smul_comm
    (MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq a b c d)).toAlgEquiv τ)),
    Q5.right_smul_mk]

/-- `E4` is homogeneous of `t₄`'s degree `e` — the analogue of `E3`'s
`mem_grading`, `t₄`'s own homogeneity (`ht₄deg`) threading through
`E4_mk_of_mem` exactly as there. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₄deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K (a + b) c d j',
      t₄ n ∈ BR.grading K (a + b) c d (j' + e))
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    {v : TowerColumn K (a + b) c} (hv : v ∈ TowerColumn.grading K (a + b) c jv)
    {w : TowerColumn K ((a + b) + c) d}
    (hw : w ∈ TowerColumn.grading K ((a + b) + c) d jw) :
    E4 K a b c d e t₄ ht₄ (Q1.mk K a b c d (BL.mk K a b c u v) w)
      ∈ Q5.grading K a b c d (j + (jv + jw + e)) := by
  rw [E4_mk_of_mem' K a b c d e t₄ ht₄ hu v w]
  refine zsmul_mem ?_ _
  exact Q5.mk_mem_grading K a b c d hu
    (ht₄deg (jv + jw) _ (BL.mk_mem_grading K (a + b) c d hv hw))

end E4

end PentagonB

end Bimod

end Superfusion
