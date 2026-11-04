/-
Superfusion / Bimod / EdgeEquiv2

Milestone M8a-8c′-2b-ii (roadmap v3, second block): **equivariance of
the second pentagon edge** `E2 t₂ = (id_{C_{b,c}} ⊗_signed t₂) ∘
q2Assoc : Q2 → Q3`.  Unlike `E1` (first block, `EdgeEquiv.lean`), `E2`
folds the associator `q2Assoc` into its own generator formula
(`E2_mk_of_mem`), so `End`-descent from a general
`RelTensor.map`/`smap` composition law does not apply (the METHOD note
of 2026-07-19): each transport is closed *at the generator level*
`Q2.mk (BR.mk u v) w` (`u` homogeneous where a sign is produced), by
unfolding through the slot laws of `B_R` (M8a-7c-3) and of both
endpoint vertices `Q2`, `Q3` (M8a-8c′-2a″) and substituting the
`E2_mk_of_mem` formula on each side (a "generator-∀ formulation" — the
WARNING-sanctioned alternative to a full `z : Q2`-universal statement,
since `E2_mk_of_mem` itself is only available at the generator level).

* the `b`, `c`-slots (through the exposed `C_{b,c}` factor): pass
  through with the amplification's own sign `(-1)^{e|y|}`
  (`smap_comp_leftActionEnd`'s prediction, confirmed here at the
  generator level — no extra hypothesis on `t₂` is needed, since these
  slots never touch `t₂`'s domain);
* the `a`, `d`-slots (through the inner `B_L(a,b+c,d)`-shaped factor,
  i.e. `t₂`'s own domain/codomain): the two mid-of-mid signs at `Q2`
  and `Q3` are the *same* Koszul sign (both keyed to `u`'s degree), so
  they cancel exactly, leaving only whatever extra equivariance `t₂`
  itself satisfies for that slot — supplied as an explicit hypothesis
  (`ht₂A`, `ht₂D`), mirroring `E1`'s `htA`/`htB`/`htC` pattern.  The
  `d`-slot additionally needs `v`'s own degree, since `Q2`'s
  middle-slot sign is keyed to the *combined* `B_R`-degree
  `|u| + |v|`, not `|u|` alone;
* the right action: plain, along the associativity recast
  `T_{a+b+c+d} ≅ T_{a+((b+c)+d)}` of the total coefficient algebra
  (`stdTowerCast`, M8a-8c′-0's device) — again conditional on `t₂`'s
  own right-equivariance (`ht₂R`);
* the grading: `t₂`'s own degree-`e` homogeneity (`ht₂deg`) transports
  through `E2_mk_of_mem` exactly as `E1`'s `hte` did.
-/
import Superfusion.Bimod.QuadEdge2b
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

namespace E2

variable (e : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i →
  ∀ n : Q2rInner K a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- `E2_mk_of_mem`, restated through the synonym-valued `mk`s of `Q2`,
`B_R` and `Q3` (the track's discipline) — bridges the raw
`RelTensor.mk` spelling of `E2_mk_of_mem` to the generator lemmas of
`Q2` and `Q3`, by `rfl` (`Q2.mk`, `Q3.mk` unfold to `RelTensor.mk`). -/
private theorem E2_mk_of_mem' {j : ZMod 2} {u : TowerColumn K b c}
    (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          Q3.mk K a b c d u
            (t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)) :=
  E2_mk_of_mem K a b c d e t₂ ht₂ hu v w

/-- `E2` transports the `b`-slot through the exposed `C_{b,c}` factor,
with the amplification's own sign — no extra hypothesis on `t₂` is
needed, since the `b`-slot never touches `t₂`'s domain. -/
theorem comp_bslot {i j : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (y • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (y • E2 K a b c d e t₂ ht₂
            (Q2.mk K a b c d (BR.mk K a b c u v) w)) := by
  have hL : E2 K a b c d e t₂ ht₂ (y • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * (i + j)) : ℤˣ) : ℤ) •
          Q3.mk K a b c d (y • u)
            (t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)) := by
    rw [Q2.bslot_smul_mk, BR.bslot_smul_mk]
    exact E2_mk_of_mem' K a b c d e t₂ ht₂
      ((vadd_eq_add i j) ▸ SetLike.GradedSMul.smul_mem hy hu) v w
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm y,
    Q3.bslot_smul_mk, smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `E2` transports the `c`-slot through the exposed `C_{b,c}` factor,
with the amplification's own sign. -/
theorem comp_cslot {i j : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading i)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (z0 • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (z0 • E2 K a b c d e t₂ ht₂
            (Q2.mk K a b c d (BR.mk K a b c u v) w)) := by
  have hL : E2 K a b c d e t₂ ht₂ (z0 • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * (i + j)) : ℤˣ) : ℤ) •
          Q3.mk K a b c d (z0 • u)
            (t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)) := by
    rw [Q2.cslot_smul_mk, BR.cslot_smul_mk]
    exact E2_mk_of_mem' K a b c d e t₂ ht₂
      ((vadd_eq_add i j) ▸ SetLike.GradedSMul.smul_mem hz0 hu) v w
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm z0,
    Q3.cslot_smul_mk, smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `E2` transports the `a`-slot up to `t₂`'s own equivariance scalar
`s` for it — the mid-of-mid Koszul signs of `Q2` and `Q3` (both keyed
to `u`'s degree `j`) cancel exactly, mirroring `E1`'s
`comp_aslot`/`comp_bslot`/`comp_cslot` pass-through pattern. -/
theorem comp_aslot {s : ℤ} {k j : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht₂A : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) (x • v) w)
        = s • (x • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (x • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = s • (x • E2 K a b c d e t₂ ht₂
            (Q2.mk K a b c d (BR.mk K a b c u v) w)) := by
  have hL : E2 K a b c d e t₂ ht₂ (x • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (k * j) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (s • Q3.mk K a b c d u
            (x • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))) := by
    rw [Q2.aslot_smul_mk, BR.aslot_smul_mk_of_mem K a b c hx hu, map_zsmul,
      LinearMap.smul_apply, map_zsmul,
      E2_mk_of_mem' K a b c d e t₂ ht₂ hu (x • v) w, ht₂A, map_zsmul]
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm x,
    Q3.aslot_smul_mk_of_mem K a b c d hx hu]
  simp only [smul_smul]
  congr 1
  ring

/-- `E2` transports the `d`-slot up to `t₂`'s own equivariance scalar
`s'` for it and a residual sign `(-1)^{m|v|}` — `Q2`'s middle-slot
sign is keyed to the *combined* `B_R`-degree `|u|+|v|` (not `|u|`
alone), while `Q3`'s is keyed to `|u|` alone, so one factor
`(-1)^{m|v|}` survives. -/
theorem comp_dslot {s' : ℤ} {m j jv : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₂D : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v (τ • w))
        = s' • (τ • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    {v : TowerColumn K a (b + c)} (hv : v ∈ TowerColumn.grading K a (b + c) jv)
    (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (m * jv) : ℤˣ) : ℤ) • s' •
          (τ • E2 K a b c d e t₂ ht₂
            (Q2.mk K a b c d (BR.mk K a b c u v) w)) := by
  have hL : E2 K a b c d e t₂ ht₂ (τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (s' • Q3.mk K a b c d u
            (τ • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))) := by
    rw [Q2.dslot_smul_mk_of_mem K a b c d hτ (BR.mk_mem_grading K a b c hu hv),
      map_zsmul, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v (τ • w), ht₂D, map_zsmul]
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm τ,
    Q3.dslot_smul_mk_of_mem K a b c d hτ hu, mul_add m j jv, sgn_add,
    Units.val_mul]
  simp only [smul_smul]
  congr 1
  ring

/-! ### The clean-form `d`-slot transport (M8a-8c′-2c-ii, part A)

`comp_dslot`'s residual sign `(-1)^{m|v|}` is an artifact of phrasing
`ht₂D` against the *raw* second-factor action `mk v (τ • w)`.
Rephrasing it against `Q2rInner`'s own **signed** `d`-slot action
(the `RelTensor.mk` shape of `B_L(a,b{+}c,d)`'s own `c`-position slot,
`τ • mk v w = (-1)^{|τ||v|} mk v (τ • w)` — `RouteBimod.lean`'s
`cslot_smul_mk_of_mem` convention, spelled out at `Q2rInner`'s own
tower index `T_{(a+b)+c}` rather than `B_L`'s literal `T_{a+(b+c)}`,
since the two are only *propositionally* equal) makes the residual
dissolve exactly: the sign contributed by unwinding `ht₂D'` cancels
against `comp_dslot`'s own `(-1)^{m|v|}`, leaving the clean,
component-independent conclusion `E2 (τ • z) = s' • (τ • E2 z)`. -/

/-- The right coefficient action of `TowerColumn K a (b+c)`, recast to
`T_{(a+b)+c}` (`RouteRecast.lean`'s device), is graded — the missing
`GradedRightSMul` instance needed to run `midAlgHom` at `Q2rInner`'s
own spelling of the tower index (mirroring `BR`'s own recast
`GradedRightSMul` instance, `RouteCompat.lean`). -/
instance Q2rInner.recast_gradedRightSMul :
    GradedRightSMul (stdTower (K := K) (a + b + c)).grading
      (TowerColumn.grading K a (b + c)) where
  smul_mem _ _ _ _ hτ hw := by
    rw [column_recast_op_smul_def]
    exact GradedRightSMul.smul_mem
      (stdTowerCast_mem_grading K (add_assoc a b c) hτ) hw

/-- `Q2rInner`'s own signed `d`-slot action, mirroring `Q1`'s `d`-slot
construction (`QuadActions.lean`) at `Q2rInner`'s own spelling of the
tower index `T_{(a+b)+c}`. -/
noncomputable instance Q2rInner.dslotModule : Module (stdTower (K := K) d).carrier
    (Q2rInner K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (a + b + c)).carrier
      (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d))
    ((midAlgHom (stdTower (K := K) (a + b + c)).grading
      (TowerColumn.grading K a (b + c)) (stdTower (K := K) d).grading
      (TowerColumn.superCommSMul K (a + b + c) d)).toRingHom)

/-- The sign law of `Q2rInner`'s own `d`-slot action: for homogeneous
`τ`, `v`, `τ • mk v w = (-1)^{|τ||v|} mk v (τ • w)`. -/
theorem Q2rInner.dslot_smul_of_mem {jv m : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    {v : TowerColumn K a (b + c)}
    (hv : v ∈ TowerColumn.grading K a (b + c) jv)
    (w : TowerColumn K (a + b + c) d) :
    τ • (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w
        : Q2rInner K a b c d)
      = ((sgn (m * jv) : ℤˣ) : ℤ) •
          (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v (τ • w)
          : Q2rInner K a b c d) :=
  midEnd_mk_of_mem (stdTower (K := K) (a + b + c)).grading
    (TowerColumn.grading K a (b + c)) (stdTower (K := K) d).grading
    (TowerColumn.superCommSMul K (a + b + c) d) hv hτ w

private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

/-- The `ZMod 2`-arithmetic fact behind `comp_dslot'`'s exact
cancellation: `Q2`'s outer sign (keyed to the combined degree
`j + jv`) combines with `Q2rInner`'s own sign (keyed to `jv`) to leave
exactly `Q3`'s own sign (keyed to `j` alone). -/
private theorem zmod2_dslot2_deg : ∀ m j jv : ZMod 2,
    m * (j + jv) + m * jv = m * j := by decide

/-- **The clean-form `d`-slot transport**: rephrased against
`Q2rInner`'s own signed `d`-slot action (`ht₂D'`), `E2`'s `d`-slot
transport is *component-independent* — `t₂`'s own equivariance scalar
`s'`, with no residual sign at all (the `(-1)^{m|v|}` of `comp_dslot`
dissolves exactly against the sign difference between the raw and
signed phrasings). -/
theorem comp_dslot' {s' : ℤ} {m j jv : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₂D' : ∀ x : Q2rInner K a b c d,
      t₂ (τ • x) = s' • (τ • t₂ x))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    {v : TowerColumn K a (b + c)} (hv : v ∈ TowerColumn.grading K a (b + c) jv)
    (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂ (τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = s' • (τ • E2 K a b c d e t₂ ht₂
          (Q2.mk K a b c d (BR.mk K a b c u v) w)) := by
  have hX : (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
        (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v (τ • w)
        : Q2rInner K a b c d)
      = ((sgn (m * jv) : ℤˣ) : ℤ) •
          (τ • (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w
            : Q2rInner K a b c d)) := by
    rw [Q2rInner.dslot_smul_of_mem K a b c d hτ hv, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have hL : E2 K a b c d e t₂ ht₂ (τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (((sgn (m * jv) : ℤˣ) : ℤ) •
            (s' • Q3.mk K a b c d u
              (τ • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
                (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))))) := by
    rw [Q2.dslot_smul_mk_of_mem K a b c d hτ (BR.mk_mem_grading K a b c hu hv),
      map_zsmul, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v (τ • w), hX, map_zsmul,
      ht₂D', map_zsmul, map_zsmul]
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm τ,
    Q3.dslot_smul_mk_of_mem K a b c d hτ hu]
  simp only [smul_smul]
  congr 1
  have hsgn : ((sgn (m * (j + jv)) : ℤˣ) : ℤ) * ((sgn (m * jv) : ℤˣ) : ℤ)
      = ((sgn (m * j) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_dslot2_deg]
  linear_combination ((sgn (e * j) : ℤˣ) : ℤ) * s' * hsgn

/-- The associativity recast of the total coefficient algebra used by
`comp_right`. -/
private theorem right_recast_eq :
    a + b + c + d = a + (b + c + d) := by ring

/-- `E2` transports the right action plainly, along the recast
`T_{a+b+c+d} ≅ T_{a+((b+c)+d)}` (`stdTowerCast`, M8a-8c′-0's device) —
conditional on `t₂`'s own right-equivariance for it. -/
theorem comp_right {j : ZMod 2}
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht₂R : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d) :
    E2 K a b c d e t₂ ht₂
        (MulOpposite.op τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq a b c d)).toAlgEquiv τ)
          • E2 K a b c d e t₂ ht₂
              (Q2.mk K a b c d (BR.mk K a b c u v) w) := by
  have hL : E2 K a b c d e t₂ ht₂
      (MulOpposite.op τ • Q2.mk K a b c d (BR.mk K a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          Q3.mk K a b c d u
            (MulOpposite.op ((stdTowerCast (K := K)
                  (right_recast_eq a b c d)).toAlgEquiv τ)
              • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
                (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)) := by
    rw [Q2.right_smul_mk, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v (MulOpposite.op τ • w), ht₂R]
  rw [hL, E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w, smul_comm
    (MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq a b c d)).toAlgEquiv τ)),
    Q3.right_smul_mk]

/-- `E2` is homogeneous of `t₂`'s degree `e` — the analogue of `E1`'s
`mem_grading`, `t₂`'s own homogeneity (`ht₂deg`) threading through
`E2_mk_of_mem` exactly as `E1`'s `hte` did there. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn.grading K a (b + c)) (TowerColumn.grading K (a + b + c) d) jj,
        t₂ n ∈ Q3Inner.grading K a b c d (jj + e))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    {v : TowerColumn K a (b + c)} (hv : v ∈ TowerColumn.grading K a (b + c) jv)
    {w : TowerColumn K (a + b + c) d}
    (hw : w ∈ TowerColumn.grading K (a + b + c) d jw) :
    E2 K a b c d e t₂ ht₂ (Q2.mk K a b c d (BR.mk K a b c u v) w)
      ∈ Q3.grading K a b c d (j + (jv + jw + e)) := by
  rw [E2_mk_of_mem' K a b c d e t₂ ht₂ hu v w]
  refine zsmul_mem ?_ _
  exact Q3.mk_mem_grading K a b c d hu
    (ht₂deg (jv + jw) _ (mk_mem_relGrading _ _ hv hw))

end E2

end PentagonB

end Bimod

end Superfusion
