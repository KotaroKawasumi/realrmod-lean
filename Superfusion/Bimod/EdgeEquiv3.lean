/-
Superfusion / Bimod / EdgeEquiv3

Milestone M8a-8c′-2b-ii (roadmap v3, third block): **equivariance of
the third pentagon edge** `E3 t₃ = (t₃ ⊗ id) ∘ assoc⁻¹ : Q3 → Q4`, for
a canonical triple intertwiner `t₃ : B_L(b,c,d) → B_R(b,c,d)`.  Unlike
`E2` (second block, `EdgeEquiv2.lean`), the associator `q3Assoc`
folded into `E3`'s definition (`QuadEdge3.lean`) carries **no sign at
all** (`E3_mk` is an unconditional identity, with no `_of_mem`
grading hypothesis) — all balancings on the `a((bc)d)`/`a(b(cd))` leg
are canonical, unlike `E2`'s recast-through `BR.mk` reshuffling.  So
every sign appearing below comes purely from the *endpoint* slot laws
of `Q3`, `Q4` (M8a-8c′-2a″) and of `t₃`'s own domain/codomain `B_L`,
`B_R` (M8a-7c-3), never from the generator formula itself:

* `E3 = t₃ ⊗ id` transports `T_a` (the *spectator* slot — `t₃`'s
  domain `B_L(b,c,d)`/codomain `B_R(b,c,d)` carry no `T_a`-action at
  all, exactly as in `E2`'s `b`, `c`-slots) through the *two* stacked
  mid-of-mid Koszul signs of `Q3` (keyed to `u`'s degree `j`) and of
  `Q3Inner = B_R(a,b{+}c,d)` (keyed to `v`'s degree `jv`), landing at
  `Q4`'s own mid-of-mid sign (keyed to the *total* degree of `t₃`'s
  image, `j+jv+e` for a `t₃` of uniform degree `e`) — the `j`, `jv`
  contributions cancel exactly against this last sign, leaving only
  the amplification's own sign `(-1)^{e|x|}` (`comp_aslot`,
  `ht₃deg`-conditional, mirroring `E2`'s `b`, `c`-slot pattern);
* `T_b`, `T_c` (`t₃`'s own domain/codomain outer slots, both *direct*
  on both sides of `t₃`) transport with exactly `t₃`'s own
  equivariance scalar and no sign at all — `E3`'s generator formula
  contributes nothing, and neither does `Q3`'s outer slot law nor
  `Q4`'s outer slot law (`comp_bslot`, `comp_cslot`, mirroring `E1`'s
  `comp_aslot`/`comp_bslot`/`comp_cslot` pass-through exactly);
* `T_d` (`t₃`'s own domain/codomain: *signed* on `B_L` — the middle
  slot — but *direct* on `B_R` — an outer slot, and on `Q3` it is the
  *other* mid-of-mid signed slot, keyed to the *same* `u`-degree `j`
  as `B_L`'s own sign): the two Koszul signs (`Q3`'s and `B_L`'s, both
  keyed to `(m,j)` for `T_d`'s own degree `m`) cancel exactly, leaving
  only `t₃`'s own equivariance scalar (`comp_dslot`, mirroring `E2`'s
  `comp_aslot`/`comp_dslot` cancellation, but here to a *clean*
  cancellation with no residual, since — unlike `E2`'s asymmetric
  `Q2`/`Q3` keying — `Q3`'s `d`-slot sign and `B_L`'s `d`-slot sign key
  to the identical pair `(m,j)`);
* the right action: **plain, with no recast at all** — `Q3`'s and
  `Q4`'s outer right-coefficient towers are both literally
  `T_{a+((b+c)+d)}` (`a+(b+c+d)` parses to the identical expression),
  and neither slot law carries a sign, so `comp_right` needs no
  hypothesis on `t₃` beyond its own definitional right-equivariance
  (already folded into `E3`'s construction via `ht₃`); the coefficient
  *recast* of `t₃`'s own domain (`T_{b+c+d}`, M8a-8c′-0) is internal to
  `ht₃` and never resurfaces at the `Q3 → Q4` level (deviating from
  the a priori expectation that `E3`'s outer right action would need a
  `stdTowerCast`, as `E2`'s did — that recast belongs to a *later*
  edge, `E4`'s `Q4l → Q4` connector, `QuadClose.lean`);
* the grading: `t₃`'s own degree-`e` homogeneity (`ht₃deg`) threading
  through `E3_mk` exactly as `E1`'s `hte`/`E2`'s `ht₂deg` did.
-/
import Superfusion.Bimod.QuadEdge3
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

namespace E3

variable (t₃ : BL K b c d →ₗ[K] BR K b c d)
variable (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
  (m : BL K b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- `E3_mk`, restated through the synonym-valued `mk`s of `Q3`, `B_R`
(the spelling of `Q3Inner`) and `Q4` (the track's discipline) —
bridges the raw `RelTensor.mk` spelling of `E3_mk` to the generator
lemmas of `Q3` and `Q4`, by `rfl` (`Q3.mk`, `BR.mk`, `Q4.mk` unfold to
`RelTensor.mk`). -/
private theorem E3_mk' (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃
        (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = Q4.mk K a b c d (t₃ (BL.mk K b c d u v)) w :=
  E3_mk K a b c d t₃ ht₃ u v w

/-- The `ZMod 2`-arithmetic fact behind the exact `T_d`-cancellation
(`comp_dslot`) and the mid-of-mid contraction inside `comp_aslot`:
doubling a product of degrees is always `0`. -/
private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

/-- The `ZMod 2`-arithmetic fact behind `comp_aslot`'s clean
`(-1)^{e|x|}` residue after the two mid-of-mid signs of `Q3`/`Q3Inner`
cancel against `Q4`'s own mid-of-mid sign. -/
private theorem zmod2_aslot_deg : ∀ e k j jv : ZMod 2,
    e * k + k * (j + jv + e) = k * (j + jv) := by decide

/-- `Q3Inner` is a `def` bridging to `B_R(a,b{+}c,d)` (M8a-8c′-2a″'s
`inferInstanceAs` discipline), so its slot instances are *separate*
(though defeq) registrations from `B_R`'s own — `rw` lemmas stated at
`B_R`'s instance do not syntactically match a smul elaborated at
`Q3Inner`'s.  These three private bridges restate the needed `B_R`
slot laws directly at `Q3Inner`'s own instance, by `exact` (full defeq
checking, unlike `rw`'s syntactic matching). -/
private theorem Q3Inner_dslot_smul (τ : (stdTower (K := K) d).carrier)
    (v : TowerColumn K (b + c) d) (w : TowerColumn K a ((b + c) + d)) :
    τ • (BR.mk K a (b + c) d v w : Q3Inner K a b c d)
      = (BR.mk K a (b + c) d (τ • v) w : Q3Inner K a b c d) :=
  BR.cslot_smul_mk K a (b + c) d τ v w

private theorem Q3Inner_aslot_smul_of_mem {jv k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {v : TowerColumn K (b + c) d}
    (hv : v ∈ TowerColumn.grading K (b + c) d jv)
    (w : TowerColumn K a ((b + c) + d)) :
    x • (BR.mk K a (b + c) d v w : Q3Inner K a b c d)
      = ((sgn (k * jv) : ℤˣ) : ℤ) •
          (BR.mk K a (b + c) d v (x • w) : Q3Inner K a b c d) :=
  BR.aslot_smul_mk_of_mem K a (b + c) d hx hv w

private theorem Q3Inner_right_smul
    (τ : ((stdTower (K := K) (a + ((b + c) + d))).carrier)ᵐᵒᵖ)
    (v : TowerColumn K (b + c) d) (w : TowerColumn K a ((b + c) + d)) :
    τ • (BR.mk K a (b + c) d v w : Q3Inner K a b c d)
      = (BR.mk K a (b + c) d v (τ • w) : Q3Inner K a b c d) :=
  BR.right_smul_mk K a (b + c) d τ v w

/-- `E3` transports the `b`-slot up to `t₃`'s own equivariance scalar
`s` for it — `T_b` is a *direct* outer slot of both `B_L(b,c,d)` and
`B_R(b,c,d)`, and `E3`'s generator formula (`E3_mk`) carries no sign
at all, so the transport is exactly `t₃`'s own scalar (no residual
sign), mirroring `E1`'s `comp_aslot`/`comp_bslot`/`comp_cslot`
pass-through pattern. -/
theorem comp_bslot {s : ℤ} {y : (stdTower (K := K) b).carrier}
    (ht₃B : ∀ m : BL K b c d, t₃ (y • m) = s • (y • t₃ m))
    (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃ (y • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = s • (y • E3 K a b c d t₃ ht₃
          (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))) := by
  rw [Q3.bslot_smul_mk, E3_mk' K a b c d t₃ ht₃ (y • u) v w,
    E3_mk' K a b c d t₃ ht₃ u v w, ← BL.aslot_smul_mk, ht₃B]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← Q4.bslot_smul_mk]

/-- `E3` transports the `c`-slot up to `t₃`'s own equivariance scalar
`s` for it — `T_c` is a *direct* outer slot of both `B_L(b,c,d)` and
`B_R(b,c,d)`, exactly parallel to `comp_bslot`. -/
theorem comp_cslot {s : ℤ} {z : (stdTower (K := K) c).carrier}
    (ht₃C : ∀ m : BL K b c d, t₃ (z • m) = s • (z • t₃ m))
    (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃ (z • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = s • (z • E3 K a b c d t₃ ht₃
          (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))) := by
  rw [Q3.cslot_smul_mk, E3_mk' K a b c d t₃ ht₃ (z • u) v w,
    E3_mk' K a b c d t₃ ht₃ u v w, ← BL.bslot_smul_mk, ht₃C]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← Q4.cslot_smul_mk]

/-- `E3` transports the `d`-slot up to `t₃`'s own equivariance scalar
`s` for it — the mid-of-mid sign of `Q3` (keyed to `u`'s degree `j`)
and `B_L`'s own signed middle-slot law for `T_d` (keyed to the *same*
`(m,j)`) cancel exactly, leaving no residual sign (unlike `E2`'s
`comp_dslot`, whose `Q2`/`Q3` signs keyed to different degrees). -/
theorem comp_dslot {s : ℤ} {j m : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₃D : ∀ n : BL K b c d, t₃ (τ • n) = s • (τ • t₃ n))
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    (v : TowerColumn K (b + c) d) (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃ (τ • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = s • (τ • E3 K a b c d t₃ ht₃
          (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))) := by
  have hv' : BL.mk K b c d u (τ • v)
      = ((sgn (m * j) : ℤˣ) : ℤ) • (τ • BL.mk K b c d u v) := by
    rw [BL.cslot_smul_mk_of_mem K b c d hτ hu, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have step1 : τ • Q3.mk K a b c d u (BR.mk K a (b + c) d v w)
      = ((sgn (m * j) : ℤˣ) : ℤ) •
          Q3.mk K a b c d u (BR.mk K a (b + c) d (τ • v) w) := by
    rw [Q3.dslot_smul_mk_of_mem K a b c d hτ hu]
    exact congrArg (fun z => ((sgn (m * j) : ℤˣ) : ℤ) • Q3.mk K a b c d u z)
      (Q3Inner_dslot_smul K a b c d τ v w)
  rw [step1, map_zsmul, E3_mk' K a b c d t₃ ht₃ u (τ • v) w, hv']
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [ht₃D]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← Q4.dslot_smul_mk, E3_mk' K a b c d t₃ ht₃ u v w, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]

/-- `E3` transports the `a`-slot up to the amplification's own sign
`(-1)^{e|x|}` — the *spectator* slot: `B_L(b,c,d)`/`B_R(b,c,d)` carry
no `T_a`-action at all, so no hypothesis on `t₃` beyond its own
uniform degree `e` is needed.  The two mid-of-mid signs of `Q3`
(keyed to `u`'s degree `j`) and of `Q3Inner = B_R(a,b{+}c,d)` (keyed
to `v`'s degree `jv`) combine to `(-1)^{k(j+jv)}`, which cancels
exactly against `Q4`'s own mid-of-mid sign `(-1)^{k(j+jv+e)}` up to
the surviving `(-1)^{ke}`, mirroring `E2`'s `b`, `c`-slot pattern
("the amplification's own sign, no extra hypothesis needed since
these slots never touch `t₂`'s domain"). -/
theorem comp_aslot {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e))
    {k j jv : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : TowerColumn K b c} (hu : u ∈ TowerColumn.grading K b c j)
    {v : TowerColumn K (b + c) d} (hv : v ∈ TowerColumn.grading K (b + c) d jv)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃ (x • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (x • E3 K a b c d t₃ ht₃
            (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))) := by
  have hL : E3 K a b c d t₃ ht₃ (x • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = ((sgn (k * (j + jv)) : ℤˣ) : ℤ) •
          Q4.mk K a b c d (t₃ (BL.mk K b c d u v)) (x • w) := by
    have step1 : x • Q3.mk K a b c d u (BR.mk K a (b + c) d v w)
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (((sgn (k * jv) : ℤˣ) : ℤ) •
              Q3.mk K a b c d u (BR.mk K a (b + c) d v (x • w))) := by
      have hA := Q3.aslot_smul_mk_of_mem K a b c d hx hu
        (BR.mk K a (b + c) d v w)
      have hC := congrArg (fun z => Q3.mk K a b c d u z)
        (Q3Inner_aslot_smul_of_mem K a b c d hx hv w)
      have hD := map_zsmul (Q3.mk K a b c d u) ((sgn (k * jv) : ℤˣ) : ℤ)
        (BR.mk K a (b + c) d v (x • w))
      exact hA.trans (congrArg (fun z => ((sgn (k * j) : ℤˣ) : ℤ) • z) (hC.trans hD))
    rw [step1, smul_smul, ← Units.val_mul, ← sgn_add, ← mul_add, map_zsmul,
      E3_mk' K a b c d t₃ ht₃ u v (x • w)]
  rw [hL, E3_mk' K a b c d t₃ ht₃ u v w,
    Q4.aslot_smul_mk_of_mem K a b c d hx
      (ht₃deg (j + jv) _ (BL.mk_mem_grading K b c d hu hv))]
  simp only [smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add]
  congr 1
  exact congrArg sgn (zmod2_aslot_deg e k j jv).symm

/-- `E3` transports the right action plainly — `Q3`'s and `Q4`'s
outer right-coefficient towers are both literally `T_{a+((b+c)+d)}`
(`a+(b+c+d)` parses to the identical expression), so no cast and no
extra hypothesis on `t₃` is needed (its own right-equivariance over
`T_{b+c+d}` is already folded into `ht₃`, internal to `t₃`'s own
domain/codomain and never touching the outer right action). -/
theorem comp_right (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
    (w : TowerColumn K a ((b + c) + d)) :
    E3 K a b c d t₃ ht₃ (τ • Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      = τ • E3 K a b c d t₃ ht₃
          (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)) := by
  have step1 : τ • Q3.mk K a b c d u (BR.mk K a (b + c) d v w)
      = Q3.mk K a b c d u (BR.mk K a (b + c) d v (τ • w)) := by
    rw [Q3.right_smul_mk]
    exact congrArg (fun z => Q3.mk K a b c d u z) (Q3Inner_right_smul K a b c d τ v w)
  rw [step1, E3_mk' K a b c d t₃ ht₃ u v (τ • w),
    E3_mk' K a b c d t₃ ht₃ u v w, Q4.right_smul_mk]

/-- `E3` is homogeneous of `t₃`'s degree `e` — the analogue of `E1`'s
`mem_grading`/`E2`'s `mem_grading`, `t₃`'s own homogeneity (`ht₃deg`)
threading through `E3_mk` exactly as there. -/
theorem mem_grading {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e))
    {j jv jw : ZMod 2} {u : TowerColumn K b c}
    (hu : u ∈ TowerColumn.grading K b c j)
    {v : TowerColumn K (b + c) d}
    (hv : v ∈ TowerColumn.grading K (b + c) d jv)
    {w : TowerColumn K a ((b + c) + d)}
    (hw : w ∈ TowerColumn.grading K a ((b + c) + d) jw) :
    E3 K a b c d t₃ ht₃ (Q3.mk K a b c d u (BR.mk K a (b + c) d v w))
      ∈ Q4.grading K a b c d (j + (jv + jw + e)) := by
  rw [E3_mk' K a b c d t₃ ht₃ u v w]
  have h := Q4.mk_mem_grading K a b c d
    (ht₃deg (j + jv) _ (BL.mk_mem_grading K b c d hu hv)) hw
  rwa [show (j + jv + e) + jw = j + (jv + jw + e) from by ring] at h

end E3

end PentagonB

end Bimod

end Superfusion
