/-
Superfusion / Bimod / EdgeEquiv5

Milestone M8a-8c′-2b-ii (roadmap v3, fifth and final block):
**equivariance of the fifth pentagon edge** `E5 t₅ = (id ⊗_signed t₅) ∘
q5Swap : Q5 → Q4r`, for a canonical triple intertwiner
`t₅ : B_L(a,b,c{+}d) → B_R(a,b,c{+}d)` of parity `e`, `(c{+}d)`-slot
super-equivariant (`ht₅`, folded into `E5`'s own construction via `smap`
and the middle swap `q5Swap`, `QuadEdge5.lean`).  As with `E3`
(`EdgeEquiv3.lean`) and `E4` (`EdgeEquiv4.lean`), the swap is folded into
`E5`'s generator formula (`E5_mk_of_mem`): `u ⊗ (v ⊗ w) ↦
(-1)^{|v|(e+|u|)} v ⊗ t₅(u ⊗ w)`, so `End`-descent does not apply; every
transport below is closed at the generator level `Q5.mk u (BR.mk v w)`,
`u`, `v` homogeneous, by unfolding through `Q5`'s own slot laws
(M8a-8c′-2a″) together with the slot laws of `B_L(a,b,c{+}d)`,
`B_R(a,b,c{+}d)` (M8a-7c-3) and — new to this file — the slot laws of the
landing space `Q4r`, built here from scratch, since `Q4r` (`QuadEdge5.lean`)
carries no slot structure of its own prior to this file.  `Q4r`'s
construction mirrors `Q5`'s own exactly, with `(a,b) ↔ (c,d)` and
`B_R(a{+}b,c,d) ↔ B_R(a,b,c{+}d)` swapped: its `c`-, `d`-slots are
*direct* (through the outer `TowerColumn K c d` factor, mirroring `Q5`'s
`a`-, `b`-slots), its `a`-, `b`-slots are the Koszul-signed mid-of-mid
action through `B_R(a,b,c{+}d)`'s own `a`- / `b`-slot (mirroring `Q5`'s
`c`-, `d`-slots), and its right action is `T_{a+(b+(c+d))}`, matching
`B_R(a,b,c{+}d)`'s own natural right tower exactly:

* the `a`, `b`-slots (`t₅`'s own domain/codomain outer slots: *direct* on
  `Q5`'s side, through `Q5`'s own outer `TowerColumn K a b` factor, but
  *signed* mid-of-mid on `Q4r`'s side, Koszul-keyed against the outer
  `(c{+}d)`-column's degree `i`): the swap/amplification sign
  `(-1)^{i(e+(k+j))}` (`k` the acting element's own degree, `j` the
  original `(a,b)`-column degree of `u`) and `Q4r`'s own mid-of-mid sign
  `(-1)^{ki}` combine to exactly cancel the base formula's own
  `(-1)^{i(e+j)}`, leaving only `t₅`'s own equivariance scalar
  (`comp_aslot`, `comp_bslot`, `ht₅A`- / `ht₅B`-conditional — a clean
  cancellation with no residual, mirroring `E3`'s/`E4`'s `comp_dslot`/
  `comp_cslot`);
* the `c`, `d`-slots (the *spectator* pair with respect to `t₅` — `t₅`'s
  domain/codomain only carry the *combined* `(c{+}d)`-slot, never `T_c`,
  `T_d` individually — but *signed* mid-of-mid on `Q5`'s side, through
  `B_R(a{+}b,c,d)`'s own `b`- / `c`-slot, Koszul-keyed against the `(a,b)`-
  column degree `j`, and *direct* on `Q4r`'s side, through `Q4r`'s own
  outer `TowerColumn K c d` factor): the swap/amplification signs combine
  to the amplification's own residual `(-1)^{ek}` (`k` the acting
  element's own degree), with no hypothesis on `t₅` beyond its own uniform
  degree `e` (`comp_cslot`, `comp_dslot`, mirroring `E3`'s `comp_aslot`
  "spectator" pattern);
* the right action: along the recast `T_{a+b+(c+d)} ≅ T_{a+(b+(c+d))}` of
  the total coefficient algebra (`stdTowerCast`, M8a-8c′-0's device) —
  `B_L(a,b,c{+}d)`'s own right-coefficient tower is literally
  `T_{a+b+(c+d)}` (matching `Q5`'s outer right action exactly, no cast
  needed *there*), while `B_R(a,b,c{+}d)`'s is `T_{a+(b+(c+d))}` (matching
  `Q4r`'s, built here to match `B_R`'s own natural tower exactly), so the
  cast lands on `t₅`'s own right-equivariance (`ht₅R`), exactly mirroring
  `E4`'s `comp_right` pattern;
* the grading: `t₅`'s own degree-`e` homogeneity (`ht₅deg`) threading
  through `E5_mk_of_mem` exactly as `E3`'s/`E4`'s did.
-/
import Superfusion.Bimod.QuadEdge5
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### The slot actions of `Q4r`

`Q4r`'s own structure mirrors `Q5`'s exactly: outer `TowerColumn K c d`
factor (direct `T_c`, `T_d`-slots), inner `B_R(a,b,c{+}d)` factor (signed
mid-of-mid `T_a`-, `T_b`-slots, keyed against the outer column's degree),
and a right action matching `B_R(a,b,c{+}d)`'s own natural tower
`T_{a+(b+(c+d))}`. -/

namespace Q4r

/-- The canonical bilinear generator map. -/
noncomputable def mk :
    TowerColumn K c d →ₗ[K] BR K a b (c + d) →ₗ[K] Q4r K a b c d :=
  RelTensor.mk K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
    (BR K a b (c + d))

/-- The `T_c`-slot action (through the outer column). -/
noncomputable instance : Module (stdTower (K := K) c).carrier
    (Q4r K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d)))
    ((leftActionEnd K (stdTower (K := K) (c + d)).carrier
      (TowerColumn K c d) (BR K a b (c + d))
      (B := (stdTower (K := K) c).carrier)).toRingHom)

theorem cslot_smul_mk (z : (stdTower (K := K) c).carrier)
    (u : TowerColumn K c d) (v : BR K a b (c + d)) :
    z • mk K a b c d u v = mk K a b c d (z • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (c + d)).carrier
    (TowerColumn K c d) (BR K a b (c + d)) z u v

/-- The `T_d`-slot action (through the outer column). -/
noncomputable instance : Module (stdTower (K := K) d).carrier
    (Q4r K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d)))
    ((leftActionEnd K (stdTower (K := K) (c + d)).carrier
      (TowerColumn K c d) (BR K a b (c + d))
      (B := (stdTower (K := K) d).carrier)).toRingHom)

theorem dslot_smul_mk (t : (stdTower (K := K) d).carrier)
    (u : TowerColumn K c d) (v : BR K a b (c + d)) :
    t • mk K a b c d u v = mk K a b c d (t • u) v :=
  leftActionEnd_mk K (stdTower (K := K) (c + d)).carrier
    (TowerColumn K c d) (BR K a b (c + d)) t u v

/-- The `T_a`-slot action: the Koszul-signed middle action through the
`a`-slot of the `B_R(a,b,c{+}d)`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (Q4r K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d)))
    ((midAlgHom (stdTower (K := K) (c + d)).grading
      (TowerColumn.grading K c d) (stdTower (K := K) a).grading
      (superCommSMul_symm (stdTower (K := K) a).grading
        (stdTower (K := K) (c + d)).grading
        (BR.superCommSMul_aslot_cslot K a b (c + d)))).toRingHom)

/-- The sign law of the `a`-slot of `Q4r`. -/
theorem aslot_smul_mk_of_mem {j k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    {u : TowerColumn K c d} (hu : u ∈ TowerColumn.grading K c d j)
    (v : BR K a b (c + d)) :
    x • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (x • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (c + d)).grading
    (TowerColumn.grading K c d) (stdTower (K := K) a).grading
    (superCommSMul_symm (stdTower (K := K) a).grading
      (stdTower (K := K) (c + d)).grading
      (BR.superCommSMul_aslot_cslot K a b (c + d))) hu hx v

/-- The `T_b`-slot action: the Koszul-signed middle action through the
`b`-slot of the `B_R(a,b,c{+}d)`-factor (mid-of-mid). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (Q4r K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d)))
    ((midAlgHom (stdTower (K := K) (c + d)).grading
      (TowerColumn.grading K c d) (stdTower (K := K) b).grading
      (superCommSMul_symm (stdTower (K := K) b).grading
        (stdTower (K := K) (c + d)).grading
        (BR.superCommSMul_bslot_cslot K a b (c + d)))).toRingHom)

/-- The sign law of the `b`-slot of `Q4r`. -/
theorem bslot_smul_mk_of_mem {j k : ZMod 2}
    {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    {u : TowerColumn K c d} (hu : u ∈ TowerColumn.grading K c d j)
    (v : BR K a b (c + d)) :
    y • mk K a b c d u v
      = ((sgn (k * j) : ℤˣ) : ℤ) • mk K a b c d u (y • v) :=
  midEnd_mk_of_mem (stdTower (K := K) (c + d)).grading
    (TowerColumn.grading K c d) (stdTower (K := K) b).grading
    (superCommSMul_symm (stdTower (K := K) b).grading
      (stdTower (K := K) (c + d)).grading
      (BR.superCommSMul_bslot_cslot K a b (c + d))) hu hy v

/-- The right action of the total coefficient algebra `T_{a+(b+(c+d))}`,
matching `B_R(a,b,c{+}d)`'s own natural right tower. -/
noncomputable instance : Module
    ((stdTower (K := K) (a + (b + (c + d)))).carrier)ᵐᵒᵖ (Q4r K a b c d) :=
  Module.compHom
    (RelTensor K (stdTower (K := K) (c + d)).carrier (TowerColumn K c d)
      (BR K a b (c + d)))
    ((rightActionEnd K (stdTower (K := K) (c + d)).carrier
      (TowerColumn K c d) (BR K a b (c + d))
      (C := (stdTower (K := K) (a + (b + (c + d)))).carrier)).toRingHom)

theorem right_smul_mk
    (τ : ((stdTower (K := K) (a + (b + (c + d)))).carrier)ᵐᵒᵖ)
    (u : TowerColumn K c d) (v : BR K a b (c + d)) :
    τ • mk K a b c d u v = mk K a b c d u (τ • v) :=
  rightActionEnd_mk K (stdTower (K := K) (c + d)).carrier
    (TowerColumn K c d) (BR K a b (c + d)) τ u v

/-- The descended grading of `Q4r`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (Q4r K a b c d) :=
  relGrading (stdTower (K := K) (c + d)).carrier
    (TowerColumn.grading K c d) (BR.grading K a b (c + d))

noncomputable instance : DirectSum.Decomposition (grading K a b c d) :=
  relDecomposition (stdTower (K := K) (c + d)).grading
    (TowerColumn.grading K c d) (BR.grading K a b (c + d))

theorem mk_mem_grading {j k : ZMod 2} {u : TowerColumn K c d}
    {v : BR K a b (c + d)}
    (hu : u ∈ TowerColumn.grading K c d j)
    (hv : v ∈ BR.grading K a b (c + d) k) :
    mk K a b c d u v ∈ grading K a b c d (j + k) :=
  mk_mem_relGrading (A := (stdTower (K := K) (c + d)).carrier)
    (TowerColumn.grading K c d) (BR.grading K a b (c + d)) hu hv

end Q4r

/-! ### The fifth edge -/

namespace E5

variable (e : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
  z ∈ (stdTower (K := K) (c + d)).grading i →
  ∀ n : BL K a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- `E5_mk_of_mem`, restated through the synonym-valued `mk`s of `Q5`
and `Q4r` (the track's discipline) — bridges the raw `RelTensor.mk`
spelling of `E5_mk_of_mem` to the generator lemmas of `Q5` and `Q4r`, by
`rfl` (`Q5.mk`, `Q4r.mk` unfold to `RelTensor.mk`). -/
private theorem E5_mk_of_mem' {i j : ZMod 2} {v : TowerColumn K c d}
    {u : TowerColumn K a b} (hv : v ∈ TowerColumn.grading K c d i)
    (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅ (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          Q4r.mk K a b c d v (t₅ (BL.mk K a b (c + d) u w)) :=
  E5_mk_of_mem K a b c d e t₅ ht₅ hv hu w

/-- The `ZMod 2`-arithmetic fact behind doubled-sign collapses (`Q4r`'s
own mid-of-mid sign squared, in `comp_aslot`'s/`comp_bslot`'s `h3`):
doubling a product of degrees is always `0`. -/
private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

/-- The `ZMod 2`-arithmetic fact behind the exact cancellation of
`comp_aslot`/`comp_bslot`: the swap/amplification sign, `Q4r`'s own
mid-of-mid sign and the base formula's sign combine to `1`. -/
private theorem zmod2_ab_deg : ∀ i e k j : ZMod 2,
    i * (e + (k + j)) + k * i = i * (e + j) := by decide

/-- The `ZMod 2`-arithmetic fact behind `comp_cslot`/`comp_dslot`'s
spectator residue `(-1)^{ek}`. -/
private theorem zmod2_cd_deg : ∀ e k j i : ZMod 2,
    k * j + (k + i) * (e + j) = e * k + i * (e + j) := by decide

/-- `E5` transports the `a`-slot up to `t₅`'s own equivariance scalar
`s` for it — `T_a` is *direct* on `Q5`'s side (through the outer
`TowerColumn K a b` factor) but the *signed* mid-of-mid `a`-slot of
`B_R(a,b,c{+}d)` on `Q4r`'s side: the swap/amplification sign
`(-1)^{i(e+(k+j))}` and `Q4r`'s own mid-of-mid sign `(-1)^{ki}` combine
to cancel the base formula's own `(-1)^{i(e+j)}` exactly, leaving only
`t₅`'s own equivariance scalar (a clean cancellation with no residual,
mirroring `E3`'s/`E4`'s `comp_dslot`/`comp_cslot`). -/
theorem comp_aslot {s : ℤ} {k j i : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht₅A : ∀ n : BL K a b (c + d), t₅ (x • n) = s • (x • t₅ n))
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅ (x • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = s • (x • E5 K a b c d e t₅ ht₅
          (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))) := by
  have h1 : x • Q5.mk K a b c d u (BR.mk K (a + b) c d v w)
      = Q5.mk K a b c d (x • u) (BR.mk K (a + b) c d v w) :=
    Q5.aslot_smul_mk K a b c d x u (BR.mk K (a + b) c d v w)
  have hxu : x • u ∈ TowerColumn.grading K a b (k + j) :=
    (vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hx hu
  have h2 : E5 K a b c d e t₅ ht₅
      (Q5.mk K a b c d (x • u) (BR.mk K (a + b) c d v w))
      = ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) •
          (s • Q4r.mk K a b c d v (x • t₅ (BL.mk K a b (c + d) u w))) := by
    rw [E5_mk_of_mem' K a b c d e t₅ ht₅ hv hxu w, ← BL.aslot_smul_mk, ht₅A]
    simp only [map_zsmul]
  have h3 : Q4r.mk K a b c d v (x • t₅ (BL.mk K a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (x • Q4r.mk K a b c d v (t₅ (BL.mk K a b (c + d) u w))) := by
    rw [Q4r.aslot_smul_mk_of_mem K a b c d hx hv
        (t₅ (BL.mk K a b (c + d) u w)),
      smul_smul, ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero,
      Units.val_one, one_smul]
  have hkey : ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) * ((sgn (k * i) : ℤˣ) : ℤ)
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_ab_deg]
  rw [h1, h2, h3, E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w, smul_comm x]
  simp only [smul_smul]
  congr 1
  linear_combination s * hkey

/-- `E5` transports the `b`-slot up to `t₅`'s own equivariance scalar
`s` for it — exactly parallel to `comp_aslot` (`T_b` is *direct* on
`Q5`'s side and the *signed* mid-of-mid `b`-slot of `B_R(a,b,c{+}d)` on
`Q4r`'s side). -/
theorem comp_bslot {s : ℤ} {k j i : ZMod 2}
    {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    (ht₅B : ∀ n : BL K a b (c + d), t₅ (y • n) = s • (y • t₅ n))
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅ (y • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = s • (y • E5 K a b c d e t₅ ht₅
          (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))) := by
  have h1 : y • Q5.mk K a b c d u (BR.mk K (a + b) c d v w)
      = Q5.mk K a b c d (y • u) (BR.mk K (a + b) c d v w) :=
    Q5.bslot_smul_mk K a b c d y u (BR.mk K (a + b) c d v w)
  have hyu : y • u ∈ TowerColumn.grading K a b (k + j) :=
    (vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hy hu
  have h2 : E5 K a b c d e t₅ ht₅
      (Q5.mk K a b c d (y • u) (BR.mk K (a + b) c d v w))
      = ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) •
          (s • Q4r.mk K a b c d v (y • t₅ (BL.mk K a b (c + d) u w))) := by
    rw [E5_mk_of_mem' K a b c d e t₅ ht₅ hv hyu w, ← BL.bslot_smul_mk, ht₅B]
    simp only [map_zsmul]
  have h3 : Q4r.mk K a b c d v (y • t₅ (BL.mk K a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (y • Q4r.mk K a b c d v (t₅ (BL.mk K a b (c + d) u w))) := by
    rw [Q4r.bslot_smul_mk_of_mem K a b c d hy hv
        (t₅ (BL.mk K a b (c + d) u w)),
      smul_smul, ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero,
      Units.val_one, one_smul]
  have hkey : ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) * ((sgn (k * i) : ℤˣ) : ℤ)
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_ab_deg]
  rw [h1, h2, h3, E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w, smul_comm y]
  simp only [smul_smul]
  congr 1
  linear_combination s * hkey

/-- `E5` transports the `c`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot with respect to `t₅` (`B_L`/`B_R`
carry no separate `T_c`-action, only the *combined* `(c{+}d)`-slot does):
the *signed* mid-of-mid `c`-slot of `Q5` (through `B_R(a{+}b,c,d)`'s own
`b`-slot) and the *direct* `c`-slot of `Q4r` combine with the swap sign
to leave exactly the amplification's residual `(-1)^{ek}`, with no
hypothesis on `t₅` beyond its own uniform degree `e` (mirroring `E3`'s
`comp_aslot`). -/
theorem comp_cslot {k j i : ZMod 2} {z : (stdTower (K := K) c).carrier}
    (hz : z ∈ (stdTower (K := K) c).grading k)
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅ (z • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (z • E5 K a b c d e t₅ ht₅
            (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))) := by
  have hzv : z • v ∈ TowerColumn.grading K c d (k + i) :=
    (vadd_eq_add k i) ▸ SetLike.GradedSMul.smul_mem hz hv
  have hL : E5 K a b c d e t₅ ht₅
      (z • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (((sgn ((k + i) * (e + j)) : ℤˣ) : ℤ) •
            (z • Q4r.mk K a b c d v (t₅ (BL.mk K a b (c + d) u w)))) := by
    rw [Q5.cslot_smul_mk_of_mem K a b c d hz hu, BR.bslot_smul_mk, map_zsmul,
      E5_mk_of_mem' K a b c d e t₅ ht₅ hzv hu w, ← Q4r.cslot_smul_mk]
  rw [hL, smul_smul, ← Units.val_mul, ← sgn_add,
    E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w, smul_comm z, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_cd_deg]

/-- `E5` transports the `d`-slot up to the amplification's own sign
`(-1)^{ek}` — exactly parallel to `comp_cslot` (`T_d` is the *spectator*
slot with respect to `t₅`, *signed* mid-of-mid on `Q5`'s side through
`B_R(a{+}b,c,d)`'s own `c`-slot, *direct* on `Q4r`'s side). -/
theorem comp_dslot {k j i : ZMod 2} {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅ (t • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (t • E5 K a b c d e t₅ ht₅
            (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))) := by
  have htv : t • v ∈ TowerColumn.grading K c d (k + i) :=
    (vadd_eq_add k i) ▸ SetLike.GradedSMul.smul_mem ht hv
  have hL : E5 K a b c d e t₅ ht₅
      (t • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (((sgn ((k + i) * (e + j)) : ℤˣ) : ℤ) •
            (t • Q4r.mk K a b c d v (t₅ (BL.mk K a b (c + d) u w)))) := by
    rw [Q5.dslot_smul_mk_of_mem K a b c d ht hu, BR.cslot_smul_mk, map_zsmul,
      E5_mk_of_mem' K a b c d e t₅ ht₅ htv hu w, ← Q4r.dslot_smul_mk]
  rw [hL, smul_smul, ← Units.val_mul, ← sgn_add,
    E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w, smul_comm t, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_cd_deg]

/-- The associativity recast of the total coefficient algebra used by
`comp_right`: `B_L(a,b,c{+}d)`'s own right-coefficient tower is
literally `T_{a+b+(c+d)}` (matching `Q5`'s outer right action exactly),
while `B_R(a,b,c{+}d)`'s is `T_{a+(b+(c+d))}` (matching `Q4r`'s), so the
cast lands on `t₅`'s own right-equivariance (`ht₅R`). -/
private theorem right_recast_eq5 : a + b + (c + d) = a + (b + (c + d)) := by
  ring

/-- `E5` transports the right action along the recast
`T_{a+b+(c+d)} ≅ T_{a+(b+(c+d))}` (`stdTowerCast`, M8a-8c′-0's device) —
conditional on `t₅`'s own right-equivariance for it (its domain's right
tower already matches `Q5`'s outer one exactly, so no cast is needed on
the source side of `ht₅R`). -/
theorem comp_right {i j : ZMod 2}
    (τ : (stdTower (K := K) (a + b + (c + d))).carrier)
    (ht₅R : ∀ n : BL K a b (c + d),
      t₅ (MulOpposite.op τ • n)
        = MulOpposite.op ((stdTowerCast (K := K)
              (right_recast_eq5 a b c d)).toAlgEquiv τ) • t₅ n)
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    (w : TowerColumn K (a + b) (c + d)) :
    E5 K a b c d e t₅ ht₅
        (MulOpposite.op τ • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = MulOpposite.op ((stdTowerCast (K := K)
            (right_recast_eq5 a b c d)).toAlgEquiv τ)
          • E5 K a b c d e t₅ ht₅
              (Q5.mk K a b c d u (BR.mk K (a + b) c d v w)) := by
  have hL : E5 K a b c d e t₅ ht₅
      (MulOpposite.op τ • Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          Q4r.mk K a b c d v
            (MulOpposite.op ((stdTowerCast (K := K)
                  (right_recast_eq5 a b c d)).toAlgEquiv τ)
              • t₅ (BL.mk K a b (c + d) u w)) := by
    rw [Q5.right_smul_mk, BR.right_smul_mk,
      E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu (MulOpposite.op τ • w),
      ← BL.right_smul_mk, ht₅R]
  rw [hL, E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w, smul_comm
    (MulOpposite.op ((stdTowerCast (K := K)
      (right_recast_eq5 a b c d)).toAlgEquiv τ)), Q4r.right_smul_mk]

/-- `E5` is homogeneous of `t₅`'s degree `e` — the analogue of `E3`'s
`mem_grading`/`E4`'s `mem_grading`, `t₅`'s own homogeneity (`ht₅deg`)
threading through `E5_mk_of_mem` exactly as there. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₅deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K a b (c + d) j',
      t₅ n ∈ BR.grading K a b (c + d) (j' + e))
    {u : TowerColumn K a b} (hu : u ∈ TowerColumn.grading K a b j)
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d jv)
    {w : TowerColumn K (a + b) (c + d)}
    (hw : w ∈ TowerColumn.grading K (a + b) (c + d) jw) :
    E5 K a b c d e t₅ ht₅ (Q5.mk K a b c d u (BR.mk K (a + b) c d v w))
      ∈ Q4r.grading K a b c d (j + (jv + jw + e)) := by
  rw [E5_mk_of_mem' K a b c d e t₅ ht₅ hv hu w]
  refine zsmul_mem ?_ _
  have h := Q4r.mk_mem_grading K a b c d hv
    (ht₅deg (j + jw) _ (BL.mk_mem_grading K a b (c + d) hu hw))
  rwa [show jv + (j + jw + e) = j + (jv + jw + e) from by ring] at h

end E5

end PentagonB

end Bimod

end Superfusion
