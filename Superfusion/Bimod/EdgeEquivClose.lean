/-
Superfusion / Bimod / EdgeEquivClose

Milestone M8a-8c′-2b-ii (roadmap v3, sixth and final block): **equivariance
of the closing connector** `q4Close : Q4r ≃ Q4` (`QuadClose.lean`) — the
sign-free bottom-route identification

  `Q4r = C_{c,d} ⊗_{T_{c+d}} B_R(a,b,c{+}d) ≃ Q4 = B_R(b,c,d)
  ⊗_{T_{(b+c)+d}} C_{a,(b+c)+d}`.

Unlike
`E1..E5` (which each involve a genuine triple intertwiner and hence carry
`ht*`-conditional signs), `q4Close` carries **no intertwiner** — its two
legs (`q4lAssoc`, all balancings canonical; `q4Recast`, identity on the
`B_R(b,c,d)`-factor and the column cast on the coefficient factor) are
both sign-free, so every transport law below is a **clean equivariance**
`q4Close (ξ • g) = ξ • q4Close g`, unconditionally (no `ht*` hypotheses):

* the `a`-, `b`-slots (`comp_aslot`, `comp_bslot`): both sides carry an
  internal Koszul sign from the mid-of-mid structure of `Q4r`'s outer
  factor (`comp_aslot`) resp. `BR(b,c,d)`'s own `a'`-slot (`comp_bslot`)
  — but the sign computed via `Q4r`'s own route and the sign computed via
  `Q4`'s own route are *literally the same* (`sgn(k*(i+j))`, the
  Koszul sign keyed against the *combined* degree of the `(c,d)`- and
  `(b,c{+}d)`-column factors), so the two signs cancel in the transport
  law itself, leaving unconditional equivariance;
* the `c`-, `d`-slots (`comp_cslot`, `comp_dslot`): fully **direct**, no
  sign anywhere, on both sides (both slots act through a column's own
  first- or second-index slot on each side of the connector) — the
  simplest of the four;
* the right action (`comp_right`): transports along the coefficient
  recast `T_{a+(b+(c+d))} ≅ T_{a+(b+c+d)}` (`stdTowerCast`, M8a-8c′-0's
  device, keyed by the *same* associativity equality `add_assoc b c d`
  used to build `q4Close` itself) — a genuine cast, no sign, sourced from
  the new cast-compatibility lemma `columnCast_symm_coeff` (this file);
* the grading (`mem_grading`): `q4Close` is homogeneous of degree `0`
  (preserves the total Koszul degree exactly).

Two new cast-compatibility lemmas for `columnCast` are added alongside
`RouteRecast.lean`'s own two (`columnCast_symm_rslot`,
`columnCast_symm_symm_rslot`): `columnCast_symm_lslot` (the untouched
first-index slot commutes trivially with the cast — feeds `comp_aslot`)
and `columnCast_symm_coeff` (the natural coefficient action transports
along the induced sum-level tower cast — feeds `comp_right`), both
`subst`-`refl` facts exactly as their two forerunners.
-/
import Superfusion.Bimod.EdgeEquiv5
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

/-! ### Two more cast-compatibility lemmas for `columnCast` -/

/-- The column cast leaves the untouched first-index slot action alone
(the `a`-slot of `TowerColumn K a x`, unaffected by recasting the second
index `x`) — a `subst`-`refl` fact, mirroring `columnCast_symm_rslot`. -/
theorem columnCast_symm_lslot {x y : ZMod 8} (h : x = y)
    (t : (stdTower (K := K) a).carrier) (w : TowerColumn K a y) :
    columnCast K a h.symm (t • w) = t • columnCast K a h.symm w := by
  subst h
  rfl

/-- The column cast intertwines the *natural coefficient* action (as
opposed to `columnCast_symm_rslot`'s second-index slot action) along the
induced tower cast of the total sum — a `subst`-`refl` fact. -/
theorem columnCast_symm_coeff {x y : ZMod 8} (h : x = y)
    (τ : (stdTower (K := K) (a + y)).carrier) (v : TowerColumn K a y) :
    columnCast K a h.symm (MulOpposite.op τ • v)
      = MulOpposite.op ((stdTowerCast (K := K) (congrArg (a + ·) h)).toAlgEquiv.symm τ)
          • columnCast K a h.symm v := by
  subst h
  rfl

omit [Invertible (2 : K)] in
/-- The column cast preserves the descended grading — a `subst`-`refl`
fact. -/
theorem columnCast_symm_mem_grading {x y : ZMod 8} (h : x = y) {j : ZMod 2}
    {w : TowerColumn K a y} (hw : w ∈ TowerColumn.grading K a y j) :
    columnCast K a h.symm w ∈ TowerColumn.grading K a x j := by
  subst h
  exact hw

namespace PentagonB

attribute [local instance 500] leftModule rightModule

/-! ### Transport of `q4Close` -/

namespace Q4Close

/-- `q4Close_mk`, restated through the synonym-valued `mk`s of `Q4r`,
`BR` and `Q4` (the track's discipline) — bridges the raw `RelTensor.mk`
spelling of `q4Close_mk` to the generator lemmas of `Q4r` and `Q4`, by
`rfl` (`Q4r.mk`, `BR.mk`, `Q4.mk` unfold to `RelTensor.mk`). -/
private theorem q4Close_mk' (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d))) :
    q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = Q4.mk K a b c d (BR.mk K b c d v u)
          (columnCast K a (add_assoc b c d).symm w) :=
  q4Close_mk K a b c d v u w

/-- **`q4Close` transports the `a`-slot**, unconditionally and
sign-free: `Q4r`'s own mid-of-mid `a`-sign (keyed by the `(c,d)`-column's
degree `i`) and `BR(a,b,c{+}d)`'s own `a`-sign (keyed by the
`(b,c{+}d)`-column's degree `j`) combine to `sgn(k*(i+j))`, exactly
matching the sign produced by `Q4`'s own `a`-slot law (keyed by the
*combined* degree `i+j` of the `BR(b,c,d)`-factor) — so the two signs
cancel in the transport law itself. -/
theorem comp_aslot {i j k : ZMod 2}
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K b (c + d)} (hu : u ∈ TowerColumn.grading K b (c + d) j)
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (w : TowerColumn K a (b + (c + d))) :
    q4Close K a b c d (x • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = x • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) := by
  have hL : x • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)
      = ((sgn (k * (i + j)) : ℤˣ) : ℤ) •
          Q4r.mk K a b c d v (BR.mk K a b (c + d) u (x • w)) := by
    rw [Q4r.aslot_smul_mk_of_mem K a b c d hx hv (BR.mk K a b (c + d) u w),
      BR.aslot_smul_mk_of_mem K a b (c + d) hx hu w, map_zsmul, smul_smul,
      ← Units.val_mul, ← sgn_add, ← mul_add]
  have hR : x • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = ((sgn (k * (i + j)) : ℤˣ) : ℤ) •
          q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u (x • w))) := by
    rw [q4Close_mk', Q4.aslot_smul_mk_of_mem K a b c d hx
        (BR.mk_mem_grading K b c d hv hu)
        (columnCast K a (add_assoc b c d).symm w),
      ← columnCast_symm_lslot K a (add_assoc b c d) x w, ← q4Close_mk']
  rw [hL, map_zsmul, hR]

/-- **`q4Close` transports the `b`-slot**, unconditionally and
sign-free — exactly parallel to `comp_aslot`: `Q4r`'s own mid-of-mid
`b`-sign (keyed by the `(c,d)`-column's degree `i`) matches `BR(b,c,d)`'s
own `a'`-slot sign for `T_b` (keyed by the same `i`, the degree of its
`(c,d)`-factor) exactly. -/
theorem comp_bslot {i k : ZMod 2}
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    (u : TowerColumn K b (c + d)) (w : TowerColumn K a (b + (c + d))) :
    q4Close K a b c d (y • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = y • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) := by
  have hL : y • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          Q4r.mk K a b c d v (BR.mk K a b (c + d) (y • u) w) := by
    rw [Q4r.bslot_smul_mk_of_mem K a b c d hy hv (BR.mk K a b (c + d) u w),
      BR.bslot_smul_mk K a b (c + d) y u w]
  have hR : y • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) (y • u) w)) := by
    rw [q4Close_mk', Q4.bslot_smul_mk K a b c d y (BR.mk K b c d v u)
        (columnCast K a (add_assoc b c d).symm w),
      BR.aslot_smul_mk_of_mem K b c d hy hv u]
    simp only [map_zsmul, LinearMap.smul_apply]
    rw [← q4Close_mk']
  rw [hL, map_zsmul, hR]

/-- **`q4Close` transports the `c`-slot**, fully directly (no sign, no
degree hypothesis anywhere) — the `c`-slot is the outer, direct
first-index slot of the `(c,d)`-column on both sides of the
connector. -/
theorem comp_cslot (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d))) (z : (stdTower (K := K) c).carrier) :
    q4Close K a b c d (z • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = z • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) := by
  rw [Q4r.cslot_smul_mk, q4Close_mk', q4Close_mk', Q4.cslot_smul_mk,
    BR.bslot_smul_mk K b c d z v u]

/-- **`q4Close` transports the `d`-slot**, fully directly — exactly
parallel to `comp_cslot` (the outer, direct second-index slot of the
`(c,d)`-column on both sides). -/
theorem comp_dslot (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d))) (t : (stdTower (K := K) d).carrier) :
    q4Close K a b c d (t • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = t • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) := by
  rw [Q4r.dslot_smul_mk, q4Close_mk', q4Close_mk', Q4.dslot_smul_mk,
    BR.cslot_smul_mk K b c d t v u]

/-- **`q4Close` transports the right action** along the coefficient
recast `T_{a+(b+(c+d))} ≅ T_{a+(b+c+d)}` (`stdTowerCast`, keyed by the
same associativity equality `add_assoc b c d` used to build `q4Close`
itself) — no sign, sourced from `columnCast_symm_coeff`. -/
theorem comp_right (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
    (w : TowerColumn K a (b + (c + d)))
    (τ : (stdTower (K := K) (a + (b + (c + d)))).carrier) :
    q4Close K a b c d
        (MulOpposite.op τ • Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      = MulOpposite.op ((stdTowerCast (K := K)
              (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm τ)
          • q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) := by
  rw [Q4r.right_smul_mk, BR.right_smul_mk, q4Close_mk',
    columnCast_symm_coeff K a (add_assoc b c d) τ w, ← Q4.right_smul_mk,
    ← q4Close_mk']

/-- **`q4Close` is homogeneous of degree `0`** — it preserves the total
Koszul degree exactly. -/
theorem mem_grading {i j jw : ZMod 2}
    {v : TowerColumn K c d} (hv : v ∈ TowerColumn.grading K c d i)
    {u : TowerColumn K b (c + d)} (hu : u ∈ TowerColumn.grading K b (c + d) j)
    {w : TowerColumn K a (b + (c + d))}
    (hw : w ∈ TowerColumn.grading K a (b + (c + d)) jw) :
    q4Close K a b c d (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w))
      ∈ Q4.grading K a b c d (i + (j + jw)) := by
  rw [q4Close_mk']
  have h := Q4.mk_mem_grading K a b c d (BR.mk_mem_grading K b c d hv hu)
    (columnCast_symm_mem_grading K a (add_assoc b c d) hw)
  rwa [show i + j + jw = i + (j + jw) from by ring] at h

end Q4Close

end PentagonB

end Bimod

end Superfusion
