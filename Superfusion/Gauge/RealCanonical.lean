/-
Superfusion / Gauge / RealCanonical

Milestone M9-4d, part 1 of the intrinsic gauge track: **canonicity of
`realGauge`** (`Superfusion.Gauge.RealGaugeInstance`) — injectivity of its
Brauer–Wall class map, and division-representability of its range.

**Contents.**

* `realGauge_bwClass_mem_DBW`: every `realRep a` is itself a witness that
  `realGauge.bwClass a ∈ DBW ℝ` (`Superfusion.Gauge.DBW`) — the range
  inclusion `Set.range realGauge.bwClass ⊆ DBW ℝ`.
* `realGauge_bwClass_one_orderOf`: `orderOf (realGauge.bwClass 1) = 8`,
  transported from the landed `orderOf bwGenReal = 8`
  (`Superfusion.Super.QuaternionObstruction.orderOf_bwGenReal`, M7f-5) across
  the inversion identity `realGauge.bwClass 7 = (realGauge.bwClass 1)⁻¹`
  (`7 = -1` in `ZMod 8`, and inverses share order).
* `realGauge_bwClass_injective`: the class map is injective, from the order
  computation plus the elementary fact that an element of `ZMod 8` killed by
  a hom whose generator has order `8` must be `0`.
* `realGauge_isCanonical_of_surjective`: packages injectivity with the
  range-inclusion, so that `DivisionFusionGauge.IsCanonical` (`Superfusion
  .Gauge.DBW`) follows from the *only* missing hypothesis — surjectivity of
  `realGauge.bwClass` onto `DBW ℝ`, i.e. **every real central super division
  algebra is Brauer–Wall equivalent to one of the eight `realRep`s** (the
  real division classification theorem, deliberately left open — a future
  arc of work, not attempted here).
* `realGauge_bwClassHom_one_addOrderOf`: the additive restatement of the
  order computation, via `realGauge.bwClassHom : ZMod 8 →+ Additive (BW ℝ)`.

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealGaugeInstance
import Superfusion.Super.QuaternionObstruction

namespace Superfusion

/-! ### The range lies in `DBW ℝ` -/

/-- **Every `realGauge.bwClass a` is division-representable**: `realRep a` itself is a witness,
via the field bundle of `realGauge` (`realRep_isSuperCentral`, `realRep_isGradedSimple`,
`realRep_finiteDimensional`, `realRep_nontrivial`, `realRep_isSuperDivision`,
`Superfusion.Gauge.RealReps`) together with `DivisionFusionGauge.bwClass_val` and `realGauge_D`. -/
theorem realGauge_bwClass_mem_DBW (a : ZMod 8) : realGauge.bwClass a ∈ DBW ℝ :=
  ⟨realRep a, realRep_isSuperCentral a, realRep_isGradedSimple a, realRep_finiteDimensional a,
    realRep_nontrivial a, realRep_isSuperDivision a, (realGauge.bwClass_val a).symm⟩

/-! ### Injectivity of the class map -/

/-- `(1 : ZMod 8) + 7 = 0`, so `realGauge.bwClass 1 * realGauge.bwClass 7 = 1`. -/
private theorem realGauge_bwClass_one_mul_seven :
    realGauge.bwClass 1 * realGauge.bwClass 7 = 1 := by
  have h := realGauge.bwClass_add 1 7
  rw [show (1 : ZMod 8) + 7 = 0 from by decide, realGauge.bwClass_zero] at h
  exact h.symm

/-- **`realGauge.bwClass 7` is the inverse of `realGauge.bwClass 1`** in `BW ℝ`. -/
private theorem realGauge_bwClass_seven_eq_inv :
    realGauge.bwClass 7 = (realGauge.bwClass 1)⁻¹ :=
  eq_inv_of_mul_eq_one_right realGauge_bwClass_one_mul_seven

/-- **`orderOf (realGauge.bwClass 1) = 8`**: transported from the landed `orderOf bwGenReal = 8`
(M7f-5) across `realGauge.bwClass 7 = bwGenReal` (`realGauge_bwClass_seven`, a genuine `rfl`) and
the inversion identity above (inverses share order, `orderOf_inv`). -/
theorem realGauge_bwClass_one_orderOf : orderOf (realGauge.bwClass 1) = 8 := by
  rw [← orderOf_inv, ← realGauge_bwClass_seven_eq_inv, realGauge_bwClass_seven, orderOf_bwGenReal]

/-- **The class map sends `ℕ`-casts to powers of the class of `1`**: `realGauge.bwClass n =
(realGauge.bwClass 1)^n` for `n : ℕ`, by induction on `bwClass_add`/`bwClass_zero`. -/
private theorem realGauge_bwClass_natCast_pow (n : ℕ) :
    realGauge.bwClass (n : ZMod 8) = (realGauge.bwClass 1) ^ n := by
  induction n with
  | zero => simp [realGauge.bwClass_zero]
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ZMod 8) = (n : ZMod 8) + 1 := by push_cast; ring
      rw [hcast, realGauge.bwClass_add, ih, pow_succ]

/-- **The kernel of the class map is trivial**: if `realGauge.bwClass c = 1`, writing `c` as the
cast of `c.val < 8` and using `realGauge_bwClass_natCast_pow` reduces to `(realGauge.bwClass
1)^(c.val) = 1`, i.e. `orderOf (realGauge.bwClass 1) ∣ c.val`; since the order is `8` and `c.val <
8`, this forces `c.val = 0`, i.e. `c = 0`. -/
private theorem realGauge_bwClass_eq_one_iff {c : ZMod 8} (hc : realGauge.bwClass c = 1) :
    c = 0 := by
  have hval : realGauge.bwClass (c.val : ZMod 8) = 1 := by rwa [ZMod.natCast_zmod_val]
  rw [realGauge_bwClass_natCast_pow] at hval
  have hdvd : (8 : ℕ) ∣ c.val := by
    have := orderOf_dvd_of_pow_eq_one hval
    rwa [realGauge_bwClass_one_orderOf] at this
  have hlt : c.val < 8 := ZMod.val_lt c
  have hval0 : c.val = 0 := by omega
  exact (ZMod.val_eq_zero c).mp hval0

/-- **The Brauer–Wall class map of `realGauge` is injective**: distinct skeleton floors
`realRep a`, `realRep b` have distinct Brauer–Wall classes. Route: reduce `bwClass a = bwClass b`
to `bwClass (a - b) = 1` (via `bwClass_add`, `mul_eq_right`) and apply
`realGauge_bwClass_eq_one_iff`. -/
theorem realGauge_bwClass_injective : Function.Injective realGauge.bwClass := by
  intro a b hab
  have hadd : realGauge.bwClass (a - b) * realGauge.bwClass b = realGauge.bwClass a := by
    have h := realGauge.bwClass_add (a - b) b
    rw [show a - b + b = a from by abel] at h
    exact h.symm
  rw [hab] at hadd
  have h1 : realGauge.bwClass (a - b) = 1 := mul_eq_right.mp hadd
  have h2 : a - b = 0 := realGauge_bwClass_eq_one_iff h1
  exact sub_eq_zero.mp h2

/-! ### Packaging: canonicity, modulo the classification -/

/-- **Canonicity of `realGauge`, modulo the open real division classification**: injectivity
(`realGauge_bwClass_injective`) together with the range-inclusion `realGauge_bwClass_mem_DBW`
account for everything in `DivisionFusionGauge.IsCanonical` (`Superfusion.Gauge.DBW`) except the
reverse inclusion `DBW ℝ ⊆ Set.range realGauge.bwClass` — i.e. **every real central super division
algebra is Brauer–Wall equivalent to one of the eight `realRep`s**, the real division
classification theorem. That surjectivity statement is the *only* missing hypothesis here, and is
deliberately left open — a future arc of work, not attempted in this milestone. -/
theorem realGauge_isCanonical_of_surjective
    (h : ∀ x ∈ DBW ℝ, ∃ a, realGauge.bwClass a = x) : realGauge.IsCanonical := by
  refine ⟨realGauge_bwClass_injective, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨a, rfl⟩
    exact realGauge_bwClass_mem_DBW a
  · intro x hx
    exact h x hx

/-! ### Bonus: the additive restatement -/

/-- **The additive restatement**, via the bundled hom `realGauge.bwClassHom : ZMod 8 →+ Additive
(BW ℝ)`: the additive order of the class of `1` is also `8`, matching
`realGauge_bwClass_one_orderOf` across `addOrderOf_ofMul_eq_orderOf`. -/
theorem realGauge_bwClassHom_one_addOrderOf :
    addOrderOf (realGauge.bwClassHom 1) = 8 := by
  rw [show realGauge.bwClassHom 1 = Additive.ofMul (realGauge.bwClass 1) from rfl,
    addOrderOf_ofMul_eq_orderOf]
  exact realGauge_bwClass_one_orderOf

end Superfusion
