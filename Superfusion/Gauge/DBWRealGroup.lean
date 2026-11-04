/-
Superfusion / Gauge / DBWRealGroup

A short corollary round after `Superfusion.Gauge.RealClassification2`'s
completed classification: this file packages the division-representable
Brauer–Wall classes of `ℝ` as an honest subgroup of `BW ℝ`, and identifies it
with `ZMod 8`, completing the *group-structure* determination of `DBW ℝ`.

**Contents.**

* `DBW_real_mulClosed`: `DBW ℝ` is closed under multiplication — the
  `K = ℝ` instance of the open `DBW.MulClosed` target (`Superfusion.Gauge.DBW`),
  obtained for free here from `DBW_real_eq_range` and homomorphy of
  `realGauge.bwClass` (`bwClass_add`), *without* invoking the general
  mini-Wedderburn theorem (which remains open for a general field `K`).
* `DBWRealSubgroup : Subgroup (BW ℝ)`: `DBW ℝ` packaged as a subgroup, using
  `DBW.one_mem`, `DBW_real_mulClosed`, `DBW.inv_mem`.
* `zmod8_mulEquiv_DBWReal : Multiplicative (ZMod 8) ≃* DBWRealSubgroup`: the
  bijection `zmod8_equiv_DBW_real` upgraded to a group isomorphism, via
  homomorphy of `realGauge.bwClass`.
* `DBW_real_finite`, `DBW_real_ncard`: `DBW ℝ` is a finite set of exactly `8`
  elements — cheap, quotable corollaries of the equiv above.

This completes the group-structure determination of the division-representable
Brauer–Wall classes of `ℝ`. The full statement `BW ℝ ≅ ℤ/8` (i.e. `DBW ℝ =
BW ℝ`, every Brauer–Wall class of `ℝ` is division-representable) still awaits
the general mini-Wedderburn theorem (`DBW.MulClosed` for a general field, and
the reverse inclusion `BW K ⊆ DBW K` more broadly).

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.RealClassification2

namespace Superfusion

/-! ### `DBW ℝ` is multiplicatively closed -/

/-- **`DBW ℝ` is closed under multiplication.** Both factors are of the form
`realGauge.bwClass a`, `realGauge.bwClass b` (`DBW_real_eq_range`), and their product is
`realGauge.bwClass (a + b)` (`DivisionFusionGauge.bwClass_add`), again in the range. This is the
`K = ℝ` instance of the open `DBW.MulClosed` target of `Superfusion.Gauge.DBW`, landed here without
appeal to a general mini-Wedderburn theorem. -/
theorem DBW_real_mulClosed : DBW.MulClosed (K := ℝ) := by
  intro x y hx hy
  rw [DBW_real_eq_range] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [DBW_real_eq_range]
  exact ⟨a + b, realGauge.bwClass_add a b⟩

/-! ### `DBW ℝ` as a subgroup of `BW ℝ` -/

/-- **`DBW ℝ`, packaged as a subgroup of `BW ℝ`.** The three closure properties
(`DBW.one_mem`, `DBW_real_mulClosed`, `DBW.inv_mem`) are exactly the data needed. -/
noncomputable def DBWRealSubgroup : Subgroup (BW ℝ) where
  carrier := DBW ℝ
  one_mem' := DBW.one_mem
  mul_mem' hx hy := DBW_real_mulClosed _ _ hx hy
  inv_mem' hx := DBW.inv_mem hx

/-! ### The group isomorphism with `ZMod 8` -/

/-- The class map, corestricted to `DBWRealSubgroup`, as a plain function on
`Multiplicative (ZMod 8)`. -/
private noncomputable def zmod8_mulEquiv_DBWReal_toFun (a : Multiplicative (ZMod 8)) :
    DBWRealSubgroup :=
  ⟨realGauge.bwClass (Multiplicative.toAdd a), realGauge_bwClass_mem_DBW _⟩

private theorem zmod8_mulEquiv_DBWReal_injective :
    Function.Injective zmod8_mulEquiv_DBWReal_toFun := by
  intro a b hab
  have h : realGauge.bwClass (Multiplicative.toAdd a) = realGauge.bwClass (Multiplicative.toAdd b) :=
    congrArg Subtype.val hab
  exact Multiplicative.toAdd.injective (realGauge_bwClass_injective h)

private theorem zmod8_mulEquiv_DBWReal_surjective :
    Function.Surjective zmod8_mulEquiv_DBWReal_toFun := by
  rintro ⟨x, hx⟩
  have hx' : x ∈ Set.range realGauge.bwClass := DBW_real_eq_range ▸ hx
  obtain ⟨a, rfl⟩ := hx'
  exact ⟨Multiplicative.ofAdd a, rfl⟩

private theorem zmod8_mulEquiv_DBWReal_map_mul (a b : Multiplicative (ZMod 8)) :
    zmod8_mulEquiv_DBWReal_toFun (a * b)
      = zmod8_mulEquiv_DBWReal_toFun a * zmod8_mulEquiv_DBWReal_toFun b := by
  apply Subtype.ext
  show realGauge.bwClass (Multiplicative.toAdd (a * b))
      = realGauge.bwClass (Multiplicative.toAdd a) * realGauge.bwClass (Multiplicative.toAdd b)
  rw [toAdd_mul]
  exact realGauge.bwClass_add _ _

/-- **The finale, upgraded to a group isomorphism**: `DBWRealSubgroup ≅ ℤ/8` as groups, via the
class map `realGauge.bwClass`, bijective by `realGauge_bwClass_injective`/`DBW_real_eq_range`
(the same data underlying `zmod8_equiv_DBW_real`) and multiplicative by `bwClass_add`. -/
noncomputable def zmod8_mulEquiv_DBWReal : Multiplicative (ZMod 8) ≃* DBWRealSubgroup where
  toEquiv := Equiv.ofBijective zmod8_mulEquiv_DBWReal_toFun
    ⟨zmod8_mulEquiv_DBWReal_injective, zmod8_mulEquiv_DBWReal_surjective⟩
  map_mul' := zmod8_mulEquiv_DBWReal_map_mul

/-! ### Finiteness -/

/-- **`DBW ℝ` is finite**: it is the range of a function out of the finite type `ZMod 8`
(`DBW_real_eq_range`). -/
theorem DBW_real_finite : (DBW ℝ).Finite := by
  rw [DBW_real_eq_range]
  exact Set.finite_range realGauge.bwClass

/-- **`DBW ℝ` has exactly `8` elements**, via the bijection `zmod8_equiv_DBW_real` with
`ZMod 8`. -/
theorem DBW_real_ncard : (DBW ℝ).ncard = 8 := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr zmod8_equiv_DBW_real.symm, Nat.card_eq_fintype_card,
    ZMod.card]

end Superfusion
