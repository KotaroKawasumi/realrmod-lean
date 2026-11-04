/-
Superfusion / GaugeChi / HchiProto

**The architecture of `hχ`** — the second identification obligation of
`GaugeChi/RealGaugeTrivialization.lean`'s `realRegularTrivializationLean`.
Design record: `docs/hchi-design.md`.

The route, and what is already proved here:

1. **The `Ttab` connector family** (§1).  `TtabAPI`'s hypothesis-free
   `TtabEverywhere` — a nonzero member of `gInterSpace … (pTable a b c)` at
   every one of the 512 triples — packages as a `ConnectorFamily`.  Its
   `parity` field is the certgen table, so `ConnectorFamily.parity_eq`
   REPRODUCES `hp` (no circularity: the family's `mem` field is
   `TtabEverywhere_mem`, which comes from `isCovered`, which never mentions
   `gParity`).
2. **The connector coboundary law** (§1).  `chiOfFamily_rescale_dm₃` at
   `(Ttab, canonical)` gives, with `ρ := ratio Ttab canonical` produced by
   choice,
     `gChiCanon = chiOfFamily Ttab · δρ`,
   so `hχ` only ever needs the CLASS of `chiOfFamily Ttab` against the table.
3. **The comparison cochain is a 4-cocycle** (§3).  `gChiCanon` satisfies the
   Gu--Wen equation `δχ = (−1)^{p ∪₁ p}` (`gChiCanon_supercocycle`) and the
   frozen table satisfies the same equation with the same `p`
   (`realLeanTable_pentagon` + `d₄_regularQuadratic`), so
     `r := gChiCanonCochain · (dyadicHom ∘ χ_table)⁻¹`
   has `δr = 1`.  `hχ` is exactly `[r] = 0` in `H⁴(ℤ/8; ℝˣ)`.
4. **The splitting** (`Cochain/HchiCore.lean`).  `ℝˣ = {±1} × ℝ_{>0}`; the
   positive factor contributes nothing (`exists_dm₃_of_pos`: the averaging
   identity `δ(∏_g f(·,·,·,g)) = f^{|G|}` plus unique divisibility), so only
   the parity cochain `rsgn ∘ r ∈ Z⁴(ℤ/8; F₂)` matters
   (`exists_dm₃_of_sign_coboundary`).
5. **`H4Detects` is now a theorem** (§4).  `h4Detects_holds` discharges it
   from `Cochain/CyclicH4.lean` — the explicit cyclic-group contracting
   homotopy, with **no certificate data of any kind** (the once-planned
   45 KB frozen `F₂` package is superseded and unnecessary).
6. **What is left** (§4–§5) is the single proposition `DetectorVanishes`:
   FOUR pentagon signs, at the quadruples `(0,0,4,4), (4,0,0,4), (4,4,0,0),
   (4,4,4,4)`.  Four is provably the minimum: no functional of weight ≤ 3 on
   `C⁴(ℤ/8;F₂)` annihilates `B⁴` while detecting the nontrivial class.
   §5 reduces it further to `DetectorVanishesTtab`, which mentions only the
   CERTIFICATE family's pentagon scalar `chiTtab` (frozen certgen matrices),
   the canonical connectors having been divided out along `δρ`.
   `hchi_of_detector` assembles it into `hχ`, and
   `realRegularTrivializationOfTtabSigns` into the final structure.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.Cochain.CyclicH4
import Superfusion.Cochain.HchiCore
import Superfusion.GaugeChi.ConnectorRescale
import Superfusion.GaugeChi.QuintChain
import Superfusion.GaugeChi.TtabAPI
import Superfusion.GaugeChi.RealGaugeTrivialization

namespace Superfusion

namespace GaugeChi

open ConnectorFamily

/-- Shorthand for the group element `a` of `Multiplicative (ZMod 8)`. -/
abbrev mg (a : ZMod 8) : Multiplicative (ZMod 8) := Multiplicative.ofAdd a

/-! ## 1. The `Ttab` connector family and the coboundary law -/

/-- **The certificate connector family.**  `TtabAPI.TtabEverywhere` at every
triple, at the frozen certgen parity table. -/
noncomputable def TtabFamily : ConnectorFamily ℝ realGauge where
  T := TtabAPI.TtabEverywhere
  parity := TtabAPI.pTable
  mem := TtabAPI.TtabEverywhere_mem
  ne_zero := TtabAPI.TtabEverywhere_ne_zero

/-- `ConnectorFamily.parity_eq` at `TtabFamily` reproduces `hp`.  This is not
circular: the `mem` field is `TtabEverywhere_mem`, whose proof (`isCovered`)
never mentions `gParity`. -/
theorem TtabFamily_parity_eq (a b c : ZMod 8) :
    TtabAPI.pTable a b c = gParity ℝ realGauge a b c :=
  TtabFamily.parity_eq a b c

/-- The pentagon scalar of the certificate family. -/
noncomputable def chiTtab (a b c d : ZMod 8) : ℝ :=
  chiOfFamily ℝ realGauge TtabFamily a b c d

/-- The unit-valued 3-cochain comparing the canonical connectors with the
certificate ones (`gTCanon = ρ • Ttab`), produced by choice. -/
noncomputable def rhoTtab : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) →
    Multiplicative (ZMod 8) → ℝˣ :=
  fun x y z => ratio TtabFamily (canonical ℝ realGauge) x.toAdd y.toAdd z.toAdd

/-- **The coboundary law at the certificate family**: the canonical pentagon
scalar differs from the certificate one by the explicit coboundary `δρ`. -/
theorem gChiCanon_eq_chiTtab_mul_dm₃ (x y z w : Multiplicative (ZMod 8)) :
    gChiCanon ℝ realGauge x.toAdd y.toAdd z.toAdd w.toAdd
      = chiTtab x.toAdd y.toAdd z.toAdd w.toAdd
        * ((dm₃ rhoTtab x y z w : ℝˣ) : ℝ) :=
  (chiOfFamily_canonical ℝ realGauge (a := x.toAdd) (b := y.toAdd) (c := z.toAdd)
      (d := w.toAdd)).symm.trans
    (chiOfFamily_rescale_dm₃ ℝ realGauge TtabFamily (canonical ℝ realGauge) x y z w)

/-- The same, in the cochain packaging the trivialization consumes. -/
theorem gChiCanonCochain_val (x y z w : Multiplicative (ZMod 8)) :
    ((gChiCanonCochain ℝ realGauge x y z w : ℝˣ) : ℝ)
      = chiTtab x.toAdd y.toAdd z.toAdd w.toAdd * ((dm₃ rhoTtab x y z w : ℝˣ) : ℝ) :=
  gChiCanon_eq_chiTtab_mul_dm₃ x y z w

/-! ## 2. The parity bridge: the two packings of `p` agree -/

/-- The `TtabAPI` packing of the parity table and the `RealGaugeTables`
packing agree at all 512 triples. -/
theorem realLeanParityTable_eq_pTable (a b c : ZMod 8) :
    realLeanParityTable (mg a) (mg b) (mg c) = TtabAPI.pTable a b c := by
  revert a b c
  decide +kernel

/-- `hp` in the form `realRegularTrivializationLean` consumes it. -/
theorem gParityCochain_eq_realLeanParityTable (a b c : Multiplicative (ZMod 8)) :
    gParityCochain ℝ realGauge a b c = realLeanParityTable a b c :=
  (TtabAPI.gParity_eq_pTable_all a.toAdd b.toAdd c.toAdd).trans
    (realLeanParityTable_eq_pTable a.toAdd b.toAdd c.toAdd).symm

/-! ## 3. The comparison cochain is a four-cocycle -/

/-- The comparison of the canonical pentagon scalar with the frozen table. -/
noncomputable def hchiRatio (a b c d : Multiplicative (ZMod 8)) : ℝˣ :=
  gChiCanonCochain ℝ realGauge a b c d * (dyadicHom ℝ (realLeanChiTable a b c d))⁻¹

/-- The frozen table satisfies the Gu--Wen equation with the table parity. -/
theorem dm₄_realLeanChiTable (a b c d e : Multiplicative (ZMod 8)) :
    dm₄ realLeanChiTable a b c d e
      = sgn (cupOne₃₃ realLeanParityTable realLeanParityTable a b c d e) := by
  have hβ : (fun x y z w => realLeanChiTable x y z w *
      sgn (regularQuadratic realLeanNuTable realLeanParityTable x y z w))
      = dm₃ realLeanBetaTable := by
    funext x y z w
    exact realLeanTable_pentagon x y z w
  have h1 : dm₄ (fun x y z w => realLeanChiTable x y z w *
      sgn (regularQuadratic realLeanNuTable realLeanParityTable x y z w)) a b c d e = 1 := by
    rw [hβ, dm₄_dm₃]
  rw [dm₄_mul, dm₄_sgn,
    d₄_regularQuadratic realLeanNuTable realLeanParityTable realLeanNuTable_parity] at h1
  have := mul_eq_one_iff_eq_inv.mp h1
  rw [this, sgn_inv]

/-- **The comparison cochain is a 4-cocycle** — the two sides satisfy the same
Gu--Wen equation, with the same parity three-cochain. -/
theorem dm₄_hchiRatio (a b c d e : Multiplicative (ZMod 8)) :
    dm₄ hchiRatio a b c d e = 1 := by
  have hp : gParityCochain ℝ realGauge = realLeanParityTable := by
    funext x y z
    exact gParityCochain_eq_realLeanParityTable x y z
  have hcanon := gChiCanon_supercocycle ℝ realGauge a b c d e
  rw [hp] at hcanon
  have htab : dm₄ (fun x y z w => dyadicHom ℝ (realLeanChiTable x y z w)) a b c d e
      = sgn (cupOne₃₃ realLeanParityTable realLeanParityTable a b c d e) := by
    rw [← map_dm₄ (dyadicHom ℝ) realLeanChiTable, dm₄_realLeanChiTable]
    exact map_sgn (dyadicHom ℝ) (dyadicHom_sign ℝ) _
  have hsplit : dm₄ hchiRatio a b c d e
      = dm₄ (gChiCanonCochain ℝ realGauge) a b c d e
        * (dm₄ (fun x y z w => dyadicHom ℝ (realLeanChiTable x y z w)) a b c d e)⁻¹ := by
    rw [← dm₄_inv, ← dm₄_mul]
    rfl
  rw [hsplit, htab, hcanon, mul_inv_cancel]

/-! ## 4. The two residual obligations, and the assembly -/

/-- The parity cochain of the comparison — the only place a sign of a pentagon
scalar is ever needed. -/
noncomputable def hchiParity (a b c d : Multiplicative (ZMod 8)) : ZMod 2 :=
  rsgn (hchiRatio a b c d)

theorem hchiParity_cocycle (a b c d e : Multiplicative (ZMod 8)) :
    d₄ hchiParity a b c d e = 0 :=
  d₄_rsgn_eq_zero hchiRatio dm₄_hchiRatio a b c d e

/-- **Obligation A — the detector.**  The `H⁴(ℤ/8;F₂)`-detecting functional of
minimal weight, evaluated on the comparison parity: FOUR pentagon
evaluations, all with labels in the subgroup `{0,4}`. -/
def DetectorVanishes : Prop :=
  hchiParity (mg 0) (mg 0) (mg 4) (mg 4) + hchiParity (mg 4) (mg 0) (mg 0) (mg 4)
      + hchiParity (mg 4) (mg 4) (mg 0) (mg 0) + hchiParity (mg 4) (mg 4) (mg 4) (mg 4)
    = 0

/-- **Obligation B — the finite `F₂` fact.**  A four-cocycle on `ℤ/8` killed by
the weight-four detector is a coboundary.  Purely finite linear algebra over
`F₂`; no pentagon input. -/
def H4Detects : Prop :=
  ∀ s : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) →
      Multiplicative (ZMod 8) → ZMod 2,
    (∀ a b c d e, d₄ s a b c d e = 0) →
    s (mg 0) (mg 0) (mg 4) (mg 4) + s (mg 4) (mg 0) (mg 0) (mg 4)
        + s (mg 4) (mg 4) (mg 0) (mg 0) + s (mg 4) (mg 4) (mg 4) (mg 4) = 0 →
    ∃ u : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → ZMod 2,
      ∀ a b c d, s a b c d = d₃ u a b c d

/-- **Obligation B is a theorem** (`Cochain/CyclicH4.lean`): no certificate
data, no pentagon input — the explicit cyclic-group homotopy. -/
theorem h4Detects_holds : H4Detects := by
  intro s hs hdet
  refine CyclicH4.h4Detects s hs ?_
  have h0 : (1 : Multiplicative (ZMod 8)) = mg 0 := rfl
  have h4 : CyclicH4.gm 4 = mg 4 := by decide
  simp only [CyclicH4.lam, h0, h4]
  exact hdet

/-- **`hχ` from the two obligations.** -/
theorem hchi_of (hB : H4Detects) (hA : DetectorVanishes) :
    ∃ γ : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → ℝˣ,
      ∀ a b c d, gChiCanonCochain ℝ realGauge a b c d
        = dyadicHom ℝ (realLeanChiTable a b c d) * dm₃ γ a b c d := by
  obtain ⟨u, hu⟩ := hB hchiParity hchiParity_cocycle hA
  obtain ⟨γ, hγ⟩ := exists_dm₃_of_sign_coboundary hchiRatio dm₄_hchiRatio u hu
  refine ⟨γ, fun a b c d => ?_⟩
  have h : gChiCanonCochain ℝ realGauge a b c d
      * (dyadicHom ℝ (realLeanChiTable a b c d))⁻¹ = dm₃ γ a b c d := hγ a b c d
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h, mul_comm]

/-- **`hχ` from the single remaining obligation.** -/
theorem hchi_of_detector (hA : DetectorVanishes) :
    ∃ γ : Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → Multiplicative (ZMod 8) → ℝˣ,
      ∀ a b c d, gChiCanonCochain ℝ realGauge a b c d
        = dyadicHom ℝ (realLeanChiTable a b c d) * dm₃ γ a b c d :=
  hchi_of h4Detects_holds hA

/-- **The real regular trivialization, modulo the single residual
obligation** `DetectorVanishes` — four pentagon signs. -/
noncomputable def realRegularTrivializationOfDetector
    (hA : DetectorVanishes) : realGauge.RegularTrivialization ℝ :=
  realRegularTrivializationLean gParityCochain_eq_realLeanParityTable
    (hchi_of_detector hA).choose (hchi_of_detector hA).choose_spec

/-! ## 5. The detector, reduced to the certificate connectors

`DetectorVanishes` still mentions the CANONICAL connectors, which exist only
by `Classical.choice`.  Dividing out the explicit coboundary `δρ` of §1
replaces them by the certificate family's own pentagon scalar `chiTtab`,
whose connectors are the frozen certgen matrices `TtabAPI.TtabEverywhere`.
`lam` kills the coboundary (`CyclicH4.lam_d₃`), so the two obligations are
equivalent — and the reduced one is the shape a pentagon-evaluation layer
would actually produce. -/

/-- `rsgn` of a multiplicative coboundary is the additive coboundary of
`rsgn`. -/
theorem rsgn_dm₃ {G : Type*} [Group G] (ρ : G → G → G → ℝˣ) (a b c d : G) :
    rsgn (dm₃ ρ a b c d) = d₃ (fun x y z => rsgn (ρ x y z)) a b c d := by
  simp only [dm₃, d₃, rsgn_mul, rsgn_inv, CyclicH4.sub_eq_add₂]

/-- The comparison of the CERTIFICATE pentagon scalar with the frozen table. -/
noncomputable def ttabRatio (a b c d : Multiplicative (ZMod 8)) : ℝˣ :=
  gChiCanonCochain ℝ realGauge a b c d * (dm₃ rhoTtab a b c d)⁻¹
    * (dyadicHom ℝ (realLeanChiTable a b c d))⁻¹

/-- **What the reduced obligation is really about**: the underlying real
number of `ttabRatio` is the certificate family's own pentagon scalar
divided by the table entry.  No canonical connector survives. -/
theorem ttabRatio_val (a b c d : Multiplicative (ZMod 8)) :
    ((ttabRatio a b c d : ℝˣ) : ℝ)
      = chiTtab a.toAdd b.toAdd c.toAdd d.toAdd
        * ((dyadicHom ℝ (realLeanChiTable a b c d) : ℝˣ) : ℝ)⁻¹ := by
  have hB : ((dm₃ rhoTtab a b c d : ℝˣ) : ℝ) ≠ 0 := (dm₃ rhoTtab a b c d).ne_zero
  simp only [ttabRatio, Units.val_mul, Units.val_inv_eq_inv_val, gChiCanonCochain_val]
  field_simp

/-- The parity of the certificate-level comparison. -/
noncomputable def ttabParity (a b c d : Multiplicative (ZMod 8)) : ZMod 2 :=
  rsgn (ttabRatio a b c d)

theorem hchiParity_eq (a b c d : Multiplicative (ZMod 8)) :
    hchiParity a b c d
      = ttabParity a b c d + d₃ (fun x y z => rsgn (rhoTtab x y z)) a b c d := by
  simp only [hchiParity, ttabParity, hchiRatio, ttabRatio, rsgn_mul, rsgn_inv, ← rsgn_dm₃]
  generalize rsgn (gChiCanonCochain ℝ realGauge a b c d) = X
  generalize rsgn (dm₃ rhoTtab a b c d) = Y
  generalize rsgn (dyadicHom ℝ (realLeanChiTable a b c d)) = Z
  revert X Y Z; decide

/-- **Obligation A, reduced to the certificate family.**  Four signs of
`chiTtab / table`, at `(0,0,4,4)`, `(4,0,0,4)`, `(4,4,0,0)`, `(4,4,4,4)`. -/
def DetectorVanishesTtab : Prop :=
  ttabParity (mg 0) (mg 0) (mg 4) (mg 4) + ttabParity (mg 4) (mg 0) (mg 0) (mg 4)
      + ttabParity (mg 4) (mg 4) (mg 0) (mg 0) + ttabParity (mg 4) (mg 4) (mg 4) (mg 4)
    = 0

private theorem z2_detector : ∀ t1 t2 t3 t4 r1 r2 r3 r4 : ZMod 2,
    t1 + t2 + t3 + t4 = 0 → r1 + r2 + r3 + r4 = 0 →
    (t1 + r1) + (t2 + r2) + (t3 + r3) + (t4 + r4) = 0 := by decide

theorem detectorVanishes_of_ttab (h : DetectorVanishesTtab) : DetectorVanishes := by
  have h0 : (1 : Multiplicative (ZMod 8)) = mg 0 := rfl
  have h4 : CyclicH4.gm 4 = mg 4 := by decide
  have hz := CyclicH4.lam_d₃ (fun x y z => rsgn (rhoTtab x y z))
  simp only [CyclicH4.lam, h0, h4] at hz
  simp only [DetectorVanishes, hchiParity_eq]
  exact z2_detector _ _ _ _ _ _ _ _ h hz

/-- **The real regular trivialization, modulo the four certificate pentagon
signs** — the maximally reduced form of the M15 endgame. -/
noncomputable def realRegularTrivializationOfTtabSigns
    (h : DetectorVanishesTtab) : realGauge.RegularTrivialization ℝ :=
  realRegularTrivializationOfDetector (detectorVanishes_of_ttab h)

end GaugeChi

end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TtabFamily_parity_eq
#print axioms Superfusion.GaugeChi.gChiCanon_eq_chiTtab_mul_dm₃
#print axioms Superfusion.GaugeChi.realLeanParityTable_eq_pTable
#print axioms Superfusion.GaugeChi.gParityCochain_eq_realLeanParityTable
#print axioms Superfusion.GaugeChi.dm₄_realLeanChiTable
#print axioms Superfusion.GaugeChi.dm₄_hchiRatio
#print axioms Superfusion.GaugeChi.hchiParity_cocycle
#print axioms Superfusion.GaugeChi.hchi_of
#print axioms Superfusion.GaugeChi.h4Detects_holds
#print axioms Superfusion.GaugeChi.realRegularTrivializationOfDetector
#print axioms Superfusion.GaugeChi.ttabRatio_val
#print axioms Superfusion.GaugeChi.detectorVanishes_of_ttab
#print axioms Superfusion.GaugeChi.realRegularTrivializationOfTtabSigns
#print axioms Superfusion.exists_dm₃_of_pos
#print axioms Superfusion.exists_dm₃_of_sign_coboundary
