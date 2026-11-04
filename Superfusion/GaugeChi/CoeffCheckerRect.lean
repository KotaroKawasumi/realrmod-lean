/-
Superfusion / GaugeChi / CoeffCheckerRect

**The rectangular coefficient checker: closing the interface gap between
`GaugeChi/CoeffChecker.lean` and `GaugeChi/TDictGaugeNative.lean`.**

`CoeffChecker`'s arithmetic layer is SQUARE: `matOfCoeff` takes
`x : ι → ι → Fin k → ℤ` to a `Matrix ι ι P`, and its transport lemma
`checkMatEq_sound_submatrix` takes ONE index equivalence `e : ι ≃ Fin σ`.
The `hsz`-free device of `TDictGaugeNative` is RECTANGULAR: a native
connector is

  `NativeT = Matrix (Fin σR.1 ⊕ Fin σR.2) (Fin σL.1 ⊕ Fin σL.2) D_{a+(b+c)}`

and the identity it must satisfy at a slot generator is

  `routeRMat y * T = c • (T * routeLNativeMat y)`,   `c = sgn(|y|·e)`,

whose three matrices live at THREE different shapes:

| | rows | columns |
|---|---|---|
| `X = routeRMat y` | `Fin σR.1 ⊕ Fin σR.2` | `Fin σR.1 ⊕ Fin σR.2` |
| `T` | `Fin σR.1 ⊕ Fin σR.2` | `Fin σL.1 ⊕ Fin σL.2` |
| `Y = routeLNativeMat y` | `Fin σL.1 ⊕ Fin σL.2` | `Fin σL.1 ⊕ Fin σL.2` |

At the 12 exceptional triples `(x,4,4)` and `(4,4,x)`, `x ∈ {1,2,3,5,6,7}`
(`docs/route-layer-design.md` §1.5) the row and column index types are
**genuinely different types**: `Fin 4 ⊕ Fin 0` versus `Fin 2 ⊕ Fin 2`.  A
single-equivalence transport cannot state, let alone prove, the identity
there.

## What this file adds

* §R1 `matOfCoeff₂ : (ιr → ιc → Fin k → ℤ) → Matrix ιr ιc P` with the
  rectangular `convCoeff₂` / `matOfCoeff₂_mul` (row/inner/column types all
  independent), `matOfCoeff₂_zsmul`, `matOfCoeff₂_injective`.
* §R2 `checkMatEq_sound₂` and **`checkMatEq_sound_submatrix₂`**, the
  two-equivalence transport `(eR : ιR ≃ Fin σ) (eL : ιL ≃ Fin σ)` producing
  exactly `X * T = c • (T * Y)` at the three shapes above.
* §R3 the square layer of `CoeffChecker` **re-derived** from the rectangular
  one — `matOfCoeff` is *definitionally* `matOfCoeff₂` at `ιc = ιr`
  (`matOfCoeff_eq_matOfCoeff₂` is `rfl`), so the rollout can use ONE device.
* §R4 the `realGauge` consumers: `realCheckMatEq₂_sound'` at an arbitrary
  pair of frame equivalences, and `realCheckMatEqFrame_sound`, stated
  directly at the `Fin p ⊕ Fin q` frames that `NativeT` uses.
* §R5 **the single-`σ` justification, proved in Lean at all 512 triples**:
  `realGauge_gaugeSize_total_eq` says the row total `σR.1 + σR.2` equals the
  column total `σL.1 + σL.2` everywhere, while
  `realGauge_gaugeSize_ne` records that the *sizes themselves* do not agree
  everywhere.  So one `σ` per triple always suffices, and the two
  equivalences of `checkMatEq_sound_submatrix₂` are the only generalization
  the native device needs.
* §R6 a self-test at the exceptional shape `Fin 4 ⊕ Fin 0` × `Fin 2 ⊕ Fin 2`
  over `D₃` (`k = 8`, `σ = 4`), discharged by `decide +kernel`, with a
  negative control.
* §R7 `nativeIntertwine_of_cert`, the interface check against
  `TDictGaugeNative`: a checked certificate delivers
  `X * T = c • (T * Y)` at `NativeT`'s own types — the exact shape of
  `hAint`/`hBint`/`hCint` in
  `gtOfTNative_mem_interSpace_of_slot_generators` — with the remaining
  semantic bridge (T4 of `docs/route-layer-design.md` §5) isolated as three
  explicit `= matOfCoeff₂ …` hypotheses.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.CoeffChecker
import Superfusion.GaugeChi.TDictGaugeNative

namespace Superfusion

open Module

/-! ## R1. Rectangular matrices over a based algebra

Everything in `CoeffChecker`'s T2 with the single index type `ι` split into
three: `ιr` (rows), `ιm` (the contracted middle) and `ιc` (columns).  Only
the middle one needs to be a `Fintype`. -/

section CoeffRect

variable {R : Type*} [CommRing R] {P : Type*} [Ring P] [Algebra R P]
variable {ιr ιm ιc : Type*} {k : ℕ}

/-- **The rectangular `matOfCoeff`**: the `ιr × ιc` matrix over `P` presented
by the integer coefficient array `x`.  At `ιc = ιr` this is definitionally
`CoeffChecker.matOfCoeff` (see `matOfCoeff_eq_matOfCoeff₂`). -/
noncomputable def matOfCoeff₂ (bP : Basis (Fin k) R P) (x : ιr → ιc → Fin k → ℤ) :
    Matrix ιr ιc P :=
  Matrix.of fun r s => ∑ g, ((x r s g : ℤ) : R) • bP g

theorem matOfCoeff₂_apply (bP : Basis (Fin k) R P) (x : ιr → ιc → Fin k → ℤ)
    (r : ιr) (s : ιc) :
    matOfCoeff₂ bP x r s = ∑ g, ((x r s g : ℤ) : R) • bP g := rfl

/-- **The square device is a special case, definitionally.**  This is what
lets §R3 re-derive every square lemma of `CoeffChecker` from its rectangular
counterpart, so that the 512-triple rollout uses one device only. -/
theorem matOfCoeff_eq_matOfCoeff₂ (bP : Basis (Fin k) R P) (x : ιr → ιr → Fin k → ℤ) :
    matOfCoeff bP x = matOfCoeff₂ bP x := rfl

variable [Fintype ιm]

/-- **The rectangular convolution**: `(ιr × ιm) ⋆ (ιm × ιc) → (ιr × ιc)`.
`co i` is the inverse of `idx i`, as in `CoeffChecker.convCoeff`; at
`ιr = ιm = ιc` the two definitions are literally the same term. -/
def convCoeff₂ (sg : Fin k → Fin k → ℤ) (co : Fin k → Fin k → Fin k)
    (x : ιr → ιm → Fin k → ℤ) (y : ιm → ιc → Fin k → ℤ) : ιr → ιc → Fin k → ℤ :=
  fun r t h => ∑ s, ∑ i, sg i (co i h) * x r s i * y s t (co i h)

theorem convCoeff_eq_convCoeff₂ (sg : Fin k → Fin k → ℤ) (co : Fin k → Fin k → Fin k)
    (x y : ιm → ιm → Fin k → ℤ) : convCoeff sg co x y = convCoeff₂ sg co x y := rfl

/-- Reindexing a sum by the bijection `co i` (whose inverse is `idx i`). -/
private theorem reindex_sum₂ {M : Type*} [AddCommMonoid M]
    {idx co : Fin k → Fin k → Fin k}
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (i : Fin k) (F : Fin k → M) : ∑ j, F j = ∑ h, F (co i h) :=
  (Equiv.sum_comp (⟨co i, idx i, hco' i, hco i⟩ : Fin k ≃ Fin k) F).symm

/-- **T2, rectangular.**  Multiplication of matrices over `P` at independent
row/middle/column index types is convolution of coefficient arrays. -/
theorem matOfCoeff₂_mul {bP : Basis (Fin k) R P}
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (x : ιr → ιm → Fin k → ℤ) (y : ιm → ιc → Fin k → ℤ) :
    matOfCoeff₂ bP x * matOfCoeff₂ bP y = matOfCoeff₂ bP (convCoeff₂ sg co x y) := by
  classical
  ext r t
  rw [Matrix.mul_apply]
  have key : ∀ s : ιm, matOfCoeff₂ bP x r s * matOfCoeff₂ bP y s t
      = ∑ i : Fin k, ∑ h : Fin k,
          ((sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R) • bP h := by
    intro s
    rw [matOfCoeff₂_apply, matOfCoeff₂_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (reindex_sum₂ hco hco' i
      (fun j => (((x r s i : ℤ) : R) • bP i) * (((y s t j : ℤ) : R) • bP j))).trans ?_
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hmul, smul_smul, smul_smul, hco' i h]
    congr 1
    push_cast
    ring
  have hR : ∀ h : Fin k, ((convCoeff₂ sg co x y r t h : ℤ) : R) • bP h
      = ∑ s : ιm, ∑ i : Fin k,
          ((sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R) • bP h := by
    intro h
    show ((∑ s : ιm, ∑ i : Fin k, sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R)
      • bP h = _
    push_cast
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_smul
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (key s).trans Finset.sum_comm),
    matOfCoeff₂_apply, Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => hR h)]
  exact Finset.sum_comm

omit [Fintype ιm] in
theorem matOfCoeff₂_zsmul (bP : Basis (Fin k) R P) (c : ℤ) (x : ιr → ιc → Fin k → ℤ) :
    c • matOfCoeff₂ bP x = matOfCoeff₂ bP (fun r s g => c * x r s g) := by
  ext r s
  rw [Matrix.smul_apply, matOfCoeff₂_apply, matOfCoeff₂_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Int.cast_smul_eq_zsmul R c, smul_smul]
  congr 1
  push_cast
  ring

omit [Fintype ιm] in
/-- The coefficient array of a rectangular matrix over a based algebra is
unique.  Not needed for soundness; it is what turns a nonzero coefficient
into a nonzero connector (`gtOfTNative_ne_zero`'s hypothesis). -/
theorem matOfCoeff₂_injective [CharZero R] (bP : Basis (Fin k) R P) :
    Function.Injective (matOfCoeff₂ (ιr := ιr) (ιc := ιc) bP) := by
  intro x y hxy
  funext r s g
  have h1 : ∑ e, ((x r s e : ℤ) : R) • bP e = ∑ e, ((y r s e : ℤ) : R) • bP e :=
    congrFun (congrFun hxy r) s
  have h2 : ∑ e, (((x r s e : ℤ) : R) - ((y r s e : ℤ) : R)) • bP e = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
  have h3 := (Fintype.linearIndependent_iff.mp bP.linearIndependent) _ h2 g
  exact Int.cast_injective (sub_eq_zero.mp h3)

end CoeffRect

/-! ## R2. The rectangular certificate transport

The `List`-level checker of `CoeffChecker` (`coeffGet`, `coeffOf`, `convL`,
`checkAll`, `checkMatEq`) is **reused verbatim**: by `realGauge_gaugeSize_total_eq`
(§R5) the row total and the column total agree at every one of the 512
triples, so all three certificates `X`, `T`, `Y` are `σ × σ × k` integer
arrays for a single `σ`.  What has to change is only the *typed* conclusion,
and that is what the two equivalences do. -/

section CheckerRect

variable {R : Type*} [CommRing R] {P : Type*} [Ring P] [Algebra R P]

/-- **T3, rectangular, at the flat frame.**  Identical content to
`checkMatEq_sound`, restated for `matOfCoeff₂`; the proof is the square one
because `convCoeff₂` at `Fin σ` is `convCoeff`. -/
theorem checkMatEq_sound₂ {k σ : ℕ} (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff₂ (ιr := Fin σ) (ιc := Fin σ) bP (coeffOf σ k X)
        * matOfCoeff₂ bP (coeffOf σ k T)
      = c • (matOfCoeff₂ bP (coeffOf σ k T) * matOfCoeff₂ bP (coeffOf σ k Y)) := by
  rw [matOfCoeff₂_mul hmul hco hco', matOfCoeff₂_mul hmul hco hco', matOfCoeff₂_zsmul]
  refine congrArg (matOfCoeff₂ bP) ?_
  funext r t h
  have hb := checkAll_sound hchk r t h
  rw [beq_iff_eq, convL_eq, convL_eq] at hb
  exact hb

/-- **The two-equivalence transport — the deliverable.**

`X * T = c • (T * Y)` at the three *different* shapes the native device
produces:

* `X : Matrix ιR ιR P` (the right route at a slot generator),
* `T : Matrix ιR ιL P` (the connector),
* `Y : Matrix ιL ιL P` (the recast left route at the same generator),

from ONE checked `σ × σ × k` integer certificate.  `eR` and `eL` are the two
frame equivalences; they may be equivalences of genuinely different types
(`Fin 4 ⊕ Fin 0 ≃ Fin 4` and `Fin 2 ⊕ Fin 2 ≃ Fin 4` at the 12 exceptional
triples), which is exactly what `checkMatEq_sound_submatrix` cannot express. -/
theorem checkMatEq_sound_submatrix₂ {k σ : ℕ} {ιR ιL : Type*} [Fintype ιR] [Fintype ιL]
    (eR : ιR ≃ Fin σ) (eL : ιL ≃ Fin σ) (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff₂ (ιr := ιR) (ιc := ιR) bP (fun r s => coeffOf σ k X (eR r) (eR s))
        * matOfCoeff₂ (ιr := ιR) (ιc := ιL) bP (fun r s => coeffOf σ k T (eR r) (eL s))
      = c • (matOfCoeff₂ (ιr := ιR) (ιc := ιL) bP (fun r s => coeffOf σ k T (eR r) (eL s))
          * matOfCoeff₂ (ιr := ιL) (ιc := ιL) bP
              (fun r s => coeffOf σ k Y (eL r) (eL s))) := by
  have hX : matOfCoeff₂ (ιr := ιR) (ιc := ιR) bP (fun r s => coeffOf σ k X (eR r) (eR s))
      = (matOfCoeff₂ (ιr := Fin σ) (ιc := Fin σ) bP (coeffOf σ k X)).submatrix eR eR := rfl
  have hT : matOfCoeff₂ (ιr := ιR) (ιc := ιL) bP (fun r s => coeffOf σ k T (eR r) (eL s))
      = (matOfCoeff₂ (ιr := Fin σ) (ιc := Fin σ) bP (coeffOf σ k T)).submatrix eR eL := rfl
  have hY : matOfCoeff₂ (ιr := ιL) (ιc := ιL) bP (fun r s => coeffOf σ k Y (eL r) (eL s))
      = (matOfCoeff₂ (ιr := Fin σ) (ιc := Fin σ) bP (coeffOf σ k Y)).submatrix eL eL := rfl
  rw [hX, hT, hY, Matrix.submatrix_mul_equiv _ _ _ eR _,
    Matrix.submatrix_mul_equiv _ _ _ eL _,
    checkMatEq_sound₂ bP hmul hco hco' c X T Y hchk]
  rfl

end CheckerRect

/-! ## R3. The square layer, re-derived from the rectangular one

`matOfCoeff` is `matOfCoeff₂` at `ιc = ιr` and `convCoeff` is `convCoeff₂` at
`ιr = ιm = ιc`, both by `rfl`, so each square statement of `CoeffChecker` is
an instance of its rectangular counterpart.  The four theorems below restate
`matOfCoeff_mul`, `matOfCoeff_zsmul`, `checkMatEq_sound` and
`checkMatEq_sound_submatrix` *verbatim* and prove them from §R1–§R2 alone.
Consequence: the rollout may standardize on the rectangular device, and the
square one is retained only for the triples where it is more convenient. -/

section SquareFromRect

variable {R : Type*} [CommRing R] {P : Type*} [Ring P] [Algebra R P]
variable {ι : Type*} {k : ℕ}

theorem matOfCoeff_mul_of_rect [Fintype ι] {bP : Basis (Fin k) R P}
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (x y : ι → ι → Fin k → ℤ) :
    matOfCoeff bP x * matOfCoeff bP y = matOfCoeff bP (convCoeff sg co x y) :=
  matOfCoeff₂_mul hmul hco hco' x y

theorem matOfCoeff_zsmul_of_rect (bP : Basis (Fin k) R P) (c : ℤ)
    (x : ι → ι → Fin k → ℤ) :
    c • matOfCoeff bP x = matOfCoeff bP (fun r s g => c * x r s g) :=
  matOfCoeff₂_zsmul bP c x

theorem checkMatEq_sound_of_rect {σ : ℕ} (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff bP (coeffOf σ k X) * matOfCoeff bP (coeffOf σ k T)
      = c • (matOfCoeff bP (coeffOf σ k T) * matOfCoeff bP (coeffOf σ k Y)) :=
  checkMatEq_sound₂ bP hmul hco hco' c X T Y hchk

theorem checkMatEq_sound_submatrix_of_rect {σ : ℕ} [Fintype ι] (e : ι ≃ Fin σ)
    (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff (ι := ι) bP (fun r s => coeffOf σ k X (e r) (e s))
        * matOfCoeff bP (fun r s => coeffOf σ k T (e r) (e s))
      = c • (matOfCoeff bP (fun r s => coeffOf σ k T (e r) (e s))
          * matOfCoeff bP (fun r s => coeffOf σ k Y (e r) (e s))) :=
  checkMatEq_sound_submatrix₂ e e bP hmul hco hco' c X T Y hchk

end SquareFromRect

/-! ## R4. The `realGauge` consumers

`co = idx` for every `realRep a` (`realRepMulIdx_eq_xor`), so a single
involution lemma discharges both inverse hypotheses, exactly as in
`CoeffChecker`'s `realCheckMatEq_sound`. -/

section RealInstanceRect

/-- **The rectangular consumer at `realRepBasis`**, at an arbitrary pair of
frame equivalences. -/
theorem realCheckMatEq₂_sound' (a : ZMod 8) {σ : ℕ} {ιR ιL : Type*}
    [Fintype ιR] [Fintype ιL] (eR : ιR ≃ Fin σ) (eL : ιL ≃ Fin σ)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ (realRepDim a.val) (realCoN a.val) (realSignN a.val) c X T Y
      = true) :
    matOfCoeff₂ (ιr := ιR) (ιc := ιR) (realRepBasis a)
          (fun r s => coeffOf σ (realRepDim a.val) X (eR r) (eR s))
        * matOfCoeff₂ (ιr := ιR) (ιc := ιL) (realRepBasis a)
          (fun r s => coeffOf σ (realRepDim a.val) T (eR r) (eL s))
      = c • (matOfCoeff₂ (ιr := ιR) (ιc := ιL) (realRepBasis a)
            (fun r s => coeffOf σ (realRepDim a.val) T (eR r) (eL s))
          * matOfCoeff₂ (ιr := ιL) (ιc := ιL) (realRepBasis a)
            (fun r s => coeffOf σ (realRepDim a.val) Y (eL r) (eL s))) :=
  checkMatEq_sound_submatrix₂ eR eL (realRepBasis a) (realRepBasisAux_mul a.val)
    (realRepMulIdxAux_involutive a.val) (realRepMulIdxAux_involutive a.val) c X T Y hchk

/-- **The frame equivalence the native device uses**: `matrixSuper`'s index
type `Fin p ⊕ Fin q` flattened to `Fin σ`, given `p + q = σ`. -/
def frameEquiv {p q σ : ℕ} (h : p + q = σ) : Fin p ⊕ Fin q ≃ Fin σ :=
  finSumFinEquiv.trans (finCongr h)

@[simp] theorem frameEquiv_inl {p q σ : ℕ} (h : p + q = σ) (i : Fin p) :
    frameEquiv h (Sum.inl i) = ⟨i.val, h ▸ Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right p q)⟩ :=
  rfl

@[simp] theorem frameEquiv_inr {p q σ : ℕ} (h : p + q = σ) (j : Fin q) :
    frameEquiv h (Sum.inr j) = ⟨p + j.val, h ▸ Nat.add_lt_add_left j.isLt p⟩ :=
  rfl

theorem frameEquiv_val_inl {p q σ : ℕ} (h : p + q = σ) (i : Fin p) :
    (frameEquiv h (Sum.inl i)).val = i.val := rfl

theorem frameEquiv_val_inr {p q σ : ℕ} (h : p + q = σ) (j : Fin q) :
    (frameEquiv h (Sum.inr j)).val = p + j.val := rfl

/-- **The consumer the 512-triple rollout calls.**  Stated directly at the
`Fin pR ⊕ Fin qR` / `Fin pL ⊕ Fin qL` frames of
`TDictGaugeNative.NativeT`, with the two size totals supplied as numeral
equalities (`rfl` at a concrete triple; always satisfiable by
`realGauge_gaugeSize_total_eq`). -/
theorem realCheckMatEqFrame_sound (a : ZMod 8) {pR qR pL qL σ : ℕ}
    (hR : pR + qR = σ) (hL : pL + qL = σ) (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ (realRepDim a.val) (realCoN a.val) (realSignN a.val) c X T Y
      = true) :
    matOfCoeff₂ (ιr := Fin pR ⊕ Fin qR) (ιc := Fin pR ⊕ Fin qR) (realRepBasis a)
          (fun r s => coeffOf σ (realRepDim a.val) X (frameEquiv hR r) (frameEquiv hR s))
        * matOfCoeff₂ (ιr := Fin pR ⊕ Fin qR) (ιc := Fin pL ⊕ Fin qL) (realRepBasis a)
          (fun r s => coeffOf σ (realRepDim a.val) T (frameEquiv hR r) (frameEquiv hL s))
      = c • (matOfCoeff₂ (ιr := Fin pR ⊕ Fin qR) (ιc := Fin pL ⊕ Fin qL) (realRepBasis a)
            (fun r s => coeffOf σ (realRepDim a.val) T (frameEquiv hR r) (frameEquiv hL s))
          * matOfCoeff₂ (ιr := Fin pL ⊕ Fin qL) (ιc := Fin pL ⊕ Fin qL) (realRepBasis a)
            (fun r s => coeffOf σ (realRepDim a.val) Y (frameEquiv hL r) (frameEquiv hL s))) :=
  realCheckMatEq₂_sound' a (frameEquiv hR) (frameEquiv hL) c X T Y hchk

end RealInstanceRect

/-! ## R5. Why ONE `σ` suffices — checked at all 512 triples

`checkMatEq_sound_submatrix₂` takes two equivalences into the *same* `Fin σ`.
That is legitimate exactly because the row total of the right frame and the
column total of the left frame agree at every triple, which is a closed
`decide` over `(ZMod 8)³`.  The second theorem records that this is a strictly
weaker statement than `hsz`: the sizes themselves differ at 12 triples
(`docs/route-layer-design.md` §1.5), which is why the square device is not
enough. -/

section SizeTotals

/-- **The single-`σ` justification.**  At all 512 triples the right frame's
row total equals the left frame's column total, so one flat certificate
dimension `σ` serves both index types.  (Structurally:
`|σL| = |Γ.size a b| · |Γ.size (a+b) c|` and
`|σR| = |Γ.size b c| · |Γ.size a (b+c)|`, and the two products agree because
`realSize` is multiplicative on totals.) -/
theorem realGauge_gaugeSize_total_eq :
    ∀ a b c : ZMod 8,
      (realGauge.gaugeSizeR a b c).1 + (realGauge.gaugeSizeR a b c).2
        = (realGauge.gaugeSizeL a b c).1 + (realGauge.gaugeSizeL a b c).2 := by
  decide +kernel

/-- …but the sizes themselves do NOT agree everywhere, which is why the
square, one-equivalence transport cannot cover the rollout. -/
theorem realGauge_gaugeSize_ne :
    ¬ (∀ a b c : ZMod 8, realGauge.gaugeSizeR a b c = realGauge.gaugeSizeL a b c) := by
  decide +kernel

/-- The exceptional shape, spelled out: at `(1,4,4)` the right frame is `4|0`
and the left frame is `2|2` — different index types, equal totals. -/
theorem realGauge_gaugeSize_144 :
    realGauge.gaugeSizeR 1 4 4 = (4, 0) ∧ realGauge.gaugeSizeL 1 4 4 = (2, 2) := by
  decide +kernel

end SizeTotals

/-! ## R6. Self-test: a genuinely rectangular instance

The shape is the exceptional one — rows `Fin 4 ⊕ Fin 0`, columns
`Fin 2 ⊕ Fin 2`, `σ = 4` — over `D₃` (`k = 8`), which is where the sign table
does real work.  `X = e₁ · I₄`, `Y = e₁ · I₄`, and `T` is the band matrix with
`e₂` on the diagonal and on the superdiagonal; the identity checked is
`X · T = (−1) • (T · Y)`, i.e. the anticommutation `e₁e₂ = −e₂e₁` propagated
through a `4 × 4` frame.  Negative control: the same data with `c = 1` is
rejected. -/

section SelfTestRect

/-- `g₀ · I_σ` as a coefficient array. -/
def diagCoeff (σ k g₀ : ℕ) : List (List (List ℤ)) :=
  (List.range σ).map fun r => (List.range σ).map fun s =>
    (List.range k).map fun g => if r = s ∧ g = g₀ then 1 else 0

/-- `g₀` on the diagonal and the superdiagonal. -/
def bandCoeff (σ k g₀ : ℕ) : List (List (List ℤ)) :=
  (List.range σ).map fun r => (List.range σ).map fun s =>
    (List.range k).map fun g => if (r = s ∨ s = r + 1) ∧ g = g₀ then 1 else 0

/-- **The integer certificate** — `4² · 8 = 128` entry tests, `4 · 8 = 32`
multiply-adds each. -/
theorem rectCert :
    checkMatEq 4 8 (realCoN 3) (realSignN 3) (-1)
      (diagCoeff 4 8 1) (bandCoeff 4 8 2) (diagCoeff 4 8 1) = true := by
  decide +kernel

/-- **Negative control** — the same three matrices with `c = 1` are rejected,
so the sign table is genuinely doing the work. -/
theorem rectCert_reject :
    checkMatEq 4 8 (realCoN 3) (realSignN 3) 1
      (diagCoeff 4 8 1) (bandCoeff 4 8 2) (diagCoeff 4 8 1) = false := by
  decide +kernel

/-- **The rectangular self-test.**  `X * T = (−1) • (T * Y)` with
`X : Matrix (Fin 4 ⊕ Fin 0) (Fin 4 ⊕ Fin 0) (realRep 3)`,
`T : Matrix (Fin 4 ⊕ Fin 0) (Fin 2 ⊕ Fin 2) (realRep 3)` and
`Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (realRep 3)`: three genuinely
different shapes, one integer certificate, no `native_decide`. -/
theorem rectSelfTest :
    matOfCoeff₂ (ιr := Fin 4 ⊕ Fin 0) (ιc := Fin 4 ⊕ Fin 0) (realRepBasis 3)
          (fun r s => coeffOf 4 (realRepDim (3 : ZMod 8).val) (diagCoeff 4 8 1)
            (frameEquiv (by norm_num) r) (frameEquiv (by norm_num) s))
        * matOfCoeff₂ (ιr := Fin 4 ⊕ Fin 0) (ιc := Fin 2 ⊕ Fin 2) (realRepBasis 3)
          (fun r s => coeffOf 4 (realRepDim (3 : ZMod 8).val) (bandCoeff 4 8 2)
            (frameEquiv (by norm_num) r) (frameEquiv (by norm_num) s))
      = (-1 : ℤ) •
        (matOfCoeff₂ (ιr := Fin 4 ⊕ Fin 0) (ιc := Fin 2 ⊕ Fin 2) (realRepBasis 3)
            (fun r s => coeffOf 4 (realRepDim (3 : ZMod 8).val) (bandCoeff 4 8 2)
              (frameEquiv (by norm_num) r) (frameEquiv (by norm_num) s))
          * matOfCoeff₂ (ιr := Fin 2 ⊕ Fin 2) (ιc := Fin 2 ⊕ Fin 2) (realRepBasis 3)
            (fun r s => coeffOf 4 (realRepDim (3 : ZMod 8).val) (diagCoeff 4 8 1)
              (frameEquiv (by norm_num) r) (frameEquiv (by norm_num) s))) :=
  realCheckMatEqFrame_sound 3 (by norm_num) (by norm_num) (-1) _ _ _ rectCert

end SelfTestRect

/-! ## R7. The interface check against `TDictGaugeNative`

The point of the rectangular device is to feed `hAint`/`hBint`/`hCint` of
`GaugeChi.gtOfTNative_mem_interSpace_of_slot_generators`, whose shape is

  `routeRMat y * T = c • (T * routeLNativeMat y)`,   `T : NativeT ℝ realGauge a b c`.

`nativeIntertwine_of_cert` produces exactly that identity, at `NativeT`'s own
index and coefficient types, from one checked integer certificate — with the
**semantic bridge isolated as its three explicit hypotheses** `hX`, `hT`,
`hY` ("this route matrix / this connector is `matOfCoeff₂` of that frozen
integer literal").  Those three are T4 of `docs/route-layer-design.md` §5 and
are the only thing still missing between here and a per-triple certificate;
everything else on the path is now closed. -/

section NativeInterface

open GaugeChi

/-- **The rectangular certificate, delivered at `NativeT`'s own types.**
`X` is the right route at a slot generator, `Y` the recast left route at the
same generator, `T` the native connector; the three shapes are
`R × R`, `L × L` and `R × L` and are genuinely different types at the 12
exceptional triples.  Hypotheses `hX`/`hT`/`hY` are the semantic bridge (T4);
`hchk` is the kernel-checked integer certificate; `hR`/`hL` are the two frame
totals, equal by `realGauge_gaugeSize_total_eq` and `rfl` at a concrete
triple. -/
theorem nativeIntertwine_of_cert (a b c : ZMod 8) {σ : ℕ}
    (hR : (realGauge.gaugeSizeR a b c).1 + (realGauge.gaugeSizeR a b c).2 = σ)
    (hL : (realGauge.gaugeSizeL a b c).1 + (realGauge.gaugeSizeL a b c).2 = σ)
    (T : NativeT ℝ realGauge a b c)
    (X : Matrix (Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2)
          (Fin (realGauge.gaugeSizeR a b c).1 ⊕ Fin (realGauge.gaugeSizeR a b c).2)
          (realGauge.D (a + (b + c))).carrier)
    (Y : Matrix (Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2)
          (Fin (realGauge.gaugeSizeL a b c).1 ⊕ Fin (realGauge.gaugeSizeL a b c).2)
          (realGauge.D (a + (b + c))).carrier)
    (c₀ : ℤ) (XL TL YL : List (List (List ℤ)))
    (hX : X = matOfCoeff₂ (realRepBasis (a + (b + c)))
            (fun r s => coeffOf σ (realRepDim (a + (b + c)).val) XL
              (frameEquiv hR r) (frameEquiv hR s)))
    (hT : T = matOfCoeff₂ (realRepBasis (a + (b + c)))
            (fun r s => coeffOf σ (realRepDim (a + (b + c)).val) TL
              (frameEquiv hR r) (frameEquiv hL s)))
    (hY : Y = matOfCoeff₂ (realRepBasis (a + (b + c)))
            (fun r s => coeffOf σ (realRepDim (a + (b + c)).val) YL
              (frameEquiv hL r) (frameEquiv hL s)))
    (hchk : checkMatEq σ (realRepDim (a + (b + c)).val) (realCoN (a + (b + c)).val)
      (realSignN (a + (b + c)).val) c₀ XL TL YL = true) :
    X * T = c₀ • (T * Y) := by
  subst hX
  subst hT
  subst hY
  exact realCheckMatEqFrame_sound (a + (b + c)) hR hL c₀ XL TL YL hchk

end NativeInterface

#print axioms checkMatEq_sound_submatrix₂
#print axioms realCheckMatEqFrame_sound
#print axioms realGauge_gaugeSize_total_eq
#print axioms rectSelfTest
#print axioms nativeIntertwine_of_cert

end Superfusion
