/-
Superfusion / GaugeChi / CoeffChecker

**The scalable, kernel-decidable arithmetic layer** of the route plan
(`docs/route-layer-design.md` §5, items T1–T3).  Nothing in this file
mentions `gInterSpace`, routes or gauges: it is pure finite algebra, and it
is what turns each of the per-triple matrix identities

    X · T = ±(T · Y)      (matrices over `D_{a+b+c}`)

of the 512-point rollout into a **closed integer computation** that the
kernel can check with `decide +kernel`.

Three layers.

* **T1 — `realRepBasis_mul`.**  Each of the eight coordinate algebras
  `realRep a` has a *signed monomial* basis: in `Gauge/RealRepsBasis.lean`'s
  explicit basis,

      realRepBasis a i * realRepBasis a j
        = (realRepMulSign a i j : ℝ) • realRepBasis a (realRepMulIdx a i j).

  For the six tower labels this is an `OddDouble` induction against the
  explicit product `(a,b)(c,d) = (ac + ε·b·Jd, ad + b·Jc)`; the index
  recursion is `xor` on the block bits (`towerIdx`, and
  `realRepMulIdx_eq_xor`) and the sign carries the two Koszul factors
  `(−1)^{|j'|}` (from `J`) and `ε` (from `g² = ε`).  For `a = 4` it is the
  quaternion table on `1, i, j, k`; for `a = 0` it is trivial.
  `realRepBasis_zero` (`GaugeChi/RouteMatrixProto.lean`) is the companion
  already in place.

* **T2 — `matOfCoeff`.**  A matrix over a based algebra `P` is presented by
  its integer coefficient array `x : ι → ι → Fin k → ℤ`, and matrix
  multiplication becomes the *convolution* `convCoeff` of coefficient arrays
  against the monomial table (`matOfCoeff_mul`).  Because the table is
  monomial, one product of two `D`-elements costs `k²`, not `k³`: the
  `j`-summation is reindexed by the bijection `j ↦ idx i j`, whose inverse
  `co` is part of the table data.  `matOfCoeff_injective` is the converse
  direction (only needed for debugging and for nonvanishing arguments).

* **T3 — `checkAll` / `checkMatEq`.**  The integer identity is then a closed
  `Bool`, computed by a `List`-based program (`convL`) — measured in
  `docs/route-layer-design.md` §4.2 to be ≈ 50× faster under the kernel than
  a `Matrix.mulᵣ`-based `decide`.  `checkMatEq_sound` is the only bridge that
  touches `ℝ`; nothing is ever `decide`d over `ℝ`.

The self-tests at the end exercise the whole stack: an `8 × 8` identity over
`D₁` by `decide +kernel`, a genuine convolution over `D₁`, the Clifford
anticommutation `e₁e₂ = −e₂e₁` in `D₃`, and one end-to-end transport of a
checked integer certificate to a matrix identity over `ℝ`.

### Corrections to `docs/route-layer-design.md` §5

1. **The doc's `convCoeff` is a factor `k` too slow.**  As written there,
   `convCoeff … r t h = ∑ s ∑ i ∑ j, if idx i j = h then sg i j * x r s i *
   y s t j else 0`, so producing all `σ²·k` output entries costs `σ³k³` —
   exactly the "flattened real `M × M`, dense" row of §4.3, i.e. the monomial
   table buys *nothing*.  The saving only materialises if the `j`-loop is
   removed, which needs the *inverse* table `co` (`co i` inverse to `idx i`)
   and the sum `∑ s ∑ i, sg i (co i h) * x r s i * y s t (co i h)`: `σ³k²`.
   For the eight coordinate algebras this costs nothing extra, because
   `idx = co = xor` (`realRepMulIdx_eq_xor`, `realRepMulIdx_involutive`), so
   `checkMatEq_sound` is instantiated with the *same* function twice.

2. **The tower case of T1 cannot fix `ε` to a numeral.**  `divisionTower ε n`
   is a type family in `ε`, and `((-1 : ℤ) : ℝ)` is not syntactically
   `(-1 : ℝ)`, so `towerBasis_mul` keeps `ε : ℝ` a variable and takes the
   integer parameter `e` with `hε : ε = (e : ℝ)`; only the *sign*, an
   `ℤ`-valued function, is specialised.

3. **New elaboration trap** (add to §2.6/§10.3): `(divisionTower ε (n+1)).carrier`
   and `OddDouble (divisionTower ε n).grading ε` are defeq but carry
   *different* `Mul`/`Module` instance terms, and **a type ascription does not
   switch the instance** — `(x : (divisionTower ε (n+1)).carrier) * y` still
   elaborates at `OddDouble`'s `Mul` when `x` is an `OddDouble.mk`.  The
   instance has to be named: `tower_mul_eq` / `tower_smul_eq` are `rfl`
   lemmas stated with `@HMul.hMul (OddDouble …) … instHMul`, and every case of
   the induction opens by rewriting with them.  Same for `quatEvenSuper.carrier`
   versus `ℍ[ℝ]` (`quat_mul_eq` / `quat_smul_eq`).

4. **`decide` refuses a goal with free variables.**  The `| _ + 7` branch of
   any `realRepDim`-indexed bundle therefore cannot be `decide`d in place even
   though `realRepDim (m + 7)` reduces to `2`; the closed statement is
   `decide`d at the concrete floor (`invol1`, `xor3`, …) and transported by
   `exact`.

Design record: `docs/route-layer-design.md` (§5 T1–T3, §4 for the measured
kernel costs).
-/
import Superfusion.Gauge.RealRepsBasis

namespace Superfusion

open Module

/-! ## T1. The signed monomial multiplication tables

### 1.1 The tower tables -/

/-- `(−1)^{popcount}` of the low `n` bits of `j`, as an integer: the sign by
which the parity involution `J` acts on the `j`-th basis vector of floor
`n`. -/
def natPar : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n + 1, j => if 2 ^ n ≤ j then -natPar n (j % 2 ^ n) else natPar n (j % 2 ^ n)

/-- The product index of two tower basis indices, by the block recursion:
the top bits add mod `2` and the sub-indices multiply.  (This is `xor`; see
`realRepMulIdxAux_eq_xor`, checked at the floors `n ≤ 3` this project uses.) -/
def towerIdx : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, i, j =>
      (if 2 ^ n ≤ i then (if 2 ^ n ≤ j then 0 else 2 ^ n)
        else (if 2 ^ n ≤ j then 2 ^ n else 0)) + towerIdx n (i % 2 ^ n) (j % 2 ^ n)

/-- The product sign of two tower basis indices at parameter `ε = e`.  The
factor `natPar n j'` comes from `J` (present exactly when `i` is in the high
block, i.e. carries a `g`), the factor `e` from `g² = ε` (present exactly
when both indices are high). -/
def towerSign (e : ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | n + 1, i, j =>
      (if 2 ^ n ≤ i then natPar n (j % 2 ^ n) else 1)
        * (if 2 ^ n ≤ i then (if 2 ^ n ≤ j then e else 1) else 1)
        * towerSign e n (i % 2 ^ n) (j % 2 ^ n)

theorem towerIdx_lt : ∀ (n i j : ℕ), towerIdx n i j < 2 ^ n
  | 0, _, _ => by simp [towerIdx]
  | n + 1, i, j => by
      have h := towerIdx_lt n (i % 2 ^ n) (j % 2 ^ n)
      have h2 := two_pow_add_self n
      rw [towerIdx]
      split <;> split <;> omega

/-- The tower product index, as a `Fin`. -/
def towerIdxFin (n : ℕ) (i j : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨towerIdx n i.val j.val, towerIdx_lt n i.val j.val⟩

/-! ### 1.2 Block bookkeeping

The four helpers `tb_low`/`tb_high`/`tp_low`/`tp_high` restate
`RealRepsBasis`'s anchors in the form the induction needs: the floor-`n+1`
index is given by its *value*, so that `omega` can discharge the block
arithmetic. -/

private theorem mod_low {n j : ℕ} (h : j < 2 ^ n) : j % 2 ^ n = j :=
  Nat.mod_eq_of_lt h

private theorem mod_high {n : ℕ} {j : ℕ} (hlt : j < 2 ^ (n + 1)) (h : 2 ^ n ≤ j) :
    j % 2 ^ n = j - 2 ^ n := by
  have h2 := two_pow_add_self n
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

private theorem tb_low (ε : ℝ) (n : ℕ) (i : Fin (2 ^ n)) (i2 : Fin (2 ^ (n + 1)))
    (hi2 : i2.val = i.val) :
    towerBasis ε (n + 1) i2
      = OddDouble.mk (divisionTower ε n).grading ε (towerBasis ε n i) 0 := by
  rw [show i2 = ⟨(i : ℕ), towerIndexLow_lt n i⟩ from Fin.ext hi2]
  exact towerBasis_low ε n i

private theorem tb_high (ε : ℝ) (n : ℕ) (i : Fin (2 ^ n)) (i2 : Fin (2 ^ (n + 1)))
    (hi2 : i2.val = 2 ^ n + i.val) :
    towerBasis ε (n + 1) i2
      = OddDouble.mk (divisionTower ε n).grading ε 0 (towerBasis ε n i) := by
  rw [show i2 = ⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ from Fin.ext hi2]
  exact towerBasis_high ε n i

private theorem tp_low (n : ℕ) (i : Fin (2 ^ n)) (i2 : Fin (2 ^ (n + 1)))
    (hi2 : i2.val = i.val) : towerIndexParity (n + 1) i2 = towerIndexParity n i := by
  rw [show i2 = ⟨(i : ℕ), towerIndexLow_lt n i⟩ from Fin.ext hi2]
  exact towerIndexParity_low n i

private theorem tp_high (n : ℕ) (i : Fin (2 ^ n)) (i2 : Fin (2 ^ (n + 1)))
    (hi2 : i2.val = 2 ^ n + i.val) :
    towerIndexParity (n + 1) i2 = towerIndexParity n i + 1 := by
  rw [show i2 = ⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ from Fin.ext hi2]
  exact towerIndexParity_high n i

/-- `natPar` is the sign attached to `towerIndexParity`. -/
theorem natPar_spec : ∀ (n : ℕ) (j : Fin (2 ^ n)),
    (towerIndexParity n j = 0 ∧ natPar n j.val = 1) ∨
      (towerIndexParity n j = 1 ∧ natPar n j.val = -1)
  | 0, _ => Or.inl ⟨rfl, rfl⟩
  | n + 1, j => by
      rcases Nat.lt_or_ge j.val (2 ^ n) with h | h
      · have hp := tp_low n ⟨j.val, h⟩ j rfl
        have hn : natPar (n + 1) j.val = natPar n j.val := by
          rw [natPar, if_neg (by omega), mod_low h]
        rcases natPar_spec n ⟨j.val, h⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hp.trans h1, hn.trans h2⟩
        · exact Or.inr ⟨hp.trans h1, hn.trans h2⟩
      · have hjm : j.val % 2 ^ n = j.val - 2 ^ n := mod_high j.isLt h
        have hlt : j.val - 2 ^ n < 2 ^ n := by
          have := j.isLt; have := two_pow_add_self n; omega
        have hp := tp_high n ⟨j.val - 2 ^ n, hlt⟩ j
          (by show j.val = 2 ^ n + (j.val - 2 ^ n); omega)
        have hn : natPar (n + 1) j.val = -natPar n (j.val - 2 ^ n) := by
          rw [natPar, if_pos h, hjm]
        rcases natPar_spec n ⟨j.val - 2 ^ n, hlt⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨by rw [hp, h1]; decide, by rw [hn, h2]⟩
        · exact Or.inl ⟨by rw [hp, h1]; decide, by rw [hn, h2]; norm_num⟩

/-- The parity involution acts on a tower basis vector by the sign
`natPar`. -/
theorem parityMap_towerBasis (ε : ℝ) (n : ℕ) (j : Fin (2 ^ n)) :
    parityMap (divisionTower ε n).grading (towerBasis ε n j)
      = ((natPar n j.val : ℤ) : ℝ) • towerBasis ε n j := by
  rcases natPar_spec n j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hm : towerBasis ε n j ∈ (divisionTower ε n).grading 0 := h1 ▸ towerBasis_mem ε n j
    rw [parityMap_of_mem_zero _ hm, h2]
    norm_num
  · have hm : towerBasis ε n j ∈ (divisionTower ε n).grading 1 := h1 ▸ towerBasis_mem ε n j
    rw [parityMap_of_mem_one _ hm, h2]
    norm_num

/-! ### 1.3 The four `OddDouble` products

**Elaboration trap (new; cf. `docs/route-layer-design.md` §2.6/§10.3).**
`(divisionTower ε (n+1)).carrier` and `OddDouble (divisionTower ε n).grading ε`
are defeq, but their `Mul`/`Module` instances are *different terms*
(`SuperAlgebra.ring` of the bundled odd double, versus `OddDouble.instRing`),
so `rw` cannot cross between them — and a type ascription does **not** force
the instance: `(x : (divisionTower ε (n+1)).carrier) * y` still elaborates
with `OddDouble`'s `Mul` whenever `x` was written as an `OddDouble.mk`.
The two `rfl` lemmas `tower_mul_eq` / `tower_smul_eq` convert a goal from the
`divisionTower` instances (which is what a statement about `towerBasis ε (n+1)`
produces) to the `OddDouble` instances (which is what a statement about
`OddDouble.mk` produces); every case of the induction opens with them. -/

section TowerProducts

variable (ε : ℝ) (n : ℕ)

/-- Instance transfer for `*` (see the section note).  A type *ascription*
does not switch the instance — the instance has to be named. -/
theorem tower_mul_eq (x y : (divisionTower ε (n + 1)).carrier) :
    x * y = @HMul.hMul (OddDouble (divisionTower ε n).grading ε)
      (OddDouble (divisionTower ε n).grading ε) (OddDouble (divisionTower ε n).grading ε)
      instHMul x y := rfl

/-- Instance transfer for `•` (see the section note). -/
theorem tower_smul_eq (σ : ℝ) (x : (divisionTower ε (n + 1)).carrier) :
    σ • x = @HSMul.hSMul ℝ (OddDouble (divisionTower ε n).grading ε)
      (OddDouble (divisionTower ε n).grading ε) instHSMul σ x := rfl

private theorem tw_ll (a c : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε a 0 : (divisionTower ε (n + 1)).carrier)
        * (OddDouble.mk (divisionTower ε n).grading ε c 0 : (divisionTower ε (n + 1)).carrier)
      = (OddDouble.mk (divisionTower ε n).grading ε (a * c) 0 :
          (divisionTower ε (n + 1)).carrier) := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem tw_lh (a d : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε a 0 : (divisionTower ε (n + 1)).carrier)
        * (OddDouble.mk (divisionTower ε n).grading ε 0 d : (divisionTower ε (n + 1)).carrier)
      = (OddDouble.mk (divisionTower ε n).grading ε 0 (a * d) :
          (divisionTower ε (n + 1)).carrier) := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem tw_hl (b c : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε 0 b : (divisionTower ε (n + 1)).carrier)
        * (OddDouble.mk (divisionTower ε n).grading ε c 0 : (divisionTower ε (n + 1)).carrier)
      = (OddDouble.mk (divisionTower ε n).grading ε 0
            (b * parityMap (divisionTower ε n).grading c) :
          (divisionTower ε (n + 1)).carrier) := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem tw_hh (b d : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε 0 b : (divisionTower ε (n + 1)).carrier)
        * (OddDouble.mk (divisionTower ε n).grading ε 0 d : (divisionTower ε (n + 1)).carrier)
      = (OddDouble.mk (divisionTower ε n).grading ε
            (ε • (b * parityMap (divisionTower ε n).grading d)) 0 :
          (divisionTower ε (n + 1)).carrier) := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem tw_smul_left (σ : ℝ) (a : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε (σ • a) 0 :
        (divisionTower ε (n + 1)).carrier)
      = σ • (OddDouble.mk (divisionTower ε n).grading ε a 0 :
          (divisionTower ε (n + 1)).carrier) := by
  refine (OddDouble.ext (divisionTower ε n).grading ε ?_ ?_).symm <;> simp

private theorem tw_smul_right (σ : ℝ) (a : (divisionTower ε n).carrier) :
    (OddDouble.mk (divisionTower ε n).grading ε 0 (σ • a) :
        (divisionTower ε (n + 1)).carrier)
      = σ • (OddDouble.mk (divisionTower ε n).grading ε 0 a :
          (divisionTower ε (n + 1)).carrier) := by
  refine (OddDouble.ext (divisionTower ε n).grading ε ?_ ?_).symm <;> simp

end TowerProducts

/-- **T1, the tower case.**  The canonical basis of `divisionTower ε n` is a
signed monomial basis, with index `towerIdx` and sign `towerSign`. -/
theorem towerBasis_mul (ε : ℝ) (e : ℤ) (hε : ε = (e : ℝ)) :
    ∀ (n : ℕ) (i j : Fin (2 ^ n)),
      towerBasis ε n i * towerBasis ε n j
        = ((towerSign e n i.val j.val : ℤ) : ℝ) • towerBasis ε n (towerIdxFin n i j)
  | 0, i, j => by
      simp only [towerBasis_zero_apply, towerSign, Int.cast_one, one_smul]
      exact one_mul 1
  | n + 1, i, j => by
      rw [tower_mul_eq ε n, tower_smul_eq ε n]
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have hsucc := two_pow_add_self n
      obtain ⟨I, hI⟩ : ∃ I : Fin (2 ^ n), I.val = i.val % 2 ^ n :=
        ⟨⟨i.val % 2 ^ n, Nat.mod_lt _ hpos⟩, rfl⟩
      obtain ⟨J, hJ⟩ : ∃ J : Fin (2 ^ n), J.val = j.val % 2 ^ n :=
        ⟨⟨j.val % 2 ^ n, Nat.mod_lt _ hpos⟩, rfl⟩
      have IH := towerBasis_mul ε e hε n I J
      have hpar := parityMap_towerBasis ε n J
      rcases Nat.lt_or_ge i.val (2 ^ n) with hi | hi <;>
        rcases Nat.lt_or_ge j.val (2 ^ n) with hj | hj
      · -- low · low : `(A,0)(C,0) = (AC, 0)`
        have h1 : ¬ (2 ^ n ≤ i.val) := by omega
        have h2 : ¬ (2 ^ n ≤ j.val) := by omega
        have hIv : I.val = i.val := by rw [hI, mod_low hi]
        have hJv : J.val = j.val := by rw [hJ, mod_low hj]
        have hidx : (towerIdxFin (n + 1) i j).val = (towerIdxFin n I J).val := by
          show towerIdx (n + 1) i.val j.val = towerIdx n I.val J.val
          rw [towerIdx]; simp only [if_neg h1, if_neg h2, zero_add, hI, hJ]
        have hsg : towerSign e (n + 1) i.val j.val = towerSign e n I.val J.val := by
          rw [towerSign]; simp only [if_neg h1, one_mul, hI, hJ]
        rw [tb_low ε n I i hIv.symm, tb_low ε n J j hJv.symm,
          tb_low ε n (towerIdxFin n I J) (towerIdxFin (n + 1) i j) hidx,
          tw_ll, IH, hsg, tw_smul_left]
      · -- low · high : `(A,0)(0,D) = (0, AD)`
        have h1 : ¬ (2 ^ n ≤ i.val) := by omega
        have hIv : I.val = i.val := by rw [hI, mod_low hi]
        have hJv : J.val = j.val - 2 ^ n := by rw [hJ, mod_high j.isLt hj]
        have hidx : (towerIdxFin (n + 1) i j).val = 2 ^ n + (towerIdxFin n I J).val := by
          show towerIdx (n + 1) i.val j.val = 2 ^ n + towerIdx n I.val J.val
          rw [towerIdx]; simp only [if_neg h1, if_pos hj, hI, hJ]
        have hsg : towerSign e (n + 1) i.val j.val = towerSign e n I.val J.val := by
          rw [towerSign]; simp only [if_neg h1, one_mul, hI, hJ]
        rw [tb_low ε n I i hIv.symm, tb_high ε n J j (by omega),
          tb_high ε n (towerIdxFin n I J) (towerIdxFin (n + 1) i j) hidx,
          tw_lh, IH, hsg, tw_smul_right]
      · -- high · low : `(0,B)(C,0) = (0, B·JC)`
        have h2 : ¬ (2 ^ n ≤ j.val) := by omega
        have hIv : I.val = i.val - 2 ^ n := by rw [hI, mod_high i.isLt hi]
        have hJv : J.val = j.val := by rw [hJ, mod_low hj]
        have hidx : (towerIdxFin (n + 1) i j).val = 2 ^ n + (towerIdxFin n I J).val := by
          show towerIdx (n + 1) i.val j.val = 2 ^ n + towerIdx n I.val J.val
          rw [towerIdx]; simp only [if_pos hi, if_neg h2, hI, hJ]
        have hsg : towerSign e (n + 1) i.val j.val
            = natPar n J.val * towerSign e n I.val J.val := by
          rw [towerSign]; simp only [if_pos hi, if_neg h2, mul_one, hI, hJ]
        rw [tb_high ε n I i (by omega), tb_low ε n J j hJv.symm,
          tb_high ε n (towerIdxFin n I J) (towerIdxFin (n + 1) i j) hidx,
          tw_hl, hpar, mul_smul_comm, IH, smul_smul, tw_smul_right, hsg]
        push_cast
        ring_nf
      · -- high · high : `(0,B)(0,D) = (ε·B·JD, 0)`
        have hIv : I.val = i.val - 2 ^ n := by rw [hI, mod_high i.isLt hi]
        have hJv : J.val = j.val - 2 ^ n := by rw [hJ, mod_high j.isLt hj]
        have hidx : (towerIdxFin (n + 1) i j).val = (towerIdxFin n I J).val := by
          show towerIdx (n + 1) i.val j.val = towerIdx n I.val J.val
          rw [towerIdx]; simp only [if_pos hi, if_pos hj, zero_add, hI, hJ]
        have hsg : towerSign e (n + 1) i.val j.val
            = natPar n J.val * e * towerSign e n I.val J.val := by
          rw [towerSign]; simp only [if_pos hi, if_pos hj, hI, hJ]
        rw [tb_high ε n I i (by omega), tb_high ε n J j (by omega),
          tb_low ε n (towerIdxFin n I J) (towerIdxFin (n + 1) i j) hidx,
          tw_hh, hpar, mul_smul_comm, IH, smul_smul, smul_smul, tw_smul_left, hsg, hε]
        push_cast
        ring_nf

/-! ### 1.4 The quaternion table

`realRep 4 = quatEvenSuper` is purely even, so it is *not* a floor of either
tower and gets its own table: the Klein four-group `1, i, j, k` with the
standard quaternion signs.  (The index rule is still `xor`; the sign 2-cocycle
is a different one.) -/

section Quaternions

open Quaternion

/-- Instance transfer for `*` on the quaternion floor. -/
theorem quat_mul_eq (x y : quatEvenSuper.carrier) :
    x * y = @HMul.hMul ℍ[ℝ] ℍ[ℝ] ℍ[ℝ] instHMul x y := rfl

/-- Instance transfer for `•` on the quaternion floor. -/
theorem quat_smul_eq (σ : ℝ) (x : quatEvenSuper.carrier) :
    σ • x = @HSMul.hSMul ℝ ℍ[ℝ] ℍ[ℝ] instHSMul σ x := rfl

/-- `quatBasis` is `1, i, j, k` in coordinates. -/
theorem quatBasis_apply (i : Fin 4) :
    quatBasis i = (![(⟨1, 0, 0, 0⟩ : ℍ[ℝ]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i :
      quatEvenSuper.carrier) := by
  refine (Basis.apply_eq_iff (b := quatBasis)).mpr ?_
  refine Finsupp.ext fun j => ?_
  show (QuaternionAlgebra.basisOneIJK (-1 : ℝ) (0 : ℝ) (-1 : ℝ)).repr
      (![(⟨1, 0, 0, 0⟩ : ℍ[ℝ]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i) j = _
  rw [QuaternionAlgebra.coe_basisOneIJK_repr]
  fin_cases i <;> fin_cases j <;> simp

/-- The quaternion product index: the Klein four-group table (`= xor`). -/
def quatIdxFin (i j : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] i j

/-- The quaternion product sign: rows `1, i, j, k`. -/
def quatSign (i j : ℕ) : ℤ :=
  (([[1, 1, 1, 1], [1, -1, 1, -1], [1, -1, -1, 1], [1, 1, -1, -1]] :
      List (List ℤ)).getD i []).getD j 0

/-- **T1, the quaternion case.** -/
theorem quatBasis_mul (i j : Fin 4) :
    quatBasis i * quatBasis j
      = ((quatSign i.val j.val : ℤ) : ℝ) • quatBasis (quatIdxFin i j) := by
  rw [quat_mul_eq, quat_smul_eq]
  simp only [quatBasis_apply]
  fin_cases i <;> fin_cases j <;>
    (apply QuaternionAlgebra.ext <;> simp [quatSign, quatIdxFin])

end Quaternions

/-! ### 1.5 The eight labels

`realRepMulIdxAux` / `realRepMulSignAux` dispatch exactly as `realRepBasisAux`
does, so each case of `realRepBasisAux_mul` is a single `exact`. -/

theorem realRepDim_pos : ∀ m : ℕ, 0 < realRepDim m
  | 0 => Nat.succ_pos _
  | 1 => Nat.succ_pos _
  | 2 => Nat.succ_pos _
  | 3 => Nat.succ_pos _
  | 4 => Nat.succ_pos _
  | 5 => Nat.succ_pos _
  | 6 => Nat.succ_pos _
  | _ + 7 => Nat.succ_pos _

/-- The product index of the canonical basis of the `m`-th representative. -/
def realRepMulIdxAux :
    (m : ℕ) → Fin (realRepDim m) → Fin (realRepDim m) → Fin (realRepDim m)
  | 0, i, _ => i
  | 1, i, j => towerIdxFin 1 i j
  | 2, i, j => towerIdxFin 2 i j
  | 3, i, j => towerIdxFin 3 i j
  | 4, i, j => quatIdxFin i j
  | 5, i, j => towerIdxFin 3 i j
  | 6, i, j => towerIdxFin 2 i j
  | _ + 7, i, j => towerIdxFin 1 i j

/-- The product sign of the canonical basis of the `m`-th representative. -/
def realRepMulSignAux : (m : ℕ) → Fin (realRepDim m) → Fin (realRepDim m) → ℤ
  | 0, _, _ => 1
  | 1, i, j => towerSign (-1) 1 i.val j.val
  | 2, i, j => towerSign (-1) 2 i.val j.val
  | 3, i, j => towerSign (-1) 3 i.val j.val
  | 4, i, j => quatSign i.val j.val
  | 5, i, j => towerSign 1 3 i.val j.val
  | 6, i, j => towerSign 1 2 i.val j.val
  | _ + 7, i, j => towerSign 1 1 i.val j.val

theorem realRepBasisAux_mul : ∀ (m : ℕ) (i j : Fin (realRepDim m)),
    realRepBasisAux m i * realRepBasisAux m j
      = ((realRepMulSignAux m i j : ℤ) : ℝ)
          • realRepBasisAux m (realRepMulIdxAux m i j)
  | 0, i, j => by
      show (Basis.singleton (Fin 1) ℝ) i * (Basis.singleton (Fin 1) ℝ) j
        = ((1 : ℤ) : ℝ) • (Basis.singleton (Fin 1) ℝ) i
      simp [Basis.singleton_apply]
  | 1, i, j => towerBasis_mul (-1 : ℝ) (-1 : ℤ) (by norm_num) 1 i j
  | 2, i, j => towerBasis_mul (-1 : ℝ) (-1 : ℤ) (by norm_num) 2 i j
  | 3, i, j => towerBasis_mul (-1 : ℝ) (-1 : ℤ) (by norm_num) 3 i j
  | 4, i, j => quatBasis_mul i j
  | 5, i, j => towerBasis_mul (1 : ℝ) (1 : ℤ) (by norm_num) 3 i j
  | 6, i, j => towerBasis_mul (1 : ℝ) (1 : ℤ) (by norm_num) 2 i j
  | _ + 7, i, j => towerBasis_mul (1 : ℝ) (1 : ℤ) (by norm_num) 1 i j

/-! The involution and `xor` facts are closed statements only at a *concrete*
floor, so they are `decide`d there and transported to the eight labels by
`exact` (definitional unfolding of `realRepMulIdxAux`).  `decide` refuses a
goal with free variables, which is why the `_ + 7` branch cannot be `decide`d
in place even though `realRepDim (m + 7) = 2` definitionally. -/

private theorem invol1 : ∀ i j : Fin (2 ^ 1), towerIdxFin 1 i (towerIdxFin 1 i j) = j := by
  decide
private theorem invol2 : ∀ i j : Fin (2 ^ 2), towerIdxFin 2 i (towerIdxFin 2 i j) = j := by
  decide
private theorem invol3 : ∀ i j : Fin (2 ^ 3), towerIdxFin 3 i (towerIdxFin 3 i j) = j := by
  decide
private theorem involQ : ∀ i j : Fin 4, quatIdxFin i (quatIdxFin i j) = j := by decide

private theorem xor1 : ∀ i j : Fin (2 ^ 1), (towerIdxFin 1 i j).val = i.val ^^^ j.val := by
  decide
private theorem xor2 : ∀ i j : Fin (2 ^ 2), (towerIdxFin 2 i j).val = i.val ^^^ j.val := by
  decide
private theorem xor3 : ∀ i j : Fin (2 ^ 3), (towerIdxFin 3 i j).val = i.val ^^^ j.val := by
  decide
private theorem xorQ : ∀ i j : Fin 4, (quatIdxFin i j).val = i.val ^^^ j.val := by decide

/-- `realRepMulIdxAux m i ·` is an involution — the `xor` structure.  This is
what makes the coefficient convolution of §2 cost `k²` rather than `k³`. -/
theorem realRepMulIdxAux_involutive : ∀ (m : ℕ) (i j : Fin (realRepDim m)),
    realRepMulIdxAux m i (realRepMulIdxAux m i j) = j
  | 0 => fun i j => by
      have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show i = j
      exact Fin.ext (hi.trans hj.symm)
  | 1 => invol1
  | 2 => invol2
  | 3 => invol3
  | 4 => involQ
  | 5 => invol3
  | 6 => invol2
  | _ + 7 => invol1

/-- **The product index of every canonical basis is `xor`**: each `realRep a`
is a *twisted group algebra* of `(ℤ/2)^m`.  (Checked label by label; only
`m ≤ 3` occurs.) -/
theorem realRepMulIdxAux_eq_xor : ∀ (m : ℕ) (i j : Fin (realRepDim m)),
    (realRepMulIdxAux m i j).val = i.val ^^^ j.val
  | 0 => fun i j => by
      have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show i.val = i.val ^^^ j.val
      rw [hi, hj]
      decide
  | 1 => xor1
  | 2 => xor2
  | 3 => xor3
  | 4 => xorQ
  | 5 => xor3
  | 6 => xor2
  | _ + 7 => xor1

/-- **The product index** of `realRepBasis a`. -/
def realRepMulIdx (a : ZMod 8) :
    Fin (realRepDim a.val) → Fin (realRepDim a.val) → Fin (realRepDim a.val) :=
  realRepMulIdxAux a.val

/-- **The product sign** of `realRepBasis a`. -/
def realRepMulSign (a : ZMod 8) :
    Fin (realRepDim a.val) → Fin (realRepDim a.val) → ℤ :=
  realRepMulSignAux a.val

/-- **T1.**  `realRepBasis a` is a signed monomial basis of `realRep a`.
Together with `realRepBasis_zero` (`GaugeChi/RouteMatrixProto.lean`) and
`realRepBasis_mem` (`Gauge/RealRepsBasis.lean`) this is the whole coordinate
description of the eight coefficient algebras. -/
theorem realRepBasis_mul (a : ZMod 8) (i j : Fin (realRepDim a.val)) :
    realRepBasis a i * realRepBasis a j
      = ((realRepMulSign a i j : ℤ) : ℝ) • realRepBasis a (realRepMulIdx a i j) :=
  realRepBasisAux_mul a.val i j

theorem realRepMulIdx_involutive (a : ZMod 8) (i j : Fin (realRepDim a.val)) :
    realRepMulIdx a i (realRepMulIdx a i j) = j :=
  realRepMulIdxAux_involutive a.val i j

theorem realRepMulIdx_eq_xor (a : ZMod 8) (i j : Fin (realRepDim a.val)) :
    (realRepMulIdx a i j).val = i.val ^^^ j.val :=
  realRepMulIdxAux_eq_xor a.val i j

/-! ## T2. Matrices over a based algebra, as integer coefficient arrays

Generic in the base ring `R`, the based algebra `P`, and the (finite,
decidable) matrix index type `ι`.  The transport style is the one of
`Superfusion/Super/BottCertificate.lean:172-177` (`(Int.castRingHom K).mapMatrix`),
upgraded from "matrices over the base ring" to "matrices over a based
algebra". -/

section Coeff

variable {R : Type*} [CommRing R] {P : Type*} [Ring P] [Algebra R P]
variable {ι : Type*} {k : ℕ}

/-- The matrix over `P` presented by the integer coefficient array `x`. -/
noncomputable def matOfCoeff (bP : Basis (Fin k) R P) (x : ι → ι → Fin k → ℤ) :
    Matrix ι ι P :=
  Matrix.of fun r s => ∑ g, ((x r s g : ℤ) : R) • bP g

theorem matOfCoeff_apply (bP : Basis (Fin k) R P) (x : ι → ι → Fin k → ℤ) (r s : ι) :
    matOfCoeff bP x r s = ∑ g, ((x r s g : ℤ) : R) • bP g := rfl

variable [Fintype ι]

/-- **The convolution of coefficient arrays** against a signed monomial table.
`co i` is the inverse of `idx i` (`realRepMulIdx_involutive` for the eight
coordinate algebras), which is what removes the `k`-fold `if idx i j = h`
search and makes one `P`-multiplication cost `k²` instead of `k³`. -/
def convCoeff (sg : Fin k → Fin k → ℤ) (co : Fin k → Fin k → Fin k)
    (x y : ι → ι → Fin k → ℤ) : ι → ι → Fin k → ℤ :=
  fun r t h => ∑ s, ∑ i, sg i (co i h) * x r s i * y s t (co i h)

/-- Reindexing a sum by the bijection `co i` (whose inverse is `idx i`). -/
private theorem reindex_sum {M : Type*} [AddCommMonoid M]
    {idx co : Fin k → Fin k → Fin k}
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (i : Fin k) (F : Fin k → M) : ∑ j, F j = ∑ h, F (co i h) :=
  (Equiv.sum_comp (⟨co i, idx i, hco' i, hco i⟩ : Fin k ≃ Fin k) F).symm

/-- **T2.**  Matrix multiplication over `P` is convolution of coefficient
arrays. -/
theorem matOfCoeff_mul {bP : Basis (Fin k) R P}
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (x y : ι → ι → Fin k → ℤ) :
    matOfCoeff bP x * matOfCoeff bP y = matOfCoeff bP (convCoeff sg co x y) := by
  classical
  ext r t
  rw [Matrix.mul_apply]
  have key : ∀ s : ι, matOfCoeff bP x r s * matOfCoeff bP y s t
      = ∑ i : Fin k, ∑ h : Fin k,
          ((sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R) • bP h := by
    intro s
    rw [matOfCoeff_apply, matOfCoeff_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (reindex_sum hco hco' i
      (fun j => (((x r s i : ℤ) : R) • bP i) * (((y s t j : ℤ) : R) • bP j))).trans ?_
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hmul, smul_smul, smul_smul, hco' i h]
    congr 1
    push_cast
    ring
  have hR : ∀ h : Fin k, ((convCoeff sg co x y r t h : ℤ) : R) • bP h
      = ∑ s : ι, ∑ i : Fin k,
          ((sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R) • bP h := by
    intro h
    show ((∑ s : ι, ∑ i : Fin k, sg i (co i h) * x r s i * y s t (co i h) : ℤ) : R)
      • bP h = _
    push_cast
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_smul
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (key s).trans Finset.sum_comm),
    matOfCoeff_apply, Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => hR h)]
  exact Finset.sum_comm

omit [Fintype ι] in
theorem matOfCoeff_zsmul (bP : Basis (Fin k) R P) (c : ℤ) (x : ι → ι → Fin k → ℤ) :
    c • matOfCoeff bP x = matOfCoeff bP (fun r s g => c * x r s g) := by
  ext r s
  rw [Matrix.smul_apply, matOfCoeff_apply, matOfCoeff_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Int.cast_smul_eq_zsmul R c, smul_smul]
  congr 1
  push_cast
  ring

omit [Fintype ι] in
/-- The coefficient array of a matrix over a based algebra is unique.  Not
needed for soundness (`checkMatEq_sound` only uses `matOfCoeff_mul`), but it
is what turns a *nonzero coefficient* into a *nonzero matrix*. -/
theorem matOfCoeff_injective [CharZero R] (bP : Basis (Fin k) R P) :
    Function.Injective (matOfCoeff (ι := ι) bP) := by
  intro x y hxy
  funext r s g
  have h1 : ∑ e, ((x r s e : ℤ) : R) • bP e = ∑ e, ((y r s e : ℤ) : R) • bP e :=
    congrFun (congrFun hxy r) s
  have h2 : ∑ e, (((x r s e : ℤ) : R) - ((y r s e : ℤ) : R)) • bP e = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
  have h3 := (Fintype.linearIndependent_iff.mp bP.linearIndependent) _ h2 g
  exact Int.cast_injective (sub_eq_zero.mp h3)

end Coeff

/-! ## T3. The kernel checker

The integer identity produced by T2 is closed data.  It is **not** stated as
an equality of `Fin σ → Fin σ → Fin k → ℤ` functions and `decide`d — that is
the `Matrix.mulᵣ` trap of `docs/route-layer-design.md` §4.1.  It is computed
by a `List` program and reduced as a `Bool` with `decide +kernel` (§4.2). -/

section Checker

/-- Read a `σ × σ × k` integer array out of nested list literals. -/
def coeffGet (L : List (List (List ℤ))) (r s g : ℕ) : ℤ :=
  ((L.getD r []).getD s []).getD g 0

/-- The `Fin`-indexed coefficient array of a nested list literal.  The *data*
stays in list form (fast under the kernel) while the *statement* is in
`Fin`-function form (what T2 consumes). -/
def coeffOf (σ k : ℕ) (L : List (List (List ℤ))) : Fin σ → Fin σ → Fin k → ℤ :=
  fun r s g => coeffGet L r.val s.val g.val

/-- ℕ-indexed shadow of a `Fin`-indexed table (junk `0` out of range). -/
def natTable2 {α : Type*} [Zero α] (k : ℕ) (f : Fin k → Fin k → α) : ℕ → ℕ → α :=
  fun i j => if hi : i < k then if hj : j < k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

theorem natTable2_apply {α : Type*} [Zero α] {k : ℕ} (f : Fin k → Fin k → α)
    (i j : Fin k) : natTable2 k f i.val j.val = f i j := by
  rw [natTable2, dif_pos i.isLt, dif_pos j.isLt]

/-- ℕ-indexed shadow of the `Fin`-valued cofactor table. -/
def natCo (k : ℕ) (co : Fin k → Fin k → Fin k) : ℕ → ℕ → ℕ :=
  fun i h => if hi : i < k then if hh : h < k then (co ⟨i, hi⟩ ⟨h, hh⟩).val else 0 else 0

theorem natCo_apply {k : ℕ} (co : Fin k → Fin k → Fin k) (i h : Fin k) :
    natCo k co i.val h.val = (co i h).val := by
  rw [natCo, dif_pos i.isLt, dif_pos h.isLt]

/-- The `List` program computing one entry of `convCoeff`.  This is what the
kernel actually runs; `convL_eq` is the only bridge back to `Finset.sum`. -/
def convL (σ k : ℕ) (coN : ℕ → ℕ → ℕ) (sgN : ℕ → ℕ → ℤ)
    (x y : List (List (List ℤ))) (r t h : ℕ) : ℤ :=
  ((List.range σ).map fun s =>
    ((List.range k).map fun i =>
      sgN i (coN i h) * coeffGet x r s i * coeffGet y s t (coN i h)).sum).sum

theorem sum_range_eq_listSum (f : ℕ → ℤ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_range_eq_listSum f n, List.range_succ,
        List.map_append, List.sum_append]
      simp

theorem sum_fin_eq_listSum (n : ℕ) (f : ℕ → ℤ) :
    ∑ i : Fin n, f i.val = ((List.range n).map f).sum := by
  rw [Fin.sum_univ_eq_sum_range, sum_range_eq_listSum]

theorem convL_eq {σ k : ℕ} {sg : Fin k → Fin k → ℤ} {co : Fin k → Fin k → Fin k}
    (x y : List (List (List ℤ))) (r t : Fin σ) (h : Fin k) :
    convL σ k (natCo k co) (natTable2 k sg) x y r.val t.val h.val
      = convCoeff sg co (coeffOf σ k x) (coeffOf σ k y) r t h := by
  show _ = ∑ s : Fin σ, ∑ i : Fin k,
    sg i (co i h) * coeffOf σ k x r s i * coeffOf σ k y s t (co i h)
  rw [convL, ← sum_fin_eq_listSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← sum_fin_eq_listSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [natCo_apply, natTable2_apply]
  rfl

/-- The `List`-based `Bool` driver: `≤ σ²·k` tests, each an `Int` comparison
of two `convL` entries.  Reduce with `decide +kernel`. -/
def checkAll (σ k : ℕ) (p : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range σ).all fun r => (List.range σ).all fun t => (List.range k).all fun h => p r t h

theorem checkAll_sound {σ k : ℕ} {p : ℕ → ℕ → ℕ → Bool} (hchk : checkAll σ k p = true)
    (r t : Fin σ) (g : Fin k) : p r.val t.val g.val = true := by
  rw [checkAll, List.all_eq_true] at hchk
  have h1 := hchk r.val (List.mem_range.mpr r.isLt)
  rw [List.all_eq_true] at h1
  have h2 := h1 t.val (List.mem_range.mpr t.isLt)
  rw [List.all_eq_true] at h2
  exact h2 g.val (List.mem_range.mpr g.isLt)

/-- **The per-triple certificate**: `X · T = c • (T · Y)` as integer
coefficient arrays. -/
def checkMatEq (σ k : ℕ) (coN : ℕ → ℕ → ℕ) (sgN : ℕ → ℕ → ℤ) (c : ℤ)
    (X T Y : List (List (List ℤ))) : Bool :=
  checkAll σ k fun r t h =>
    convL σ k coN sgN X T r t h == c * convL σ k coN sgN T Y r t h

/-- **T3.**  A `true` integer certificate gives the matrix identity over the
based algebra.  This is the only place where `ℝ` (or any base) is touched;
nothing is ever `decide`d over `ℝ`. -/
theorem checkMatEq_sound {R : Type*} [CommRing R] {P : Type*} [Ring P] [Algebra R P]
    {k σ : ℕ} (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff bP (coeffOf σ k X) * matOfCoeff bP (coeffOf σ k T)
      = c • (matOfCoeff bP (coeffOf σ k T) * matOfCoeff bP (coeffOf σ k Y)) := by
  rw [matOfCoeff_mul hmul hco hco', matOfCoeff_mul hmul hco hco', matOfCoeff_zsmul]
  refine congrArg (matOfCoeff bP) ?_
  funext r t h
  have hb := checkAll_sound hchk r t h
  rw [beq_iff_eq, convL_eq, convL_eq] at hb
  exact hb

/-- **Reindexing.**  The matrices of the 512-triple rollout are indexed by the
`matrixSuper` frame `Fin p ⊕ Fin q`, not by `Fin σ`.  `Matrix.submatrix` along
an equivalence carries a checked certificate over unchanged. -/
theorem checkMatEq_sound_submatrix {R : Type*} [CommRing R] {P : Type*} [Ring P]
    [Algebra R P] {k σ : ℕ} {ι : Type*} [Fintype ι] (e : ι ≃ Fin σ)
    (bP : Basis (Fin k) R P)
    {idx co : Fin k → Fin k → Fin k} {sg : Fin k → Fin k → ℤ}
    (hmul : ∀ i j, bP i * bP j = ((sg i j : ℤ) : R) • bP (idx i j))
    (hco : ∀ i j, co i (idx i j) = j) (hco' : ∀ i h, idx i (co i h) = h)
    (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ k (natCo k co) (natTable2 k sg) c X T Y = true) :
    matOfCoeff (ι := ι) bP (fun r s => coeffOf σ k X (e r) (e s))
        * matOfCoeff bP (fun r s => coeffOf σ k T (e r) (e s))
      = c • (matOfCoeff bP (fun r s => coeffOf σ k T (e r) (e s))
          * matOfCoeff bP (fun r s => coeffOf σ k Y (e r) (e s))) := by
  have hsub : ∀ Z : List (List (List ℤ)),
      matOfCoeff (ι := ι) bP (fun r s => coeffOf σ k Z (e r) (e s))
        = (matOfCoeff bP (coeffOf σ k Z)).submatrix e e := fun _ => rfl
  rw [hsub, hsub, hsub, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    checkMatEq_sound bP hmul hco hco' c X T Y hchk]
  rfl

end Checker

/-! ## The eight coordinate algebras, wired into the checker

`co = idx` for every `realRep a` (the index rule is `xor`,
`realRepMulIdx_eq_xor`), so a single involution lemma discharges both
inverse hypotheses of `checkMatEq_sound`. -/

section RealInstance

/-- The `ℕ`-level sign table of the `m`-th representative. -/
def realSignN (m : ℕ) : ℕ → ℕ → ℤ := natTable2 (realRepDim m) (realRepMulSignAux m)

/-- The `ℕ`-level cofactor table of the `m`-th representative. -/
def realCoN (m : ℕ) : ℕ → ℕ → ℕ := natCo (realRepDim m) (realRepMulIdxAux m)

/-- **The consumer lemma at `realRepBasisAux`.**  A `true` integer certificate
gives `X · T = c • (T · Y)` as matrices over the `m`-th coordinate algebra. -/
theorem realCheckMatEq_sound (m σ : ℕ) (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ (realRepDim m) (realCoN m) (realSignN m) c X T Y = true) :
    matOfCoeff (ι := Fin σ) (realRepBasisAux m) (coeffOf σ (realRepDim m) X)
        * matOfCoeff (realRepBasisAux m) (coeffOf σ (realRepDim m) T)
      = c • (matOfCoeff (realRepBasisAux m) (coeffOf σ (realRepDim m) T)
          * matOfCoeff (realRepBasisAux m) (coeffOf σ (realRepDim m) Y)) :=
  checkMatEq_sound (realRepBasisAux m) (realRepBasisAux_mul m)
    (realRepMulIdxAux_involutive m) (realRepMulIdxAux_involutive m) c X T Y hchk

/-- **The consumer lemma at `realRepBasis`** (the `ZMod 8`-indexed spelling the
per-triple generated files will use). -/
theorem realCheckMatEq_sound' (a : ZMod 8) (σ : ℕ) (c : ℤ) (X T Y : List (List (List ℤ)))
    (hchk : checkMatEq σ (realRepDim a.val) (realCoN a.val) (realSignN a.val) c X T Y
      = true) :
    matOfCoeff (ι := Fin σ) (realRepBasis a) (coeffOf σ (realRepDim a.val) X)
        * matOfCoeff (realRepBasis a) (coeffOf σ (realRepDim a.val) T)
      = c • (matOfCoeff (realRepBasis a) (coeffOf σ (realRepDim a.val) T)
          * matOfCoeff (realRepBasis a) (coeffOf σ (realRepDim a.val) Y)) :=
  realCheckMatEq_sound a.val σ c X T Y hchk

end RealInstance

/-! ## Self-tests

Small but real instances of the whole stack, all reduced by `decide +kernel`
(never `native_decide`).  Measured wall clock is recorded in the report of
`docs/route-layer-design.md` §5. -/

section SelfTest

/-- The `σ × σ` identity, as a coefficient array (uses `realRepBasis _ 0 = 1`). -/
def idCoeff (σ k : ℕ) : List (List (List ℤ)) :=
  (List.range σ).map fun r => (List.range σ).map fun s =>
    (List.range k).map fun g => if r = s ∧ g = 0 then 1 else 0

/-- `g · I₈` over `D₁` (`g` is the odd generator, basis index `1`). -/
def genDiag8 : List (List (List ℤ)) :=
  (List.range 8).map fun r => (List.range 8).map fun s => if r = s then [0, 1] else [0, 0]

/-- A `D₁`-valued band matrix: `1` on the diagonal, `g` on the superdiagonal. -/
def band8 : List (List (List ℤ)) :=
  (List.range 8).map fun r => (List.range 8).map fun s =>
    if r = s then [1, 0] else if s = r + 1 then [0, 1] else [0, 0]

/-- **Self-test 1** — the `8 × 8` identity over `D₁` (a `16 × 16` real matrix):
`I · I = 1 • (I · I)`.  `8² · 2 = 128` checks, `2 · 8 · 2 = 32` multiply-adds
each. -/
theorem selfTest_id8 :
    checkMatEq 8 2 (realCoN 1) (realSignN 1) 1 (idCoeff 8 2) (idCoeff 8 2) (idCoeff 8 2)
      = true := by
  decide +kernel

/-- **Self-test 2** — a genuine convolution over `D₁ = ℂ`: `g·I · M = M · g·I`
for a band matrix `M`.  (Exercises the sign `g² = −1` on the superdiagonal.) -/
theorem selfTest_band8 :
    checkMatEq 8 2 (realCoN 1) (realSignN 1) 1 genDiag8 band8 genDiag8 = true := by
  decide +kernel

/-- **Self-test 3** — the Clifford anticommutation `e₁ e₂ = −e₂ e₁` in `D₃`
(`k = 8`, `σ = 1`): the sign table is doing real work here. -/
theorem selfTest_cliff3 :
    checkMatEq 1 8 (realCoN 3) (realSignN 3) (-1)
      [[[0, 1, 0, 0, 0, 0, 0, 0]]] [[[0, 0, 1, 0, 0, 0, 0, 0]]]
      [[[0, 1, 0, 0, 0, 0, 0, 0]]] = true := by
  decide +kernel

/-- **Negative control** — the same three matrices with `c = 1` are *rejected*.
Without this the positive tests would not show that the sign table is doing
anything. -/
theorem selfTest_cliff3_reject :
    checkMatEq 1 8 (realCoN 3) (realSignN 3) 1
      [[[0, 1, 0, 0, 0, 0, 0, 0]]] [[[0, 0, 1, 0, 0, 0, 0, 0]]]
      [[[0, 1, 0, 0, 0, 0, 0, 0]]] = false := by
  decide +kernel

/-- **Negative control** — `g·I · M = M · g·I` fails with `c = −1`. -/
theorem selfTest_band8_reject :
    checkMatEq 8 2 (realCoN 1) (realSignN 1) (-1) genDiag8 band8 genDiag8 = false := by
  decide +kernel

/-- **Self-test 4** — the same certificate transported to an identity of
matrices over `ℝ`: this is the shape every per-triple generator check will
have. -/
theorem selfTest_cliff3_real :
    matOfCoeff (ι := Fin 1) (realRepBasisAux 3) (coeffOf 1 8 [[[0, 1, 0, 0, 0, 0, 0, 0]]])
        * matOfCoeff (realRepBasisAux 3) (coeffOf 1 8 [[[0, 0, 1, 0, 0, 0, 0, 0]]])
      = (-1 : ℤ) • (matOfCoeff (realRepBasisAux 3) (coeffOf 1 8 [[[0, 0, 1, 0, 0, 0, 0, 0]]])
          * matOfCoeff (realRepBasisAux 3) (coeffOf 1 8 [[[0, 1, 0, 0, 0, 0, 0, 0]]])) :=
  realCheckMatEq_sound 3 1 (-1) _ _ _ selfTest_cliff3

/-- **Self-test 5** — the `8 × 8` identity transported to `ℝ`, at the `ZMod 8`
spelling. -/
theorem selfTest_id8_real :
    matOfCoeff (ι := Fin 8) (realRepBasis 1) (coeffOf 8 (realRepDim (1 : ZMod 8).val)
          (idCoeff 8 2))
        * matOfCoeff (realRepBasis 1) (coeffOf 8 (realRepDim (1 : ZMod 8).val) (idCoeff 8 2))
      = (1 : ℤ) • (matOfCoeff (realRepBasis 1)
            (coeffOf 8 (realRepDim (1 : ZMod 8).val) (idCoeff 8 2))
          * matOfCoeff (realRepBasis 1) (coeffOf 8 (realRepDim (1 : ZMod 8).val)
            (idCoeff 8 2))) :=
  realCheckMatEq_sound' 1 8 1 _ _ _ selfTest_id8

end SelfTest

#print axioms selfTest_id8_real
#print axioms selfTest_cliff3_real
#print axioms realRepBasis_mul
#print axioms checkMatEq_sound

end Superfusion
