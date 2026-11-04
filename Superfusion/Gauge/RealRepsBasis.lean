/-
Superfusion / Gauge / RealRepsBasis

M15 semantic-bridge step 1: **explicit homogeneous bases of the eight
coordinate algebras `realRep a`, tied to the constructors**.

`divisionTower ε n` has carrier the `n`-fold iterated pair
`(⋯(K × K)⋯)` (each floor is `OddDouble`, i.e. `A ⊕ A·g` realized on
`A × A`).  We build the canonical basis
`towerBasis ε n : Basis (Fin (2 ^ n)) ℝ _` by the same recursion as the
tower itself; at floor `n + 1` the index block `i < 2 ^ n` is the pair
`(e_i, 0)` (the `A`-coordinate) and the block `2 ^ n + i` is `(0, e_i)`
(the `A·g`-coordinate).  The anchor lemmas `towerBasis_low` /
`towerBasis_high` record exactly this identification — they are the
point of the file: downstream, coordinate certificates can name a basis
vector and know which tower element it is.

`towerIndexParity` is the matching block recursion on indices (low block
keeps parity, high block adds `1` — popcount mod 2), and
`towerBasis_mem` places each basis vector in its grading layer, using
the `OddDouble` grading `(OddDouble 𝒜 ε)ᵢ = 𝒜ᵢ × 𝒜ᵢ₊₁`: a pair `(x, 0)`
with `x ∈ 𝒜 j` is in degree `j`, a pair `(0, y)` with `y ∈ 𝒜 j` is in
degree `j + 1`.

The quaternion floor `realRep 4` (purely even `ℍ[ℝ]`) gets Mathlib's
basis `1, i, j, k` (`QuaternionAlgebra.basisOneIJK`), all even.

`realRepBasis a` bundles the eight cases along the dimension table
`realRepDim = [1, 2, 4, 8, 4, 8, 4, 2]`, with parity `realRepBasisParity`
and homogeneity `realRepBasis_mem`.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge).
-/
import Superfusion.Gauge.RealReps

namespace Superfusion

open Module Quaternion

/-! ### Index bookkeeping for the block split -/

/-- The index arithmetic of the block split: `2 ^ n + 2 ^ n = 2 ^ (n + 1)`. -/
theorem two_pow_add_self (n : ℕ) : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
  rw [pow_succ, mul_two]

/-- A low-block index `i < 2 ^ n` is an index of floor `n + 1`. -/
theorem towerIndexLow_lt (n : ℕ) (i : Fin (2 ^ n)) : (i : ℕ) < 2 ^ (n + 1) := by
  have h1 := i.isLt
  have h2 := two_pow_add_self n
  omega

/-- A high-block index `2 ^ n + i` is an index of floor `n + 1`. -/
theorem towerIndexHigh_lt (n : ℕ) (i : Fin (2 ^ n)) :
    2 ^ n + (i : ℕ) < 2 ^ (n + 1) := by
  have h1 := i.isLt
  have h2 := two_pow_add_self n
  omega

/-! ### The tower basis -/

/-- The canonical homogeneous basis of `divisionTower ε n`, indexed by
`Fin (2 ^ n)` and built by the same recursion as the tower: floor `0` is
the singleton basis of `ℝ`; at floor `n + 1` (carrier
`OddDouble … = A × A`) the index block `i < 2 ^ n` is the pair
`(e_i, 0)` and the block `2 ^ n + i` is `(0, e_i)` — see the anchor
lemmas `towerBasis_low` / `towerBasis_high`. -/
noncomputable def towerBasis (ε : ℝ) :
    (n : ℕ) → Basis (Fin (2 ^ n)) ℝ (divisionTower ε n).carrier
  | 0 => (Basis.singleton (Fin 1) ℝ).reindex (finCongr (pow_zero 2).symm)
  | n + 1 =>
      ((towerBasis ε n).prod (towerBasis ε n)).reindex
        (finSumFinEquiv.trans (finCongr (two_pow_add_self n)))

/-- At floor `0` every (i.e. the unique) basis vector is `1 : ℝ`. -/
theorem towerBasis_zero_apply (ε : ℝ) (i : Fin (2 ^ 0)) :
    towerBasis ε 0 i = (1 : ℝ) := by
  show ((Basis.singleton (Fin 1) ℝ).reindex (finCongr (pow_zero 2).symm)) i
    = (1 : ℝ)
  rw [Basis.reindex_apply, Basis.singleton_apply]

/-- **Low-block anchor**: at floor `n + 1`, the basis vector of index
`i < 2 ^ n` is the pair `(e_i, 0)` — the `i`-th basis vector of the
`A`-coordinate of `A ⊕ A·g`. -/
theorem towerBasis_low (ε : ℝ) (n : ℕ) (i : Fin (2 ^ n)) :
    towerBasis ε (n + 1) ⟨(i : ℕ), towerIndexLow_lt n i⟩ =
      OddDouble.mk (divisionTower ε n).grading ε (towerBasis ε n i) 0 := by
  have hsymm : (finSumFinEquiv.trans (finCongr (two_pow_add_self n))).symm
      (⟨(i : ℕ), towerIndexLow_lt n i⟩ : Fin (2 ^ (n + 1))) = Sum.inl i := by
    rw [Equiv.symm_trans_apply,
      show (finCongr (two_pow_add_self n)).symm
          (⟨(i : ℕ), towerIndexLow_lt n i⟩ : Fin (2 ^ (n + 1)))
        = Fin.castAdd (2 ^ n) i from Fin.ext rfl,
      finSumFinEquiv_symm_apply_castAdd]
  show (((towerBasis ε n).prod (towerBasis ε n)).reindex
      (finSumFinEquiv.trans (finCongr (two_pow_add_self n))))
      ⟨(i : ℕ), towerIndexLow_lt n i⟩ = _
  rw [Basis.reindex_apply, hsymm]
  exact Prod.ext (Basis.prod_apply_inl_fst _ _ _) (Basis.prod_apply_inl_snd _ _ _)

/-- **High-block anchor**: at floor `n + 1`, the basis vector of index
`2 ^ n + i` is the pair `(0, e_i)` — the `i`-th basis vector of the
`A·g`-coordinate of `A ⊕ A·g`. -/
theorem towerBasis_high (ε : ℝ) (n : ℕ) (i : Fin (2 ^ n)) :
    towerBasis ε (n + 1) ⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ =
      OddDouble.mk (divisionTower ε n).grading ε 0 (towerBasis ε n i) := by
  have hsymm : (finSumFinEquiv.trans (finCongr (two_pow_add_self n))).symm
      (⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ : Fin (2 ^ (n + 1)))
      = Sum.inr i := by
    rw [Equiv.symm_trans_apply,
      show (finCongr (two_pow_add_self n)).symm
          (⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ : Fin (2 ^ (n + 1)))
        = Fin.natAdd (2 ^ n) i from Fin.ext rfl,
      finSumFinEquiv_symm_apply_natAdd]
  show (((towerBasis ε n).prod (towerBasis ε n)).reindex
      (finSumFinEquiv.trans (finCongr (two_pow_add_self n))))
      ⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ = _
  rw [Basis.reindex_apply, hsymm]
  exact Prod.ext (Basis.prod_apply_inr_fst _ _ _) (Basis.prod_apply_inr_snd _ _ _)

/-! ### Index parity -/

/-- Parity of a tower basis index, by the block recursion: at floor
`n + 1` the low block `i < 2 ^ n` keeps the parity of the sub-index, the
high block `2 ^ n + i` adds `1`.  (Equivalently the popcount of the
index mod 2, but defined by the block recursion so that proofs align
with `towerBasis`.) -/
def towerIndexParity : (n : ℕ) → Fin (2 ^ n) → ZMod 2
  | 0, _ => 0
  | n + 1, i =>
      if h : (i : ℕ) < 2 ^ n then towerIndexParity n ⟨(i : ℕ), h⟩
      else
        towerIndexParity n ⟨(i : ℕ) - 2 ^ n, by
          have h1 := i.isLt
          have h2 := two_pow_add_self n
          omega⟩ + 1

/-- The low block keeps the parity of the sub-index. -/
theorem towerIndexParity_low (n : ℕ) (i : Fin (2 ^ n)) :
    towerIndexParity (n + 1) ⟨(i : ℕ), towerIndexLow_lt n i⟩ =
      towerIndexParity n i :=
  (dif_pos i.isLt).trans (congrArg (towerIndexParity n) (Fin.ext rfl))

/-- The high block adds `1` to the parity of the sub-index. -/
theorem towerIndexParity_high (n : ℕ) (i : Fin (2 ^ n)) :
    towerIndexParity (n + 1) ⟨2 ^ n + (i : ℕ), towerIndexHigh_lt n i⟩ =
      towerIndexParity n i + 1 := by
  have hge : ¬ 2 ^ n + (i : ℕ) < 2 ^ n := by omega
  have hlt : 2 ^ n + (i : ℕ) - 2 ^ n < 2 ^ n := by
    have h1 := i.isLt
    omega
  refine (dif_neg hge).trans ?_
  exact congrArg (fun t => towerIndexParity n t + 1)
    (Fin.ext (show 2 ^ n + (i : ℕ) - 2 ^ n = (i : ℕ) by omega) :
      (⟨2 ^ n + (i : ℕ) - 2 ^ n, hlt⟩ : Fin (2 ^ n)) = i)

private theorem zmod2_succ_succ : ∀ p : ZMod 2, p + 1 + 1 = p := by decide

/-- **Homogeneity of the tower basis**: the `i`-th basis vector of floor
`n` lies in the grading layer `towerIndexParity n i`.  Low-block vectors
`(e_i, 0)` sit in the degree of `e_i` (the second coordinate `0` is in
every layer), high-block vectors `(0, e_i)` in that degree plus one,
matching `OddDouble`'s grading `(OddDouble 𝒜 ε)ᵢ = 𝒜ᵢ × 𝒜ᵢ₊₁`. -/
theorem towerBasis_mem (ε : ℝ) :
    ∀ (n : ℕ) (i : Fin (2 ^ n)),
      towerBasis ε n i ∈ (divisionTower ε n).grading (towerIndexParity n i)
  | 0, _ => mem_evenGrading_zero ℝ ℝ _
  | n + 1, j => by
      rcases Nat.lt_or_ge (j : ℕ) (2 ^ n) with h | h
      · have hj : j = ⟨((⟨(j : ℕ), h⟩ : Fin (2 ^ n)) : ℕ),
            towerIndexLow_lt n ⟨(j : ℕ), h⟩⟩ := Fin.ext rfl
        rw [hj, towerBasis_low, towerIndexParity_low]
        exact OddDouble.mk_mem_grading _ ε (towerBasis_mem ε n _) (zero_mem _)
      · have hlt : (j : ℕ) - 2 ^ n < 2 ^ n := by
          have h1 := j.isLt
          have h2 := two_pow_add_self n
          omega
        have hj : j = ⟨2 ^ n + ((⟨(j : ℕ) - 2 ^ n, hlt⟩ : Fin (2 ^ n)) : ℕ),
            towerIndexHigh_lt n ⟨(j : ℕ) - 2 ^ n, hlt⟩⟩ :=
          Fin.ext (show (j : ℕ) = 2 ^ n + ((j : ℕ) - 2 ^ n) by omega)
        rw [hj, towerBasis_high, towerIndexParity_high]
        refine OddDouble.mk_mem_grading _ ε (zero_mem _) ?_
        rw [zmod2_succ_succ]
        exact towerBasis_mem ε n _

/-! ### The quaternion floor -/

/-- The explicit basis `1, i, j, k` of the quaternion floor
`quatEvenSuper` (`= realRep 4` definitionally; the carrier is `ℍ[ℝ]`
definitionally). -/
noncomputable def quatBasis : Basis (Fin 4) ℝ quatEvenSuper.carrier :=
  QuaternionAlgebra.basisOneIJK _ _ _

/-- The quaternion basis is purely even: every vector lies in layer `0`
(which is `⊤`, by `evenGrading_zero`). -/
theorem quatBasis_mem (i : Fin 4) : quatBasis i ∈ quatEvenSuper.grading 0 :=
  mem_evenGrading_zero ℝ ℍ[ℝ] _

/-! ### The per-label bundle -/

/-- Dimension table of the eight representatives, matching `a.val` under
`realRepAux`: `[1, 2, 4, 8, 4, 8, 4, 2]`. -/
def realRepDim : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 4
  | 5 => 8
  | 6 => 4
  | _ => 2

/-- The canonical homogeneous basis of the `m`-th representative
(`realRepAux m`), dispatching case by case exactly as `realRepAux` does:
`0` the singleton on `ℝ`, `1..3` the `ε = -1` tower bases, `4` the
quaternion basis `1, i, j, k`, `5..7` the `ε = 1` tower bases of floors
`3, 2, 1`. -/
noncomputable def realRepBasisAux :
    (m : ℕ) → Basis (Fin (realRepDim m)) ℝ (realRepAux m).carrier
  | 0 => Basis.singleton (Fin 1) ℝ
  | 1 => towerBasis (-1) 1
  | 2 => towerBasis (-1) 2
  | 3 => towerBasis (-1) 3
  | 4 => quatBasis
  | 5 => towerBasis 1 3
  | 6 => towerBasis 1 2
  | _ + 7 => towerBasis 1 1

/-- Parity table of `realRepBasisAux`: `0` on the purely even floors
(`ℝ` at `0`, `ℍ[ℝ]` at `4`), `towerIndexParity` on the tower floors. -/
def realRepBasisParityAux : (m : ℕ) → Fin (realRepDim m) → ZMod 2
  | 0, _ => 0
  | 1, i => towerIndexParity 1 i
  | 2, i => towerIndexParity 2 i
  | 3, i => towerIndexParity 3 i
  | 4, _ => 0
  | 5, i => towerIndexParity 3 i
  | 6, i => towerIndexParity 2 i
  | _ + 7, i => towerIndexParity 1 i

/-- Homogeneity of `realRepBasisAux`: the `i`-th basis vector of the
`m`-th representative lies in layer `realRepBasisParityAux m i`. -/
theorem realRepBasisAux_mem :
    ∀ (m : ℕ) (i : Fin (realRepDim m)),
      realRepBasisAux m i ∈ (realRepAux m).grading (realRepBasisParityAux m i)
  | 0, _ => mem_evenGrading_zero ℝ ℝ _
  | 1, i => towerBasis_mem (-1) 1 i
  | 2, i => towerBasis_mem (-1) 2 i
  | 3, i => towerBasis_mem (-1) 3 i
  | 4, i => quatBasis_mem i
  | 5, i => towerBasis_mem 1 3 i
  | 6, i => towerBasis_mem 1 2 i
  | _ + 7, i => towerBasis_mem 1 1 i

/-- **The canonical homogeneous basis of `realRep a`** (Table 1),
indexed by `Fin (realRepDim a.val)`: the per-label bundling of
`realRepBasisAux` along `realRep a = realRepAux a.val`. -/
noncomputable def realRepBasis (a : ZMod 8) :
    Basis (Fin (realRepDim a.val)) ℝ (realRep a).carrier :=
  realRepBasisAux a.val

/-- The parity of the `i`-th basis vector of `realRep a`. -/
def realRepBasisParity (a : ZMod 8) : Fin (realRepDim a.val) → ZMod 2 :=
  realRepBasisParityAux a.val

/-- **Homogeneity of the bundled bases**: `realRepBasis a i` lies in the
grading layer `realRepBasisParity a i` of `realRep a`. -/
theorem realRepBasis_mem (a : ZMod 8) (i : Fin (realRepDim a.val)) :
    realRepBasis a i ∈ (realRep a).grading (realRepBasisParity a i) :=
  realRepBasisAux_mem a.val i

end Superfusion
