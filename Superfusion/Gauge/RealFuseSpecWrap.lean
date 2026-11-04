/-
Superfusion / Gauge / RealFuseSpecWrap

M15 semantic-bridge GROUP C: value-pinning spec theorems for the
**wrap pairs** — the branches of `RealFuse4` whose Clifford floors sum
*past* the Bott floor `4` and therefore route through a floor-`4`
quaternion certificate.

**Landed here** (the two `ε = +1` wraps that hit the floor exactly, so
that the certificate is the field-generic `towerFourQuatSuper`):

* `realFuseMatrix_5_7 : realFuseMatrix 5 7 = !![…]` (16 × 16),
* `realFuseMatrix_6_6 : realFuseMatrix 6 6 = !![…]` (16 × 16).

Both factor as `towerFuse (1 : ℝ) a b ; towerFourQuatSuper ℝ`, and the
whole computation splits into two halves, each pinned separately and
reusable for the remaining wraps:

1. **The tower half** is *sign-free*.  `towerFuse ε a b` sends the
   left-major frame vector `towerBasis ε a i ᵍ⊗ towerBasis ε b j` to
   `towerBasis ε (a+b) (i + 2^a · j)` with coefficient `1`: the tower
   basis is the monomial basis in *increasing* generator order, the
   fusion concatenates two already-ordered blocks, so no generator ever
   has to be moved past another and the Koszul sign never fires.  The
   application lemmas `towerFuse_a_one_tmul_{one,gen}` and
   `towerFuse_a_two_tmul_{one,g1,g2,g1g2}` are stated **generically in
   the left floor `a`**, so the same four lemmas serve `(5,7)` (`a = 3`,
   `b = 1`) and `(6,6)` (`a = 2`, `b = 2`) — and would serve the
   `ε = -1` mirrors `(1,3)`, `(2,2)` unchanged.
2. **The certificate half** carries all the signs.
   `quatHom = towerLift 1 (quatGamma ℝ) 4` sends `towerBasis 1 4 k` to
   the product `∏_{m ∈ bits k} γ_m` in increasing `m` (each tower step
   multiplies the *new* generator on the right, `towerLift_succ_mk`),
   and every such product is either antidiagonal (`offM a b`) or
   diagonal (`diaM a b`) with `a, b ∈ {±1, ±i, ±j, ±k}` — two nonzero
   entries per column, which is exactly the shape of the frozen
   literals.  `qv4_0 … qv4_15` pin the sixteen products;
   `qc4_0 … qc4_15` re-express them in the target frame
   `matrixSuperBasis quatBasis 1 1` (index `e + 4·(s' + 2·r')`).

**Instance-diamond notes** (these cost the most time; recorded for the
remaining branches):

* `ℍ[ℝ]`'s `Mul`/`Neg`/`SMul` are *not* on the same instance path that
  `mul_neg`, `neg_one_smul`, `one_mul` are stated at: those lemmas
  typecheck in **term mode** (`exact mul_neg a b` works) but `rw`/`simp`
  cannot see them (`fail_if_success rw [mul_neg]` succeeds).  Every sign
  is therefore carried as a *literal* (`n1`, `nqi`, `nqj`, `nqk`) and
  every Hamilton relation is proved once, by `mk_mul_mk` + `ext` +
  `norm_num` (`qi_nqj`, …, `nqk_nqk`).
* `(quatEvenSuper.matrixSuper 1 1).carrier` and the bare
  `Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[ℝ]` are definitionally but
  *not* instance-transparently equal; `smul_dstQ` crosses the gap once,
  with `show` (default transparency) rather than `rw`.  Taking a
  hypothesis `hM : M = Matrix.single r c v` instead of writing the
  `Matrix.single` inline is what keeps the `HSMul` type argument in the
  *bundled* spelling, so that `rw [smul_dstQ …]` matches the goal.
* In the final assembly, `rw [LinearMap.toMatrix_apply]` re-instantiates
  the map at the *basis-derived* instances, which no longer match the
  `towerFourQuatSuper`-derived ones; the fix is to never state the
  column lemmas against `.toLinearMap`, and to route the goal through
  `realFuseMatrix_apply` + a single `show` into the branch-composite
  spelling.
* `fin_cases` must be run on honest `Fin 16`, not on
  `Fin ((realSize 5 7).1 + … )`: hoisting the entry computation into a
  `have key : ∀ i j : Fin 16, …` before `Matrix.ext` turns a
  `maxRecDepth`/`maxSteps` blowup into a few seconds.  The per-branch
  `set_option maxRecDepth 40000` is still needed for the 256 entry
  goals.

**Not landed** (needs `divisionTowerNegFourQuatSuper`, resp. the
matrix-ampliation tail): `(1,3)`, `(2,2)`, `(2,3)`, `(3,3)`, `(5,5)`,
`(5,6)`.  All six route through a *composite* floor-`4` certificate
(`cliffThetaEquiv.symm`, `oddDoubleGtensorDivisionOneEquiv.symm`,
`hypFuse`, `matrixSuperGtensorRight`) whose inverse direction has to be
evaluated on a basis first; the two halves above are unchanged and
reusable once that is done.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseMatrix
import Superfusion.Super.QuaternionTower

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

/-! ### The quaternion units and the explicit basis dictionary -/

/-- The quaternion unit `i`. -/
private def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The quaternion unit `j`. -/
private def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- The quaternion unit `k`. -/
private def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

private theorem quatBasis_0 : quatBasis 0 = (1 : ℍ[ℝ]) := by
  have h : (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)) 0 = (1 : ℍ[ℝ]) := by
    rw [Basis.apply_eq_iff]; ext i; fin_cases i <;> simp
  exact h

private theorem quatBasis_1 : quatBasis 1 = qi := by
  have h : (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)) 1 = qi := by
    rw [Basis.apply_eq_iff]; ext i; fin_cases i <;> simp [qi]
  exact h

private theorem quatBasis_2 : quatBasis 2 = qj := by
  have h : (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)) 2 = qj := by
    rw [Basis.apply_eq_iff]; ext i; fin_cases i <;> simp [qj]
  exact h

private theorem quatBasis_3 : quatBasis 3 = qk := by
  have h : (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)) 3 = qk := by
    rw [Basis.apply_eq_iff]; ext i; fin_cases i <;> simp [qk]
  exact h

/-! ### The negated units, as literals (the `Neg` of `ℍ[ℝ]` does not
match `mul_neg`'s instance path, so every sign is carried as a literal) -/

/-- `-1`, as a literal. -/
private def n1 : ℍ[ℝ] := ⟨-1, 0, 0, 0⟩
/-- `-i`, as a literal. -/
private def nqi : ℍ[ℝ] := ⟨0, -1, 0, 0⟩
/-- `-j`, as a literal. -/
private def nqj : ℍ[ℝ] := ⟨0, 0, -1, 0⟩
/-- `-k`, as a literal. -/
private def nqk : ℍ[ℝ] := ⟨0, 0, 0, -1⟩

private theorem neg_one_q : -(1 : ℍ[ℝ]) = n1 := by
  show -(1 : ℍ[ℝ]) = (⟨-1, 0, 0, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem neg_qi : -qi = nqi := by
  show -(⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = (⟨0, -1, 0, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem neg_qj : -qj = nqj := by
  show -(⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = (⟨0, 0, -1, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem neg_qk : -qk = nqk := by
  show -(⟨0, 0, 0, 1⟩ : ℍ[ℝ]) = (⟨0, 0, 0, -1⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

/-! ### The eight Hamilton products that occur in the certificate -/

private theorem qi_nqj : qi * nqj = nqk := by
  show (⟨0,1,0,0⟩ : ℍ[ℝ]) * ⟨0,0,-1,0⟩ = (⟨0,0,0,-1⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem nqi_qj : nqi * qj = nqk := by
  show (⟨0,-1,0,0⟩ : ℍ[ℝ]) * ⟨0,0,1,0⟩ = (⟨0,0,0,-1⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem qi_nqk : qi * nqk = qj := by
  show (⟨0,1,0,0⟩ : ℍ[ℝ]) * ⟨0,0,0,-1⟩ = (⟨0,0,1,0⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem nqi_qk : nqi * qk = qj := by
  show (⟨0,-1,0,0⟩ : ℍ[ℝ]) * ⟨0,0,0,1⟩ = (⟨0,0,1,0⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem qj_nqk : qj * nqk = nqi := by
  show (⟨0,0,1,0⟩ : ℍ[ℝ]) * ⟨0,0,0,-1⟩ = (⟨0,-1,0,0⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem nqj_qk : nqj * qk = nqi := by
  show (⟨0,0,-1,0⟩ : ℍ[ℝ]) * ⟨0,0,0,1⟩ = (⟨0,-1,0,0⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem nqk_qk : nqk * qk = 1 := by
  show (⟨0,0,0,-1⟩ : ℍ[ℝ]) * ⟨0,0,0,1⟩ = (1 : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

private theorem nqk_nqk : nqk * nqk = n1 := by
  show (⟨0,0,0,-1⟩ : ℍ[ℝ]) * ⟨0,0,0,-1⟩ = (⟨-1,0,0,0⟩ : ℍ[ℝ])
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> norm_num

/-! ### The two shapes of a `M_{1|1}(ℍ)` monomial -/

/-- The antidiagonal matrix with upper entry `a`, lower entry `b`. -/
private noncomputable def offM (a b : ℍ[ℝ]) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[ℝ] :=
  Matrix.single (Sum.inl 0) (Sum.inr 0) a
    + Matrix.single (Sum.inr 0) (Sum.inl 0) b

/-- The diagonal matrix with upper entry `a`, lower entry `b`. -/
private noncomputable def diaM (a b : ℍ[ℝ]) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[ℝ] :=
  Matrix.single (Sum.inl 0) (Sum.inl 0) a
    + Matrix.single (Sum.inr 0) (Sum.inr 0) b

private theorem diaM_one : diaM 1 1 = 1 := by
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [diaM]

private theorem offM_mul_offM (a b c d : ℍ[ℝ]) :
    offM a b * offM c d = diaM (a * d) (b * c) := by
  simp [offM, diaM, add_mul, mul_add]
  exact add_comm _ _

private theorem diaM_mul_offM (a b c d : ℍ[ℝ]) :
    diaM a b * offM c d = offM (a * c) (b * d) := by
  simp [offM, diaM, add_mul, mul_add]

/-! ### The quaternion gamma system, decomposed -/

private theorem gamma_0 : quatGamma ℝ 0 = offM 1 1 := by
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [offM] <;> rfl

private theorem gamma_1 : quatGamma ℝ 1 = offM qi nqi := by
  rw [← neg_qi]
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [offM, qi] <;> rfl

private theorem gamma_2 : quatGamma ℝ 2 = offM qj nqj := by
  rw [← neg_qj]
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [offM, qj] <;> rfl

private theorem gamma_3 : quatGamma ℝ 3 = offM qk nqk := by
  rw [← neg_qk]
  refine Matrix.ext fun r c => ?_
  have h1 : ∀ x : Fin 1, x = 0 := fun x => Subsingleton.elim x 0
  rcases r with r | r <;> rcases c with c | c <;> rw [h1 r, h1 c] <;>
    simp [offM, qk] <;> rfl


/-! ### The iterated lift into `M_{1|1}(ℍ)`, floor by floor -/

/-- The quaternion gamma lift at floor `n` (`quatHom` is `n = 4`). -/
private noncomputable def QL (n : ℕ) (hn : n ≤ 4) :
    (divisionTower (1 : ℝ) n).carrier →ₐ[ℝ]
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[ℝ] :=
  towerLift (1 : ℝ) (quatGamma ℝ) 4 (quatGamma_sq ℝ) (quatGamma_anti ℝ) n hn

/-- One tower step on the `A`-coordinate. -/
private theorem QL_left (n : ℕ) (hn : n + 1 ≤ 4)
    (a : (divisionTower (1 : ℝ) n).carrier) :
    QL (n + 1) hn
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) a 0)
      = QL n (Nat.le_of_succ_le hn) a := by
  have h : QL (n + 1) hn
      (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) a 0)
      = QL n (Nat.le_of_succ_le hn) a
        + QL n (Nat.le_of_succ_le hn) 0 * quatGamma ℝ n :=
    towerLift_succ_mk (1 : ℝ) (quatGamma ℝ) 4 (quatGamma_sq ℝ)
      (quatGamma_anti ℝ) n hn a 0
  rw [map_zero, zero_mul, add_zero] at h
  exact h

/-- One tower step on the `A·g`-coordinate. -/
private theorem QL_right (n : ℕ) (hn : n + 1 ≤ 4)
    (a : (divisionTower (1 : ℝ) n).carrier) :
    QL (n + 1) hn
        (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 a)
      = QL n (Nat.le_of_succ_le hn) a * quatGamma ℝ n := by
  have h : QL (n + 1) hn
      (OddDouble.mk (divisionTower (1 : ℝ) n).grading (1 : ℝ) 0 a)
      = QL n (Nat.le_of_succ_le hn) 0
        + QL n (Nat.le_of_succ_le hn) a * quatGamma ℝ n :=
    towerLift_succ_mk (1 : ℝ) (quatGamma ℝ) 4 (quatGamma_sq ℝ)
      (quatGamma_anti ℝ) n hn 0 a
  rw [map_zero, zero_add] at h
  exact h

/-- The concrete floor-`1` step. -/
private theorem QL1_left (a : (divisionTower (1 : ℝ) 0).carrier) :
    QL 1 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 0).grading (1 : ℝ) a 0)
      = QL 0 (by omega) a := QL_left 0 (by omega) a

private theorem QL1_right (a : (divisionTower (1 : ℝ) 0).carrier) :
    QL 1 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 0).grading (1 : ℝ) 0 a)
      = QL 0 (by omega) a * quatGamma ℝ 0 := QL_right 0 (by omega) a

private theorem QL2_left (a : (divisionTower (1 : ℝ) 1).carrier) :
    QL 2 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) a 0)
      = QL 1 (by omega) a := QL_left 1 (by omega) a

private theorem QL2_right (a : (divisionTower (1 : ℝ) 1).carrier) :
    QL 2 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0 a)
      = QL 1 (by omega) a * quatGamma ℝ 1 := QL_right 1 (by omega) a

private theorem QL3_left (a : (divisionTower (1 : ℝ) 2).carrier) :
    QL 3 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 2).grading (1 : ℝ) a 0)
      = QL 2 (by omega) a := QL_left 2 (by omega) a

private theorem QL3_right (a : (divisionTower (1 : ℝ) 2).carrier) :
    QL 3 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 2).grading (1 : ℝ) 0 a)
      = QL 2 (by omega) a * quatGamma ℝ 2 := QL_right 2 (by omega) a

private theorem QL4_left (a : (divisionTower (1 : ℝ) 3).carrier) :
    QL 4 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 3).grading (1 : ℝ) a 0)
      = QL 3 (by omega) a := QL_left 3 (by omega) a

private theorem QL4_right (a : (divisionTower (1 : ℝ) 3).carrier) :
    QL 4 (by omega) (OddDouble.mk (divisionTower (1 : ℝ) 3).grading (1 : ℝ) 0 a)
      = QL 3 (by omega) a * quatGamma ℝ 3 := QL_right 3 (by omega) a

/-! ### The tower-basis dictionary at floors `1`–`4` (generic `ε`) -/

private theorem tb1_0 (e : ℝ) :
    towerBasis e 1 0
      = OddDouble.mk (divisionTower e 0).grading e (towerBasis e 0 0) 0 :=
  towerBasis_low e 0 0

private theorem tb1_1 (e : ℝ) :
    towerBasis e 1 1
      = OddDouble.mk (divisionTower e 0).grading e 0 (towerBasis e 0 0) :=
  towerBasis_high e 0 0

private theorem tb2_0 (e : ℝ) :
    towerBasis e 2 0
      = OddDouble.mk (divisionTower e 1).grading e (towerBasis e 1 0) 0 :=
  towerBasis_low e 1 0

private theorem tb2_1 (e : ℝ) :
    towerBasis e 2 1
      = OddDouble.mk (divisionTower e 1).grading e (towerBasis e 1 1) 0 :=
  towerBasis_low e 1 1

private theorem tb2_2 (e : ℝ) :
    towerBasis e 2 2
      = OddDouble.mk (divisionTower e 1).grading e 0 (towerBasis e 1 0) :=
  towerBasis_high e 1 0

private theorem tb2_3 (e : ℝ) :
    towerBasis e 2 3
      = OddDouble.mk (divisionTower e 1).grading e 0 (towerBasis e 1 1) :=
  towerBasis_high e 1 1

private theorem tb3_0 (e : ℝ) :
    towerBasis e 3 0
      = OddDouble.mk (divisionTower e 2).grading e (towerBasis e 2 0) 0 :=
  towerBasis_low e 2 0

private theorem tb3_1 (e : ℝ) :
    towerBasis e 3 1
      = OddDouble.mk (divisionTower e 2).grading e (towerBasis e 2 1) 0 :=
  towerBasis_low e 2 1

private theorem tb3_2 (e : ℝ) :
    towerBasis e 3 2
      = OddDouble.mk (divisionTower e 2).grading e (towerBasis e 2 2) 0 :=
  towerBasis_low e 2 2

private theorem tb3_3 (e : ℝ) :
    towerBasis e 3 3
      = OddDouble.mk (divisionTower e 2).grading e (towerBasis e 2 3) 0 :=
  towerBasis_low e 2 3

private theorem tb3_4 (e : ℝ) :
    towerBasis e 3 4
      = OddDouble.mk (divisionTower e 2).grading e 0 (towerBasis e 2 0) :=
  towerBasis_high e 2 0

private theorem tb3_5 (e : ℝ) :
    towerBasis e 3 5
      = OddDouble.mk (divisionTower e 2).grading e 0 (towerBasis e 2 1) :=
  towerBasis_high e 2 1

private theorem tb3_6 (e : ℝ) :
    towerBasis e 3 6
      = OddDouble.mk (divisionTower e 2).grading e 0 (towerBasis e 2 2) :=
  towerBasis_high e 2 2

private theorem tb3_7 (e : ℝ) :
    towerBasis e 3 7
      = OddDouble.mk (divisionTower e 2).grading e 0 (towerBasis e 2 3) :=
  towerBasis_high e 2 3

private theorem tb4_0 (e : ℝ) :
    towerBasis e 4 0
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 0) 0 :=
  towerBasis_low e 3 0

private theorem tb4_1 (e : ℝ) :
    towerBasis e 4 1
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 1) 0 :=
  towerBasis_low e 3 1

private theorem tb4_2 (e : ℝ) :
    towerBasis e 4 2
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 2) 0 :=
  towerBasis_low e 3 2

private theorem tb4_3 (e : ℝ) :
    towerBasis e 4 3
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 3) 0 :=
  towerBasis_low e 3 3

private theorem tb4_4 (e : ℝ) :
    towerBasis e 4 4
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 4) 0 :=
  towerBasis_low e 3 4

private theorem tb4_5 (e : ℝ) :
    towerBasis e 4 5
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 5) 0 :=
  towerBasis_low e 3 5

private theorem tb4_6 (e : ℝ) :
    towerBasis e 4 6
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 6) 0 :=
  towerBasis_low e 3 6

private theorem tb4_7 (e : ℝ) :
    towerBasis e 4 7
      = OddDouble.mk (divisionTower e 3).grading e (towerBasis e 3 7) 0 :=
  towerBasis_low e 3 7

private theorem tb4_8 (e : ℝ) :
    towerBasis e 4 8
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 0) :=
  towerBasis_high e 3 0

private theorem tb4_9 (e : ℝ) :
    towerBasis e 4 9
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 1) :=
  towerBasis_high e 3 1

private theorem tb4_10 (e : ℝ) :
    towerBasis e 4 10
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 2) :=
  towerBasis_high e 3 2

private theorem tb4_11 (e : ℝ) :
    towerBasis e 4 11
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 3) :=
  towerBasis_high e 3 3

private theorem tb4_12 (e : ℝ) :
    towerBasis e 4 12
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 4) :=
  towerBasis_high e 3 4

private theorem tb4_13 (e : ℝ) :
    towerBasis e 4 13
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 5) :=
  towerBasis_high e 3 5

private theorem tb4_14 (e : ℝ) :
    towerBasis e 4 14
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 6) :=
  towerBasis_high e 3 6

private theorem tb4_15 (e : ℝ) :
    towerBasis e 4 15
      = OddDouble.mk (divisionTower e 3).grading e 0 (towerBasis e 3 7) :=
  towerBasis_high e 3 7


/-! ### The floor-`0` anchor -/

private theorem QL0_basis : QL 0 (by omega) (towerBasis (1 : ℝ) 0 0) = 1 := by
  have h : towerBasis (1 : ℝ) 0 0 = (1 : (divisionTower (1 : ℝ) 0).carrier) :=
    towerBasis_zero_apply (1 : ℝ) 0
  rw [h]
  exact map_one _

/-! ### The sixteen values of the quaternion certificate on the
floor-`4` tower basis -/

private theorem qv4_0 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 0) = diaM 1 1 := by
  rw [tb4_0, QL4_left, tb3_0, QL3_left, tb2_0, QL2_left, tb1_0, QL1_left, QL0_basis]
  exact diaM_one.symm

private theorem qv4_1 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 1) = offM 1 1 := by
  rw [tb4_1, QL4_left, tb3_1, QL3_left, tb2_1, QL2_left, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_2 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 2) = offM qi nqi := by
  rw [tb4_2, QL4_left, tb3_2, QL3_left, tb2_2, QL2_right, tb1_0, QL1_left, QL0_basis, one_mul, gamma_1]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_3 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 3) = diaM nqi qi := by
  rw [tb4_3, QL4_left, tb3_3, QL3_left, tb2_3, QL2_right, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_1, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_4 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 4) = offM qj nqj := by
  rw [tb4_4, QL4_left, tb3_4, QL3_right, tb2_0, QL2_left, tb1_0, QL1_left, QL0_basis, one_mul, gamma_2]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_5 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 5) = diaM nqj qj := by
  rw [tb4_5, QL4_left, tb3_5, QL3_right, tb2_1, QL2_left, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_2, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_6 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 6) = diaM nqk nqk := by
  rw [tb4_6, QL4_left, tb3_6, QL3_right, tb2_2, QL2_right, tb1_0, QL1_left, QL0_basis, one_mul, gamma_1, gamma_2, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_7 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 7) = offM nqk nqk := by
  rw [tb4_7, QL4_left, tb3_7, QL3_right, tb2_3, QL2_right, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_1, gamma_2, offM_mul_offM, diaM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_8 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 8) = offM qk nqk := by
  rw [tb4_8, QL4_right, tb3_0, QL3_left, tb2_0, QL2_left, tb1_0, QL1_left, QL0_basis, one_mul, gamma_3]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_9 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 9) = diaM nqk qk := by
  rw [tb4_9, QL4_right, tb3_1, QL3_left, tb2_1, QL2_left, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_3, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_10 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 10) = diaM qj qj := by
  rw [tb4_10, QL4_right, tb3_2, QL3_left, tb2_2, QL2_right, tb1_0, QL1_left, QL0_basis, one_mul, gamma_1, gamma_3, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_11 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 11) = offM qj qj := by
  rw [tb4_11, QL4_right, tb3_3, QL3_left, tb2_3, QL2_right, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_1, gamma_3, offM_mul_offM, diaM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_12 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 12) = diaM nqi nqi := by
  rw [tb4_12, QL4_right, tb3_4, QL3_right, tb2_0, QL2_left, tb1_0, QL1_left, QL0_basis, one_mul, gamma_2, gamma_3, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_13 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 13) = offM nqi nqi := by
  rw [tb4_13, QL4_right, tb3_5, QL3_right, tb2_1, QL2_left, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_2, gamma_3, offM_mul_offM, diaM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_14 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 14) = offM 1 n1 := by
  rw [tb4_14, QL4_right, tb3_6, QL3_right, tb2_2, QL2_right, tb1_0, QL1_left, QL0_basis, one_mul, gamma_1, gamma_2, gamma_3, offM_mul_offM, diaM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]

private theorem qv4_15 :
    QL 4 (by omega) (towerBasis (1 : ℝ) 4 15) = diaM n1 1 := by
  rw [tb4_15, QL4_right, tb3_7, QL3_right, tb2_3, QL2_right, tb1_1, QL1_right, QL0_basis, one_mul, gamma_0, gamma_1, gamma_2, gamma_3, offM_mul_offM, diaM_mul_offM, offM_mul_offM]
  all_goals congr 1 <;> try simp [qi_nqj, nqi_qj, qi_nqk, nqi_qk, qj_nqk, nqj_qk, nqk_qk, nqk_nqk]


/-! ### The target frame dictionary at `M_{1|1}(ℍ)`

`matrixSuperBasis quatBasis 1 1` is indexed by `e + 4·(s' + 2·r')`, so
the four corners occupy the index blocks `0–3` (upper-left), `4–7`
(upper-right), `8–11` (lower-left), `12–15` (lower-right), each carrying
the quaternion basis `1, i, j, k`. -/

private theorem dstQ_0 : matrixSuperBasis quatBasis 1 1 0
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 0) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dstQ_1 : matrixSuperBasis quatBasis 1 1 1
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 1) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dstQ_2 : matrixSuperBasis quatBasis 1 1 2
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 2) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 2

private theorem dstQ_3 : matrixSuperBasis quatBasis 1 1 3
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 3) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 3

private theorem dstQ_4 : matrixSuperBasis quatBasis 1 1 4
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 0) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dstQ_5 : matrixSuperBasis quatBasis 1 1 5
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 1) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

private theorem dstQ_6 : matrixSuperBasis quatBasis 1 1 6
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 2) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 2

private theorem dstQ_7 : matrixSuperBasis quatBasis 1 1 7
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 3) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 3

private theorem dstQ_8 : matrixSuperBasis quatBasis 1 1 8
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 0) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dstQ_9 : matrixSuperBasis quatBasis 1 1 9
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 1) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dstQ_10 : matrixSuperBasis quatBasis 1 1 10
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 2) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 2

private theorem dstQ_11 : matrixSuperBasis quatBasis 1 1 11
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (quatBasis 3) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 3

private theorem dstQ_12 : matrixSuperBasis quatBasis 1 1 12
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 0) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dstQ_13 : matrixSuperBasis quatBasis 1 1 13
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 1) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

private theorem dstQ_14 : matrixSuperBasis quatBasis 1 1 14
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 2) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 2

private theorem dstQ_15 : matrixSuperBasis quatBasis 1 1 15
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (quatBasis 3) :=
  matrixSuperBasis_apply_pair quatBasis 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 3

/-! ### Scalar multiples in the matrix frame

The `SMul` of `(quatEvenSuper.matrixSuper 1 1).carrier` and the `SMul`
of the bare `Matrix … ℍ[ℝ]` are definitionally equal but *not*
instance-transparently so; `show` crosses the gap once, here. -/

private theorem smul_dstQ (t : ℝ) {r c : Fin 1 ⊕ Fin 1}
    {v : quatEvenSuper.carrier} {M : (quatEvenSuper.matrixSuper 1 1).carrier}
    (hM : M = Matrix.single r c v) :
    t • M = Matrix.single r c (t • v) := by
  subst hM
  show (t • (Matrix.single r c v :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) quatEvenSuper.carrier))
    = Matrix.single r c (t • v)
  refine Matrix.ext fun x y => ?_
  rw [Matrix.smul_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

/-! ### Signed frame vectors of the quaternion factor -/

private theorem sb_p_0 : (1 : ℝ) • quatBasis 0 = (1 : ℍ[ℝ]) := by
  rw [quatBasis_0]; exact one_smul ℝ _

private theorem sb_p_1 : (1 : ℝ) • quatBasis 1 = qi := by
  rw [quatBasis_1]; exact one_smul ℝ _

private theorem sb_p_2 : (1 : ℝ) • quatBasis 2 = qj := by
  rw [quatBasis_2]; exact one_smul ℝ _

private theorem sb_p_3 : (1 : ℝ) • quatBasis 3 = qk := by
  rw [quatBasis_3]; exact one_smul ℝ _

private theorem sb_m_0 : (-1 : ℝ) • quatBasis 0 = n1 := by
  rw [quatBasis_0]
  show (-1 : ℝ) • (1 : ℍ[ℝ]) = (⟨-1, 0, 0, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem sb_m_1 : (-1 : ℝ) • quatBasis 1 = nqi := by
  rw [quatBasis_1]
  show (-1 : ℝ) • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = (⟨0, -1, 0, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem sb_m_2 : (-1 : ℝ) • quatBasis 2 = nqj := by
  rw [quatBasis_2]
  show (-1 : ℝ) • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = (⟨0, 0, -1, 0⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

private theorem sb_m_3 : (-1 : ℝ) • quatBasis 3 = nqk := by
  rw [quatBasis_3]
  show (-1 : ℝ) • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) = (⟨0, 0, 0, -1⟩ : ℍ[ℝ])
  apply QuaternionAlgebra.ext <;> norm_num

/-! ### The certificate values in target-frame coordinates -/

private theorem qc4_0 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  rw [smul_dstQ (1 : ℝ) dstQ_0, smul_dstQ (1 : ℝ) dstQ_12, sb_p_0]
  exact qv4_0

private theorem qc4_1 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 1)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  rw [smul_dstQ (1 : ℝ) dstQ_4, smul_dstQ (1 : ℝ) dstQ_8, sb_p_0]
  exact qv4_1

private theorem qc4_2 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 2)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  rw [smul_dstQ (1 : ℝ) dstQ_5, smul_dstQ (-1 : ℝ) dstQ_9, sb_p_1, sb_m_1]
  exact qv4_2

private theorem qc4_3 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 3)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_1, smul_dstQ (1 : ℝ) dstQ_13, sb_m_1, sb_p_1]
  exact qv4_3

private theorem qc4_4 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 4)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  rw [smul_dstQ (1 : ℝ) dstQ_6, smul_dstQ (-1 : ℝ) dstQ_10, sb_p_2, sb_m_2]
  exact qv4_4

private theorem qc4_5 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 5)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_2, smul_dstQ (1 : ℝ) dstQ_14, sb_m_2, sb_p_2]
  exact qv4_5

private theorem qc4_6 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 6)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_3, smul_dstQ (-1 : ℝ) dstQ_15, sb_m_3]
  exact qv4_6

private theorem qc4_7 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 7)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_7, smul_dstQ (-1 : ℝ) dstQ_11, sb_m_3]
  exact qv4_7

private theorem qc4_8 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 8)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  rw [smul_dstQ (1 : ℝ) dstQ_7, smul_dstQ (-1 : ℝ) dstQ_11, sb_p_3, sb_m_3]
  exact qv4_8

private theorem qc4_9 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 9)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_3, smul_dstQ (1 : ℝ) dstQ_15, sb_m_3, sb_p_3]
  exact qv4_9

private theorem qc4_10 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 10)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  rw [smul_dstQ (1 : ℝ) dstQ_2, smul_dstQ (1 : ℝ) dstQ_14, sb_p_2]
  exact qv4_10

private theorem qc4_11 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 11)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  rw [smul_dstQ (1 : ℝ) dstQ_6, smul_dstQ (1 : ℝ) dstQ_10, sb_p_2]
  exact qv4_11

private theorem qc4_12 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 12)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_1, smul_dstQ (-1 : ℝ) dstQ_13, sb_m_1]
  exact qv4_12

private theorem qc4_13 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 13)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_5, smul_dstQ (-1 : ℝ) dstQ_9, sb_m_1]
  exact qv4_13

private theorem qc4_14 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 14)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  rw [smul_dstQ (1 : ℝ) dstQ_4, smul_dstQ (-1 : ℝ) dstQ_8, sb_p_0, sb_m_0]
  exact qv4_14

private theorem qc4_15 :
    (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  rw [smul_dstQ (-1 : ℝ) dstQ_0, smul_dstQ (1 : ℝ) dstQ_12, sb_m_0, sb_p_0]
  exact qv4_15


/-! ### Shared graded-tensor application lemmas (re-derived; the copies
in `RealFuseSpecPilot` / `RealFuseSpecTower` are `private` there) -/

private theorem superRefl_apply (P : SuperAlgebra ℝ) (x : P.carrier) :
    (SuperAlgEquiv.refl P).toAlgEquiv x = x := rfl

private theorem gtensorUnitorLeft_one_tmul (P : SuperAlgebra ℝ)
    {jp : ZMod 2} {v : P.carrier} (hv : v ∈ P.grading jp) :
    (gtensorUnitorLeft P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v) = v := by
  have hcomm := gtensorComm_tmul_of_mem (SuperAlgebra.base ℝ) P
    (show (1 : ℝ) ∈ (SuperAlgebra.base ℝ).grading 0 from
      mem_evenGrading_zero ℝ ℝ 1) hv
  rw [mul_zero, uzpow_zero, one_smul] at hcomm
  have hru := gunitorRightHom_tmul P.grading v (1 : ℝ)
  rw [map_one, mul_one] at hru
  show gunitorRightHom P.grading
      ((gtensorComm (SuperAlgebra.base ℝ) P).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := P.grading) ℝ (1 : ℝ) v)) = v
  rw [hcomm]
  exact hru

private theorem equivGradedTensor_tmul_one {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t 1)
      = OddDouble.mk 𝒜 ε t 0 := by
  rw [OddDouble.equivGradedTensor_tmul, map_one, mul_one, OddDouble.inl_apply]

private theorem equivGradedTensor_tmul_e {A : Type*} [Ring A]
    [Algebra ℝ A] (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜] (ε : ℝ)
    (t : A) :
    OddDouble.equivGradedTensor 𝒜 ε
        (GradedTensorProduct.tmul (𝒜 := 𝒜) (ℬ := AdjoinOdd.grading ε) ℝ t
          (AdjoinOdd.e ε))
      = OddDouble.mk 𝒜 ε 0 t := by
  rw [OddDouble.equivGradedTensor_tmul, OddDouble.inl_apply, OddDouble.inr_e]
  refine OddDouble.ext 𝒜 ε ?_ ?_ <;> simp [parityMap_one]

private theorem adjoinOddEquivTowerOne_e (ε : ℝ) :
    (adjoinOddEquivTowerOne ε).toAlgEquiv (AdjoinOdd.e ε)
      = OddDouble.gen (SuperAlgebra.base ℝ).grading ε := by
  have hin : ((gtensorUnitorLeft (SuperAlgebra.adjoinOdd ε)).toAlgEquiv).symm
        (AdjoinOdd.e ε)
      = GradedTensorProduct.tmul (𝒜 := (SuperAlgebra.base ℝ).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ (1 : ℝ)
          (AdjoinOdd.e ε) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (gtensorUnitorLeft_one_tmul (SuperAlgebra.adjoinOdd ε)
      (AdjoinOdd.e_mem_grading_one ε)).symm
  show OddDouble.equivGradedTensor (SuperAlgebra.base ℝ).grading ε
      (((gtensorUnitorLeft (SuperAlgebra.adjoinOdd ε)).toAlgEquiv).symm
        (AdjoinOdd.e ε))
      = OddDouble.gen (SuperAlgebra.base ℝ).grading ε
  rw [hin]
  exact equivGradedTensor_tmul_e (SuperAlgebra.base ℝ).grading ε (1 : ℝ)

private theorem towerSuccEquiv_symm_tmul_one (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε n).grading ε t 0 := by
  have hin : (OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
        (OddDouble.mk (divisionTower ε n).grading ε t 0)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ t
          (1 : (SuperAlgebra.adjoinOdd ε).carrier) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (equivGradedTensor_tmul_one (divisionTower ε n).grading ε t).symm
  have hone : (adjoinOddEquivTowerOne ε).toAlgEquiv
      (1 : (SuperAlgebra.adjoinOdd ε).carrier) = 1 := map_one _
  have happ := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε n)) (adjoinOddEquivTowerOne ε)
    t (1 : (SuperAlgebra.adjoinOdd ε).carrier)
  rw [superRefl_apply, hone] at happ
  show ((towerSuccEquiv ε n).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε n).grading ε t 0
  rw [AlgEquiv.symm_apply_eq]
  show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (1 : (divisionTower ε 1).carrier)
      = ((SuperAlgEquiv.refl (divisionTower ε n)).gtensorCongr
          (adjoinOddEquivTowerOne ε)).toAlgEquiv
        ((OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
          (OddDouble.mk (divisionTower ε n).grading ε t 0))
  rw [hin, happ]

private theorem towerSuccEquiv_symm_tmul_gen (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε n).grading ε 0 t := by
  have hin : (OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
        (OddDouble.mk (divisionTower ε n).grading ε 0 t)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (SuperAlgebra.adjoinOdd ε).grading) ℝ t
          (AdjoinOdd.e ε) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (equivGradedTensor_tmul_e (divisionTower ε n).grading ε t).symm
  have happ := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε n)) (adjoinOddEquivTowerOne ε)
    t (AdjoinOdd.e ε)
  rw [superRefl_apply, adjoinOddEquivTowerOne_e] at happ
  show ((towerSuccEquiv ε n).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε n).grading ε 0 t
  rw [AlgEquiv.symm_apply_eq]
  show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ t
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
      = ((SuperAlgEquiv.refl (divisionTower ε n)).gtensorCongr
          (adjoinOddEquivTowerOne ε)).toAlgEquiv
        ((OddDouble.equivGradedTensor (divisionTower ε n).grading ε).symm
          (OddDouble.mk (divisionTower ε n).grading ε 0 t))
  rw [hin, happ]

private theorem towerSuccEquiv_one (ε : ℝ) (n : ℕ) :
    (towerSuccEquiv ε n).toAlgEquiv (1 : (divisionTower ε (n + 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (1 : (divisionTower ε n).carrier)
          (1 : (divisionTower ε 1).carrier) := by
  rw [show GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ
        (1 : (divisionTower ε n).carrier)
        (1 : (divisionTower ε 1).carrier)
      = (1 : ((divisionTower ε n).gtensor (divisionTower ε 1)).carrier) from
    gtensor_one_one (divisionTower ε n) (divisionTower ε 1)]
  exact map_one _

private theorem towerSuccEquiv_mk_left (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε t 0)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (1 : (divisionTower ε 1).carrier) := by
  have h := towerSuccEquiv_symm_tmul_one ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

private theorem towerSuccEquiv_mk_right (ε : ℝ) (n : ℕ)
    (t : (divisionTower ε n).carrier) :
    (towerSuccEquiv ε n).toAlgEquiv
        (OddDouble.mk (divisionTower ε n).grading ε 0 t)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε n).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ t
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := towerSuccEquiv_symm_tmul_gen ε n t
  exact ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε n).toAlgEquiv)).mp h).symm

private theorem towerSuccEquiv_zero_one (ε : ℝ) :
    (towerSuccEquiv ε 0).toAlgEquiv (1 : (divisionTower ε (0 + 1)).carrier)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
          (1 : (divisionTower ε 1).carrier) :=
  towerSuccEquiv_one ε 0

private theorem gtensorAssoc_symm_tmul (P Q R : SuperAlgebra ℝ)
    (x : P.carrier) (y : Q.carrier) (z : R.carrier) :
    (gtensorAssoc P Q R).symm.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := P.grading)
          (ℬ := (Q.gtensor R).grading) ℝ x
          (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := R.grading) ℝ y z))
      = GradedTensorProduct.tmul (𝒜 := (P.gtensor Q).grading)
          (ℬ := R.grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y)
          z := by
  show ((gtensorAssoc P Q R).toAlgEquiv).symm
      (GradedTensorProduct.tmul (𝒜 := P.grading)
        (ℬ := (Q.gtensor R).grading) ℝ x
        (GradedTensorProduct.tmul (𝒜 := Q.grading) (ℬ := R.grading) ℝ y z))
      = GradedTensorProduct.tmul (𝒜 := (P.gtensor Q).grading)
          (ℬ := R.grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := P.grading) (ℬ := Q.grading) ℝ x y)
          z
  rw [AlgEquiv.symm_apply_eq]
  exact (gtensorAssoc_tmul P Q R x y z).symm

private theorem towerFuse_a_zero_tmul (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 0).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ)) = u := by
  have h := gunitorRightHom_tmul (divisionTower ε a).grading u (1 : ℝ)
  rw [map_one, mul_one] at h
  exact h

/-! ### `towerFuse ε a 1` on the two right-frame vectors -/

private theorem towerFuse_a_one_tmul_one (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ u
          (1 : (divisionTower ε 1).carrier))
      = OddDouble.mk (divisionTower ε a).grading ε u 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 0)
    u (1 : (divisionTower ε (0 + 1)).carrier)
  rw [superRefl_apply, towerSuccEquiv_zero_one] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 0)
    (divisionTower ε 1) u (1 : ℝ) (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (a + 0) u
  have e1 : (towerFuse ε a 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ u
        (1 : (divisionTower ε 1).carrier))
      = (towerSuccEquiv ε (a + 0)).symm.toAlgEquiv
          (((towerFuse ε a 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ u
                  (1 : (divisionTower ε (0 + 1)).carrier))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

private theorem towerFuse_a_one_tmul_gen (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ u
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = OddDouble.mk (divisionTower ε a).grading ε 0 u := by
  have h0 := towerSuccEquiv_symm_tmul_gen ε 0 (1 : ℝ)
  have hg : (towerSuccEquiv ε 0).toAlgEquiv
      (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 0).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (1 : ℝ)
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) :=
    ((AlgEquiv.symm_apply_eq ((towerSuccEquiv ε 0).toAlgEquiv)).mp h0).symm
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 0)
    u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, hg] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 0)
    (divisionTower ε 1) u (1 : ℝ)
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 0)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 0).grading) ℝ u (1 : ℝ))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_a_zero_tmul] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (a + 0) u
  have e1 : (towerFuse ε a 1).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ u
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
      = (towerSuccEquiv ε (a + 0)).symm.toAlgEquiv
          (((towerFuse ε a 0).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 0)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 0)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (0 + 1)).grading) ℝ u
                  (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1



/-! ### The tower-basis dictionary at floor `1` -/

private theorem towerBasis_one_zero (ε : ℝ) :
    towerBasis ε 1 0 = (1 : (divisionTower ε 1).carrier) := by
  have h := towerBasis_low ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

private theorem towerBasis_one_one (ε : ℝ) :
    towerBasis ε 1 1 = OddDouble.gen (SuperAlgebra.base ℝ).grading ε := by
  have h := towerBasis_high ε 0 0
  rw [towerBasis_zero_apply] at h
  exact h

/-! ### The `(5,7)` branch: `Cl_{3,0} ᵍ⊗ Cl_{1,0} ≅ D₁^{⊗̂4} ≅ M_{1|1}(ℍ)` -/

private theorem col57_0 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 0)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 0 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 0)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_0]
  exact qc4_0

private theorem col57_1 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 1)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 0)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 0 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 0)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_8]
  exact qc4_8

private theorem col57_2 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 2)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 1)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 1 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 1)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_1]
  exact qc4_1

private theorem col57_3 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 3)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 1)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 1 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 1)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_9]
  exact qc4_9

private theorem col57_4 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 4)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 2)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 2 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 2)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_2]
  exact qc4_2

private theorem col57_5 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 5)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 2)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 2 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 2)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_10]
  exact qc4_10

private theorem col57_6 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 6)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 3)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 3 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 3)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_3]
  exact qc4_3

private theorem col57_7 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 7)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 3)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 3 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 3)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_11]
  exact qc4_11

private theorem col57_8 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 8)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 4)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 4 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 4)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_4]
  exact qc4_4

private theorem col57_9 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 9)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 4)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 4 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 4)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_12]
  exact qc4_12

private theorem col57_10 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 10)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 5)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 5 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 5)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_5]
  exact qc4_5

private theorem col57_11 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 11)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 5)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 5 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 5)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_13]
  exact qc4_13

private theorem col57_12 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 12)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 6)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 6 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 6)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_6]
  exact qc4_6

private theorem col57_13 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 13)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 6)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 6 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 6)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_14]
  exact qc4_14

private theorem col57_14 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 14)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 7)
          (towerBasis 1 1 0) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 7 0
  rw [towerBasis_one_zero] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 7)
          _))
    = _
  rw [towerFuse_a_one_tmul_one, ← tb4_7]
  exact qc4_7

private theorem col57_15 :
    ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 1)
          (towerBasis 1 3) (towerBasis 1 1) 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 3)
        (B := divisionTower (1 : ℝ) 1)
        (towerBasis 1 3) (towerBasis 1 1) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 7)
          (towerBasis 1 1 1) :=
    gtensorBasis_apply_pair (towerBasis 1 3) (towerBasis 1 1) 7 1
  rw [towerBasis_one_one] at hsrc
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 3 1).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (towerBasis 1 3 7)
          _))
    = _
  rw [towerFuse_a_one_tmul_gen, ← tb4_15]
  exact qc4_15

set_option maxRecDepth 40000 in
/-- **Deliverable `(5,7)`**: `Cl_{3,0} ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℍ)`, the
`ε = +1` wrap through the Bott floor: the sign-free tower permutation
`(i, j) ↦ i + 8·j`, followed by the quaternion gamma monomials of the
floor-`4` certificate. -/
theorem realFuseMatrix_5_7 :
    realFuseMatrix 5 7
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  have hcol : ∀ c : Fin 16,
      ((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
          (gtensorBasis (A := divisionTower (1 : ℝ) 3)
            (B := divisionTower (1 : ℝ) 1)
            (towerBasis 1 3) (towerBasis 1 1) c)
        = (![1, 1, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![0, 7, 4, 3, 5, 2, 1, 6, 6, 1, 2, 5, 3, 4, 7, 0] c)
          + (![1, -1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, -1, 1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![12, 11, 8, 15, 9, 14, 13, 10, 10, 13, 14, 9, 15, 8, 11, 12] c) := by
    intro c
    fin_cases c
    · exact col57_0
    · exact col57_1
    · exact col57_2
    · exact col57_3
    · exact col57_4
    · exact col57_5
    · exact col57_6
    · exact col57_7
    · exact col57_8
    · exact col57_9
    · exact col57_10
    · exact col57_11
    · exact col57_12
    · exact col57_13
    · exact col57_14
    · exact col57_15
  have key : ∀ i j : Fin 16,
      ((matrixSuperBasis quatBasis 1 1).repr
          (((towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)).toAlgEquiv
            (gtensorBasis (A := divisionTower (1 : ℝ) 3)
              (B := divisionTower (1 : ℝ) 1)
              (towerBasis 1 3) (towerBasis 1 1) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
             0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
             0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    rw [hcol j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j

/-! ### `towerFuse ε a 2` on the four right-frame vectors -/

private theorem towerFuse_a_two_tmul_one (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (1 : (divisionTower ε 2).carrier))
      = OddDouble.mk (divisionTower ε (a + 1)).grading ε
          (OddDouble.mk (divisionTower ε a).grading ε u 0) 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 1)
    u (1 : (divisionTower ε (1 + 1)).carrier)
  rw [superRefl_apply, towerSuccEquiv_one] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 1)
    (divisionTower ε 1) u (1 : (divisionTower ε 1).carrier) (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u (1 : (divisionTower ε 1).carrier))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_a_one_tmul_one] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (a + 1) (OddDouble.mk (divisionTower ε a).grading ε u 0)
  have e1 : (towerFuse ε a 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (1 : (divisionTower ε 2).carrier))
      = (towerSuccEquiv ε (a + 1)).symm.toAlgEquiv
          (((towerFuse ε a 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (1 : (divisionTower ε (1 + 1)).carrier))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

private theorem towerFuse_a_two_tmul_g1 (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))
      = OddDouble.mk (divisionTower ε (a + 1)).grading ε
          (OddDouble.mk (divisionTower ε a).grading ε 0 u) 0 := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0)
  rw [superRefl_apply, towerSuccEquiv_mk_left] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 1)
    (divisionTower ε 1) u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) (1 : (divisionTower ε 1).carrier)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
    (1 : (divisionTower ε 1).carrier)
  rw [superRefl_apply, towerFuse_a_one_tmul_gen] at h3
  have h4 := towerSuccEquiv_symm_tmul_one ε (a + 1) (OddDouble.mk (divisionTower ε a).grading ε 0 u)
  have e1 : (towerFuse ε a 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))
      = (towerSuccEquiv ε (a + 1)).symm.toAlgEquiv
          (((towerFuse ε a 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

private theorem towerFuse_a_two_tmul_g2 (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier)))
      = OddDouble.mk (divisionTower ε (a + 1)).grading ε 0
          (OddDouble.mk (divisionTower ε a).grading ε u 0) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε 0
        (1 : (divisionTower ε 1).carrier))
  rw [superRefl_apply, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 1)
    (divisionTower ε 1) u (1 : (divisionTower ε 1).carrier) (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u (1 : (divisionTower ε 1).carrier))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_a_one_tmul_one] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (a + 1) (OddDouble.mk (divisionTower ε a).grading ε u 0)
  have e1 : (towerFuse ε a 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε 0
            (1 : (divisionTower ε 1).carrier)))
      = (towerSuccEquiv ε (a + 1)).symm.toAlgEquiv
          (((towerFuse ε a 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε 0
        (1 : (divisionTower ε 1).carrier)))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

private theorem towerFuse_a_two_tmul_g1g2 (ε : ℝ) (a : ℕ)
    (u : (divisionTower ε a).carrier) :
    (towerFuse ε a 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε 2).grading) ℝ u
          (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = OddDouble.mk (divisionTower ε (a + 1)).grading ε 0
          (OddDouble.mk (divisionTower ε a).grading ε 0 u) := by
  have h1 := SuperAlgEquiv.gtensorCongr_tmul
    (SuperAlgEquiv.refl (divisionTower ε a)) (towerSuccEquiv ε 1)
    u (OddDouble.mk (divisionTower ε 1).grading ε 0
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
  rw [superRefl_apply, towerSuccEquiv_mk_right] at h1
  have h2 := gtensorAssoc_symm_tmul (divisionTower ε a) (divisionTower ε 1)
    (divisionTower ε 1) u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  have h3 := SuperAlgEquiv.gtensorCongr_tmul (towerFuse ε a 1)
    (SuperAlgEquiv.refl (divisionTower ε 1))
    (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
      (ℬ := (divisionTower ε 1).grading) ℝ u (OddDouble.gen (SuperAlgebra.base ℝ).grading ε))
    (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)
  rw [superRefl_apply, towerFuse_a_one_tmul_gen] at h3
  have h4 := towerSuccEquiv_symm_tmul_gen ε (a + 1) (OddDouble.mk (divisionTower ε a).grading ε 0 u)
  have e1 : (towerFuse ε a 2).toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
        (ℬ := (divisionTower ε 2).grading) ℝ u
        (OddDouble.mk (divisionTower ε 1).grading ε 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))
      = (towerSuccEquiv ε (a + 1)).symm.toAlgEquiv
          (((towerFuse ε a 1).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
            ((gtensorAssoc (divisionTower ε a) (divisionTower ε 1)
                (divisionTower ε 1)).symm.toAlgEquiv
              (((SuperAlgEquiv.refl (divisionTower ε a)).gtensorCongr
                  (towerSuccEquiv ε 1)).toAlgEquiv
                (GradedTensorProduct.tmul
                  (𝒜 := (divisionTower ε a).grading)
                  (ℬ := (divisionTower ε (1 + 1)).grading) ℝ u
                  (OddDouble.mk (divisionTower ε 1).grading ε 0
        (OddDouble.gen (SuperAlgebra.base ℝ).grading ε)))))) := rfl
  rw [h1, h2, h3, h4] at e1
  exact e1

/-! ### The tower-basis dictionary at floor `2` -/

private theorem towerBasis_two_zero (ε : ℝ) :
    towerBasis ε 2 0 = (1 : (divisionTower ε 2).carrier) := by
  have h := tb2_0 ε
  rw [towerBasis_one_zero] at h
  exact h

private theorem towerBasis_two_one (ε : ℝ) :
    towerBasis ε 2 1
      = OddDouble.mk (divisionTower ε 1).grading ε
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) 0 := by
  have h := tb2_1 ε
  rw [towerBasis_one_one] at h
  exact h

private theorem towerBasis_two_two (ε : ℝ) :
    towerBasis ε 2 2
      = OddDouble.mk (divisionTower ε 1).grading ε 0
          (1 : (divisionTower ε 1).carrier) := by
  have h := tb2_2 ε
  rw [towerBasis_one_zero] at h
  exact h

private theorem towerBasis_two_three (ε : ℝ) :
    towerBasis ε 2 3
      = OddDouble.mk (divisionTower ε 1).grading ε 0
          (OddDouble.gen (SuperAlgebra.base ℝ).grading ε) := by
  have h := tb2_3 ε
  rw [towerBasis_one_one] at h
  exact h

/-! ### Floor `4` in terms of floor `2` -/

private theorem tb4c_0 (ε : ℝ) :
    towerBasis ε 4 0
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 0) 0) 0 := by
  rw [tb4_0, tb3_0]

private theorem tb4c_1 (ε : ℝ) :
    towerBasis ε 4 1
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 1) 0) 0 := by
  rw [tb4_1, tb3_1]

private theorem tb4c_2 (ε : ℝ) :
    towerBasis ε 4 2
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 2) 0) 0 := by
  rw [tb4_2, tb3_2]

private theorem tb4c_3 (ε : ℝ) :
    towerBasis ε 4 3
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 3) 0) 0 := by
  rw [tb4_3, tb3_3]

private theorem tb4c_4 (ε : ℝ) :
    towerBasis ε 4 4
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 0)) 0 := by
  rw [tb4_4, tb3_4]

private theorem tb4c_5 (ε : ℝ) :
    towerBasis ε 4 5
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 1)) 0 := by
  rw [tb4_5, tb3_5]

private theorem tb4c_6 (ε : ℝ) :
    towerBasis ε 4 6
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 2)) 0 := by
  rw [tb4_6, tb3_6]

private theorem tb4c_7 (ε : ℝ) :
    towerBasis ε 4 7
      = OddDouble.mk (divisionTower ε 3).grading ε
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 3)) 0 := by
  rw [tb4_7, tb3_7]

private theorem tb4c_8 (ε : ℝ) :
    towerBasis ε 4 8
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 0) 0) := by
  rw [tb4_8, tb3_0]

private theorem tb4c_9 (ε : ℝ) :
    towerBasis ε 4 9
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 1) 0) := by
  rw [tb4_9, tb3_1]

private theorem tb4c_10 (ε : ℝ) :
    towerBasis ε 4 10
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 2) 0) := by
  rw [tb4_10, tb3_2]

private theorem tb4c_11 (ε : ℝ) :
    towerBasis ε 4 11
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε (towerBasis ε 2 3) 0) := by
  rw [tb4_11, tb3_3]

private theorem tb4c_12 (ε : ℝ) :
    towerBasis ε 4 12
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 0)) := by
  rw [tb4_12, tb3_4]

private theorem tb4c_13 (ε : ℝ) :
    towerBasis ε 4 13
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 1)) := by
  rw [tb4_13, tb3_5]

private theorem tb4c_14 (ε : ℝ) :
    towerBasis ε 4 14
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 2)) := by
  rw [tb4_14, tb3_6]

private theorem tb4c_15 (ε : ℝ) :
    towerBasis ε 4 15
      = OddDouble.mk (divisionTower ε 3).grading ε 0
          (OddDouble.mk (divisionTower ε 2).grading ε 0 (towerBasis ε 2 3)) := by
  rw [tb4_15, tb3_7]


/-! ### The `(6,6)` branch: `Cl_{2,0} ᵍ⊗ Cl_{2,0} ≅ D₁^{⊗̂4} ≅ M_{1|1}(ℍ)` -/

private theorem col66_0 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 0)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 0
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          (1 : (divisionTower (1 : ℝ) 2).carrier) := by
    rw [← towerBasis_two_zero]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 0 0
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          _))
    = _
  rw [towerFuse_a_two_tmul_one, ← tb4c_0]
  exact qc4_0

private theorem col66_1 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 1)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 1
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ)
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)) 0) := by
    rw [← towerBasis_two_one]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 0 1
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1, ← tb4c_4]
  exact qc4_4

private theorem col66_2 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 2)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 2
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (1 : (divisionTower (1 : ℝ) 1).carrier)) := by
    rw [← towerBasis_two_two]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 0 2
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          _))
    = _
  rw [towerFuse_a_two_tmul_g2, ← tb4c_8]
  exact qc4_8

private theorem col66_3 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 3)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 3
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))) := by
    rw [← towerBasis_two_three]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 0 3
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 0)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1g2, ← tb4c_12]
  exact qc4_12

private theorem col66_4 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 4)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 4
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          (1 : (divisionTower (1 : ℝ) 2).carrier) := by
    rw [← towerBasis_two_zero]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 1 0
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          _))
    = _
  rw [towerFuse_a_two_tmul_one, ← tb4c_1]
  exact qc4_1

private theorem col66_5 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 5)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 5
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ)
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)) 0) := by
    rw [← towerBasis_two_one]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 1 1
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1, ← tb4c_5]
  exact qc4_5

private theorem col66_6 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 6)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 6
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (1 : (divisionTower (1 : ℝ) 1).carrier)) := by
    rw [← towerBasis_two_two]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 1 2
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          _))
    = _
  rw [towerFuse_a_two_tmul_g2, ← tb4c_9]
  exact qc4_9

private theorem col66_7 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 7)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 7
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))) := by
    rw [← towerBasis_two_three]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 1 3
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 1)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1g2, ← tb4c_13]
  exact qc4_13

private theorem col66_8 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 8)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 5
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 9 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 8
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          (1 : (divisionTower (1 : ℝ) 2).carrier) := by
    rw [← towerBasis_two_zero]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 2 0
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          _))
    = _
  rw [towerFuse_a_two_tmul_one, ← tb4c_2]
  exact qc4_2

private theorem col66_9 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 9)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 3
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 15 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 9
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ)
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)) 0) := by
    rw [← towerBasis_two_one]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 2 1
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1, ← tb4c_6]
  exact qc4_6

private theorem col66_10 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 10)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 2
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 14 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 10
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (1 : (divisionTower (1 : ℝ) 1).carrier)) := by
    rw [← towerBasis_two_two]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 2 2
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          _))
    = _
  rw [towerFuse_a_two_tmul_g2, ← tb4c_10]
  exact qc4_10

private theorem col66_11 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 11)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 4
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 8 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 11
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))) := by
    rw [← towerBasis_two_three]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 2 3
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 2)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1g2, ← tb4c_14]
  exact qc4_14

private theorem col66_12 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 12)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 1
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 13 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 12
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          (1 : (divisionTower (1 : ℝ) 2).carrier) := by
    rw [← towerBasis_two_zero]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 3 0
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          _))
    = _
  rw [towerFuse_a_two_tmul_one, ← tb4c_3]
  exact qc4_3

private theorem col66_13 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 13)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 7
        + (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 11 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 13
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ)
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ)) 0) := by
    rw [← towerBasis_two_one]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 3 1
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1, ← tb4c_7]
  exact qc4_7

private theorem col66_14 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 14)
      = (1 : ℝ) • matrixSuperBasis quatBasis 1 1 6
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 10 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 14
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (1 : (divisionTower (1 : ℝ) 1).carrier)) := by
    rw [← towerBasis_two_two]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 3 2
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          _))
    = _
  rw [towerFuse_a_two_tmul_g2, ← tb4c_11]
  exact qc4_11

private theorem col66_15 :
    ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 2)
          (B := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) (towerBasis 1 2) 15)
      = (-1 : ℝ) • matrixSuperBasis quatBasis 1 1 0
        + (1 : ℝ) • matrixSuperBasis quatBasis 1 1 12 := by
  have hsrc : gtensorBasis (A := divisionTower (1 : ℝ) 2)
        (B := divisionTower (1 : ℝ) 2)
        (towerBasis 1 2) (towerBasis 1 2) 15
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          (OddDouble.mk (divisionTower (1 : ℝ) 1).grading (1 : ℝ) 0
            (OddDouble.gen (SuperAlgebra.base ℝ).grading (1 : ℝ))) := by
    rw [← towerBasis_two_three]
    exact gtensorBasis_apply_pair (towerBasis 1 2) (towerBasis 1 2) 3 3
  rw [hsrc]
  show (towerFourQuatSuper ℝ).toAlgEquiv
      ((towerFuse (1 : ℝ) 2 2).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 2).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (towerBasis 1 2 3)
          _))
    = _
  rw [towerFuse_a_two_tmul_g1g2, ← tb4c_15]
  exact qc4_15

set_option maxRecDepth 40000 in
/-- **Deliverable `(6,6)`**: `Cl_{2,0} ᵍ⊗ Cl_{2,0} ≅ M_{1|1}(ℍ)`, the
second `ε = +1` wrap through the Bott floor: the sign-free tower
permutation `(i, j) ↦ i + 4·j`, followed by the quaternion gamma
monomials. -/
theorem realFuseMatrix_6_6 :
    realFuseMatrix 6 6
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
           0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
           0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
           0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
           0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
           0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by
  have hcol : ∀ c : Fin 16,
      ((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
          (gtensorBasis (A := divisionTower (1 : ℝ) 2)
            (B := divisionTower (1 : ℝ) 2)
            (towerBasis 1 2) (towerBasis 1 2) c)
        = (![1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![0, 6, 7, 1, 4, 2, 3, 5, 5, 3, 2, 4, 1, 7, 6, 0] c)
          + (![1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1] c : ℝ)
              • matrixSuperBasis quatBasis 1 1 (![12, 10, 11, 13, 8, 14, 15, 9, 9, 15, 14, 8, 13, 11, 10, 12] c) := by
    intro c
    fin_cases c
    · exact col66_0
    · exact col66_1
    · exact col66_2
    · exact col66_3
    · exact col66_4
    · exact col66_5
    · exact col66_6
    · exact col66_7
    · exact col66_8
    · exact col66_9
    · exact col66_10
    · exact col66_11
    · exact col66_12
    · exact col66_13
    · exact col66_14
    · exact col66_15
  have key : ∀ i j : Fin 16,
      ((matrixSuperBasis quatBasis 1 1).repr
          (((towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)).toAlgEquiv
            (gtensorBasis (A := divisionTower (1 : ℝ) 2)
              (B := divisionTower (1 : ℝ) 2)
              (towerBasis 1 2) (towerBasis 1 2) j))) i
        = (!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
             0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
             0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
             0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0;
             0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
             0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
             1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
             0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
             0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
             0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0] : Matrix (Fin 16) (Fin 16) ℝ) i j := by
    intro i j
    rw [hcol j, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, Basis.repr_self_apply,
      Basis.repr_self_apply, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  refine Matrix.ext fun i j => ?_
  rw [realFuseMatrix_apply]
  exact key i j


end Superfusion
