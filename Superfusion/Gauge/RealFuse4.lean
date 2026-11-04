/-
Superfusion / Gauge / RealFuse4

Milestone M9-4b-ii-4: **the remaining twenty real fusion pairs**
(toward `64` total; `44` landed in `RealFuse1`–`RealFuse3`).  Every pair
here is built by **reduction through already-landed pieces** — no new
generator/gamma-matrix construction, with one exception noted below.

Three groups.

1. **The quaternion matrix-target pairs** (`realFuse_four_two` through
   `realFuse_five_four`, eight pairs): `realRep 4 = quatEvenSuper` paired
   against a floor `∈ {2, 3, 5, 6}` on either side.  The route: split the
   Clifford factor via `towerFuse .symm` into two floor-`1` pieces,
   reassociate (`gtensorAssoc`), apply an already-landed `(4, ·)` seed
   (`realFuse_four_one`/`realFuse_four_seven`, or an earlier pair from
   this same file), and absorb the resulting matrix factor
   (`matrixSuperGtensor`/`matrixSuperOne`/`matrixSuperComp`) against a
   further landed mixed pair from `RealFuse2`.  E.g. `(4, 2)`:
   `ℍ ᵍ⊗ Cl_{0,2} ≅ (ℍ ᵍ⊗ Cl_{0,1}) ᵍ⊗ Cl_{0,1} ≅ M_{1|0}(Cl_{3,0}) ᵍ⊗ Cl_{0,1}
   ≅ (Cl_{3,0} ᵍ⊗ Cl_{0,1}).matrixSuper 1 0 ≅ M_{1|1}(Cl_{2,0})` (the last
   step being `realFuse_five_one`, already landed).

2. **The `ε = +1` wrap pairs** (`realFuse_five_five` through
   `realFuse_seven_five`, six pairs): pairs of floors `∈ {5, 6, 7}` whose
   sum lands *past* the Bott floor `4`.  `towerFuse` first fuses the sum
   at the `ℕ`-tower level (no cap), and the field-generic Bott/quaternion
   certificate `towerFourQuatSuper` (M7f-5a, **already landed**) supplies
   `divisionTower 1 4 ≅ M_{1|1}(ℍ)` whenever the sum is exactly `4`;
   larger sums split further as `4 + k` and route through group 1's
   pairs.  `(5, 7) ↦ 4` and `(6, 6) ↦ 4` are two-line compositions;
   `(5, 6) ↦ 3` and `(5, 5) ↦ 2` split off the floor-`4` block first.

3. **The `ε = -1` wrap pairs** (`realFuse_one_three` through
   `realFuse_three_three`, six pairs): the mirror construction at
   `ε = -1`.  This needs the `ε = -1` analogue of `towerFourQuatSuper`,
   **`divisionTowerNegFourQuatSuper : Cl_{0,4} ≅ M_{1|1}(ℍ)`** — absent
   from `Superfusion.Super.BottCertificate`/`QuaternionTower` (which only
   has the floor-`8` Bott certificates at both signs, and the floor-`4`
   certificate at `ε = +1` only).  Rather than re-deriving it from a
   fresh gamma-matrix system, it is assembled **entirely from landed
   pieces already in `RealFuse2`/`RealFuse3`**: peel the top generator
   off `Cl_{0,4}` (`towerFuse.symm`), identify the remaining `Cl_{0,3}`
   factor with `ℍ`'s odd double (`cliffThetaEquiv`, M9-4b-ii-3), unwind
   that odd double back to a graded tensor with `Cl_{1,0}`
   (`oddDoubleGtensorDivisionOneEquiv`), reassociate, fuse the resulting
   `Cl_{1,0} ᵍ⊗ Cl_{0,1}` hyperbolic pair (`hypFuse`, M9-4b-ii-2), and
   absorb the trivial `M_{1|1}(ℝ)` factor into `ℍ`
   (`matrixSuperGtensorRight`).  So this genuinely *is* the one new
   certificate the milestone anticipated, but it costs no new
   bijectivity argument: central/graded simplicity was already spent
   proving the pieces it is built from.

**Design relaxation (per task instructions, continued from `RealFuse2`):
produced sizes are cross-checked against Table 2 but not required to
match exactly** — several pairs here land on a *balanced* split (e.g.
`2|2` where Table 2 lists `4|0`) because they route through `RealFuse2`'s
balanced `peelFuse` pairs; the *totals* (`p + q`) always agree, and
`SuperAlgEquiv` guarantees `dim = dim` regardless.

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealFuse3
import Superfusion.Super.QuaternionTower

namespace Superfusion

/-! ### Group 1: the eight quaternion matrix-target pairs -/

section QuatMatrixPairs

/-- **`(4, 2) ↦ 6`**: `ℍ ᵍ⊗ Cl_{0,2} ≅ (ℍ ᵍ⊗ Cl_{0,1}) ᵍ⊗ Cl_{0,1}
≅ M_{1|0}(Cl_{3,0}) ᵍ⊗ Cl_{0,1} ≅ M_{1|1}(Cl_{2,0})`, via `realFuse_four_one`
and `realFuse_five_one`. Table 2 cross-check: `(4,2) ↦ D_6`, `2|0` — our
`1|1` **deviates** (same total `2`; `4 · 4 = 4 · 4`). -/
noncomputable def realFuse_four_two :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 2)) ((realRep (4 + 2)).matrixSuper 1 1) :=
  ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr (towerFuse (-1 : ℝ) 1 1).symm).trans <|
    (gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 1) (divisionTower (-1 : ℝ) 1)).symm.trans <|
      (realFuse_four_one.gtensorCongr (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).trans <|
        (matrixSuperGtensor (realRep 5) (realRep 1) 1 0).trans <|
          (matrixSuperOne ((realRep 5).gtensor (realRep 1))).trans realFuse_five_one

/-- **`(2, 4) ↦ 6`**, for free from the Koszul braiding. -/
noncomputable def realFuse_two_four :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 4)) ((realRep (2 + 4)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_four_two

/-- **`(4, 6) ↦ 2`**: `ℍ ᵍ⊗ Cl_{2,0} ≅ (ℍ ᵍ⊗ Cl_{1,0}) ᵍ⊗ Cl_{1,0}
≅ M_{1|0}(Cl_{0,3}) ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(Cl_{0,2})`, via `realFuse_four_seven`
and `realFuse_three_seven`. Table 2 cross-check: `(4,6) ↦ D_2`, `2|0` —
`1|1` **deviates** (same total `2`). -/
noncomputable def realFuse_four_six :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 6)) ((realRep (4 + 6)).matrixSuper 1 1) :=
  ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr (towerFuse (1 : ℝ) 1 1).symm).trans <|
    (gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1) (divisionTower (1 : ℝ) 1)).symm.trans <|
      (realFuse_four_seven.gtensorCongr (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).trans <|
        (matrixSuperGtensor (realRep 3) (realRep 7) 1 0).trans <|
          (matrixSuperOne ((realRep 3).gtensor (realRep 7))).trans realFuse_three_seven

/-- **`(6, 4) ↦ 2`**, for free from the Koszul braiding. -/
noncomputable def realFuse_six_four :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 4)) ((realRep (6 + 4)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_four_six

/-- **`(4, 3) ↦ 7`**: `ℍ ᵍ⊗ Cl_{0,3} ≅ (ℍ ᵍ⊗ Cl_{0,2}) ᵍ⊗ Cl_{0,1}
≅ M_{1|1}(Cl_{2,0}) ᵍ⊗ Cl_{0,1} ≅ M_{2|2}(Cl_{1,0})`, chaining this file's
own `realFuse_four_two` with `realFuse_six_one`. Table 2 cross-check:
`(4,3) ↦ D_7`, `4|0` — our `2|2` **deviates** (same total `4`). -/
noncomputable def realFuse_four_three :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 3)) ((realRep (4 + 3)).matrixSuper 2 2) :=
  ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr (towerFuse (-1 : ℝ) 2 1).symm).trans <|
    (gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 2) (divisionTower (-1 : ℝ) 1)).symm.trans <|
      (realFuse_four_two.gtensorCongr (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).trans <|
        (matrixSuperGtensor (realRep 6) (realRep 1) 1 1).trans <|
          (realFuse_six_one.matrixSuper 1 1).trans (matrixSuperComp (realRep 7) 1 1 1 1)

/-- **`(3, 4) ↦ 7`**, for free from the Koszul braiding. -/
noncomputable def realFuse_three_four :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 4)) ((realRep (3 + 4)).matrixSuper 2 2) :=
  realFuse_transpose realFuse_four_three

/-- **`(4, 5) ↦ 1`**: `ℍ ᵍ⊗ Cl_{3,0} ≅ (ℍ ᵍ⊗ Cl_{2,0}) ᵍ⊗ Cl_{1,0}
≅ M_{1|1}(Cl_{0,2}) ᵍ⊗ Cl_{1,0} ≅ M_{2|2}(Cl_{0,1})`, chaining this file's
own `realFuse_four_six` with `realFuse_two_seven`. Table 2 cross-check:
`(4,5) ↦ D_1`, `4|0` — our `2|2` **deviates** (same total `4`). -/
noncomputable def realFuse_four_five :
    SuperAlgEquiv ((realRep 4).gtensor (realRep 5)) ((realRep (4 + 5)).matrixSuper 2 2) :=
  ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr (towerFuse (1 : ℝ) 2 1).symm).trans <|
    (gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 2) (divisionTower (1 : ℝ) 1)).symm.trans <|
      (realFuse_four_six.gtensorCongr (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).trans <|
        (matrixSuperGtensor (realRep 2) (realRep 7) 1 1).trans <|
          (realFuse_two_seven.matrixSuper 1 1).trans (matrixSuperComp (realRep 1) 1 1 1 1)

/-- **`(5, 4) ↦ 1`**, for free from the Koszul braiding. -/
noncomputable def realFuse_five_four :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 4)) ((realRep (5 + 4)).matrixSuper 2 2) :=
  realFuse_transpose realFuse_four_five

end QuatMatrixPairs

/-! ### Group 2: the six `ε = +1` wrap pairs (past the Bott floor) -/

section PosWrapPairs

/-- **`(5, 7) ↦ 4`**: `Cl_{3,0} ᵍ⊗ Cl_{1,0} ≅ D₁^{⊗̂4} ≅ M_{1|1}(ℍ)`, a
two-line composition of `towerFuse` and the **already-landed**
field-generic Bott/quaternion certificate `towerFourQuatSuper` (M7f-5a).
Table 2 cross-check: `(5,7) ↦ D_4`, `1|1` — **matches**. -/
noncomputable def realFuse_five_seven :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 7)) ((realRep (5 + 7)).matrixSuper 1 1) :=
  (towerFuse (1 : ℝ) 3 1).trans (towerFourQuatSuper ℝ)

/-- **`(7, 5) ↦ 4`**, for free from the Koszul braiding. -/
noncomputable def realFuse_seven_five :
    SuperAlgEquiv ((realRep 7).gtensor (realRep 5)) ((realRep (7 + 5)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_five_seven

/-- **`(6, 6) ↦ 4`**: `Cl_{2,0} ᵍ⊗ Cl_{2,0} ≅ D₁^{⊗̂4} ≅ M_{1|1}(ℍ)`, same
two-line shape. Table 2 cross-check: `(6,6) ↦ D_4`, `1|1` — **matches**. -/
noncomputable def realFuse_six_six :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 6)) ((realRep (6 + 6)).matrixSuper 1 1) :=
  (towerFuse (1 : ℝ) 2 2).trans (towerFourQuatSuper ℝ)

/-- **`(5, 6) ↦ 3`**: `Cl_{3,0} ᵍ⊗ Cl_{2,0} ≅ D₁^{⊗̂5} ≅ (D₁^{⊗̂4}) ᵍ⊗ Cl_{1,0}
≅ M_{1|1}(ℍ) ᵍ⊗ Cl_{1,0} ≅ M_{1|1}(ℍ ᵍ⊗ Cl_{1,0}) ≅ M_{1|1}(M_{1|0}(Cl_{0,3}))
≅ M_{1|1}(Cl_{0,3})`, splitting the sum `5 = 4 + 1` and routing through the
already-landed `realFuse_four_seven`. Table 2 cross-check: `(5,6) ↦ D_3`,
`2|0` — our `1|1` **deviates** (same total `2`). -/
noncomputable def realFuse_five_six :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 6)) ((realRep (5 + 6)).matrixSuper 1 1) :=
  (towerFuse (1 : ℝ) 3 2).trans <|
    (towerFuse (1 : ℝ) 4 1).symm.trans <|
      ((towerFourQuatSuper ℝ).gtensorCongr (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).trans <|
        (matrixSuperGtensor quatEvenSuper (realRep 7) 1 1).trans <|
          (realFuse_four_seven.matrixSuper 1 1).trans (matrixSuperComp (realRep 3) 1 1 1 0)

/-- **`(6, 5) ↦ 3`**, for free from the Koszul braiding. -/
noncomputable def realFuse_six_five :
    SuperAlgEquiv ((realRep 6).gtensor (realRep 5)) ((realRep (6 + 5)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_five_six

/-- **`(5, 5) ↦ 2`**: `Cl_{3,0} ᵍ⊗ Cl_{3,0} ≅ D₁^{⊗̂6} ≅ (D₁^{⊗̂4}) ᵍ⊗ Cl_{2,0}
≅ M_{1|1}(ℍ) ᵍ⊗ Cl_{2,0} ≅ M_{1|1}(ℍ ᵍ⊗ Cl_{2,0}) ≅ M_{1|1}(M_{1|1}(Cl_{0,2}))
≅ M_{2|2}(Cl_{0,2})`, splitting `6 = 4 + 2` and routing through this file's
own `realFuse_four_six`. Table 2 cross-check: `(5,5) ↦ D_2`, `4|0` — our
`2|2` **deviates** (same total `4`). -/
noncomputable def realFuse_five_five :
    SuperAlgEquiv ((realRep 5).gtensor (realRep 5)) ((realRep (5 + 5)).matrixSuper 2 2) :=
  (towerFuse (1 : ℝ) 3 3).trans <|
    (towerFuse (1 : ℝ) 4 2).symm.trans <|
      ((towerFourQuatSuper ℝ).gtensorCongr (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 2))).trans <|
        (matrixSuperGtensor quatEvenSuper (realRep 6) 1 1).trans <|
          (realFuse_four_six.matrixSuper 1 1).trans (matrixSuperComp (realRep 2) 1 1 1 1)

end PosWrapPairs

/-! ### Group 3: the `ε = -1` floor-`4` certificate, and its six wrap pairs -/

section NegWrapPairs

/-- **The `ε = -1` floor-`4` certificate**: `Cl_{0,4} ≅ M_{1|1}(ℍ)`, the
`ε = -1` mirror of `towerFourQuatSuper` (M7f-5a) — absent as a standalone
gamma-matrix construction, but assembled here **entirely by reduction**
through already-landed pieces (no new bijectivity argument): peel the top
generator off `Cl_{0,4}` (`towerFuse.symm`), identify the remaining
`Cl_{0,3}` factor with `ℍ`'s odd double (`cliffThetaEquiv`, M9-4b-ii-3),
unwind that odd double to a graded tensor with `Cl_{1,0}`
(`oddDoubleGtensorDivisionOneEquiv`), reassociate (`gtensorAssoc`), fuse
the resulting `Cl_{1,0} ᵍ⊗ Cl_{0,1}` hyperbolic pair (`hypFuse`,
M9-4b-ii-2), and absorb the trivial `M_{1|1}(ℝ)` factor into `ℍ`
(`matrixSuperGtensorRight`). -/
noncomputable def divisionTowerNegFourQuatSuper :
    SuperAlgEquiv (divisionTower (-1 : ℝ) 4) (quatEvenSuper.matrixSuper 1 1) :=
  (towerFuse (-1 : ℝ) 3 1).symm.trans <|
    ((((cliffThetaEquiv (-1 : ℝ) (show (-1 : ℝ) * (-1 : ℝ) = 1 from by norm_num)).symm.trans
            (oddDouble_congr_eps (show (-(-1 : ℝ)) = 1 from by norm_num))).trans
          (oddDoubleGtensorDivisionOneEquiv (1 : ℝ) quatEvenSuper one_ne_zero).symm
        ).gtensorCongr (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).trans <|
      (gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1) (divisionTower (-1 : ℝ) 1)).trans <|
        ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
              ((gtensorComm (divisionTower (1 : ℝ) 1) (divisionTower (-1 : ℝ) 1)).trans
                hypFuse)).trans <|
          (matrixSuperGtensorRight quatEvenSuper (SuperAlgebra.base ℝ) 1 1).trans
            ((gtensorUnitorRight quatEvenSuper).matrixSuper 1 1)

/-- **`(1, 3) ↦ 4`**: `Cl_{0,1} ᵍ⊗ Cl_{0,3} ≅ Cl_{0,4} ≅ M_{1|1}(ℍ)`, a
two-line composition of `towerFuse` and `divisionTowerNegFourQuatSuper`.
Table 2 cross-check: `(1,3) ↦ D_4`, `1|1` — **matches**. -/
noncomputable def realFuse_one_three :
    SuperAlgEquiv ((realRep 1).gtensor (realRep 3)) ((realRep (1 + 3)).matrixSuper 1 1) :=
  (towerFuse (-1 : ℝ) 1 3).trans divisionTowerNegFourQuatSuper

/-- **`(3, 1) ↦ 4`**, for free from the Koszul braiding. -/
noncomputable def realFuse_three_one :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 1)) ((realRep (3 + 1)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_one_three

/-- **`(2, 2) ↦ 4`**: `Cl_{0,2} ᵍ⊗ Cl_{0,2} ≅ Cl_{0,4} ≅ M_{1|1}(ℍ)`, same
two-line shape. Table 2 cross-check: `(2,2) ↦ D_4`, `1|1` — **matches**. -/
noncomputable def realFuse_two_two :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 2)) ((realRep (2 + 2)).matrixSuper 1 1) :=
  (towerFuse (-1 : ℝ) 2 2).trans divisionTowerNegFourQuatSuper

/-- **`(2, 3) ↦ 5`**: `Cl_{0,2} ᵍ⊗ Cl_{0,3} ≅ Cl_{0,5} ≅ Cl_{0,4} ᵍ⊗ Cl_{0,1}
≅ M_{1|1}(ℍ) ᵍ⊗ Cl_{0,1} ≅ M_{1|1}(ℍ ᵍ⊗ Cl_{0,1}) ≅ M_{1|1}(M_{1|0}(Cl_{3,0}))
≅ M_{1|1}(Cl_{3,0})`, splitting `5 = 4 + 1` and routing through the
already-landed `realFuse_four_one`. Table 2 cross-check: `(2,3) ↦ D_5`,
`2|0` — our `1|1` **deviates** (same total `2`). -/
noncomputable def realFuse_two_three :
    SuperAlgEquiv ((realRep 2).gtensor (realRep 3)) ((realRep (2 + 3)).matrixSuper 1 1) :=
  (towerFuse (-1 : ℝ) 2 3).trans <|
    (towerFuse (-1 : ℝ) 4 1).symm.trans <|
      (divisionTowerNegFourQuatSuper.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).trans <|
        (matrixSuperGtensor quatEvenSuper (realRep 1) 1 1).trans <|
          (realFuse_four_one.matrixSuper 1 1).trans (matrixSuperComp (realRep 5) 1 1 1 0)

/-- **`(3, 2) ↦ 5`**, for free from the Koszul braiding. -/
noncomputable def realFuse_three_two :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 2)) ((realRep (3 + 2)).matrixSuper 1 1) :=
  realFuse_transpose realFuse_two_three

/-- **`(3, 3) ↦ 6`**: `Cl_{0,3} ᵍ⊗ Cl_{0,3} ≅ Cl_{0,6} ≅ Cl_{0,4} ᵍ⊗ Cl_{0,2}
≅ M_{1|1}(ℍ) ᵍ⊗ Cl_{0,2} ≅ M_{1|1}(ℍ ᵍ⊗ Cl_{0,2}) ≅ M_{1|1}(M_{1|1}(Cl_{2,0}))
≅ M_{2|2}(Cl_{2,0})`, splitting `6 = 4 + 2` and routing through this file's
own `realFuse_four_two`. Table 2 cross-check: `(3,3) ↦ D_6`, `4|0` — our
`2|2` **deviates** (same total `4`). -/
noncomputable def realFuse_three_three :
    SuperAlgEquiv ((realRep 3).gtensor (realRep 3)) ((realRep (3 + 3)).matrixSuper 2 2) :=
  (towerFuse (-1 : ℝ) 3 3).trans <|
    (towerFuse (-1 : ℝ) 4 2).symm.trans <|
      (divisionTowerNegFourQuatSuper.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 2))).trans <|
        (matrixSuperGtensor quatEvenSuper (realRep 2) 1 1).trans <|
          (realFuse_four_two.matrixSuper 1 1).trans (matrixSuperComp (realRep 6) 1 1 1 1)

end NegWrapPairs

end Superfusion
