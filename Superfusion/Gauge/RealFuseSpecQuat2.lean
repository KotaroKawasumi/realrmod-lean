/-
Superfusion / Gauge / RealFuseSpecQuat2

M15 semantic-bridge, GROUP 3 continued: the **`M_{1|1}`-target quaternion
pairs** that `RealFuseSpecQuat` parked.

**Landed here** (kernel-checked; no proof holes, no kernel-reducing
tactics beyond `decide`, no new axioms — each depends only on `propext`,
`Classical.choice`, `Quot.sound`):

* `realFuseMatrix_4_2` (`16 × 16`) — `ℍ ᵍ⊗ Cl_{0,2} ≅ M_{1|1}(Cl_{2,0})`,
* `realFuseMatrix_4_6` (`16 × 16`) — `ℍ ᵍ⊗ Cl_{2,0} ≅ M_{1|1}(Cl_{0,2})`,
* `realFuseMatrix_2_4`, `realFuseMatrix_6_4` — the two Koszul transposes
  they release, discharged from `RealFuseSpecTranspose`'s conditional
  `…_of_forward` statements.

## Method: the prefix is a signed permutation onto a landed branch

`realFuse_four_two` (`RealFuse4`) is the six-stage composite

```
ℍ ᵍ⊗ T₂⁻ → ℍ ᵍ⊗ (T₁⁻ ᵍ⊗ T₁⁻) → (ℍ ᵍ⊗ T₁⁻) ᵍ⊗ T₁⁻
         → M_{1|0}(T₃⁺) ᵍ⊗ T₁⁻ → M_{1|0}(T₃⁺ ᵍ⊗ T₁⁻) → T₃⁺ ᵍ⊗ T₁⁻
         → M_{1|1}(T₂⁺)
```

whose **last stage is the already-pinned branch `realFuse_five_one`**
(`realFuseMatrix_5_1`, `RealFuseSpecTransposeClose`), and whose target
frame is literally `realFuseDstBasis 5 1`.  So the whole file never
re-evaluates the seed: it only has to show that the five-stage *prefix*
carries the source frame of `(4,2)` to the source frame of `(5,1)` by a
signed permutation, and then compare two literals.

* `preGen` — the prefix, computed **once**, generic in `ε` and in the
  seed `F : ℍ ᵍ⊗ T₁ ≅ M_{1|0}(T₃)` and the tail
  `G : T₃ ᵍ⊗ T₁ ≅ C`.  The composite is fed in as a hypothesis `hE`
  (`rfl` at each call site), so no rewrite ever meets the
  `realRep`-versus-`divisionTower` spelling mismatch (lesson of
  `RealFuseSpecQuat`'s `toMatrix_of_coord`).
* `tail10` — the `1|0` ampliation tail is **sign-free**:
  `sumParity 1 0 (inl 0) = 0` kills `msg_single'`'s column twist, and
  `matrixSuperOne` then reads off the single entry.
* `colGen` — one column: name the two frame vectors (`gb_at`), cross the
  prefix (`preGen`), pull the seed's coefficient out of the left tensor
  slot (`gtmul_smul_left`).  Sixteen one-line instances per branch, each
  fed by a `val41_*` / `val47_*` value of `RealFuseSpecQuat`.
* `entry_split` — column data to matrix entries:
  `M_{ab}[i][j] = c_j · M_{seed}[i][σ j]`.
* `mulCode` / `master42` / `master46` — the comparison of the two
  literals is done in `ℕ`, on packed base-3 value codes, by a single
  kernel `decide` over the `256` points.  This is the same discipline as
  `RealFuseSpecPeel3`: no `N²` tactic goal with real arithmetic in it.

## Not landed here — `(4,3)` and `(4,5)`

Both have the same tower half (`towerFuse ε 2 1` split, `gtensorAssoc`),
but their third stage is `realFuse_four_two` / `realFuse_four_six`
themselves, which land in `M_{1|1}` with **two** nonzero entries per
column, and their tail is the *`1 1 1 1`* ampliation
`matrixSuperGtensor (realRep 6) (realRep 1) 1 1 ;
(realFuse_six_one).matrixSuper 1 1 ; matrixSuperComp (realRep 7) 1 1 1 1`
whose inner seed `realFuse_six_one` again has two entries per column.
So each of the `32` columns is a **four**-term sum, and
`matrixSuperGtensor`'s column twist `sgn (sumParity 1 1 s · |b|)` is
genuinely active (`RealFuse4`'s own docstring flags it).  Concretely what
is still missing:

* a `col2_of_matrix` lemma turning a landed `realFuseMatrix` column with
  two nonzeros into the two-term value
  `E (bA j) = a₁ • bC I₁ + a₂ • bC I₂` (`Finset.sum_ite_eq'` on the
  `Basis.sum_repr` expansion) — applied to `realFuseMatrix_4_2` /
  `realFuseMatrix_4_6` above and to `realFuseMatrix_6_1` /
  `realFuseMatrix_2_7`;
* a two-entry variant of `RealFuseSpecWrap3`'s `termG` for the
  `matrixSuperComp T 1 1 1 1` collapse (`termG` is written for
  `… 1 1 1 0`);
* the `32 × 4` column assembly, and the `1024`-point code certificate.

The same three items are what `RealFuseSpecWrap3` lists as blocking
`(3,3)` and `(5,5)`; the two-term values of `realFuse_four_two` /
`realFuse_four_six` that both need are now one `col2_of_matrix` away
from this file's `realFuseMatrix_4_2` / `realFuseMatrix_4_6`.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 7).
-/
import Superfusion.Gauge.RealFuseSpecPeel3
import Superfusion.Gauge.RealFuseSpecTransposeClose
import Superfusion.Gauge.RealFuseSpecWrap3
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

open private q1 towerFuse_basis hmem_tone superRefl_apply
  gtensorAssoc_symm_tmul matrixSuperOne_symm_single
  val41_0_0 val41_0_1 val41_1_0 val41_1_1 val41_2_0 val41_2_1 val41_3_0 val41_3_1
  val47_0_0 val47_0_1 val47_1_0 val47_1_1 val47_2_0 val47_2_1 val47_3_0 val47_3_1
  from Superfusion.Gauge.RealFuseSpecQuat

open private msg_single' from Superfusion.Gauge.RealFuseSpecWrap2

open private gtmul_smul_left single_smulG smul_dstG
  from Superfusion.Gauge.RealFuseSpecWrap3

open private towerBasis_one_zero towerBasis_one_one
  from Superfusion.Gauge.RealFuseSpecWrap

open private fuseNegCode fuseDecode_negCode
  from Superfusion.Gauge.RealFuseSpecTranspose

/-! ### Value-code arithmetic

`fuseDecode` sends `1 ↦ 1`, `2 ↦ -1`, everything else to `0`.  A branch
whose prefix is a signed permutation of an already-pinned branch is
checked by one `decide` in `ℕ`, over the codes. -/

/-- Multiplying a decoded value by a decoded sign, at the code level. -/
private def mulCode : ℕ → ℕ → ℕ
  | 1, k => k
  | 2, k => fuseNegCode k
  | _, _ => 0

private theorem mulCode_spec (a k : ℕ) (ha : a = 1 ∨ a = 2) :
    fuseDecode a * fuseDecode k = fuseDecode (mulCode a k) := by
  rcases ha with rfl | rfl
  · show (1 : ℝ) * fuseDecode k = fuseDecode k
    rw [one_mul]
  · show (-1 : ℝ) * fuseDecode k = fuseDecode (fuseNegCode k)
    rw [fuseDecode_negCode, neg_one_mul]

/-! ### Generic plumbing -/

/-- The tower fusion inverse at a named index (local copy). -/
private theorem tfuseKsymm' (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a)) (j : Fin (2 ^ b))
    (k : Fin (2 ^ (a + b))) (h : (k : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)) :
    (towerFuse ε a b).symm.toAlgEquiv (towerBasis ε (a + b) k)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j) := by
  show ((towerFuse ε a b).toAlgEquiv).symm _ = _
  rw [AlgEquiv.symm_apply_eq, towerFuse_basis ε a b i j]
  exact congrArg (towerBasis ε (a + b)) (Fin.ext h)

/-- The `M_{1|0}` unit on a single-entry matrix. -/
private theorem msOne_single {P : SuperAlgebra ℝ} (v : P.carrier) :
    (matrixSuperOne P).toAlgEquiv
        (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v) = v := by
  have h : (matrixSuperOne P).toAlgEquiv
      (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v)
      = (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v)
          (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0 : Fin 1 ⊕ Fin 0) := rfl
  rw [h, Matrix.single_apply_same]

/-- The sign-free `1|0` ampliation tail: `single ⊗ w ↦ v ᵍ⊗ w`. -/
private theorem tail10 {T R : SuperAlgebra ℝ} (v : T.carrier) {jw : ZMod 2}
    {w : R.carrier} (hw : w ∈ R.grading jw) :
    (matrixSuperOne (T.gtensor R)).toAlgEquiv
        ((matrixSuperGtensor T R 1 0).toAlgEquiv
          (GradedTensorProduct.tmul
            (𝒜 := matrixGradingA (sumParity 1 0) T.grading) (ℬ := R.grading) ℝ
            (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v) w))
      = GradedTensorProduct.tmul (𝒜 := T.grading) (ℬ := R.grading) ℝ v w := by
  have h1 := msg_single' T R 1 0 (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v hw
  refine (congrArg (matrixSuperOne (T.gtensor R)).toAlgEquiv h1).trans ?_
  have h2 : ((sgn (sumParity 1 0 (Sum.inl 0 : Fin 1 ⊕ Fin 0) * jw) : ℤˣ) : ℤ)
      = 1 := by
    show ((sgn (0 * jw) : ℤˣ) : ℤ) = 1
    rw [zero_mul]
    rfl
  rw [h2, one_zsmul]
  exact msOne_single _

/-- The floor-`2` tower vector splits into two floor-`1` vectors. -/
private theorem split2 (ε : ℝ) (u0 u1 : Fin 2) (u : Fin 4)
    (h : (u : ℕ) = (u0 : ℕ) + 2 * (u1 : ℕ)) :
    (towerFuse ε 1 1).symm.toAlgEquiv (towerBasis ε 2 u)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (towerBasis ε 1 u0) (towerBasis ε 1 u1) :=
  tfuseKsymm' ε 1 1 u0 u1 u h

/-! ### The generic `(4, ·)` prefix

Both `(4,2)` and `(4,6)` are `ℍ ᵍ⊗ T_2 ≅ M_{1|0}(T_3) ᵍ⊗ T_1 ≅ T_3 ᵍ⊗ T_1`
followed by an already-pinned seed.  The prefix is computed once, generic
in `ε` and in the seed. -/

private theorem preGen {T C : SuperAlgebra ℝ} (ε : ℝ)
    (F : SuperAlgEquiv (quatEvenSuper.gtensor (divisionTower ε 1))
      (T.matrixSuper 1 0))
    (G : SuperAlgEquiv (T.gtensor (divisionTower ε 1)) C)
    (E : SuperAlgEquiv (quatEvenSuper.gtensor (divisionTower ε 2)) C)
    (hE : ∀ x, E.toAlgEquiv x
        = G.toAlgEquiv
            ((matrixSuperOne (T.gtensor (divisionTower ε 1))).toAlgEquiv
              ((matrixSuperGtensor T (divisionTower ε 1) 1 0).toAlgEquiv
                ((F.gtensorCongr
                    (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
                  ((gtensorAssoc quatEvenSuper (divisionTower ε 1)
                      (divisionTower ε 1)).symm.toAlgEquiv
                    (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                        (towerFuse ε 1 1).symm).toAlgEquiv x))))))
    (e : Fin 4) (u0 u1 : Fin 2) (u : Fin 4)
    (hu : (u : ℕ) = (u0 : ℕ) + 2 * (u1 : ℕ))
    (v : T.carrier)
    (hval : F.toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
                (ℬ := (divisionTower ε 1).grading) ℝ (quatBasis e)
                (towerBasis ε 1 u0))
            = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v) :
    E.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (quatBasis e)
          (towerBasis ε 2 u))
      = G.toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := T.grading)
            (ℬ := (divisionTower ε 1).grading) ℝ v (towerBasis ε 1 u1)) := by
  have s1 : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        (towerFuse ε 1 1).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower ε 2).grading) ℝ (quatBasis e)
          (towerBasis ε 2 u))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower ε 1).gtensor (divisionTower ε 1)).grading) ℝ
          (quatBasis e)
          (GradedTensorProduct.tmul (𝒜 := (divisionTower ε 1).grading)
            (ℬ := (divisionTower ε 1).grading) ℝ
            (towerBasis ε 1 u0) (towerBasis ε 1 u1)) := by
    have h := SuperAlgEquiv.gtensorCongr_tmul
      (SuperAlgEquiv.refl quatEvenSuper) (towerFuse ε 1 1).symm
      (quatBasis e) (towerBasis ε 2 u)
    rw [superRefl_apply, split2 ε u0 u1 u hu] at h
    exact h
  have s2 := gtensorAssoc_symm_tmul quatEvenSuper (divisionTower ε 1)
    (divisionTower ε 1) (quatBasis e) (towerBasis ε 1 u0) (towerBasis ε 1 u1)
  have s3 : (F.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower ε 1)).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower ε 1).grading) ℝ (quatBasis e)
            (towerBasis ε 1 u0))
          (towerBasis ε 1 u1))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 0) T.grading)
          (ℬ := (divisionTower ε 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v)
          (towerBasis ε 1 u1) := by
    have h := SuperAlgEquiv.gtensorCongr_tmul F
      (SuperAlgEquiv.refl (divisionTower ε 1))
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower ε 1).grading) ℝ (quatBasis e)
        (towerBasis ε 1 u0))
      (towerBasis ε 1 u1)
    rw [superRefl_apply, hval] at h
    exact h
  have s4 := tail10 (T := T) (R := divisionTower ε 1) v
    (towerBasis_mem ε 1 u1)
  refine (hE _).trans ?_
  refine congrArg G.toAlgEquiv ?_
  refine (congrArg (fun z =>
    (matrixSuperOne (T.gtensor (divisionTower ε 1))).toAlgEquiv
      ((matrixSuperGtensor T (divisionTower ε 1) 1 0).toAlgEquiv
        ((F.gtensorCongr
            (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
          ((gtensorAssoc quatEvenSuper (divisionTower ε 1)
              (divisionTower ε 1)).symm.toAlgEquiv z)))) s1).trans ?_
  refine (congrArg (fun z =>
    (matrixSuperOne (T.gtensor (divisionTower ε 1))).toAlgEquiv
      ((matrixSuperGtensor T (divisionTower ε 1) 1 0).toAlgEquiv
        ((F.gtensorCongr
            (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv z))) s2).trans ?_
  refine (congrArg (fun z =>
    (matrixSuperOne (T.gtensor (divisionTower ε 1))).toAlgEquiv
      ((matrixSuperGtensor T (divisionTower ε 1) 1 0).toAlgEquiv z)) s3).trans ?_
  exact s4

/-! ### Naming frame vectors -/

/-- The tensor frame vector at a named flat index. -/
private theorem gb_at {A B : SuperAlgebra ℝ} {m n : ℕ}
    (bA : Basis (Fin m) ℝ A.carrier) (bB : Basis (Fin n) ℝ B.carrier)
    (i : Fin m) (jx : Fin n) (J : Fin (m * n))
    (h : (J : ℕ) = (jx : ℕ) + n * (i : ℕ)) :
    gtensorBasis bA bB J
      = GradedTensorProduct.tmul (𝒜 := A.grading) (ℬ := B.grading) ℝ
          (bA i) (bB jx) := by
  have hJ : J = (⟨(jx : ℕ) + n * (i : ℕ), gtensorIndex_lt i jx⟩ : Fin (m * n)) :=
    Fin.ext h
  rw [hJ]
  exact gtensorBasis_apply bA bB i jx

/-- The `M_{1|0}(T₃)` frame vector at a named index. -/
private theorem d3g (ε : ℝ) (idx : Fin 8) :
    matrixSuperBasis (towerBasis ε 3) 1 0 idx
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (towerBasis ε 3 idx) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) idx

/-! ### The generic column lemma -/

private theorem colGen {C : SuperAlgebra ℝ} (ε ε' : ℝ)
    (F : SuperAlgEquiv (quatEvenSuper.gtensor (divisionTower ε 1))
      ((divisionTower ε' 3).matrixSuper 1 0))
    (G : SuperAlgEquiv ((divisionTower ε' 3).gtensor (divisionTower ε 1)) C)
    (E : SuperAlgEquiv (quatEvenSuper.gtensor (divisionTower ε 2)) C)
    (hE : ∀ x, E.toAlgEquiv x
        = G.toAlgEquiv
            ((matrixSuperOne
                ((divisionTower ε' 3).gtensor (divisionTower ε 1))).toAlgEquiv
              ((matrixSuperGtensor (divisionTower ε' 3)
                  (divisionTower ε 1) 1 0).toAlgEquiv
                ((F.gtensorCongr
                    (SuperAlgEquiv.refl (divisionTower ε 1))).toAlgEquiv
                  ((gtensorAssoc quatEvenSuper (divisionTower ε 1)
                      (divisionTower ε 1)).symm.toAlgEquiv
                    (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                        (towerFuse ε 1 1).symm).toAlgEquiv x))))))
    (e : Fin 4) (u0 u1 : Fin 2) (u : Fin 4) (J S : Fin 16) (c : ℝ) (idx : Fin 8)
    (hu : (u : ℕ) = (u0 : ℕ) + 2 * (u1 : ℕ))
    (hJ : (J : ℕ) = (u : ℕ) + 4 * (e : ℕ))
    (hS : (S : ℕ) = (u1 : ℕ) + 2 * (idx : ℕ))
    (hval : F.toAlgEquiv
              (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
                (ℬ := (divisionTower ε 1).grading) ℝ (quatBasis e)
                (towerBasis ε 1 u0))
            = c • matrixSuperBasis (towerBasis ε' 3) 1 0 idx) :
    E.toAlgEquiv (gtensorBasis quatBasis (towerBasis ε 2) J)
      = c • G.toAlgEquiv
          (gtensorBasis (towerBasis ε' 3) (towerBasis ε 1) S) := by
  have hval' : F.toAlgEquiv
      (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := (divisionTower ε 1).grading) ℝ (quatBasis e)
        (towerBasis ε 1 u0))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (c • towerBasis ε' 3 idx) :=
    hval.trans (smul_dstG c (d3g ε' idx))
  have hsrc := gb_at quatBasis (towerBasis ε 2) e u J hJ
  have htgt := gb_at (towerBasis ε' 3) (towerBasis ε 1) idx u1 S hS
  have hstep := preGen ε F G E hE e u0 u1 u hu (c • towerBasis ε' 3 idx) hval'
  have hpull : GradedTensorProduct.tmul (𝒜 := (divisionTower ε' 3).grading)
        (ℬ := (divisionTower ε 1).grading) ℝ (c • towerBasis ε' 3 idx)
        (towerBasis ε 1 u1)
      = c • GradedTensorProduct.tmul (𝒜 := (divisionTower ε' 3).grading)
          (ℬ := (divisionTower ε 1).grading) ℝ (towerBasis ε' 3 idx)
          (towerBasis ε 1 u1) :=
    gtmul_smul_left (divisionTower ε' 3).grading (divisionTower ε 1).grading c
      (towerBasis ε' 3 idx) (towerBasis ε 1 u1)
  refine (congrArg E.toAlgEquiv hsrc).trans ?_
  refine hstep.trans ?_
  refine (congrArg G.toAlgEquiv hpull).trans ?_
  refine (map_smul G.toAlgEquiv c _).trans ?_
  exact congrArg (fun z => c • G.toAlgEquiv z) htgt.symm

/-! ### Column-data to matrix entries -/

private theorem entry_split {A B C : SuperAlgebra ℝ} {n m k : ℕ}
    (bA : Basis (Fin n) ℝ A.carrier) (bB : Basis (Fin m) ℝ B.carrier)
    (bC : Basis (Fin k) ℝ C.carrier)
    (E : SuperAlgEquiv A C) (H : SuperAlgEquiv B C)
    (c : Fin n → ℝ) (σ : Fin n → Fin m)
    (hcol : ∀ j, E.toAlgEquiv (bA j) = c j • H.toAlgEquiv (bB (σ j)))
    (i : Fin k) (j : Fin n) :
    LinearMap.toMatrix bA bC E.toAlgEquiv.toLinearMap i j
      = c j * LinearMap.toMatrix bB bC H.toAlgEquiv.toLinearMap i (σ j) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, hcol j,
    map_smul, Finsupp.smul_apply, smul_eq_mul]

/-! ### Branch `(4,2)`: the seed values on the floor-`1` frame -/

private theorem hv41_0_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 0 := by
  rw [towerBasis_one_zero]; exact val41_0_0

private theorem hv41_0_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 7 := by
  rw [towerBasis_one_one]; exact val41_0_1

private theorem hv41_1_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 3 := by
  rw [towerBasis_one_zero]; exact val41_1_0

private theorem hv41_1_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 4 := by
  rw [towerBasis_one_one]; exact val41_1_1

private theorem hv41_2_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 6 := by
  rw [towerBasis_one_zero]; exact val41_2_0

private theorem hv41_2_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 1 := by
  rw [towerBasis_one_one]; exact val41_2_1

private theorem hv41_3_0 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 5 := by
  rw [towerBasis_one_zero]; exact val41_3_0

private theorem hv41_3_1 :
    realFuse_four_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 2 := by
  rw [towerBasis_one_one]; exact val41_3_1

/-- The `(4,2)` composite in the shape `colGen` consumes. -/
private theorem hE42 : ∀ x : (quatEvenSuper.gtensor (divisionTower (-1 : ℝ) 2)).carrier,
    realFuse_four_two.toAlgEquiv x
      = realFuse_five_one.toAlgEquiv
          ((matrixSuperOne
              ((divisionTower (1 : ℝ) 3).gtensor
                (divisionTower (-1 : ℝ) 1))).toAlgEquiv
            ((matrixSuperGtensor (divisionTower (1 : ℝ) 3)
                (divisionTower (-1 : ℝ) 1) 1 0).toAlgEquiv
              ((realFuse_four_one.gtensorCongr
                  (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
                ((gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 1)
                    (divisionTower (-1 : ℝ) 1)).symm.toAlgEquiv
                  (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                      (towerFuse (-1 : ℝ) 1 1).symm).toAlgEquiv x))))) :=
  fun _ => rfl

private def cv42 : Fin 16 → ℝ :=
  ![1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1]

private def sv42 : Fin 16 → Fin 16 :=
  ![0, 14, 1, 15, 6, 8, 7, 9, 12, 2, 13, 3, 10, 4, 11, 5]

private theorem hcol42 : ∀ j : Fin 16,
    realFuse_four_two.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 2) j)
      = cv42 j • realFuse_five_one.toAlgEquiv
          (gtensorBasis (towerBasis (1 : ℝ) 3) (towerBasis (-1 : ℝ) 1)
            (sv42 j)) := by
  intro j
  fin_cases j
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 0 0 0 0 0 0 1 0 rfl rfl rfl hv41_0_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 0 1 0 1 1 14 1 7 rfl rfl rfl hv41_0_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 0 0 1 2 2 1 1 0 rfl rfl rfl hv41_0_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 0 1 1 3 3 15 1 7 rfl rfl rfl hv41_0_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 1 0 0 0 4 6 1 3 rfl rfl rfl hv41_1_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 1 1 0 1 5 8 (-1) 4 rfl rfl rfl hv41_1_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 1 0 1 2 6 7 1 3 rfl rfl rfl hv41_1_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 1 1 1 3 7 9 (-1) 4 rfl rfl rfl hv41_1_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 2 0 0 0 8 12 1 6 rfl rfl rfl hv41_2_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 2 1 0 1 9 2 (-1) 1 rfl rfl rfl hv41_2_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 2 0 1 2 10 13 1 6 rfl rfl rfl hv41_2_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 2 1 1 3 11 3 (-1) 1 rfl rfl rfl hv41_2_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 3 0 0 0 12 10 1 5 rfl rfl rfl hv41_3_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 3 1 0 1 13 4 1 2 rfl rfl rfl hv41_3_1
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 3 0 1 2 14 11 1 5 rfl rfl rfl hv41_3_0
  · exact colGen (-1) 1 realFuse_four_one realFuse_five_one realFuse_four_two
      hE42 3 1 1 3 15 5 1 2 rfl rfl rfl hv41_3_1

/-- Entrywise reduction of `(4,2)` to the landed `(5,1)`. -/
private theorem entry42 (i j : Fin 16) :
    realFuseMatrix 4 2 i j = cv42 j * realFuseMatrix 5 1 i (sv42 j) :=
  entry_split (gtensorBasis quatBasis (towerBasis (-1 : ℝ) 2))
    (gtensorBasis (towerBasis (1 : ℝ) 3) (towerBasis (-1 : ℝ) 1))
    (matrixSuperBasis (towerBasis (1 : ℝ) 2) 1 1)
    realFuse_four_two realFuse_five_one cv42 sv42 hcol42 i j

/-! ### Branch `(4,2)`: the code certificate -/

/-- Packed row codes of the landed `realFuseMatrix 5 1`. -/
private def rows51 : Fin 16 → ℕ :=
  ![39367, 354303, 3188727, 28698543, 6564, 59076, 531684, 4785156,
    6567, 118125, 1063125, 4787343, 19684, 354312, 3188808, 14349636]

/-- Packed row codes of `realFuseMatrix 4 2` (the frozen certificate). -/
private def rows42 : Fin 16 → ℕ :=
  ![2188, 9605304, 1712421, 135, 495, 885735, 14355468, 732, 504,
    1417176, 14362029, 1461, 4375, 9585621, 3306744, 108]

/-- The `(4,2)` column signs, as value codes. -/
private def cc42 : Fin 16 → ℕ :=
  ![1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1]

private theorem cc42_ok : ∀ j : Fin 16, cc42 j = 1 ∨ cc42 j = 2 := by decide

private theorem cv42_code : ∀ j : Fin 16, cv42 j = fuseDecode (cc42 j) := by
  intro j; fin_cases j <;> rfl

/-- The landed `(5,1)` literal in decoder form. -/
private theorem dec51 (i j : Fin 16) :
    realFuseMatrix 5 1 i j = fuseDecode (rows51 i / 3 ^ (j : ℕ) % 3) := by
  rw [realFuseMatrix_5_1]
  fin_cases i <;> fin_cases j <;> rfl

/-- **The `(4,2)` table certificate**, checked by the kernel over all
`256` points. -/
private theorem master42 : ∀ i j : Fin 16,
    mulCode (cc42 j) (rows51 i / 3 ^ ((sv42 j : Fin 16) : ℕ) % 3)
      = rows42 i / 3 ^ (j : ℕ) % 3 := by decide

private theorem dec42 (i j : Fin 16) :
    realFuseMatrix 4 2 i j = fuseDecode (rows42 i / 3 ^ (j : ℕ) % 3) := by
  rw [entry42 i j, cv42_code j, dec51 i (sv42 j),
    mulCode_spec _ _ (cc42_ok j), master42 i j]

/-- **Value-pinning spec for `realFuse 4 2`** in the canonical frames of
`RealFuseMatrix`. -/
theorem realFuseMatrix_4_2 :
    realFuseMatrix 4 2
      = !![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0;
            0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1;
            0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0;
            0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  refine Matrix.ext fun i j => (dec42 i j).trans ?_
  fin_cases i <;> fin_cases j <;> rfl

/-! ### Branch `(4,6)`: the seed values on the floor-`1` frame -/

private theorem hv47_0_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 0 := by
  rw [towerBasis_one_zero]; exact val47_0_0

private theorem hv47_0_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 1 1))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 7 := by
  rw [towerBasis_one_one]; exact val47_0_1

private theorem hv47_1_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 3 := by
  rw [towerBasis_one_zero]; exact val47_1_0

private theorem hv47_1_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 4 := by
  rw [towerBasis_one_one]; exact val47_1_1

private theorem hv47_2_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 1 0))
      = (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 6 := by
  rw [towerBasis_one_zero]; exact val47_2_0

private theorem hv47_2_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 1 := by
  rw [towerBasis_one_one]; exact val47_2_1

private theorem hv47_3_0 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 1 0))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 5 := by
  rw [towerBasis_one_zero]; exact val47_3_0

private theorem hv47_3_1 :
    realFuse_four_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 1 1))
      = (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 2 := by
  rw [towerBasis_one_one]; exact val47_3_1

/-- The `(4,6)` composite in the shape `colGen` consumes. -/
private theorem hE46 :
    ∀ x : (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 2)).carrier,
    realFuse_four_six.toAlgEquiv x
      = realFuse_three_seven.toAlgEquiv
          ((matrixSuperOne
              ((divisionTower (-1 : ℝ) 3).gtensor
                (divisionTower (1 : ℝ) 1))).toAlgEquiv
            ((matrixSuperGtensor (divisionTower (-1 : ℝ) 3)
                (divisionTower (1 : ℝ) 1) 1 0).toAlgEquiv
              ((realFuse_four_seven.gtensorCongr
                  (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
                ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1)
                    (divisionTower (1 : ℝ) 1)).symm.toAlgEquiv
                  (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                      (towerFuse (1 : ℝ) 1 1).symm).toAlgEquiv x))))) :=
  fun _ => rfl

private def cv46 : Fin 16 → ℝ :=
  ![1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1]

private def sv46 : Fin 16 → Fin 16 :=
  ![0, 14, 1, 15, 6, 8, 7, 9, 12, 2, 13, 3, 10, 4, 11, 5]

private theorem hcol46 : ∀ j : Fin 16,
    realFuse_four_six.toAlgEquiv
        (gtensorBasis quatBasis (towerBasis (1 : ℝ) 2) j)
      = cv46 j • realFuse_three_seven.toAlgEquiv
          (gtensorBasis (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1)
            (sv46 j)) := by
  intro j
  fin_cases j
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 0 0 0 0 0 0 1 0 rfl rfl rfl hv47_0_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 0 1 0 1 1 14 1 7 rfl rfl rfl hv47_0_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 0 0 1 2 2 1 1 0 rfl rfl rfl hv47_0_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 0 1 1 3 3 15 1 7 rfl rfl rfl hv47_0_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 1 0 0 0 4 6 1 3 rfl rfl rfl hv47_1_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 1 1 0 1 5 8 (-1) 4 rfl rfl rfl hv47_1_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 1 0 1 2 6 7 1 3 rfl rfl rfl hv47_1_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 1 1 1 3 7 9 (-1) 4 rfl rfl rfl hv47_1_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 2 0 0 0 8 12 1 6 rfl rfl rfl hv47_2_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 2 1 0 1 9 2 (-1) 1 rfl rfl rfl hv47_2_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 2 0 1 2 10 13 1 6 rfl rfl rfl hv47_2_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 2 1 1 3 11 3 (-1) 1 rfl rfl rfl hv47_2_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 3 0 0 0 12 10 (-1) 5 rfl rfl rfl hv47_3_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 3 1 0 1 13 4 (-1) 2 rfl rfl rfl hv47_3_1
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 3 0 1 2 14 11 (-1) 5 rfl rfl rfl hv47_3_0
  · exact colGen 1 (-1) realFuse_four_seven realFuse_three_seven
      realFuse_four_six hE46 3 1 1 3 15 5 (-1) 2 rfl rfl rfl hv47_3_1

/-- Entrywise reduction of `(4,6)` to the landed `(3,7)`. -/
private theorem entry46 (i j : Fin 16) :
    realFuseMatrix 4 6 i j = cv46 j * realFuseMatrix 3 7 i (sv46 j) :=
  entry_split (gtensorBasis quatBasis (towerBasis (1 : ℝ) 2))
    (gtensorBasis (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1))
    (matrixSuperBasis (towerBasis (-1 : ℝ) 2) 1 1)
    realFuse_four_six realFuse_three_seven cv46 sv46 hcol46 i j

/-! ### Branch `(4,6)`: the code certificate -/

/-- Packed row codes of the landed `realFuseMatrix 3 7`. -/
private def rows37 : Fin 16 → ℕ :=
  ![19684, 177156, 1594404, 14349636, 6564, 59076, 531684, 4785156,
    13125, 59103, 531927, 9568125, 39367, 177165, 1594485, 28698543]

/-- Packed row codes of `realFuseMatrix 4 6` (the frozen certificate). -/
private def rows46 : Fin 16 → ℕ :=
  ![4375, 9605304, 3247695, 108, 495, 1417176, 28704375, 732, 252,
    1240029, 14355468, 735, 2188, 9585621, 1653372, 135]

private def cc46 : Fin 16 → ℕ :=
  ![1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2]

private theorem cc46_ok : ∀ j : Fin 16, cc46 j = 1 ∨ cc46 j = 2 := by decide

private theorem cv46_code : ∀ j : Fin 16, cv46 j = fuseDecode (cc46 j) := by
  intro j; fin_cases j <;> rfl

private theorem dec37 (i j : Fin 16) :
    realFuseMatrix 3 7 i j = fuseDecode (rows37 i / 3 ^ (j : ℕ) % 3) := by
  rw [realFuseMatrix_3_7]
  fin_cases i <;> fin_cases j <;> rfl

/-- **The `(4,6)` table certificate**, checked by the kernel over all
`256` points. -/
private theorem master46 : ∀ i j : Fin 16,
    mulCode (cc46 j) (rows37 i / 3 ^ ((sv46 j : Fin 16) : ℕ) % 3)
      = rows46 i / 3 ^ (j : ℕ) % 3 := by decide

private theorem dec46 (i j : Fin 16) :
    realFuseMatrix 4 6 i j = fuseDecode (rows46 i / 3 ^ (j : ℕ) % 3) := by
  rw [entry46 i j, cv46_code j, dec37 i (sv46 j),
    mulCode_spec _ _ (cc46_ok j), master46 i j]

/-- **Value-pinning spec for `realFuse 4 6`** in the canonical frames of
`RealFuseMatrix`. -/
theorem realFuseMatrix_4_6 :
    realFuseMatrix 4 6
      = !![1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0;
            0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1;
            0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
            0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
            0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  refine Matrix.ext fun i j => (dec46 i j).trans ?_
  fin_cases i <;> fin_cases j <;> rfl

/-! ### The two released transposes -/

/-- **Deliverable `(2,4)`**, discharged from the forward `(4,2)`. -/
theorem realFuseMatrix_2_4 :
    realFuseMatrix 2 4
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] :=
  realFuseMatrix_2_4_of_forward realFuseMatrix_4_2

/-- **Deliverable `(6,4)`**, discharged from the forward `(4,6)`. -/
theorem realFuseMatrix_6_4 :
    realFuseMatrix 6 4
      = !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
            0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
            0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
            0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
            0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
            0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
            0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
            0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] :=
  realFuseMatrix_6_4_of_forward realFuseMatrix_4_6

end Superfusion
