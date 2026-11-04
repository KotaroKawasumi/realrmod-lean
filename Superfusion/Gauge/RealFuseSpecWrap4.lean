/-
Superfusion / Gauge / RealFuseSpecWrap4

M15 semantic-bridge GROUP C (closing part): the two `64 × 64` **doubly
ampliated wrap pairs** `(3,3)` and `(5,5)` — the last two branches of the
floor-`4`-certificate family, and the only two whose ampliation tail runs
through a `1|1`-target seed (`realFuse_four_two` / `realFuse_four_six`)
instead of a `1|0`-target one, so that every column carries **four**
nonzero entries rather than two.

**Landed here**

* `realFuseMatrix_5_5` (`64 × 64`), through the field-generic
  `towerFourQuatSuper` and `realFuse_four_six`,
* `realFuseMatrix_3_3` (`64 × 64`), through the `ε = -1` composite
  certificate `divisionTowerNegFourQuatSuper` and `realFuse_four_two`.

Both corners are their own Koszul transposes, so no conditional
transpose is released by them.

**The machinery** — exactly the three items that `RealFuseSpecWrap3`
listed as still missing.

1. `seed46` / `seed42` — the sixteen element-level values of
   `realFuse_four_six` on `quatBasis e ᵍ⊗ towerBasis 1 2 v`, and of
   `realFuse_four_two` on `quatBasis e ᵍ⊗ towerBasis (-1) 2 v`.  Each is
   one `gtensorAssoc`/`matrixSuperOne` composition away from `val47_*` /
   `val41_*` together with `RealFuseSpecPeel`'s `c3_7_*` / `c1_5_*`.
   The `(4,2)` side additionally has to cross the Koszul braiding, since
   `realFuse_five_one` is `realFuse_transpose realFuse_one_five` and only
   the `(1,5)` direction is pinned; `c51` carries that sign (through
   `gtensorComm_tmul_of_mem` and `sgn_eq_neg_one_uzpow`, never by
   unfolding an inverse).
2. `termG2` — the two-entry variant of `RealFuseSpecWrap3.termG`.  The
   tail now ends in `matrixSuperComp T 1 1 1 1`, not `… 1 1 1 0`, so
   `Matrix.single_add` splits the inner value and each certificate entry
   contributes two frame terms; with the two entries of the floor-`4`
   certificate that is four terms per column.
3. `fG2` — the seed on *signed* quaternion literals, two-entry version.

`tfuseK` / `tfuseKsymm`, the frame dictionaries and the `congrArg`-only
assembly discipline are copied verbatim from `RealFuseSpecWrap3`
(`private`, hence not importable).

**The `64 × 64` closing step** follows `RealFuseSpecPeel3`: there is no
`N²` tactic goal anywhere.  `entry55` / `entry33` turn
`realFuseMatrix a b i j` into a four-term sum generically in `(i, j)`
(one `realFuseMatrix_apply`, one instance of `hcol55` / `hcol33`);
`coefs55` / `coefs33` rewrite the four real sign vectors as
`fuseDecode ∘ kᵥ` for base-3 code vectors (one `fin_cases j`); and
`master55` / `master33` check, in `ℕ`, all `4096` points with a single
kernel `decide` — both the disjointness (the four target-index vectors
of a column are pairwise distinct) and the base-3 digit of the frozen
`fuseRows_*` literal.

The packed literals `fuseRows_5_5` / `fuseRows_3_3` are verbatim from
`scripts/certgen/out/lean_literals/fuse_5_5.txt` / `fuse_3_3.txt`.

`#print axioms realFuseMatrix_5_5` and `#print axioms realFuseMatrix_3_3`
report only `propext`, `Classical.choice`, `Quot.sound`.

Design record: docs/real-trivialization-design.md (M15 track, semantic
bridge, step 8).
-/
import Superfusion.Gauge.RealFuseSpecWrap3
import Batteries.Tactic.OpenPrivate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Superfusion

open Module TensorProduct GradedTensorProduct Quaternion

open private q1 q1_def mem_q1 towerFuse_basis hmem_tone
  val41_0_0 val41_0_1 val41_1_0 val41_1_1 val41_2_0 val41_2_1 val41_3_0 val41_3_1
  val47_0_0 val47_0_1 val47_1_0 val47_1_1 val47_2_0 val47_2_1 val47_3_0 val47_3_1
  from Superfusion.Gauge.RealFuseSpecQuat

open private qi qj qk n1 nqi nqj nqk offM diaM
  sb_p_0 sb_p_1 sb_p_2 sb_p_3 sb_m_0 sb_m_1 sb_m_2 sb_m_3
  towerBasis_one_zero towerBasis_one_one superRefl_apply
  qv4_0 qv4_1 qv4_2 qv4_3 qv4_4 qv4_5 qv4_6 qv4_7
  qv4_8 qv4_9 qv4_10 qv4_11 qv4_12 qv4_13 qv4_14 qv4_15
  from Superfusion.Gauge.RealFuseSpecWrap

open private nqv4_0 nqv4_1 nqv4_2 nqv4_3 nqv4_4 nqv4_5 nqv4_6 nqv4_7
  nqv4_8 nqv4_9 nqv4_10 nqv4_11 nqv4_12 nqv4_13 nqv4_14 nqv4_15
  msg_single' matrixSuperMap_single' matrixSuperComp_single'
  from Superfusion.Gauge.RealFuseSpecWrap2

open private c3_7_0 c3_7_1 c3_7_2 c3_7_3 c3_7_4 c3_7_5 c3_7_6 c3_7_7
  c3_7_8 c3_7_9 c3_7_10 c3_7_11 c3_7_12 c3_7_13 c3_7_14 c3_7_15
  c1_5_0 c1_5_1 c1_5_2 c1_5_3 c1_5_4 c1_5_5 c1_5_6 c1_5_7
  c1_5_8 c1_5_9 c1_5_10 c1_5_11 c1_5_12 c1_5_13 c1_5_14 c1_5_15
  from Superfusion.Gauge.RealFuseSpecPeel

/-! ### Generic scalar/entry plumbing (copied from `RealFuseSpecWrap3`) -/

/-- A scalar pulls out of the left slot of `ᵍ⊗ₜ`. -/
private theorem gtmul_smul_left {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B] (𝒜 : ZMod 2 → Submodule ℝ A)
    (ℬ : ZMod 2 → Submodule ℝ B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (c : ℝ) (x : A) (y : B) :
    ((c • x) ᵍ⊗ₜ[ℝ] y : 𝒜 ᵍ⊗[ℝ] ℬ) = c • (x ᵍ⊗ₜ[ℝ] y) := by
  show GradedTensorProduct.of ℝ 𝒜 ℬ ((c • x) ⊗ₜ[ℝ] y) = _
  rw [← TensorProduct.smul_tmul', map_smul]

/-- Scalars pass into the entry of a single-entry matrix. -/
private theorem single_smulG {P : SuperAlgebra ℝ} {p q : ℕ} (t : ℝ)
    (r c : Fin p ⊕ Fin q) (v : P.carrier) :
    (t • (Matrix.single r c v : (P.matrixSuper p q).carrier))
      = Matrix.single r c (t • v) := by
  show (t • (Matrix.single r c v :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) P.carrier))
    = Matrix.single r c (t • v)
  refine Matrix.ext fun x y => ?_
  rw [Matrix.smul_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

/-- The same, taking the single-entry shape as a hypothesis. -/
private theorem smul_dstG {P : SuperAlgebra ℝ} {p q : ℕ} (t : ℝ)
    {r c : Fin p ⊕ Fin q} {v : P.carrier} {M : (P.matrixSuper p q).carrier}
    (hM : M = Matrix.single r c v) : t • M = Matrix.single r c (t • v) := by
  rw [hM]; exact single_smulG t r c v

/-- The `ℤ`-scalar of the Koszul twist, converted to a real coefficient. -/
private theorem zsmul_dstS {P : SuperAlgebra ℝ} (n : ℤ) {p q : ℕ}
    (r c : Fin p ⊕ Fin q) (t : ℝ) (v : P.carrier) {κ : ℝ}
    (h : ((n : ℝ)) * t = κ) :
    n • (Matrix.single r c (t • v) : (P.matrixSuper p q).carrier)
      = Matrix.single r c (κ • v) := by
  have e1 : n • (Matrix.single r c (t • v) : (P.matrixSuper p q).carrier)
      = ((n : ℝ)) • (Matrix.single r c (t • v) : (P.matrixSuper p q).carrier) :=
    (Int.cast_smul_eq_zsmul ℝ n _).symm
  rw [e1, single_smulG, smul_smul, h]

/-! ### The tower fusion at a named index -/

private theorem tfuseK (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a)) (j : Fin (2 ^ b))
    (k : Fin (2 ^ (a + b))) (h : (k : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)) :
    (towerFuse ε a b).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j))
      = towerBasis ε (a + b) k := by
  rw [towerFuse_basis ε a b i j]
  congr 1
  exact (Fin.ext h).symm

private theorem tfuseKsymm (ε : ℝ) (a b : ℕ) (i : Fin (2 ^ a)) (j : Fin (2 ^ b))
    (k : Fin (2 ^ (a + b))) (h : (k : ℕ) = (i : ℕ) + 2 ^ a * (j : ℕ)) :
    (towerFuse ε a b).symm.toAlgEquiv (towerBasis ε (a + b) k)
      = GradedTensorProduct.tmul (𝒜 := (divisionTower ε a).grading)
          (ℬ := (divisionTower ε b).grading) ℝ
          (towerBasis ε a i) (towerBasis ε b j) := by
  show ((towerFuse ε a b).toAlgEquiv).symm _ = _
  rw [AlgEquiv.symm_apply_eq]
  exact (tfuseK ε a b i j k h).symm

/-! ### The associator and the `M_{1|0}` unitor -/

/-- The associator inverse on nested pure tensors (no sign). -/
private theorem gtAssocSymm (P Q R : SuperAlgebra ℝ)
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

private theorem msOneSymmSingle (P : SuperAlgebra ℝ) (v : P.carrier) :
    (matrixSuperOne P).symm.toAlgEquiv v
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v := by
  refine Matrix.ext fun r c => ?_
  show v = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v r c
  cases r with
  | inr r => exact r.elim0
  | inl r =>
    cases c with
    | inr c => exact c.elim0
    | inl c =>
      rw [Subsingleton.elim r 0, Subsingleton.elim c 0,
        Matrix.single_apply_same]

/-- `matrixSuperOne` in the forward direction on a single entry. -/
private theorem msOneSingle (P : SuperAlgebra ℝ) (v : P.carrier) :
    (matrixSuperOne P).toAlgEquiv
        (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0) v) = v := by
  rw [← msOneSymmSingle P v]
  exact (matrixSuperOne P).toAlgEquiv.apply_symm_apply v

/-! ### The two shapes of a floor-`4` certificate value -/

private theorem offM_eq (a b : ℍ[ℝ]) : offM a b
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) a
      + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) b := rfl

private theorem diaM_eq (a b : ℍ[ℝ]) : diaM a b
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) a
      + Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) b := rfl

/-! ### The floor-`1` frame -/

private theorem tb1z (ε : ℝ) :
    towerBasis ε 1 0 = (1 : (divisionTower ε 1).carrier) := towerBasis_one_zero ε

private theorem tb1g (ε : ℝ) : towerBasis ε 1 1 = q1 ε := towerBasis_one_one ε

/-- Distributing a scalar over a two-term frame expansion. -/
private theorem smul2 {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (t s1 s2 u1 u2 : ℝ) (X Y : M) (h1 : t * s1 = u1) (h2 : t * s2 = u2) :
    t • (s1 • X + s2 • Y) = u1 • X + u2 • Y := by
  rw [smul_add, smul_smul, smul_smul, h1, h2]

/-- The Koszul twist of `matrixSuperGtensor` is trivial on the unique
column of a `1|0` matrix. -/
private theorem sgn10 (jw : ZMod 2) :
    ((sgn (sumParity 1 0 (Sum.inl 0 : Fin 1 ⊕ Fin 0) * jw) : ℤˣ) : ℤ) = 1 := by
  simp [sumParity, sgn]

/-- Distributing an integer scalar over a sum. -/
private theorem zsmul_add2 {M : Type*} [AddCommGroup M] (n : ℤ) (X Y : M) :
    n • (X + Y) = n • X + n • Y := smul_add n X Y

/-! ### Frame dictionaries -/

/-- The source frame of `M_{1|0}(D)`, generic in the index. -/
private theorem d3g (ε : ℝ) (idx : Fin 8) :
    matrixSuperBasis (towerBasis ε 3) 1 0 idx
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (towerBasis ε 3 idx) :=
  matrixSuperBasis_apply_pair (towerBasis ε 3) 1 0 (Sum.inl 0) (Sum.inl 0) idx

/-! ### The seed on signed quaternion literals, two-entry version -/

private theorem fG2 {R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (quatEvenSuper.gtensor R) (T.matrixSuper 1 1))
    (σ t1' t2' : ℝ) {e : Fin 4} {t1 t2 : ℝ} {bT : Basis (Fin 4) ℝ T.carrier}
    {K1 K2 : Fin 16} {w : R.carrier} {q : ℍ[ℝ]}
    {ra ca rb cb : Fin 1 ⊕ Fin 1} {e1 e2 : Fin 4}
    (hb : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := R.grading) ℝ (quatBasis e) w)
          = t1 • matrixSuperBasis bT 1 1 K1 + t2 • matrixSuperBasis bT 1 1 K2)
    (hd1 : matrixSuperBasis bT 1 1 K1 = Matrix.single ra ca (bT e1))
    (hd2 : matrixSuperBasis bT 1 1 K2 = Matrix.single rb cb (bT e2))
    (hq : σ • quatBasis e = q) (ht1 : σ * t1 = t1') (ht2 : σ * t2 = t2') :
    F.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := R.grading) ℝ q w)
      = Matrix.single ra ca (t1' • bT e1)
        + Matrix.single rb cb (t2' • bT e2) := by
  have h0 : GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := R.grading) ℝ q w
      = σ • GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (quatBasis e) w := by
    rw [← hq]
    exact gtmul_smul_left quatEvenSuper.grading R.grading σ (quatBasis e) w
  refine (congrArg (fun z => F.toAlgEquiv z) h0).trans ?_
  refine (map_smul F.toAlgEquiv σ _).trans ?_
  refine (congrArg (fun z => σ • z) hb).trans ?_
  refine (smul2 σ t1 t2 t1' t2' _ _ ht1 ht2).trans ?_
  exact congrArg₂ (fun x y => x + y) (smul_dstG t1' hd1) (smul_dstG t2' hd2)

/-! ### The doubly ampliated tail, on one certificate entry -/

private theorem termG2 {R T : SuperAlgebra ℝ}
    (F : SuperAlgEquiv (quatEvenSuper.gtensor R) (T.matrixSuper 1 1))
    {jw : ZMod 2} {w : R.carrier} (hw : w ∈ R.grading jw)
    (r c : Fin 1 ⊕ Fin 1) {q : ℍ[ℝ]} {t1 t2 : ℝ}
    {bT : Basis (Fin 4) ℝ T.carrier} {e1 e2 : Fin 4}
    {ra ca rb cb : Fin 1 ⊕ Fin 1}
    (hF : F.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := R.grading) ℝ q w)
          = Matrix.single ra ca (t1 • bT e1)
            + Matrix.single rb cb (t2 • bT e2))
    {κ1 κ2 : ℝ} {I1 I2 : Fin 64}
    (hI1 : matrixSuperBasis bT 2 2 I1
          = Matrix.single (collapseIndexEquiv 1 1 1 1 (r, ra))
              (collapseIndexEquiv 1 1 1 1 (c, ca)) (bT e1))
    (hI2 : matrixSuperBasis bT 2 2 I2
          = Matrix.single (collapseIndexEquiv 1 1 1 1 (r, rb))
              (collapseIndexEquiv 1 1 1 1 (c, cb)) (bT e2))
    (hκ1 : (((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) : ℝ) * t1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) : ℝ) * t2 = κ2) :
    ((matrixSuperGtensor quatEvenSuper R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = κ1 • matrixSuperBasis bT 2 2 I1 + κ2 • matrixSuperBasis bT 2 2 I2 := by
  have h1 := msg_single' quatEvenSuper R 1 1 r c q hw
  have h2 : (F.matrixSuper 1 1).toAlgEquiv
        (Matrix.single r c
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := R.grading) ℝ q w))
      = Matrix.single r c (Matrix.single ra ca (t1 • bT e1))
        + Matrix.single r c (Matrix.single rb cb (t2 • bT e2)) :=
    (matrixSuperMap_single' F 1 1 r c _).trans
      ((congrArg (fun z => Matrix.single r c z) hF).trans
        (Matrix.single_add r c _ _))
  have h3a := matrixSuperComp_single' T 1 1 1 1 r c ra ca (t1 • bT e1)
  have h3b := matrixSuperComp_single' T 1 1 1 1 r c rb cb (t2 • bT e2)
  have e1' : ((matrixSuperGtensor quatEvenSuper R 1 1).trans
        ((F.matrixSuper 1 1).trans (matrixSuperComp T 1 1 1 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := R.grading) ℝ (Matrix.single r c q) w)
      = (matrixSuperComp T 1 1 1 1).toAlgEquiv
          ((F.matrixSuper 1 1).toAlgEquiv
            ((matrixSuperGtensor quatEvenSuper R 1 1).toAlgEquiv
              (GradedTensorProduct.tmul
                (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
                (ℬ := R.grading) ℝ (Matrix.single r c q) w))) := rfl
  refine e1'.trans ?_
  refine (congrArg (fun z => (matrixSuperComp T 1 1 1 1).toAlgEquiv
      ((F.matrixSuper 1 1).toAlgEquiv z)) h1).trans ?_
  refine (congrArg (matrixSuperComp T 1 1 1 1).toAlgEquiv
      ((map_zsmul (F.matrixSuper 1 1).toAlgEquiv _ _).trans
        (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
          h2))).trans ?_
  refine ((map_zsmul (matrixSuperComp T 1 1 1 1).toAlgEquiv _ _).trans
      (congrArg (fun z => ((sgn (sumParity 1 1 c * jw) : ℤˣ) : ℤ) • z)
        ((map_add (matrixSuperComp T 1 1 1 1).toAlgEquiv _ _).trans
          (congrArg₂ (fun x y => x + y) h3a h3b)))).trans ?_
  refine (zsmul_add2 _ _ _).trans ?_
  rw [smul_dstG κ1 hI1, smul_dstG κ2 hI2]
  exact congrArg₂ (fun x y => x + y)
    (zsmul_dstS _ _ _ t1 _ hκ1) (zsmul_dstS _ _ _ t2 _ hκ2)

/-! ### The `(4,6)` seed: `ℍ ᵍ⊗ Cl_{2,0} → M_{1|1}(Cl_{0,2})` -/

private theorem unfold46
    (x : (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 2)).carrier) :
    realFuse_four_six.toAlgEquiv x
      = realFuse_three_seven.toAlgEquiv
          ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv
            ((matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv
              ((realFuse_four_seven.gtensorCongr
                  (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
                ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1)
                    (divisionTower (1 : ℝ) 1)).symm.toAlgEquiv
                  (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                      (towerFuse (1 : ℝ) 1 1).symm).toAlgEquiv x))))) := rfl

private theorem seed46 {e : Fin 4} {v : Fin 4} (v1 v2 : Fin 2)
    (hv : (v : ℕ) = (v1 : ℕ) + 2 ^ 1 * (v2 : ℕ))
    {w1 : (divisionTower (1 : ℝ) 1).carrier}
    (hw1 : towerBasis (1 : ℝ) 1 v1 = w1)
    {jw2 : ZMod 2}
    (hw2 : towerBasis (1 : ℝ) 1 v2 ∈ (divisionTower (1 : ℝ) 1).grading jw2)
    {t : ℝ} {idx : Fin 8}
    (hb : realFuse_four_seven.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis e) w1)
          = t • matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 idx)
    (hd : matrixSuperBasis (towerBasis (-1 : ℝ) 3) 1 0 idx
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (towerBasis (-1 : ℝ) 3 idx))
    {s1 s2 : ℝ} {J1 J2 : Fin 16}
    (hcol : (peelFuse (baseFuseR 2)).toAlgEquiv
            (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
              (B := divisionTower (1 : ℝ) 1)
              (towerBasis (-1) 3) (towerBasis 1 1) (finProdFinEquiv (idx, v2)))
          = s1 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
              (towerBasis (-1) 2) 1 1 J1
            + s2 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
              (towerBasis (-1) 2) 1 1 J2)
    {u1 u2 : ℝ} (hu1 : t * s1 = u1) (hu2 : t * s2 = u2) :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis e)
          (towerBasis (1 : ℝ) 2 v))
      = u1 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 J1
        + u2 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 J2 := by
  have hA : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        (towerFuse (1 : ℝ) 1 1).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis e)
          (towerBasis (1 : ℝ) 2 v))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (1 : ℝ) 1).gtensor
            (divisionTower (1 : ℝ) 1)).grading) ℝ (quatBasis e)
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 1).grading)
            (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
            (towerBasis (1 : ℝ) 1 v1) (towerBasis (1 : ℝ) 1 v2)) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl quatEvenSuper)
      (towerFuse (1 : ℝ) 1 1).symm (quatBasis e) (towerBasis (1 : ℝ) 2 v)).trans ?_
    rw [superRefl_apply]
    exact congrArg
      (fun z => GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := ((divisionTower (1 : ℝ) 1).gtensor
          (divisionTower (1 : ℝ) 1)).grading) ℝ (quatBasis e) z)
      (tfuseKsymm (1 : ℝ) 1 1 v1 v2 v hv)
  have hB : (realFuse_four_seven.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (1 : ℝ) 1)).grading)
          (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (1 : ℝ) 1).grading) ℝ (quatBasis e)
            (towerBasis (1 : ℝ) 1 v1))
          (towerBasis (1 : ℝ) 1 v2))
      = t • GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 0) (realRep 3).grading)
          (ℬ := (realRep 7).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
            (towerBasis (-1 : ℝ) 3 idx))
          (towerBasis (1 : ℝ) 1 v2) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul realFuse_four_seven
      (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1)) _ _).trans ?_
    rw [superRefl_apply, hw1, hb, hd]
    exact gtmul_smul_left _ _ t _ _
  have hC : (matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 0) (realRep 3).grading)
          (ℬ := (realRep 7).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
            (towerBasis (-1 : ℝ) 3 idx))
          (towerBasis (1 : ℝ) 1 v2))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
            (ℬ := (realRep 7).grading) ℝ (towerBasis (-1 : ℝ) 3 idx)
            (towerBasis (1 : ℝ) 1 v2)) := by
    refine (msg_single' (realRep 3) (realRep 7) 1 0 (Sum.inl 0) (Sum.inl 0)
      (towerBasis (-1 : ℝ) 3 idx) hw2).trans ?_
    rw [sgn10 jw2, one_zsmul]
  have hD : realFuse_three_seven.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 3).grading)
          (ℬ := (realRep 7).grading) ℝ (towerBasis (-1 : ℝ) 3 idx)
          (towerBasis (1 : ℝ) 1 v2))
      = s1 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 J1
        + s2 • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 J2 := by
    refine Eq.trans ?_ hcol
    exact congrArg (fun z => (peelFuse (baseFuseR 2)).toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (1 : ℝ) 1)
        idx v2).symm
  refine (unfold46 _).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv
      ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv
        ((matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv
          ((realFuse_four_seven.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv
            ((gtensorAssoc quatEvenSuper (divisionTower (1 : ℝ) 1)
                (divisionTower (1 : ℝ) 1)).symm.toAlgEquiv z))))) hA).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv
      ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv
        ((matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv
          ((realFuse_four_seven.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 1))).toAlgEquiv z))))
      (gtAssocSymm quatEvenSuper (divisionTower (1 : ℝ) 1)
        (divisionTower (1 : ℝ) 1) (quatBasis e) (towerBasis (1 : ℝ) 1 v1)
        (towerBasis (1 : ℝ) 1 v2))).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv
      ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv
        ((matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv z)))
      hB).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv
      ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv z))
      (map_smul (matrixSuperGtensor (realRep 3) (realRep 7) 1 0).toAlgEquiv
        t _)).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv
      ((matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv (t • z)))
      hC).trans ?_
  refine (congrArg (fun z => realFuse_three_seven.toAlgEquiv z)
      ((map_smul (matrixSuperOne ((realRep 3).gtensor (realRep 7))).toAlgEquiv
        t _).trans (congrArg (fun z => t • z)
          (msOneSingle ((realRep 3).gtensor (realRep 7)) _)))).trans ?_
  refine ((map_smul realFuse_three_seven.toAlgEquiv t _).trans
      (congrArg (fun z => t • z) hD)).trans ?_
  exact smul2 t s1 s2 u1 u2 _ _ hu1 hu2

/-! ### The `(5,5)` branch (`Cl_{3,0} ᵍ⊗ Cl_{3,0}`, `ε = +1`) -/

private theorem unfold55
    (x : ((divisionTower (1 : ℝ) 3).gtensor (divisionTower (1 : ℝ) 3)).carrier) :
    realFuse_five_five.toAlgEquiv x
      = ((matrixSuperGtensor quatEvenSuper (divisionTower (1 : ℝ) 2) 1 1).trans
          ((realFuse_four_six.matrixSuper 1 1).trans
            (matrixSuperComp (divisionTower (-1 : ℝ) 2) 1 1 1 1))).toAlgEquiv
          (((towerFourQuatSuper ℝ).gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 2))).toAlgEquiv
            ((towerFuse (1 : ℝ) 4 2).symm.toAlgEquiv
              ((towerFuse (1 : ℝ) 3 3).toAlgEquiv x))) := rfl

private theorem split55 (i j : Fin 8) (u : Fin 16) (v : Fin 4) (k : Fin 64)
    (h1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (h2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ)) :
    (towerFuse (1 : ℝ) 4 2).symm.toAlgEquiv
        ((towerFuse (1 : ℝ) 3 3).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 3).grading)
            (ℬ := (divisionTower (1 : ℝ) 3).grading) ℝ
            (towerBasis (1 : ℝ) 3 i) (towerBasis (1 : ℝ) 3 j)))
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (1 : ℝ) 4).grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
          (towerBasis (1 : ℝ) 4 u) (towerBasis (1 : ℝ) 2 v) := by
  rw [tfuseK (1 : ℝ) 3 3 i j k h1]
  exact tfuseKsymm (1 : ℝ) 4 2 u v k h2

private theorem colEngine55 (i j : Fin 8) (u : Fin 16) (v : Fin 4) (k : Fin 64)
    (hk1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (hk2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ))
    {jw : ZMod 2} {w : (divisionTower (1 : ℝ) 2).carrier}
    (hwv : towerBasis (1 : ℝ) 2 v = w)
    (hw : w ∈ (divisionTower (1 : ℝ) 2).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : ℍ[ℝ]}
    (hcert : (towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 u)
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    {ta1 ta2 tb1 tb2 : ℝ} {ea1 ea2 eb1 eb2 : Fin 4}
    {raa caa rab cab rba cba rbb cbb : Fin 1 ⊕ Fin 1}
    (hFa : realFuse_four_six.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ qa w)
          = Matrix.single raa caa (ta1 • towerBasis (-1 : ℝ) 2 ea1)
            + Matrix.single rab cab (ta2 • towerBasis (-1 : ℝ) 2 ea2))
    (hFb : realFuse_four_six.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ qb w)
          = Matrix.single rba cba (tb1 • towerBasis (-1 : ℝ) 2 eb1)
            + Matrix.single rbb cbb (tb2 • towerBasis (-1 : ℝ) 2 eb2))
    {κ1 κ2 κ3 κ4 : ℝ} {I1 I2 I3 I4 : Fin 64}
    (hI1 : matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, raa))
            (collapseIndexEquiv 1 1 1 1 (c1, caa)) (towerBasis (-1 : ℝ) 2 ea1))
    (hI2 : matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, rab))
            (collapseIndexEquiv 1 1 1 1 (c1, cab)) (towerBasis (-1 : ℝ) 2 ea2))
    (hI3 : matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I3
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rba))
            (collapseIndexEquiv 1 1 1 1 (c2, cba)) (towerBasis (-1 : ℝ) 2 eb1))
    (hI4 : matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I4
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rbb))
            (collapseIndexEquiv 1 1 1 1 (c2, cbb)) (towerBasis (-1 : ℝ) 2 eb2))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta2 = κ2)
    (hκ3 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb1 = κ3)
    (hκ4 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb2 = κ4) :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) (finProdFinEquiv (i, j)))
      = (κ1 • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I1
          + κ2 • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I2)
        + (κ3 • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I3
          + κ4 • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 I4) := by
  refine (congrArg (fun z => realFuse_five_five.toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) i j)).trans ?_
  refine (unfold55 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 2) 1 1).trans
        ((realFuse_four_six.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 2) 1 1 1 1))).toAlgEquiv
      (((towerFourQuatSuper ℝ).gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 2))).toAlgEquiv z))
      (split55 i j u v k hk1 hk2)).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 2) 1 1).trans
        ((realFuse_four_six.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 2) 1 1 1 1))).toAlgEquiv z)
      (SuperAlgEquiv.gtensorCongr_tmul (towerFourQuatSuper ℝ)
        (SuperAlgEquiv.refl (divisionTower (1 : ℝ) 2))
        (towerBasis (1 : ℝ) 4 u) (towerBasis (1 : ℝ) 2 v))).trans ?_
  have e3 : GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
        (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ
        ((towerFourQuatSuper ℝ).toAlgEquiv (towerBasis (1 : ℝ) 4 u))
        ((SuperAlgEquiv.refl (divisionTower (1 : ℝ) 2)).toAlgEquiv
          (towerBasis (1 : ℝ) 2 v))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (Matrix.single r2 c2 qb) w := by
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
      (divisionTower (1 : ℝ) 2).grading _ _ _
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 2) 1 1).trans
        ((realFuse_four_six.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 2) 1 1 1 1))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor quatEvenSuper
        (divisionTower (1 : ℝ) 2) 1 1).trans
        ((realFuse_four_six.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (-1 : ℝ) 2) 1 1 1 1))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG2 realFuse_four_six hw r1 c1 hFa hI1 hI2 hκ1 hκ2)
    (termG2 realFuse_four_six hw r2 c2 hFb hI3 hI4 hκ3 hκ4)


/-! ### The decoder-side transport lemmas (as in `RealFuseSpecPeel3`) -/

private theorem fuseDecode_zero : fuseDecode 0 = 0 := rfl

/-- Selecting with a real `0/1` indicator is selecting the code. -/
private theorem dmul (c : ℕ) (P : Prop) [Decidable P] :
    fuseDecode c * (if P then (1 : ℝ) else 0)
      = fuseDecode (if P then c else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero, fuseDecode_zero]

/-- Left-biased merge of two value codes. -/
private def dpick (a b : ℕ) : ℕ := if a = 0 then b else a

/-- Adding two decoded codes, one of which is `0`, is decoding their
merge.  This is the only place where "at most one column hits row `i`"
is used, and it is supplied point-by-point by the `master` tables. -/
private theorem dpick_add (a b : ℕ) (h : a = 0 ∨ b = 0) :
    fuseDecode a + fuseDecode b = fuseDecode (dpick a b) := by
  unfold dpick
  rcases h with h | h
  · subst h; rw [if_pos rfl, fuseDecode_zero, zero_add]
  · subst h
    rw [fuseDecode_zero, add_zero]
    by_cases ha : a = 0
    · rw [if_pos ha, ha]
    · rw [if_neg ha]


/-! ### The `(4,2)` seed: `ℍ ᵍ⊗ Cl_{0,2} → M_{1|1}(Cl_{2,0})`

Same shape as `seed46`, but the last leg is `realFuse_five_one`, a
Koszul transpose of the pinned `(1,5)` direction, so a braiding sign
appears (`c51`). -/

private theorem unfold42
    (x : (quatEvenSuper.gtensor (divisionTower (-1 : ℝ) 2)).carrier) :
    realFuse_four_two.toAlgEquiv x
      = realFuse_five_one.toAlgEquiv
          ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv
            ((matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv
              ((realFuse_four_one.gtensorCongr
                  (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
                ((gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 1)
                    (divisionTower (-1 : ℝ) 1)).symm.toAlgEquiv
                  (((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
                      (towerFuse (-1 : ℝ) 1 1).symm).toAlgEquiv x))))) := rfl

/-- The Koszul transpose, unfolded (no sign bookkeeping yet). -/
private theorem fuse51comm (z : ((realRep 5).gtensor (realRep 1)).carrier) :
    realFuse_five_one.toAlgEquiv z
      = realFuse_one_five.toAlgEquiv
          ((gtensorComm (realRep 5) (realRep 1)).toAlgEquiv z) := rfl

/-- Distributing an integer scalar over a two-term frame expansion. -/
private theorem zsmul2 {M : Type*} [AddCommGroup M] [Module ℝ M] (n : ℤ)
    (s1 s2 r1 r2 : ℝ) (X Y : M) (h1 : (n : ℝ) * s1 = r1)
    (h2 : (n : ℝ) * s2 = r2) :
    n • (s1 • X + s2 • Y) = r1 • X + r2 • Y := by
  rw [← Int.cast_smul_eq_zsmul ℝ n]
  exact smul2 (n : ℝ) s1 s2 r1 r2 X Y h1 h2

/-- **The `(5,1)` column values from the `(1,5)` ones**: cross the
braiding, and carry its sign into the two coefficients. -/
private theorem c51 (idx : Fin 8) (v2 : Fin 2) {pidx jw2 : ZMod 2}
    (hpi : towerBasis (1 : ℝ) 3 idx ∈ (realRep 5).grading pidx)
    (hv2 : towerBasis (-1 : ℝ) 1 v2 ∈ (realRep 1).grading jw2)
    {s1 s2 : ℝ} {J1 J2 : Fin 16}
    (hcol : (peelFuse (baseFuseL 2)).toAlgEquiv
            (gtensorBasis (A := divisionTower (-1 : ℝ) 1)
              (B := divisionTower (1 : ℝ) 3)
              (towerBasis (-1) 1) (towerBasis 1 3) (finProdFinEquiv (v2, idx)))
          = s1 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
              (towerBasis 1 2) 1 1 J1
            + s2 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
              (towerBasis 1 2) 1 1 J2)
    {r1 r2 : ℝ}
    (h1 : (((sgn (jw2 * pidx) : ℤˣ) : ℤ) : ℝ) * s1 = r1)
    (h2 : (((sgn (jw2 * pidx) : ℤˣ) : ℤ) : ℝ) * s2 = r2) :
    realFuse_five_one.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
          (ℬ := (realRep 1).grading) ℝ
          (towerBasis (1 : ℝ) 3 idx) (towerBasis (-1 : ℝ) 1 v2))
      = r1 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J1
        + r2 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J2 := by
  have hc := gtensorComm_tmul_of_mem (realRep 5) (realRep 1) hpi hv2
  have hs : ((-1 : ℤˣ) ^ (jw2 * pidx))
        • GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
            (ℬ := (realRep 5).grading) ℝ
            (towerBasis (-1 : ℝ) 1 v2) (towerBasis (1 : ℝ) 3 idx)
      = (((sgn (jw2 * pidx) : ℤˣ) : ℤ))
        • GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
            (ℬ := (realRep 5).grading) ℝ
            (towerBasis (-1 : ℝ) 1 v2) (towerBasis (1 : ℝ) 3 idx) := by
    rw [sgn_eq_neg_one_uzpow]
    rfl
  have hD : realFuse_one_five.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := (realRep 1).grading)
          (ℬ := (realRep 5).grading) ℝ
          (towerBasis (-1 : ℝ) 1 v2) (towerBasis (1 : ℝ) 3 idx))
      = s1 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J1
        + s2 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J2 := by
    refine Eq.trans ?_ hcol
    exact congrArg (fun z => (peelFuse (baseFuseL 2)).toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 1) (towerBasis (1 : ℝ) 3)
        v2 idx).symm
  refine (fuse51comm _).trans ?_
  refine (congrArg (fun z => realFuse_one_five.toAlgEquiv z) (hc.trans hs)).trans ?_
  refine ((map_zsmul realFuse_one_five.toAlgEquiv _ _).trans
    (congrArg (fun z => (((sgn (jw2 * pidx) : ℤˣ) : ℤ)) • z) hD)).trans ?_
  exact zsmul2 _ s1 s2 r1 r2 _ _ h1 h2

private theorem seed42 {e : Fin 4} {v : Fin 4} (v1 v2 : Fin 2)
    (hv : (v : ℕ) = (v1 : ℕ) + 2 ^ 1 * (v2 : ℕ))
    {w1 : (divisionTower (-1 : ℝ) 1).carrier}
    (hw1 : towerBasis (-1 : ℝ) 1 v1 = w1)
    {jw2 : ZMod 2}
    (hw2 : towerBasis (-1 : ℝ) 1 v2 ∈ (divisionTower (-1 : ℝ) 1).grading jw2)
    {t : ℝ} {idx : Fin 8}
    (hb : realFuse_four_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis e) w1)
          = t • matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 idx)
    (hd : matrixSuperBasis (towerBasis (1 : ℝ) 3) 1 0 idx
          = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
              (towerBasis (1 : ℝ) 3 idx))
    {s1 s2 : ℝ} {J1 J2 : Fin 16}
    (hcol : realFuse_five_one.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
              (ℬ := (realRep 1).grading) ℝ
              (towerBasis (1 : ℝ) 3 idx) (towerBasis (-1 : ℝ) 1 v2))
          = s1 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
              (towerBasis 1 2) 1 1 J1
            + s2 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
              (towerBasis 1 2) 1 1 J2)
    {u1 u2 : ℝ} (hu1 : t * s1 = u1) (hu2 : t * s2 = u2) :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis e)
          (towerBasis (-1 : ℝ) 2 v))
      = u1 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J1
        + u2 • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 J2 := by
  have hA : ((SuperAlgEquiv.refl quatEvenSuper).gtensorCongr
        (towerFuse (-1 : ℝ) 1 1).symm).toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis e)
          (towerBasis (-1 : ℝ) 2 v))
      = GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := ((divisionTower (-1 : ℝ) 1).gtensor
            (divisionTower (-1 : ℝ) 1)).grading) ℝ (quatBasis e)
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 1).grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
            (towerBasis (-1 : ℝ) 1 v1) (towerBasis (-1 : ℝ) 1 v2)) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul (SuperAlgEquiv.refl quatEvenSuper)
      (towerFuse (-1 : ℝ) 1 1).symm (quatBasis e)
      (towerBasis (-1 : ℝ) 2 v)).trans ?_
    rw [superRefl_apply]
    exact congrArg
      (fun z => GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
        (ℬ := ((divisionTower (-1 : ℝ) 1).gtensor
          (divisionTower (-1 : ℝ) 1)).grading) ℝ (quatBasis e) z)
      (tfuseKsymm (-1 : ℝ) 1 1 v1 v2 v hv)
  have hB : (realFuse_four_one.gtensorCongr
        (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := (quatEvenSuper.gtensor (divisionTower (-1 : ℝ) 1)).grading)
          (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ
          (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
            (ℬ := (divisionTower (-1 : ℝ) 1).grading) ℝ (quatBasis e)
            (towerBasis (-1 : ℝ) 1 v1))
          (towerBasis (-1 : ℝ) 1 v2))
      = t • GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 0) (realRep 5).grading)
          (ℬ := (realRep 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
            (towerBasis (1 : ℝ) 3 idx))
          (towerBasis (-1 : ℝ) 1 v2) := by
    refine (SuperAlgEquiv.gtensorCongr_tmul realFuse_four_one
      (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1)) _ _).trans ?_
    rw [superRefl_apply, hw1, hb, hd]
    exact gtmul_smul_left _ _ t _ _
  have hC : (matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv
        (GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 0) (realRep 5).grading)
          (ℬ := (realRep 1).grading) ℝ
          (Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
            (towerBasis (1 : ℝ) 3 idx))
          (towerBasis (-1 : ℝ) 1 v2))
      = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 0) (Sum.inl 0)
          (GradedTensorProduct.tmul (𝒜 := (realRep 5).grading)
            (ℬ := (realRep 1).grading) ℝ (towerBasis (1 : ℝ) 3 idx)
            (towerBasis (-1 : ℝ) 1 v2)) := by
    refine (msg_single' (realRep 5) (realRep 1) 1 0 (Sum.inl 0) (Sum.inl 0)
      (towerBasis (1 : ℝ) 3 idx) hw2).trans ?_
    rw [sgn10 jw2, one_zsmul]
  refine (unfold42 _).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv
      ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv
        ((matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv
          ((realFuse_four_one.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv
            ((gtensorAssoc quatEvenSuper (divisionTower (-1 : ℝ) 1)
                (divisionTower (-1 : ℝ) 1)).symm.toAlgEquiv z))))) hA).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv
      ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv
        ((matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv
          ((realFuse_four_one.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 1))).toAlgEquiv z))))
      (gtAssocSymm quatEvenSuper (divisionTower (-1 : ℝ) 1)
        (divisionTower (-1 : ℝ) 1) (quatBasis e) (towerBasis (-1 : ℝ) 1 v1)
        (towerBasis (-1 : ℝ) 1 v2))).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv
      ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv
        ((matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv z)))
      hB).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv
      ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv z))
      (map_smul (matrixSuperGtensor (realRep 5) (realRep 1) 1 0).toAlgEquiv
        t _)).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv
      ((matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv (t • z)))
      hC).trans ?_
  refine (congrArg (fun z => realFuse_five_one.toAlgEquiv z)
      ((map_smul (matrixSuperOne ((realRep 5).gtensor (realRep 1))).toAlgEquiv
        t _).trans (congrArg (fun z => t • z)
          (msOneSingle ((realRep 5).gtensor (realRep 1)) _)))).trans ?_
  refine ((map_smul realFuse_five_one.toAlgEquiv t _).trans
      (congrArg (fun z => t • z) hcol)).trans ?_
  exact smul2 t s1 s2 u1 u2 _ _ hu1 hu2

/-! ### The `(3,3)` branch (`Cl_{0,3} ᵍ⊗ Cl_{0,3}`, `ε = -1`) -/

private theorem unfold33
    (x : ((divisionTower (-1 : ℝ) 3).gtensor (divisionTower (-1 : ℝ) 3)).carrier) :
    realFuse_three_three.toAlgEquiv x
      = ((matrixSuperGtensor quatEvenSuper (divisionTower (-1 : ℝ) 2) 1 1).trans
          ((realFuse_four_two.matrixSuper 1 1).trans
            (matrixSuperComp (divisionTower (1 : ℝ) 2) 1 1 1 1))).toAlgEquiv
          ((divisionTowerNegFourQuatSuper.gtensorCongr
              (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 2))).toAlgEquiv
            ((towerFuse (-1 : ℝ) 4 2).symm.toAlgEquiv
              ((towerFuse (-1 : ℝ) 3 3).toAlgEquiv x))) := rfl

private theorem split33 (i j : Fin 8) (u : Fin 16) (v : Fin 4) (k : Fin 64)
    (h1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (h2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ)) :
    (towerFuse (-1 : ℝ) 4 2).symm.toAlgEquiv
        ((towerFuse (-1 : ℝ) 3 3).toAlgEquiv
          (GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 3).grading)
            (ℬ := (divisionTower (-1 : ℝ) 3).grading) ℝ
            (towerBasis (-1 : ℝ) 3 i) (towerBasis (-1 : ℝ) 3 j)))
      = GradedTensorProduct.tmul (𝒜 := (divisionTower (-1 : ℝ) 4).grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ
          (towerBasis (-1 : ℝ) 4 u) (towerBasis (-1 : ℝ) 2 v) := by
  rw [tfuseK (-1 : ℝ) 3 3 i j k h1]
  exact tfuseKsymm (-1 : ℝ) 4 2 u v k h2

private theorem colEngine33 (i j : Fin 8) (u : Fin 16) (v : Fin 4) (k : Fin 64)
    (hk1 : (k : ℕ) = (i : ℕ) + 8 * (j : ℕ))
    (hk2 : (k : ℕ) = (u : ℕ) + 16 * (v : ℕ))
    {jw : ZMod 2} {w : (divisionTower (-1 : ℝ) 2).carrier}
    (hwv : towerBasis (-1 : ℝ) 2 v = w)
    (hw : w ∈ (divisionTower (-1 : ℝ) 2).grading jw)
    (r1 c1 r2 c2 : Fin 1 ⊕ Fin 1) {qa qb : ℍ[ℝ]}
    (hcert : divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 u)
        = Matrix.single r1 c1 qa + Matrix.single r2 c2 qb)
    {ta1 ta2 tb1 tb2 : ℝ} {ea1 ea2 eb1 eb2 : Fin 4}
    {raa caa rab cab rba cba rbb cbb : Fin 1 ⊕ Fin 1}
    (hFa : realFuse_four_two.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ qa w)
          = Matrix.single raa caa (ta1 • towerBasis (1 : ℝ) 2 ea1)
            + Matrix.single rab cab (ta2 • towerBasis (1 : ℝ) 2 ea2))
    (hFb : realFuse_four_two.toAlgEquiv
            (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
              (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ qb w)
          = Matrix.single rba cba (tb1 • towerBasis (1 : ℝ) 2 eb1)
            + Matrix.single rbb cbb (tb2 • towerBasis (1 : ℝ) 2 eb2))
    {κ1 κ2 κ3 κ4 : ℝ} {I1 I2 I3 I4 : Fin 64}
    (hI1 : matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I1
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, raa))
            (collapseIndexEquiv 1 1 1 1 (c1, caa)) (towerBasis (1 : ℝ) 2 ea1))
    (hI2 : matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I2
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r1, rab))
            (collapseIndexEquiv 1 1 1 1 (c1, cab)) (towerBasis (1 : ℝ) 2 ea2))
    (hI3 : matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I3
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rba))
            (collapseIndexEquiv 1 1 1 1 (c2, cba)) (towerBasis (1 : ℝ) 2 eb1))
    (hI4 : matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I4
        = Matrix.single (collapseIndexEquiv 1 1 1 1 (r2, rbb))
            (collapseIndexEquiv 1 1 1 1 (c2, cbb)) (towerBasis (1 : ℝ) 2 eb2))
    (hκ1 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta1 = κ1)
    (hκ2 : (((sgn (sumParity 1 1 c1 * jw) : ℤˣ) : ℤ) : ℝ) * ta2 = κ2)
    (hκ3 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb1 = κ3)
    (hκ4 : (((sgn (sumParity 1 1 c2 * jw) : ℤˣ) : ℤ) : ℝ) * tb2 = κ4) :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) (finProdFinEquiv (i, j)))
      = (κ1 • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I1
          + κ2 • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I2)
        + (κ3 • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I3
          + κ4 • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 I4) := by
  refine (congrArg (fun z => realFuse_three_three.toAlgEquiv z)
      (gtensorBasis_apply_pair (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) i j)).trans ?_
  refine (unfold33 _).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 2) 1 1).trans
        ((realFuse_four_two.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 2) 1 1 1 1))).toAlgEquiv
      ((divisionTowerNegFourQuatSuper.gtensorCongr
          (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 2))).toAlgEquiv z))
      (split33 i j u v k hk1 hk2)).trans ?_
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 2) 1 1).trans
        ((realFuse_four_two.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 2) 1 1 1 1))).toAlgEquiv z)
      (SuperAlgEquiv.gtensorCongr_tmul divisionTowerNegFourQuatSuper
        (SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 2))
        (towerBasis (-1 : ℝ) 4 u) (towerBasis (-1 : ℝ) 2 v))).trans ?_
  have e3 : GradedTensorProduct.tmul
        (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
        (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ
        (divisionTowerNegFourQuatSuper.toAlgEquiv (towerBasis (-1 : ℝ) 4 u))
        ((SuperAlgEquiv.refl (divisionTower (-1 : ℝ) 2)).toAlgEquiv
          (towerBasis (-1 : ℝ) 2 v))
      = GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (Matrix.single r1 c1 qa) w
        + GradedTensorProduct.tmul
          (𝒜 := matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (Matrix.single r2 c2 qb) w := by
    rw [superRefl_apply, hwv, hcert]
    exact add_gtmul (matrixGradingA (sumParity 1 1) quatEvenSuper.grading)
      (divisionTower (-1 : ℝ) 2).grading _ _ _
  refine (congrArg (fun z => ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 2) 1 1).trans
        ((realFuse_four_two.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 2) 1 1 1 1))).toAlgEquiv z) e3).trans ?_
  refine (map_add ((matrixSuperGtensor quatEvenSuper
        (divisionTower (-1 : ℝ) 2) 1 1).trans
        ((realFuse_four_two.matrixSuper 1 1).trans
          (matrixSuperComp (divisionTower (1 : ℝ) 2) 1 1 1 1))).toAlgEquiv _ _).trans ?_
  exact congrArg₂ (fun x y => x + y)
    (termG2 realFuse_four_two hw r1 c1 hFa hI1 hI2 hκ1 hκ2)
    (termG2 realFuse_four_two hw r2 c2 hFb hI3 hI4 hκ3 hκ4)


/-! ### Homogeneity of the floor-`2` tower frame -/

private theorem tb2m0 (ε : ℝ) :
    towerBasis ε 2 0 ∈ (divisionTower ε 2).grading 0 := towerBasis_mem ε 2 0

private theorem tb2m1 (ε : ℝ) :
    towerBasis ε 2 1 ∈ (divisionTower ε 2).grading 1 := towerBasis_mem ε 2 1

private theorem tb2m2 (ε : ℝ) :
    towerBasis ε 2 2 ∈ (divisionTower ε 2).grading 1 := towerBasis_mem ε 2 2

private theorem tb2m3 (ε : ℝ) :
    towerBasis ε 2 3 ∈ (divisionTower ε 2).grading 0 := towerBasis_mem ε 2 3

private theorem tb1m0 (ε : ℝ) :
    towerBasis ε 1 0 ∈ (divisionTower ε 1).grading 0 := towerBasis_mem ε 1 0

private theorem tb1m1 (ε : ℝ) :
    towerBasis ε 1 1 ∈ (divisionTower ε 1).grading 1 := towerBasis_mem ε 1 1

private theorem tb3m0 (ε : ℝ) :
    towerBasis ε 3 0 ∈ (divisionTower ε 3).grading 0 := towerBasis_mem ε 3 0

private theorem tb3m1 (ε : ℝ) :
    towerBasis ε 3 1 ∈ (divisionTower ε 3).grading 1 := towerBasis_mem ε 3 1

private theorem tb3m2 (ε : ℝ) :
    towerBasis ε 3 2 ∈ (divisionTower ε 3).grading 1 := towerBasis_mem ε 3 2

private theorem tb3m3 (ε : ℝ) :
    towerBasis ε 3 3 ∈ (divisionTower ε 3).grading 0 := towerBasis_mem ε 3 3

private theorem tb3m4 (ε : ℝ) :
    towerBasis ε 3 4 ∈ (divisionTower ε 3).grading 1 := towerBasis_mem ε 3 4

private theorem tb3m5 (ε : ℝ) :
    towerBasis ε 3 5 ∈ (divisionTower ε 3).grading 0 := towerBasis_mem ε 3 5

private theorem tb3m6 (ε : ℝ) :
    towerBasis ε 3 6 ∈ (divisionTower ε 3).grading 0 := towerBasis_mem ε 3 6

private theorem tb3m7 (ε : ℝ) :
    towerBasis ε 3 7 ∈ (divisionTower ε 3).grading 1 := towerBasis_mem ε 3 7

/-! ### The `1|1` frame of a floor-`2` tower (16 entries) -/

private theorem dm2_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 0
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dm2_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 1
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dm2_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 2
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 2

private theorem dm2_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 3
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 3

private theorem dm2_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 4
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dm2_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 5
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

private theorem dm2_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 6
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 2

private theorem dm2_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 7
    = Matrix.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 3

private theorem dm2_8 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 8
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 0

private theorem dm2_9 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 9
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 1

private theorem dm2_10 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 10
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 2

private theorem dm2_11 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 11
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) 3

private theorem dm2_12 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 12
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 0

private theorem dm2_13 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 13
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 1

private theorem dm2_14 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 14
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 2

private theorem dm2_15 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 1 1 15
    = Matrix.single (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 1 1 (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) 3

/-! ### The `2|2` frame of a floor-`2` tower (64 entries) -/

private theorem dq_0 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 0
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 0

private theorem dq_1 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 1
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 1

private theorem dq_2 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 2
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 2

private theorem dq_3 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 3
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 3

private theorem dq_4 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 4
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 0

private theorem dq_5 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 5
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 1

private theorem dq_6 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 6
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 2

private theorem dq_7 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 7
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 3

private theorem dq_8 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 8
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 0

private theorem dq_9 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 9
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 1

private theorem dq_10 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 10
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 2

private theorem dq_11 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 11
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 3

private theorem dq_12 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 12
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 0

private theorem dq_13 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 13
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 1

private theorem dq_14 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 14
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 2

private theorem dq_15 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 15
    = Matrix.single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 3

private theorem dq_16 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 16
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 0

private theorem dq_17 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 17
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 1

private theorem dq_18 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 18
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 2

private theorem dq_19 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 19
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 3

private theorem dq_20 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 20
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 0

private theorem dq_21 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 21
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 1

private theorem dq_22 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 22
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 2

private theorem dq_23 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 23
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 3

private theorem dq_24 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 24
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 0

private theorem dq_25 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 25
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 1

private theorem dq_26 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 26
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 2

private theorem dq_27 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 27
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 3

private theorem dq_28 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 28
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 0

private theorem dq_29 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 29
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 1

private theorem dq_30 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 30
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 2

private theorem dq_31 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 31
    = Matrix.single (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inl 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 3

private theorem dq_32 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 32
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 0

private theorem dq_33 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 33
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 1

private theorem dq_34 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 34
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 2

private theorem dq_35 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 35
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 3

private theorem dq_36 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 36
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 0

private theorem dq_37 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 37
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 1

private theorem dq_38 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 38
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 2

private theorem dq_39 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 39
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 3

private theorem dq_40 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 40
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 0

private theorem dq_41 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 41
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 1

private theorem dq_42 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 42
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 2

private theorem dq_43 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 43
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 3

private theorem dq_44 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 44
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 0

private theorem dq_45 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 45
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 1

private theorem dq_46 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 46
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 2

private theorem dq_47 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 47
    = Matrix.single (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 3

private theorem dq_48 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 48
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 0

private theorem dq_49 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 49
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 1

private theorem dq_50 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 50
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 2

private theorem dq_51 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 51
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 0) 3

private theorem dq_52 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 52
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 0

private theorem dq_53 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 53
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 1

private theorem dq_54 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 54
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 2

private theorem dq_55 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 55
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inl 1) 3

private theorem dq_56 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 56
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 0

private theorem dq_57 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 57
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 1

private theorem dq_58 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 58
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 2

private theorem dq_59 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 59
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 0) 3

private theorem dq_60 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 60
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 0) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 0

private theorem dq_61 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 61
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 1) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 1

private theorem dq_62 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 62
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 2) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 2

private theorem dq_63 (ε : ℝ) : matrixSuperBasis (towerBasis ε 2) 2 2 63
    = Matrix.single (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) (towerBasis ε 2 3) :=
  matrixSuperBasis_apply_pair (towerBasis ε 2) 2 2 (Sum.inr 1 : Fin 2 ⊕ Fin 2) (Sum.inr 1) 3

/-! ### The sixteen `(4,6)` seed values -/

private theorem val46_0_0 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 12 :=
  seed46 0 0 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_0_0 (d3g (-1 : ℝ) 0) c3_7_0 (by norm_num) (by norm_num)

private theorem val46_0_1 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 2 1))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 11 :=
  seed46 1 0 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_0_1 (d3g (-1 : ℝ) 7) c3_7_14 (by norm_num) (by norm_num)

private theorem val46_0_2 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 2 2))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 4
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 8 :=
  seed46 0 1 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_0_0 (d3g (-1 : ℝ) 0) c3_7_1 (by norm_num) (by norm_num)

private theorem val46_0_3 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (1 : ℝ) 2 3))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 3
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 15 :=
  seed46 1 1 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_0_1 (d3g (-1 : ℝ) 7) c3_7_15 (by norm_num) (by norm_num)

private theorem val46_1_0 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 15 :=
  seed46 0 0 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_1_0 (d3g (-1 : ℝ) 3) c3_7_6 (by norm_num) (by norm_num)

private theorem val46_1_1 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 2 1))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 4
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 8 :=
  seed46 1 0 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_1_1 (d3g (-1 : ℝ) 4) c3_7_8 (by norm_num) (by norm_num)

private theorem val46_1_2 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 2 2))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 7
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 11 :=
  seed46 0 1 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_1_0 (d3g (-1 : ℝ) 3) c3_7_7 (by norm_num) (by norm_num)

private theorem val46_1_3 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (1 : ℝ) 2 3))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 12 :=
  seed46 1 1 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_1_1 (d3g (-1 : ℝ) 4) c3_7_9 (by norm_num) (by norm_num)

private theorem val46_2_0 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 10 :=
  seed46 0 0 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_2_0 (d3g (-1 : ℝ) 6) c3_7_12 (by norm_num) (by norm_num)

private theorem val46_2_1 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 2 1))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 13 :=
  seed46 1 0 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_2_1 (d3g (-1 : ℝ) 1) c3_7_2 (by norm_num) (by norm_num)

private theorem val46_2_2 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 2 2))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 14 :=
  seed46 0 1 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_2_0 (d3g (-1 : ℝ) 6) c3_7_13 (by norm_num) (by norm_num)

private theorem val46_2_3 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (1 : ℝ) 2 3))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 5
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 9 :=
  seed46 1 1 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_2_1 (d3g (-1 : ℝ) 1) c3_7_3 (by norm_num) (by norm_num)

private theorem val46_3_0 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 2 0))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 9 :=
  seed46 0 0 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_3_0 (d3g (-1 : ℝ) 5) c3_7_10 (by norm_num) (by norm_num)

private theorem val46_3_1 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 2 1))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 2
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 14 :=
  seed46 1 0 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 0)
    val47_3_1 (d3g (-1 : ℝ) 2) c3_7_4 (by norm_num) (by norm_num)

private theorem val46_3_2 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 2 2))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 13 :=
  seed46 0 1 (by norm_num) (tb1z (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_3_0 (d3g (-1 : ℝ) 5) c3_7_11 (by norm_num) (by norm_num)

private theorem val46_3_3 :
    realFuse_four_six.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (1 : ℝ) 2 3))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (-1 : ℝ) 2)
          (towerBasis (-1) 2) 1 1 10 :=
  seed46 1 1 (by norm_num) (tb1g (1 : ℝ))
    (towerBasis_mem (1 : ℝ) 1 1)
    val47_3_1 (d3g (-1 : ℝ) 2) c3_7_5 (by norm_num) (by norm_num)

/-! ### The sixty-four columns of `(5,5)` -/

private theorem col55_0 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 0)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 20) :=
  colEngine55 0 0 0 0 0 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_0)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_0 (-1 : ℝ)) (dq_40 (-1 : ℝ)) (dq_60 (-1 : ℝ)) (dq_20 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_1 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 1)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 5
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 17) :=
  colEngine55 0 1 8 0 8 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_8)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_5 (-1 : ℝ)) (dq_45 (-1 : ℝ)) (dq_57 (-1 : ℝ)) (dq_17 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_2 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 2)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 55
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 31) :=
  colEngine55 0 2 0 1 16 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_0)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_11 (-1 : ℝ)) (dq_35 (-1 : ℝ)) (dq_55 (-1 : ℝ)) (dq_31 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_3 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 3)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 50
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 26) :=
  colEngine55 0 3 8 1 24 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_8)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_14 (-1 : ℝ)) (dq_38 (-1 : ℝ)) (dq_50 (-1 : ℝ)) (dq_26 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_4 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 4)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 8
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 52
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 28) :=
  colEngine55 0 4 0 2 32 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_0)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_8 (-1 : ℝ)) (dq_32 (-1 : ℝ)) (dq_52 (-1 : ℝ)) (dq_28 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_5 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 5)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 13
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 49
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 25) :=
  colEngine55 0 5 8 2 40 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_8)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_13 (-1 : ℝ)) (dq_37 (-1 : ℝ)) (dq_49 (-1 : ℝ)) (dq_25 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_6 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 6)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 43)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 63
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 23) :=
  colEngine55 0 6 0 3 48 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_0)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_3 (-1 : ℝ)) (dq_43 (-1 : ℝ)) (dq_63 (-1 : ℝ)) (dq_23 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_7 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 7)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 46)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 58
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 18) :=
  colEngine55 0 7 8 3 56 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_8)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_6 (-1 : ℝ)) (dq_46 (-1 : ℝ)) (dq_58 (-1 : ℝ)) (dq_18 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_8 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 8)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 36)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 48
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 24) :=
  colEngine55 1 0 1 0 1 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_1)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_12 (-1 : ℝ)) (dq_36 (-1 : ℝ)) (dq_48 (-1 : ℝ)) (dq_24 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_9 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 9)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 9
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 53
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 29) :=
  colEngine55 1 1 9 0 9 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_9)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_9 (-1 : ℝ)) (dq_33 (-1 : ℝ)) (dq_53 (-1 : ℝ)) (dq_29 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_10 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 10)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 47)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 59
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 19) :=
  colEngine55 1 2 1 1 17 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_1)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_7 (-1 : ℝ)) (dq_47 (-1 : ℝ)) (dq_59 (-1 : ℝ)) (dq_19 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_11 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 11)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 42)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 22) :=
  colEngine55 1 3 9 1 25 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_9)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_2 (-1 : ℝ)) (dq_42 (-1 : ℝ)) (dq_62 (-1 : ℝ)) (dq_22 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_12 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 12)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 56
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 16) :=
  colEngine55 1 4 1 2 33 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_1)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_4 (-1 : ℝ)) (dq_44 (-1 : ℝ)) (dq_56 (-1 : ℝ)) (dq_16 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_13 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 13)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 41)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 61
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 21) :=
  colEngine55 1 5 9 2 41 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_9)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_1 (-1 : ℝ)) (dq_41 (-1 : ℝ)) (dq_61 (-1 : ℝ)) (dq_21 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_14 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 14)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 15
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 39)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 27) :=
  colEngine55 1 6 1 3 49 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_1)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_15 (-1 : ℝ)) (dq_39 (-1 : ℝ)) (dq_51 (-1 : ℝ)) (dq_27 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_15 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 15)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 34)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 54
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 30) :=
  colEngine55 1 7 9 3 57 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_9)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_10 (-1 : ℝ)) (dq_34 (-1 : ℝ)) (dq_54 (-1 : ℝ)) (dq_30 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_16 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 16)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 15
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 27) :=
  colEngine55 2 0 2 0 2 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_2)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_15 (-1 : ℝ)) (dq_39 (-1 : ℝ)) (dq_51 (-1 : ℝ)) (dq_27 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_17 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 17)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 10
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 34)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 54
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 30) :=
  colEngine55 2 1 10 0 10 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_10)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_10 (-1 : ℝ)) (dq_34 (-1 : ℝ)) (dq_54 (-1 : ℝ)) (dq_30 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_18 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 18)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 56
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 16) :=
  colEngine55 2 2 2 1 18 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_2)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_4 (-1 : ℝ)) (dq_44 (-1 : ℝ)) (dq_56 (-1 : ℝ)) (dq_16 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_19 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 19)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 41)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 21) :=
  colEngine55 2 3 10 1 26 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_10)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_1 (-1 : ℝ)) (dq_41 (-1 : ℝ)) (dq_61 (-1 : ℝ)) (dq_21 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_20 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 20)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 59
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 19) :=
  colEngine55 2 4 2 2 34 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_2)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_7 (-1 : ℝ)) (dq_47 (-1 : ℝ)) (dq_59 (-1 : ℝ)) (dq_19 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_21 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 21)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 42)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 22) :=
  colEngine55 2 5 10 2 42 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_10)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_2 (-1 : ℝ)) (dq_42 (-1 : ℝ)) (dq_62 (-1 : ℝ)) (dq_22 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_22 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 22)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 36)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 48
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 24) :=
  colEngine55 2 6 2 3 50 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_2)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_12 (-1 : ℝ)) (dq_36 (-1 : ℝ)) (dq_48 (-1 : ℝ)) (dq_24 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_23 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 23)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 9
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 29) :=
  colEngine55 2 7 10 3 58 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_10)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_9 (-1 : ℝ)) (dq_33 (-1 : ℝ)) (dq_53 (-1 : ℝ)) (dq_29 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_24 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 24)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 43)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 63
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 23) :=
  colEngine55 3 0 3 0 3 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_3)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_3 (-1 : ℝ)) (dq_43 (-1 : ℝ)) (dq_63 (-1 : ℝ)) (dq_23 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_25 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 25)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 46)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 58
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 18) :=
  colEngine55 3 1 11 0 11 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_11)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_6 (-1 : ℝ)) (dq_46 (-1 : ℝ)) (dq_58 (-1 : ℝ)) (dq_18 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_26 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 26)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 32)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 52
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 28) :=
  colEngine55 3 2 3 1 19 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_3)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_8 (-1 : ℝ)) (dq_32 (-1 : ℝ)) (dq_52 (-1 : ℝ)) (dq_28 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_27 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 27)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 37)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 49
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 25) :=
  colEngine55 3 3 11 1 27 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_11)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_13 (-1 : ℝ)) (dq_37 (-1 : ℝ)) (dq_49 (-1 : ℝ)) (dq_25 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_28 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 28)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 55
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 31) :=
  colEngine55 3 4 3 2 35 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_3)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_11 (-1 : ℝ)) (dq_35 (-1 : ℝ)) (dq_55 (-1 : ℝ)) (dq_31 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_29 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 29)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 50
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 26) :=
  colEngine55 3 5 11 2 43 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_11)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_14 (-1 : ℝ)) (dq_38 (-1 : ℝ)) (dq_50 (-1 : ℝ)) (dq_26 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_30 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 30)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 40)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 20) :=
  colEngine55 3 6 3 3 51 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_3)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_0 (-1 : ℝ)) (dq_40 (-1 : ℝ)) (dq_60 (-1 : ℝ)) (dq_20 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_31 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 31)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 45)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 17) :=
  colEngine55 3 7 11 3 59 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_11)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_5 (-1 : ℝ)) (dq_45 (-1 : ℝ)) (dq_57 (-1 : ℝ)) (dq_17 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_32 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 32)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 46)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 58
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 18) :=
  colEngine55 4 0 4 0 4 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_4)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_6 (-1 : ℝ)) (dq_46 (-1 : ℝ)) (dq_58 (-1 : ℝ)) (dq_18 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_33 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 33)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 43)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 63
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 23) :=
  colEngine55 4 1 12 0 12 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_12)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_3 (-1 : ℝ)) (dq_43 (-1 : ℝ)) (dq_63 (-1 : ℝ)) (dq_23 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_34 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 34)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 49
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 25) :=
  colEngine55 4 2 4 1 20 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_4)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_13 (-1 : ℝ)) (dq_37 (-1 : ℝ)) (dq_49 (-1 : ℝ)) (dq_25 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_35 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 35)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 52
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 28) :=
  colEngine55 4 3 12 1 28 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_12)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_8 (-1 : ℝ)) (dq_32 (-1 : ℝ)) (dq_52 (-1 : ℝ)) (dq_28 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_36 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 36)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 38)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 50
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 26) :=
  colEngine55 4 4 4 2 36 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_4)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_14 (-1 : ℝ)) (dq_38 (-1 : ℝ)) (dq_50 (-1 : ℝ)) (dq_26 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_37 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 37)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 35)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 55
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 31) :=
  colEngine55 4 5 12 2 44 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_12)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_11 (-1 : ℝ)) (dq_35 (-1 : ℝ)) (dq_55 (-1 : ℝ)) (dq_31 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_38 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 38)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 57
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 17) :=
  colEngine55 4 6 4 3 52 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_4)
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_5 (-1 : ℝ)) (dq_45 (-1 : ℝ)) (dq_57 (-1 : ℝ)) (dq_17 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_39 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 39)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 60
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 20) :=
  colEngine55 4 7 12 3 60 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_12)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_0 (-1 : ℝ)) (dq_40 (-1 : ℝ)) (dq_60 (-1 : ℝ)) (dq_20 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_40 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 40)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 34)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 54
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 30) :=
  colEngine55 5 0 5 0 5 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_5)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_0 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_10 (-1 : ℝ)) (dq_34 (-1 : ℝ)) (dq_54 (-1 : ℝ)) (dq_30 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_41 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 41)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 15
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 27) :=
  colEngine55 5 1 13 0 13 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_13)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_0 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_15 (-1 : ℝ)) (dq_39 (-1 : ℝ)) (dq_51 (-1 : ℝ)) (dq_27 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_42 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 42)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 1
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 41)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 21) :=
  colEngine55 5 2 5 1 21 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_5)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_1 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_1 (-1 : ℝ)) (dq_41 (-1 : ℝ)) (dq_61 (-1 : ℝ)) (dq_21 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_43 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 43)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 56
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 16) :=
  colEngine55 5 3 13 1 29 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_13)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_1 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_4 (-1 : ℝ)) (dq_44 (-1 : ℝ)) (dq_56 (-1 : ℝ)) (dq_16 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_44 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 44)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 42)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 22) :=
  colEngine55 5 4 5 2 37 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_5)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_2_2 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_2 (-1 : ℝ)) (dq_42 (-1 : ℝ)) (dq_62 (-1 : ℝ)) (dq_22 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_45 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 45)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 59
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 19) :=
  colEngine55 5 5 13 2 45 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_13)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_1_2 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_7 (-1 : ℝ)) (dq_47 (-1 : ℝ)) (dq_59 (-1 : ℝ)) (dq_19 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_46 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 46)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 9
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 29) :=
  colEngine55 5 6 5 3 53 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_5)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_2_3 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_9 (-1 : ℝ)) (dq_33 (-1 : ℝ)) (dq_53 (-1 : ℝ)) (dq_29 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_47 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 47)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 12
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 36)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 48
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 24) :=
  colEngine55 5 7 13 3 61 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_13)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_1_3 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_12 (-1 : ℝ)) (dq_36 (-1 : ℝ)) (dq_48 (-1 : ℝ)) (dq_24 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_48 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 48)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 9
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 33)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 29) :=
  colEngine55 6 0 6 0 6 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_6)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_9 (-1 : ℝ)) (dq_33 (-1 : ℝ)) (dq_53 (-1 : ℝ)) (dq_29 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_49 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 49)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 36)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 48
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 24) :=
  colEngine55 6 1 14 0 14 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_14)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_12 (-1 : ℝ)) (dq_36 (-1 : ℝ)) (dq_48 (-1 : ℝ)) (dq_24 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_50 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 50)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 42)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 62
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 22) :=
  colEngine55 6 2 6 1 22 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_6)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_2 (-1 : ℝ)) (dq_42 (-1 : ℝ)) (dq_62 (-1 : ℝ)) (dq_22 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_51 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 51)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 59
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 19) :=
  colEngine55 6 3 14 1 30 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_14)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_7 (-1 : ℝ)) (dq_47 (-1 : ℝ)) (dq_59 (-1 : ℝ)) (dq_19 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_52 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 52)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 41)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 21) :=
  colEngine55 6 4 6 2 38 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_6)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_1 (-1 : ℝ)) (dq_41 (-1 : ℝ)) (dq_61 (-1 : ℝ)) (dq_21 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_53 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 53)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 44)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 56
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 16) :=
  colEngine55 6 5 14 2 46 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_14)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_4 (-1 : ℝ)) (dq_44 (-1 : ℝ)) (dq_56 (-1 : ℝ)) (dq_16 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_54 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 54)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 34)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 54
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 30) :=
  colEngine55 6 6 6 3 54 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_6)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_10 (-1 : ℝ)) (dq_34 (-1 : ℝ)) (dq_54 (-1 : ℝ)) (dq_30 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_55 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 55)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 15
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 51
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 27) :=
  colEngine55 6 7 14 3 62 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_14)
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_15 (-1 : ℝ)) (dq_39 (-1 : ℝ)) (dq_51 (-1 : ℝ)) (dq_27 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_56 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 56)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 17) :=
  colEngine55 7 0 7 0 7 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_7)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_0 (dm2_5 (-1 : ℝ))
      (dm2_9 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_5 (-1 : ℝ)) (dq_45 (-1 : ℝ)) (dq_57 (-1 : ℝ)) (dq_17 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_57 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 57)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 20) :=
  colEngine55 7 1 15 0 15 (by norm_num) (by norm_num) rfl
    (tb2m0 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_15)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_0 (dm2_0 (-1 : ℝ))
      (dm2_12 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_0 (-1 : ℝ)) (dq_40 (-1 : ℝ)) (dq_60 (-1 : ℝ)) (dq_20 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_58 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 58)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 14
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 50
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 26) :=
  colEngine55 7 2 7 1 23 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_7)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_1 (dm2_2 (-1 : ℝ))
      (dm2_14 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_14 (-1 : ℝ)) (dq_38 (-1 : ℝ)) (dq_50 (-1 : ℝ)) (dq_26 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_59 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 59)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 11
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 55
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 31) :=
  colEngine55 7 3 15 1 31 (by norm_num) (by norm_num) rfl
    (tb2m1 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_15)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_1 (dm2_7 (-1 : ℝ))
      (dm2_11 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_11 (-1 : ℝ)) (dq_35 (-1 : ℝ)) (dq_55 (-1 : ℝ)) (dq_31 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_60 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 60)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 49
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 25) :=
  colEngine55 7 4 7 2 39 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_7)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (1 : ℝ) val46_3_2 (dm2_1 (-1 : ℝ))
      (dm2_13 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_13 (-1 : ℝ)) (dq_37 (-1 : ℝ)) (dq_49 (-1 : ℝ)) (dq_25 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_61 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 61)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 52
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 28) :=
  colEngine55 7 5 15 2 47 (by norm_num) (by norm_num) rfl
    (tb2m2 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_15)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (1 : ℝ) val46_0_2 (dm2_4 (-1 : ℝ))
      (dm2_8 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_8 (-1 : ℝ)) (dq_32 (-1 : ℝ)) (dq_52 (-1 : ℝ)) (dq_28 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_62 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 62)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 46)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 58
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 18) :=
  colEngine55 7 6 7 3 55 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact qv4_7)
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_3_3 (dm2_6 (-1 : ℝ))
      (dm2_10 (-1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_6 (-1 : ℝ)) (dq_46 (-1 : ℝ)) (dq_58 (-1 : ℝ)) (dq_18 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col55_63 :
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3)
          (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) 63)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 43)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 63
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2 23) :=
  colEngine55 7 7 15 3 63 (by norm_num) (by norm_num) rfl
    (tb2m3 (1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact qv4_15)
    (fG2 realFuse_four_six (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_six (1 : ℝ) (1 : ℝ) (-1 : ℝ) val46_0_3 (dm2_3 (-1 : ℝ))
      (dm2_15 (-1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_3 (-1 : ℝ)) (dq_43 (-1 : ℝ)) (dq_63 (-1 : ℝ)) (dq_23 (-1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

/-! ### The packed literal for `(5,5)` (verbatim from the certificate generator) -/

/-- Packed row codes for `realFuseMatrix 5 5` (64 × 64).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_5_5 : Fin 64 → ℕ :=
  ![3140085802216924267432140043, 6461191308215807137408707,
    719867529496230271766361, 2289122546861686108457891577591,
    38767147849294829256232071, 523347635730299319352063599,
    381520424476947685496127364467, 4310342238857673340007037,
    254346949651347255172731427323, 88629381196713297336627,
    58149761318370977947736841, 28260772184378082574896526791,
    265888143589637795003649, 84782316550449091835886018201,
    9420257394792816201191935413, 174449283955112933460573003,
    38767147849294829643121119, 523347635729681645955779649,
    763040848953895370144966115117, 2159602588488666407394933,
    1570042907187397808810581747, 12922382616431611948700157,
    719867529496240732296711, 2289122546861686108175462041839,
    531776287179212827881519, 42391158275249565503291251569,
    9420257394792747570814570557, 174449283955112933508402693,
    254346949651347257714597255733, 88629381196619154177483,
    116299486163745578581198209, 14130386092189064164240718361,
    254346949651397289259696255359, 97492319316271655253729,
    116299498321411037652475917, 14130386092639348070131715733,
    292476957948563917231827, 84782316550465776643183169757,
    4710128697546571366270331751, 348898494964233112536526479,
    3140085806269685311583210959, 6461300727204937487506449,
    1437765517188082860713757, 1144561273430848613571941881893,
    38766819592327435106574933, 523347634378829928282787563,
    763040848953893517124777261089, 2156648275782115573637241,
    505187472820223943534123, 42391158275232895947189069987,
    4710128697546502735892966841, 348898494964233112574790231,
    254346949651397286717830427111, 97492319316365798452239,
    58149749160705518905156947, 28260772183927798669005529437,
    38766819592327434718623003, 523347634379447601679071507,
    381520424476949538516316214121, 4313296551564224173646631,
    1570042903135048546923700129, 12922273197442479274079481,
    1437765517188093320889813, 1144561273430848613289512344683]

/-- Packed literal for `realFuseMatrix 5 5`: decode digit `j` of
`fuseRows_5_5 i`. -/
def fuseLit_5_5 : Matrix (Fin 64) (Fin 64) ℝ :=
  Matrix.of fun i j =>
    match fuseRows_5_5 i / 3 ^ (j : ℕ) % 3 with
    | 1 => (1 : ℝ)
    | 2 => -1
    | _ => 0

/-! ### The four columns of `hcol55`, as data -/

private def vv551 : Fin 64 → ℝ :=
  ![1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1,
    -1, -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1,
    1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1,
    -1]

private def vv552 : Fin 64 → ℝ :=
  ![1, -1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1, 1,
    -1, 1, 1, 1, -1, 1, -1, -1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1,
    -1, -1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, 1,
    1, -1, -1, -1, 1]

private def vv553 : Fin 64 → ℝ :=
  ![1, 1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, -1,
    -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1,
    -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1,
    -1, 1, 1]

private def vv554 : Fin 64 → ℝ :=
  ![1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1,
    -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1,
    1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1,
    1, -1, -1, -1]

private def kv551 : Fin 64 → ℕ :=
  ![1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2,
    2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1,
    1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2]

private def kv552 : Fin 64 → ℕ :=
  ![1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1,
    2, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2,
    1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1]

private def kv553 : Fin 64 → ℕ :=
  ![1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2,
    1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1,
    1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1]

private def kv554 : Fin 64 → ℕ :=
  ![1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1,
    1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2,
    1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2]

private def nv551 : Fin 64 → Fin 64 :=
  ![0, 5, 11, 14, 8, 13, 3, 6, 12, 9, 7, 2, 4, 1, 15, 10, 15, 10, 4, 1, 7,
    2, 12, 9, 3, 6, 8, 13, 11, 14, 0, 5, 6, 3, 13, 8, 14, 11, 5, 0, 10, 15,
    1, 4, 2, 7, 9, 12, 9, 12, 2, 7, 1, 4, 10, 15, 5, 0, 14, 11, 13, 8, 6, 3]

private def nv552 : Fin 64 → Fin 64 :=
  ![40, 45, 35, 38, 32, 37, 43, 46, 36, 33, 47, 42, 44, 41, 39, 34, 39, 34,
    44, 41, 47, 42, 36, 33, 43, 46, 32, 37, 35, 38, 40, 45, 46, 43, 37, 32,
    38, 35, 45, 40, 34, 39, 41, 44, 42, 47, 33, 36, 33, 36, 42, 47, 41, 44,
    34, 39, 45, 40, 38, 35, 37, 32, 46, 43]

private def nv553 : Fin 64 → Fin 64 :=
  ![60, 57, 55, 50, 52, 49, 63, 58, 48, 53, 59, 62, 56, 61, 51, 54, 51, 54,
    56, 61, 59, 62, 48, 53, 63, 58, 52, 49, 55, 50, 60, 57, 58, 63, 49, 52,
    50, 55, 57, 60, 54, 51, 61, 56, 62, 59, 53, 48, 53, 48, 62, 59, 61, 56,
    54, 51, 57, 60, 50, 55, 49, 52, 58, 63]

private def nv554 : Fin 64 → Fin 64 :=
  ![20, 17, 31, 26, 28, 25, 23, 18, 24, 29, 19, 22, 16, 21, 27, 30, 27, 30,
    16, 21, 19, 22, 24, 29, 23, 18, 28, 25, 31, 26, 20, 17, 18, 23, 25, 28,
    26, 31, 17, 20, 30, 27, 21, 16, 22, 19, 29, 24, 29, 24, 22, 19, 21, 16,
    30, 27, 17, 20, 26, 31, 25, 28, 18, 23]

/-! ### The `4096`-point kernel certificate -/

private def tt551 (i j : Fin 64) : ℕ :=
  if nv551 j = i then kv551 j else 0

private def tt552 (i j : Fin 64) : ℕ :=
  if nv552 j = i then kv552 j else 0

private def tt553 (i j : Fin 64) : ℕ :=
  if nv553 j = i then kv553 j else 0

private def tt554 (i j : Fin 64) : ℕ :=
  if nv554 j = i then kv554 j else 0

/-- **The table certificate.**  For every one of the `64 x 64` points:
the first three conjuncts say that merging the four column contributions
never merges two nonzero codes (i.e. at most one of the four `hcol55`
columns lands on row `i`), and the last says that the surviving code is
exactly the base-3 digit `j` of `fuseRows_5_5`.  Checked by the kernel. -/
private theorem master55 : ∀ i j : Fin 64,
    (tt551 i j = 0 ∨ tt552 i j = 0)
  ∧ (tt553 i j = 0 ∨ tt554 i j = 0)
  ∧ (dpick (tt551 i j) (tt552 i j) = 0
      ∨ dpick (tt553 i j) (tt554 i j) = 0)
  ∧ dpick (dpick (tt551 i j) (tt552 i j)) (dpick (tt553 i j) (tt554 i j))
      = fuseRows_5_5 i / 3 ^ (j : ℕ) % 3 := by decide

set_option maxHeartbeats 16000000 in
private theorem hcol55 : ∀ j : Fin 64,
    realFuse_five_five.toAlgEquiv
        (gtensorBasis (A := divisionTower (1 : ℝ) 3) (B := divisionTower (1 : ℝ) 3)
          (towerBasis (1 : ℝ) 3) (towerBasis (1 : ℝ) 3) j)
      = (vv551 j • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2
          (nv551 j)
        + vv552 j • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2
          (nv552 j))
        + (vv553 j • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2
          (nv553 j)
        + vv554 j • matrixSuperBasis (towerBasis (-1 : ℝ) 2) 2 2
          (nv554 j))
     := by
  intro j
  fin_cases j
  · exact col55_0
  · exact col55_1
  · exact col55_2
  · exact col55_3
  · exact col55_4
  · exact col55_5
  · exact col55_6
  · exact col55_7
  · exact col55_8
  · exact col55_9
  · exact col55_10
  · exact col55_11
  · exact col55_12
  · exact col55_13
  · exact col55_14
  · exact col55_15
  · exact col55_16
  · exact col55_17
  · exact col55_18
  · exact col55_19
  · exact col55_20
  · exact col55_21
  · exact col55_22
  · exact col55_23
  · exact col55_24
  · exact col55_25
  · exact col55_26
  · exact col55_27
  · exact col55_28
  · exact col55_29
  · exact col55_30
  · exact col55_31
  · exact col55_32
  · exact col55_33
  · exact col55_34
  · exact col55_35
  · exact col55_36
  · exact col55_37
  · exact col55_38
  · exact col55_39
  · exact col55_40
  · exact col55_41
  · exact col55_42
  · exact col55_43
  · exact col55_44
  · exact col55_45
  · exact col55_46
  · exact col55_47
  · exact col55_48
  · exact col55_49
  · exact col55_50
  · exact col55_51
  · exact col55_52
  · exact col55_53
  · exact col55_54
  · exact col55_55
  · exact col55_56
  · exact col55_57
  · exact col55_58
  · exact col55_59
  · exact col55_60
  · exact col55_61
  · exact col55_62
  · exact col55_63

/-! ### From `hcol55` to a single matrix entry -/

/-- The entry formula, generic in `i` and `j`: one `realFuseMatrix_apply`,
one instance of `hcol55`, no case split. -/
private theorem entry55 (i j : Fin 64) :
    realFuseMatrix 5 5 i j
      = (vv551 j * (if nv551 j = i then 1 else 0)
          + vv552 j * (if nv552 j = i then 1 else 0))
        + (vv553 j * (if nv553 j = i then 1 else 0)
          + vv554 j * (if nv554 j = i then 1 else 0)) := by
  have h1 : realFuseMatrix 5 5 i j
      = (realFuseDstBasis 5 5).repr
          ((realFuse 5 5).toAlgEquiv (realFuseSrcBasis 5 5 j)) i :=
    realFuseMatrix_apply 5 5 i j
  have h2 : (realFuse 5 5).toAlgEquiv (realFuseSrcBasis 5 5 j)
      = (vv551 j • realFuseDstBasis 5 5 (nv551 j)
          + vv552 j • realFuseDstBasis 5 5 (nv552 j))
        + (vv553 j • realFuseDstBasis 5 5 (nv553 j)
          + vv554 j • realFuseDstBasis 5 5 (nv554 j)) := hcol55 j
  rw [h1, h2, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rfl

/-- The four real sign vectors are the decodings of the four code
vectors.  One `fin_cases` on `j`; four definitional checks each. -/
private theorem coefs55 (j : Fin 64) :
    vv551 j = fuseDecode (kv551 j)
  ∧ vv552 j = fuseDecode (kv552 j)
  ∧ vv553 j = fuseDecode (kv553 j)
  ∧ vv554 j = fuseDecode (kv554 j) := by
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Deliverable `(5,5)`** (`64 x 64`): the fusion matrix is the packed
base-3 literal emitted by `scripts/certgen`. -/
theorem realFuseMatrix_5_5 : ∀ (i j : Fin 64),
    realFuseMatrix 5 5 i j = fuseLit_5_5 i j := by
  intro i j
  obtain ⟨h1, h2, h3, h4⟩ := master55 i j
  refine (entry55 i j).trans ?_
  rw [(coefs55 j).1, (coefs55 j).2.1, (coefs55 j).2.2.1, (coefs55 j).2.2.2,
    dmul, dmul, dmul, dmul]
  show (fuseDecode (tt551 i j) + fuseDecode (tt552 i j))
      + (fuseDecode (tt553 i j) + fuseDecode (tt554 i j)) = _
  rw [dpick_add _ _ h1, dpick_add _ _ h2, dpick_add _ _ h3, h4]
  rfl

/-! ### The sixteen `(4,2)` seed values -/

private theorem val42_0_0 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 0
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 12 :=
  seed42 0 0 (by norm_num) (tb1z (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_0_0 (d3g (1 : ℝ) 0)
    (c51 0 0 (tb3m0 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_0
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_0_1 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 2 1))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 7
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 11 :=
  seed42 1 0 (by norm_num) (tb1g (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_0_1 (d3g (1 : ℝ) 7)
    (c51 7 0 (tb3m7 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_7
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_0_2 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 2 2))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 4
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 8 :=
  seed42 0 1 (by norm_num) (tb1z (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_0_0 (d3g (1 : ℝ) 0)
    (c51 0 1 (tb3m0 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_8
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_0_3 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 0)
          (towerBasis (-1 : ℝ) 2 3))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 15 :=
  seed42 1 1 (by norm_num) (tb1g (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_0_1 (d3g (1 : ℝ) 7)
    (c51 7 1 (tb3m7 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_15
      (r1 := (-1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_1_0 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 3
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 15 :=
  seed42 0 0 (by norm_num) (tb1z (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_1_0 (d3g (1 : ℝ) 3)
    (c51 3 0 (tb3m3 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_3
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_1_1 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 2 1))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 4
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 8 :=
  seed42 1 0 (by norm_num) (tb1g (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_1_1 (d3g (1 : ℝ) 4)
    (c51 4 0 (tb3m4 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_4
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_1_2 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 2 2))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 7
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 11 :=
  seed42 0 1 (by norm_num) (tb1z (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_1_0 (d3g (1 : ℝ) 3)
    (c51 3 1 (tb3m3 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_11
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_1_3 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 1)
          (towerBasis (-1 : ℝ) 2 3))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 0
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 12 :=
  seed42 1 1 (by norm_num) (tb1g (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_1_1 (d3g (1 : ℝ) 4)
    (c51 4 1 (tb3m4 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_12
      (r1 := (-1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_2_0 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 6
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 10 :=
  seed42 0 0 (by norm_num) (tb1z (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_2_0 (d3g (1 : ℝ) 6)
    (c51 6 0 (tb3m6 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_6
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_2_1 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 2 1))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 1
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 13 :=
  seed42 1 0 (by norm_num) (tb1g (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_2_1 (d3g (1 : ℝ) 1)
    (c51 1 0 (tb3m1 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_1
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_2_2 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 2 2))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 2
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 14 :=
  seed42 0 1 (by norm_num) (tb1z (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_2_0 (d3g (1 : ℝ) 6)
    (c51 6 1 (tb3m6 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_14
      (r1 := (-1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_2_3 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 2)
          (towerBasis (-1 : ℝ) 2 3))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 9 :=
  seed42 1 1 (by norm_num) (tb1g (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_2_1 (d3g (1 : ℝ) 1)
    (c51 1 1 (tb3m1 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_9
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_3_0 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 2 0))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 5
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 9 :=
  seed42 0 0 (by norm_num) (tb1z (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_3_0 (d3g (1 : ℝ) 5)
    (c51 5 0 (tb3m5 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_5
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_3_1 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 2 1))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 2
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 14 :=
  seed42 1 0 (by norm_num) (tb1g (-1 : ℝ)) (tb1m0 (-1 : ℝ))
    val41_3_1 (d3g (1 : ℝ) 2)
    (c51 2 0 (tb3m2 (1 : ℝ)) (tb1m0 (-1 : ℝ)) c1_5_2
      (r1 := (1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_3_2 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 2 2))
      = (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 1
        + (-1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 13 :=
  seed42 0 1 (by norm_num) (tb1z (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_3_0 (d3g (1 : ℝ) 5)
    (c51 5 1 (tb3m5 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_13
      (r1 := (-1 : ℝ)) (r2 := (-1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

private theorem val42_3_3 :
    realFuse_four_two.toAlgEquiv
        (GradedTensorProduct.tmul (𝒜 := quatEvenSuper.grading)
          (ℬ := (divisionTower (-1 : ℝ) 2).grading) ℝ (quatBasis 3)
          (towerBasis (-1 : ℝ) 2 3))
      = (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 6
        + (1 : ℝ) • matrixSuperBasis (P := divisionTower (1 : ℝ) 2)
          (towerBasis 1 2) 1 1 10 :=
  seed42 1 1 (by norm_num) (tb1g (-1 : ℝ)) (tb1m1 (-1 : ℝ))
    val41_3_1 (d3g (1 : ℝ) 2)
    (c51 2 1 (tb3m2 (1 : ℝ)) (tb1m1 (-1 : ℝ)) c1_5_10
      (r1 := (1 : ℝ)) (r2 := (1 : ℝ)) (by simp [sgn]) (by simp [sgn]))
    (by norm_num) (by norm_num)

/-! ### The sixty-four columns of `(3,3)` -/

private theorem col33_0 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 0)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 0
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 20) :=
  colEngine33 0 0 0 0 0 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_0)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_0 (1 : ℝ)) (dq_40 (1 : ℝ)) (dq_60 (1 : ℝ)) (dq_20 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_1 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 1)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 36)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 48
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 24) :=
  colEngine33 0 1 8 0 8 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_8)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_12 (1 : ℝ)) (dq_36 (1 : ℝ)) (dq_48 (1 : ℝ)) (dq_24 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_2 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 2)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 11
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 55
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 31) :=
  colEngine33 0 2 0 1 16 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_0)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_11 (1 : ℝ)) (dq_35 (1 : ℝ)) (dq_55 (1 : ℝ)) (dq_31 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_3 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 3)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 59
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 19) :=
  colEngine33 0 3 8 1 24 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_8)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_7 (1 : ℝ)) (dq_47 (1 : ℝ)) (dq_59 (1 : ℝ)) (dq_19 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_4 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 4)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 52
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 28) :=
  colEngine33 0 4 0 2 32 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_0)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_8 (1 : ℝ)) (dq_32 (1 : ℝ)) (dq_52 (1 : ℝ)) (dq_28 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_5 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 5)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 44)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 56
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 16) :=
  colEngine33 0 5 8 2 40 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_8)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_4 (1 : ℝ)) (dq_44 (1 : ℝ)) (dq_56 (1 : ℝ)) (dq_16 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_6 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 6)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 43)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 63
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 23) :=
  colEngine33 0 6 0 3 48 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_0)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_3 (1 : ℝ)) (dq_43 (1 : ℝ)) (dq_63 (1 : ℝ)) (dq_23 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_7 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 7)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 15
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 39)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 27) :=
  colEngine33 0 7 8 3 56 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_8)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (dq_15 (1 : ℝ)) (dq_39 (1 : ℝ)) (dq_51 (1 : ℝ)) (dq_27 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_8 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 8)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 6
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 46)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 58
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 18) :=
  colEngine33 1 0 1 0 1 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_1)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_6 (1 : ℝ)) (dq_46 (1 : ℝ)) (dq_58 (1 : ℝ)) (dq_18 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_9 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 9)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 34)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 54
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 30) :=
  colEngine33 1 1 9 0 9 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_9)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_10 (1 : ℝ)) (dq_34 (1 : ℝ)) (dq_54 (1 : ℝ)) (dq_30 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_10 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 10)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 13
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 49
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 25) :=
  colEngine33 1 2 1 1 17 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_1)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_13 (1 : ℝ)) (dq_37 (1 : ℝ)) (dq_49 (1 : ℝ)) (dq_25 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_11 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 11)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 41)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 61
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 21) :=
  colEngine33 1 3 9 1 25 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_9)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_1 (1 : ℝ)) (dq_41 (1 : ℝ)) (dq_61 (1 : ℝ)) (dq_21 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_12 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 12)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 50
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 26) :=
  colEngine33 1 4 1 2 33 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_1)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_14 (1 : ℝ)) (dq_38 (1 : ℝ)) (dq_50 (1 : ℝ)) (dq_26 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_13 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 13)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 42)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 22) :=
  colEngine33 1 5 9 2 41 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_9)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_2 (1 : ℝ)) (dq_42 (1 : ℝ)) (dq_62 (1 : ℝ)) (dq_22 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_14 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 14)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 17) :=
  colEngine33 1 6 1 3 49 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_1)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_5 (1 : ℝ)) (dq_45 (1 : ℝ)) (dq_57 (1 : ℝ)) (dq_17 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_15 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 15)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 9
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 33)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 29) :=
  colEngine33 1 7 9 3 57 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_9)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_9 (1 : ℝ)) (dq_33 (1 : ℝ)) (dq_53 (1 : ℝ)) (dq_29 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_16 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 16)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 45)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 17) :=
  colEngine33 2 0 2 0 2 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_2)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_5 (1 : ℝ)) (dq_45 (1 : ℝ)) (dq_57 (1 : ℝ)) (dq_17 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_17 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 17)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 9
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 29) :=
  colEngine33 2 1 10 0 10 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_10)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_9 (1 : ℝ)) (dq_33 (1 : ℝ)) (dq_53 (1 : ℝ)) (dq_29 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_18 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 18)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 38)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 50
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 26) :=
  colEngine33 2 2 2 1 18 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_2)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_14 (1 : ℝ)) (dq_38 (1 : ℝ)) (dq_50 (1 : ℝ)) (dq_26 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_19 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 19)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 42)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 22) :=
  colEngine33 2 3 10 1 26 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_10)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_2 (1 : ℝ)) (dq_42 (1 : ℝ)) (dq_62 (1 : ℝ)) (dq_22 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_20 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 20)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 49
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 25) :=
  colEngine33 2 4 2 2 34 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_2)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_13 (1 : ℝ)) (dq_37 (1 : ℝ)) (dq_49 (1 : ℝ)) (dq_25 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_21 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 21)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 1
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 41)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 21) :=
  colEngine33 2 5 10 2 42 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_10)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_1 (1 : ℝ)) (dq_41 (1 : ℝ)) (dq_61 (1 : ℝ)) (dq_21 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_22 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 22)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 46)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 58
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 18) :=
  colEngine33 2 6 2 3 50 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_2)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_6 (1 : ℝ)) (dq_46 (1 : ℝ)) (dq_58 (1 : ℝ)) (dq_18 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_23 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 23)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 10
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 34)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 54
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 30) :=
  colEngine33 2 7 10 3 58 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_10)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_10 (1 : ℝ)) (dq_34 (1 : ℝ)) (dq_54 (1 : ℝ)) (dq_30 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_24 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 24)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 43)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 63
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 23) :=
  colEngine33 3 0 3 0 3 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_3)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_3 (1 : ℝ)) (dq_43 (1 : ℝ)) (dq_63 (1 : ℝ)) (dq_23 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_25 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 25)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 15
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 27) :=
  colEngine33 3 1 11 0 11 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_11)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_15 (1 : ℝ)) (dq_39 (1 : ℝ)) (dq_51 (1 : ℝ)) (dq_27 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_26 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 26)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 32)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 52
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 28) :=
  colEngine33 3 2 3 1 19 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_3)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_8 (1 : ℝ)) (dq_32 (1 : ℝ)) (dq_52 (1 : ℝ)) (dq_28 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_27 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 27)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 56
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 16) :=
  colEngine33 3 3 11 1 27 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_11)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_4 (1 : ℝ)) (dq_44 (1 : ℝ)) (dq_56 (1 : ℝ)) (dq_16 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_28 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 28)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 55
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 31) :=
  colEngine33 3 4 3 2 35 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_3)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_11 (1 : ℝ)) (dq_35 (1 : ℝ)) (dq_55 (1 : ℝ)) (dq_31 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_29 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 29)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 7
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 59
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 19) :=
  colEngine33 3 5 11 2 43 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_11)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_7 (1 : ℝ)) (dq_47 (1 : ℝ)) (dq_59 (1 : ℝ)) (dq_19 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_30 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 30)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 60
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 20) :=
  colEngine33 3 6 3 3 51 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_3)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (dq_0 (1 : ℝ)) (dq_40 (1 : ℝ)) (dq_60 (1 : ℝ)) (dq_20 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_31 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 31)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 12
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 36)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 48
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 24) :=
  colEngine33 3 7 11 3 59 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_11)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_12 (1 : ℝ)) (dq_36 (1 : ℝ)) (dq_48 (1 : ℝ)) (dq_24 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_32 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 32)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 15
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 51
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 27) :=
  colEngine33 4 0 4 0 4 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_4)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_15 (1 : ℝ)) (dq_39 (1 : ℝ)) (dq_51 (1 : ℝ)) (dq_27 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_33 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 33)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 3
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 43)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 63
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 23) :=
  colEngine33 4 1 12 0 12 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_12)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_0 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_3 (1 : ℝ)) (dq_43 (1 : ℝ)) (dq_63 (1 : ℝ)) (dq_23 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_34 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 34)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 4
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 56
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 16) :=
  colEngine33 4 2 4 1 20 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_4)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_4 (1 : ℝ)) (dq_44 (1 : ℝ)) (dq_56 (1 : ℝ)) (dq_16 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_35 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 35)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 8
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 52
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 28) :=
  colEngine33 4 3 12 1 28 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_12)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_1_1 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_8 (1 : ℝ)) (dq_32 (1 : ℝ)) (dq_52 (1 : ℝ)) (dq_28 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_36 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 36)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 47)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 59
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 19) :=
  colEngine33 4 4 4 2 36 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_4)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_7 (1 : ℝ)) (dq_47 (1 : ℝ)) (dq_59 (1 : ℝ)) (dq_19 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_37 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 37)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 35)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 55
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 31) :=
  colEngine33 4 5 12 2 44 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_12)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_2 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_11 (1 : ℝ)) (dq_35 (1 : ℝ)) (dq_55 (1 : ℝ)) (dq_31 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_38 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 38)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 36)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 48
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 24) :=
  colEngine33 4 6 4 3 52 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_4)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_12 (1 : ℝ)) (dq_36 (1 : ℝ)) (dq_48 (1 : ℝ)) (dq_24 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_39 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 39)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 40)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 20) :=
  colEngine33 4 7 12 3 60 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_12)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_1 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_1_3 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_1 (by norm_num) (by norm_num))
    (dq_0 (1 : ℝ)) (dq_40 (1 : ℝ)) (dq_60 (1 : ℝ)) (dq_20 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_40 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 40)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 9
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 53
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 29) :=
  colEngine33 5 0 5 0 5 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_5)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_9 (1 : ℝ)) (dq_33 (1 : ℝ)) (dq_53 (1 : ℝ)) (dq_29 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_41 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 41)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 5
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 57
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 17) :=
  colEngine33 5 1 13 0 13 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_13)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_3_0 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_5 (1 : ℝ)) (dq_45 (1 : ℝ)) (dq_57 (1 : ℝ)) (dq_17 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_42 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 42)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 2
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 42)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 62
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 22) :=
  colEngine33 5 2 5 1 21 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_5)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_2 (1 : ℝ)) (dq_42 (1 : ℝ)) (dq_62 (1 : ℝ)) (dq_22 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_43 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 43)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 14
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 50
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 26) :=
  colEngine33 5 3 13 1 29 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_13)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_3_1 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_14 (1 : ℝ)) (dq_38 (1 : ℝ)) (dq_50 (1 : ℝ)) (dq_26 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_44 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 44)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 41)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 21) :=
  colEngine33 5 4 5 2 37 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_5)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_1 (1 : ℝ)) (dq_41 (1 : ℝ)) (dq_61 (1 : ℝ)) (dq_21 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_45 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 45)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 37)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 49
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 25) :=
  colEngine33 5 5 13 2 45 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_13)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_2 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_13 (1 : ℝ)) (dq_37 (1 : ℝ)) (dq_49 (1 : ℝ)) (dq_25 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_46 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 46)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 34)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 54
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 30) :=
  colEngine33 5 6 5 3 53 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_5)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (dq_10 (1 : ℝ)) (dq_34 (1 : ℝ)) (dq_54 (1 : ℝ)) (dq_30 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_47 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 47)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 46)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 58
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 18) :=
  colEngine33 5 7 13 3 61 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_13)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_3 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_3_3 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_3 (by norm_num) (by norm_num))
    (dq_6 (1 : ℝ)) (dq_46 (1 : ℝ)) (dq_58 (1 : ℝ)) (dq_18 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_48 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 48)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 10
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 34)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 54
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 30) :=
  colEngine33 6 0 6 0 6 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_6)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_10 (1 : ℝ)) (dq_34 (1 : ℝ)) (dq_54 (1 : ℝ)) (dq_30 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_49 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 49)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 6
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 46)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 58
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 18) :=
  colEngine33 6 1 14 0 14 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_14)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_0 (dm2_6 (1 : ℝ))
      (dm2_10 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_6 (1 : ℝ)) (dq_46 (1 : ℝ)) (dq_58 (1 : ℝ)) (dq_18 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_50 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 50)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 1
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 41)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 61
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 21) :=
  colEngine33 6 2 6 1 22 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_6)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_1 (1 : ℝ)) (dq_41 (1 : ℝ)) (dq_61 (1 : ℝ)) (dq_21 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_51 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 51)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 13
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 37)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 49
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 25) :=
  colEngine33 6 3 14 1 30 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_14)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_2_1 (dm2_1 (1 : ℝ))
      (dm2_13 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_13 (1 : ℝ)) (dq_37 (1 : ℝ)) (dq_49 (1 : ℝ)) (dq_25 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_52 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 52)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 2
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 42)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 62
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 22) :=
  colEngine33 6 4 6 2 38 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_6)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_2 (1 : ℝ)) (dq_42 (1 : ℝ)) (dq_62 (1 : ℝ)) (dq_22 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_53 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 53)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 14
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 38)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 50
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 26) :=
  colEngine33 6 5 14 2 46 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_14)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_2 (dm2_2 (1 : ℝ))
      (dm2_14 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_14 (1 : ℝ)) (dq_38 (1 : ℝ)) (dq_50 (1 : ℝ)) (dq_26 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_54 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 54)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 9
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 33)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 53
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 29) :=
  colEngine33 6 6 6 3 54 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_6)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (dq_9 (1 : ℝ)) (dq_33 (1 : ℝ)) (dq_53 (1 : ℝ)) (dq_29 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_55 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 55)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 5
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 45)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 57
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 17) :=
  colEngine33 6 7 14 3 62 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_14)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_p_2 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (1 : ℝ) val42_2_3 (dm2_5 (1 : ℝ))
      (dm2_9 (1 : ℝ)) sb_m_2 (by norm_num) (by norm_num))
    (dq_5 (1 : ℝ)) (dq_45 (1 : ℝ)) (dq_57 (1 : ℝ)) (dq_17 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_56 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 56)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 12
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 36)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 48
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 24) :=
  colEngine33 7 0 7 0 7 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_7)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_12 (1 : ℝ)) (dq_36 (1 : ℝ)) (dq_48 (1 : ℝ)) (dq_24 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_57 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 57)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 0
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 40)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 60
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 20) :=
  colEngine33 7 1 15 0 15 (by norm_num) (by norm_num) rfl
    (tb2m0 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_15)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_0 (dm2_0 (1 : ℝ))
      (dm2_12 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_0 (1 : ℝ)) (dq_40 (1 : ℝ)) (dq_60 (1 : ℝ)) (dq_20 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_58 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 58)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 7
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 47)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 59
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 19) :=
  colEngine33 7 2 7 1 23 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_7)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_7 (1 : ℝ)) (dq_47 (1 : ℝ)) (dq_59 (1 : ℝ)) (dq_19 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_59 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 59)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 11
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 35)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 55
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 31) :=
  colEngine33 7 3 15 1 31 (by norm_num) (by norm_num) rfl
    (tb2m1 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_15)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (1 : ℝ) val42_0_1 (dm2_7 (1 : ℝ))
      (dm2_11 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_11 (1 : ℝ)) (dq_35 (1 : ℝ)) (dq_55 (1 : ℝ)) (dq_31 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_60 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 60)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 4
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 44)
        + ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 56
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 16) :=
  colEngine33 7 4 7 2 39 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_7)
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_4 (1 : ℝ)) (dq_44 (1 : ℝ)) (dq_56 (1 : ℝ)) (dq_16 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_61 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 61)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 8
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 32)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 52
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 28) :=
  colEngine33 7 5 15 2 47 (by norm_num) (by norm_num) rfl
    (tb2m2 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_15)
    (fG2 realFuse_four_two (-1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_2 (dm2_4 (1 : ℝ))
      (dm2_8 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_8 (1 : ℝ)) (dq_32 (1 : ℝ)) (dq_52 (1 : ℝ)) (dq_28 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_62 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 62)
      = ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 15
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 39)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 51
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 27) :=
  colEngine33 7 6 7 3 55 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0) (Sum.inl 0) (by exact nqv4_7)
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_15 (1 : ℝ)) (dq_39 (1 : ℝ)) (dq_51 (1 : ℝ)) (dq_27 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

private theorem col33_63 :
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3)
          (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) 63)
      = ((1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 3
          + (-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 43)
        + ((-1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 63
          + (1 : ℝ) • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2 23) :=
  colEngine33 7 7 15 3 63 (by norm_num) (by norm_num) rfl
    (tb2m3 (-1 : ℝ)) (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0) (Sum.inr 0) (Sum.inr 0) (by exact nqv4_15)
    (fG2 realFuse_four_two (-1 : ℝ) (1 : ℝ) (-1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_m_0 (by norm_num) (by norm_num))
    (fG2 realFuse_four_two (1 : ℝ) (-1 : ℝ) (1 : ℝ) val42_0_3 (dm2_3 (1 : ℝ))
      (dm2_15 (1 : ℝ)) sb_p_0 (by norm_num) (by norm_num))
    (dq_3 (1 : ℝ)) (dq_43 (1 : ℝ)) (dq_63 (1 : ℝ)) (dq_23 (1 : ℝ))
    (by simp [sumParity]) (by simp [sumParity])
    (by simp [sumParity]) (by simp [sumParity])

/-! ### The packed literal for `(3,3)` (verbatim from the certificate generator) -/

/-- Packed row codes for `realFuseMatrix 3 3` (64 × 64).  Row `i` is
the base-3 numeral whose digit `j` (least-significant digit = column 0)
is the value code of entry `(i, j)`; codes: 0 ↦ 0, 1 ↦ 1, 2 ↦ -1. -/
def fuseRows_3_3 : Fin 64 → ℕ :=
  ![3140085802216924267432140043, 1436780746285909709834079,
    12922382616431610788033013, 1144561273430843054228945789889,
    84782316550465769017585685013, 348898494964233112574790231,
    292476957948595298297997, 9420257394642721565894936319,
    254346949651397289259696255359, 116299498321411037652475917,
    97492319316271655253729, 28260772183927775792213074467,
    523347635729681645955779649, 2159602588488666407394933,
    19383573924647414822357721, 763040848953895370144966115117,
    84782316550449091835886018201, 174449283955112933460573003,
    265888143589637795003649, 4710128697396408100595967747,
    1570042903135048546923700129, 1437765517188093320889813,
    6461300727204938651362239, 1144561273430848613289512344683,
    523347634378829928282787563, 4313296551564220686921279,
    19383902181614809358903907, 381520424476949539363604825751,
    127173474825748676174947127427, 116299486163745578581198209,
    177258762393238308295917, 28260772184378059698104071839,
    127173474825748678716812955837, 116299486163745578724687279,
    177258762393144165136773, 28260772184378082574896526791,
    523347634379447601679071507, 4313296551564224173646631,
    19383902181614809746855837, 381520424476949538516316214121,
    3140085806269685311583210959, 718882758594057120886683,
    12922273197442480437935271, 2289122546861680549114895485587,
    42391158275249565503291251569, 348898458491236735360957107,
    531776287179212827881519, 9420257394792747570814570557,
    523347635730299319352063599, 2159602588488662920551483,
    19383573924647415209246769, 763040848953895370992254722373,
    254346949651397286717830427111, 116299498321411037767267173,
    97492319316365798452239, 28260772183927798669005529437,
    42391158275232888321591585243, 174449247482116556332833321,
    505187472820255324600293, 4710128697546571366270331751,
    1570042907187397808810581747, 719867529496240732296711,
    6461191308215805976741563, 2289122546861686108175462041839]

/-- Packed literal for `realFuseMatrix 3 3`: decode digit `j` of
`fuseRows_3_3 i`. -/
def fuseLit_3_3 : Matrix (Fin 64) (Fin 64) ℝ :=
  Matrix.of fun i j =>
    match fuseRows_3_3 i / 3 ^ (j : ℕ) % 3 with
    | 1 => (1 : ℝ)
    | 2 => -1
    | _ => 0

/-! ### The four columns of `hcol33`, as data -/

private def vv331 : Fin 64 → ℝ :=
  ![1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1,
    -1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, -1, -1, 1]

private def vv332 : Fin 64 → ℝ :=
  ![1, 1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1,
    -1, 1, 1, 1, -1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, -1,
    -1, -1, 1, 1, 1, -1]

private def vv333 : Fin 64 → ℝ :=
  ![1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, -1,
    1, 1, -1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1,
    -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1,
    1, -1, -1, -1]

private def vv334 : Fin 64 → ℝ :=
  ![1, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1,
    -1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1,
    1, 1, 1]

private def kv331 : Fin 64 → ℕ :=
  ![1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1,
    1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2,
    1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]

private def kv332 : Fin 64 → ℕ :=
  ![1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1,
    1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2,
    2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2]

private def kv333 : Fin 64 → ℕ :=
  ![1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2,
    1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1,
    1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2]

private def kv334 : Fin 64 → ℕ :=
  ![1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2,
    1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1,
    2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1]

private def nv331 : Fin 64 → Fin 64 :=
  ![0, 12, 11, 7, 8, 4, 3, 15, 6, 10, 13, 1, 14, 2, 5, 9, 5, 9, 14, 2, 13,
    1, 6, 10, 3, 15, 8, 4, 11, 7, 0, 12, 15, 3, 4, 8, 7, 11, 12, 0, 9, 5,
    2, 14, 1, 13, 10, 6, 10, 6, 1, 13, 2, 14, 9, 5, 12, 0, 7, 11, 4, 8, 15,
    3]

private def nv332 : Fin 64 → Fin 64 :=
  ![40, 36, 35, 47, 32, 44, 43, 39, 46, 34, 37, 41, 38, 42, 45, 33, 45, 33,
    38, 42, 37, 41, 46, 34, 43, 39, 32, 44, 35, 47, 40, 36, 39, 43, 44, 32,
    47, 35, 36, 40, 33, 45, 42, 38, 41, 37, 34, 46, 34, 46, 41, 37, 42, 38,
    33, 45, 36, 40, 47, 35, 44, 32, 39, 43]

private def nv333 : Fin 64 → Fin 64 :=
  ![60, 48, 55, 59, 52, 56, 63, 51, 58, 54, 49, 61, 50, 62, 57, 53, 57, 53,
    50, 62, 49, 61, 58, 54, 63, 51, 52, 56, 55, 59, 60, 48, 51, 63, 56, 52,
    59, 55, 48, 60, 53, 57, 62, 50, 61, 49, 54, 58, 54, 58, 61, 49, 62, 50,
    53, 57, 48, 60, 59, 55, 56, 52, 51, 63]

private def nv334 : Fin 64 → Fin 64 :=
  ![20, 24, 31, 19, 28, 16, 23, 27, 18, 30, 25, 21, 26, 22, 17, 29, 17, 29,
    26, 22, 25, 21, 18, 30, 23, 27, 28, 16, 31, 19, 20, 24, 27, 23, 16, 28,
    19, 31, 24, 20, 29, 17, 22, 26, 21, 25, 30, 18, 30, 18, 21, 25, 22, 26,
    29, 17, 24, 20, 19, 31, 16, 28, 27, 23]

/-! ### The `4096`-point kernel certificate -/

private def tt331 (i j : Fin 64) : ℕ :=
  if nv331 j = i then kv331 j else 0

private def tt332 (i j : Fin 64) : ℕ :=
  if nv332 j = i then kv332 j else 0

private def tt333 (i j : Fin 64) : ℕ :=
  if nv333 j = i then kv333 j else 0

private def tt334 (i j : Fin 64) : ℕ :=
  if nv334 j = i then kv334 j else 0

/-- **The table certificate.**  For every one of the `64 x 64` points:
the first three conjuncts say that merging the four column contributions
never merges two nonzero codes (i.e. at most one of the four `hcol33`
columns lands on row `i`), and the last says that the surviving code is
exactly the base-3 digit `j` of `fuseRows_3_3`.  Checked by the kernel. -/
private theorem master33 : ∀ i j : Fin 64,
    (tt331 i j = 0 ∨ tt332 i j = 0)
  ∧ (tt333 i j = 0 ∨ tt334 i j = 0)
  ∧ (dpick (tt331 i j) (tt332 i j) = 0
      ∨ dpick (tt333 i j) (tt334 i j) = 0)
  ∧ dpick (dpick (tt331 i j) (tt332 i j)) (dpick (tt333 i j) (tt334 i j))
      = fuseRows_3_3 i / 3 ^ (j : ℕ) % 3 := by decide

set_option maxHeartbeats 16000000 in
private theorem hcol33 : ∀ j : Fin 64,
    realFuse_three_three.toAlgEquiv
        (gtensorBasis (A := divisionTower (-1 : ℝ) 3) (B := divisionTower (-1 : ℝ) 3)
          (towerBasis (-1 : ℝ) 3) (towerBasis (-1 : ℝ) 3) j)
      = (vv331 j • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2
          (nv331 j)
        + vv332 j • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2
          (nv332 j))
        + (vv333 j • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2
          (nv333 j)
        + vv334 j • matrixSuperBasis (towerBasis (1 : ℝ) 2) 2 2
          (nv334 j))
     := by
  intro j
  fin_cases j
  · exact col33_0
  · exact col33_1
  · exact col33_2
  · exact col33_3
  · exact col33_4
  · exact col33_5
  · exact col33_6
  · exact col33_7
  · exact col33_8
  · exact col33_9
  · exact col33_10
  · exact col33_11
  · exact col33_12
  · exact col33_13
  · exact col33_14
  · exact col33_15
  · exact col33_16
  · exact col33_17
  · exact col33_18
  · exact col33_19
  · exact col33_20
  · exact col33_21
  · exact col33_22
  · exact col33_23
  · exact col33_24
  · exact col33_25
  · exact col33_26
  · exact col33_27
  · exact col33_28
  · exact col33_29
  · exact col33_30
  · exact col33_31
  · exact col33_32
  · exact col33_33
  · exact col33_34
  · exact col33_35
  · exact col33_36
  · exact col33_37
  · exact col33_38
  · exact col33_39
  · exact col33_40
  · exact col33_41
  · exact col33_42
  · exact col33_43
  · exact col33_44
  · exact col33_45
  · exact col33_46
  · exact col33_47
  · exact col33_48
  · exact col33_49
  · exact col33_50
  · exact col33_51
  · exact col33_52
  · exact col33_53
  · exact col33_54
  · exact col33_55
  · exact col33_56
  · exact col33_57
  · exact col33_58
  · exact col33_59
  · exact col33_60
  · exact col33_61
  · exact col33_62
  · exact col33_63

/-! ### From `hcol33` to a single matrix entry -/

/-- The entry formula, generic in `i` and `j`: one `realFuseMatrix_apply`,
one instance of `hcol33`, no case split. -/
private theorem entry33 (i j : Fin 64) :
    realFuseMatrix 3 3 i j
      = (vv331 j * (if nv331 j = i then 1 else 0)
          + vv332 j * (if nv332 j = i then 1 else 0))
        + (vv333 j * (if nv333 j = i then 1 else 0)
          + vv334 j * (if nv334 j = i then 1 else 0)) := by
  have h1 : realFuseMatrix 3 3 i j
      = (realFuseDstBasis 3 3).repr
          ((realFuse 3 3).toAlgEquiv (realFuseSrcBasis 3 3 j)) i :=
    realFuseMatrix_apply 3 3 i j
  have h2 : (realFuse 3 3).toAlgEquiv (realFuseSrcBasis 3 3 j)
      = (vv331 j • realFuseDstBasis 3 3 (nv331 j)
          + vv332 j • realFuseDstBasis 3 3 (nv332 j))
        + (vv333 j • realFuseDstBasis 3 3 (nv333 j)
          + vv334 j • realFuseDstBasis 3 3 (nv334 j)) := hcol33 j
  rw [h1, h2, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    Basis.repr_self_apply, Basis.repr_self_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rfl

/-- The four real sign vectors are the decodings of the four code
vectors.  One `fin_cases` on `j`; four definitional checks each. -/
private theorem coefs33 (j : Fin 64) :
    vv331 j = fuseDecode (kv331 j)
  ∧ vv332 j = fuseDecode (kv332 j)
  ∧ vv333 j = fuseDecode (kv333 j)
  ∧ vv334 j = fuseDecode (kv334 j) := by
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Deliverable `(3,3)`** (`64 x 64`): the fusion matrix is the packed
base-3 literal emitted by `scripts/certgen`. -/
theorem realFuseMatrix_3_3 : ∀ (i j : Fin 64),
    realFuseMatrix 3 3 i j = fuseLit_3_3 i j := by
  intro i j
  obtain ⟨h1, h2, h3, h4⟩ := master33 i j
  refine (entry33 i j).trans ?_
  rw [(coefs33 j).1, (coefs33 j).2.1, (coefs33 j).2.2.1, (coefs33 j).2.2.2,
    dmul, dmul, dmul, dmul]
  show (fuseDecode (tt331 i j) + fuseDecode (tt332 i j))
      + (fuseDecode (tt333 i j) + fuseDecode (tt334 i j)) = _
  rw [dpick_add _ _ h1, dpick_add _ _ h2, dpick_add _ _ h3, h4]
  rfl

end Superfusion
