/-
Superfusion / Gauge / FusionGauge

Milestone M9-2 of the intrinsic gauge track: **`DivisionFusionGauge`**, the
centerpiece definition of the track — the skeletal fusion data
`(G, D_a, σ, φ_{a,b})` of the paper's superbicategory skeleton, over a
*general* group `G` with central super division representatives `D_a`.

**Group convention.**  We use `[AddGroup G]` with `a + b` in indices, matching
`Superfusion.Super.TowerStd`'s `stdTower`/`stdFuse` verbatim (`stdFuse a b :
T_a ᵍ⊗ T_b ≅ M_{s(a,b)}(T_{a+b})`, with `ZMod 8`'s native additive structure):
the concrete `ℝ`-instance of M9-4 will simply take `G := ZMod 8` and reuse
`stdTower`/`stdFuse` as the data fields with **no** bridging `Multiplicative`
wrapper needed.  (The alternative — `[Group G]` with a multiplicative
convention and a `Multiplicative (ZMod 8)` instance at the `ℝ`-round — would
force every occurrence of `stdFuse`'s `a + b` to be rewritten through
`Multiplicative.ofAdd`/`toAdd` coercions; additive avoids that entirely.)

**Design decisions (per the track's guidance, recorded here verbatim):**

* `G` is a *general* `AddGroup`, not `DBW(K)` — the Brauer–Wall group
  specialization is a later (`DBWGauge`) refinement, not part of this
  skeleton.
* `φ_{a,b}` (the field `fuse`) carries **no coherence conditions**: their
  *failure* is exactly the data the pentagon parity/sign cocycle `(p, χ)`
  will measure in later milestones — imposing coherence here would beg the
  question.
* There is **no section condition** `[D_a] = a` relating `D_a` to a
  Brauer–Wall class `a : G`; that is meaningful only once `G = DBW(K)`
  (the later `DBWGauge` specialization) and is not assumed of a general `G`.
* The sizes `σ_{a,b} = size a b : ℕ × ℕ` are *data*, not derived — exactly
  mirroring `stdFuse`'s `fuseSize`.

**Per-object conditions.**  Matching `Superfusion.Super.PentagonParity`'s
hypotheses on each tower floor (`IsSuperCentral`, `IsGradedSimple`,
`FiniteDimensional`, plus a `Nontrivial` instance needed downstream for
`Bimod.finrank_D_pos`) and `Superfusion.Bimod.ColumnSimple`'s super-division
predicate for the fibers: `IsGradedSimple` is *not* derived from
`Bimod.IsSuperDivision` this round (that a super division algebra is
automatically graded-simple is true but unproved in this codebase, and
proving it is out of scope here) — it is carried as an independent field,
exactly as the design guidance anticipated.

**Contents:**

* the structure `DivisionFusionGauge K G` itself;
* derived basics: total-size positivity (`DivisionFusionGauge.size_pos`),
  total-size multiplicativity (`DivisionFusionGauge.finrank_fuse`, the
  `finrank`-transport of `fuse` — the tensor-product finrank formula
  through the type-synonym identification `GradedTensorProduct.of`), the
  size-normalization predicate `DivisionFusionGauge.IsSizeNormalized`, and the pure
  `ℕ`-arithmetic composition-preserves-normalization fact
  (`size_compose_normalized`, matching `matrixSuperComp`'s composite size
  formula `(p'*p+q'*q, p'*q+q'*p)`);
* **the odd-unit collapse isomorphism** deferred from M9-1c
  (`Superfusion.Gauge.SizeRigidity`'s docstring): `matrixSuperOddCollapse`,
  `M_{p|q}(P) ≅ M_{p+q|0}(P)` for `P` carrying an odd unit `w`, built as
  conjugation by the diagonal matrix with `1` in the first `p` slots and
  `w` in the last `q` (`diagUnitsConjAlgEquiv`), followed by the evident
  reindexing of `Fin p ⊕ Fin q` onto `Fin (p+q) ⊕ Fin 0`.

The `ZMod 8` instance itself (`G := ZMod 8`, `D := stdTower`,
`fuse := stdFuse`, sizes `:= fuseSize`) is **not** attempted this round: the
division/central/graded-simple checks on `stdTower` floors are milestone
M9-4's task.  The fields would line up as: `central := stdTower_isSuperCentral`
composed with the paper's odd-unit dichotomy giving `division`,
`gradedSimple := stdTower_isGradedSimple`, `findim`/`nontriv` from the
existing `stdTower` instances, `size := fuseSize`, `fuse := stdFuse`.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.SizeRigidity

namespace Superfusion

open Module
open scoped TensorProduct

/-! ### Conjugation by a diagonal matrix of units -/

section DiagConj

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

private theorem diagUnits_mul_inv (d : n → Aˣ) :
    Matrix.diagonal (fun a => (d a : A)) *
      Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have : (fun a => (d a : A) * (((d a)⁻¹ : Aˣ) : A)) = fun _ : n => (1 : A) := by
    funext a; exact (d a).mul_inv
  rw [this, Matrix.diagonal_one]

private theorem diagUnits_inv_mul (d : n → Aˣ) :
    Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
      Matrix.diagonal (fun a => (d a : A)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have : (fun a => (((d a)⁻¹ : Aˣ) : A) * (d a : A)) = fun _ : n => (1 : A) := by
    funext a; exact (d a).inv_mul
  rw [this, Matrix.diagonal_one]

/-- **Conjugation by a diagonal matrix of units** is a `K`-algebra automorphism of
`Matrix n n A`: `X ↦ D X D⁻¹` for `D = diagonal d`.  Multiplicativity and the two-sided
inverse both reduce to `(d a)⁻¹ * d a = 1` (`diagUnits_inv_mul`/`diagUnits_mul_inv`);
`K`-linearity is entrywise distributivity; fixing scalars uses that `algebraMap K A c` is a
scalar matrix, central in `Matrix n n A`. -/
noncomputable def diagUnitsConjAlgEquiv (d : n → Aˣ) : Matrix n n A ≃ₐ[K] Matrix n n A where
  toFun X := Matrix.diagonal (fun a => (d a : A)) * X *
    Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
  invFun X := Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) * X *
    Matrix.diagonal (fun a => (d a : A))
  left_inv X := by
    show Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
        (Matrix.diagonal (fun a => (d a : A)) * X *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) *
        Matrix.diagonal (fun a => (d a : A)) = X
    rw [show Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
        (Matrix.diagonal (fun a => (d a : A)) * X *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) *
        Matrix.diagonal (fun a => (d a : A))
        = (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
            Matrix.diagonal (fun a => (d a : A))) * X *
          (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
            Matrix.diagonal (fun a => (d a : A))) from by noncomm_ring,
      diagUnits_inv_mul, one_mul, mul_one]
  right_inv X := by
    show Matrix.diagonal (fun a => (d a : A)) *
        (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) * X *
          Matrix.diagonal (fun a => (d a : A))) *
        Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) = X
    rw [show Matrix.diagonal (fun a => (d a : A)) *
        (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) * X *
          Matrix.diagonal (fun a => (d a : A))) *
        Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
        = (Matrix.diagonal (fun a => (d a : A)) *
            Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) * X *
          (Matrix.diagonal (fun a => (d a : A)) *
            Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) from by noncomm_ring,
      diagUnits_mul_inv, one_mul, mul_one]
  map_mul' X Y := by
    show Matrix.diagonal (fun a => (d a : A)) * (X * Y) *
        Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
      = (Matrix.diagonal (fun a => (d a : A)) * X *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) *
        (Matrix.diagonal (fun a => (d a : A)) * Y *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)))
    rw [show (Matrix.diagonal (fun a => (d a : A)) * X *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) *
        (Matrix.diagonal (fun a => (d a : A)) * Y *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)))
        = Matrix.diagonal (fun a => (d a : A)) * X *
          (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) *
            Matrix.diagonal (fun a => (d a : A))) * Y *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) from by noncomm_ring,
      diagUnits_inv_mul]
    noncomm_ring
  map_add' X Y := by
    show Matrix.diagonal (fun a => (d a : A)) * (X + Y) *
        Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
      = Matrix.diagonal (fun a => (d a : A)) * X *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
        + Matrix.diagonal (fun a => (d a : A)) * Y *
          Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))
    noncomm_ring
  commutes' c := by
    show Matrix.diagonal (fun a => (d a : A)) * algebraMap K (Matrix n n A) c *
        Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) = algebraMap K (Matrix n n A) c
    rw [show Matrix.diagonal (fun a => (d a : A)) * algebraMap K (Matrix n n A) c
        = algebraMap K (Matrix n n A) c * Matrix.diagonal (fun a => (d a : A)) from
      (Algebra.commutes c _).symm, mul_assoc, diagUnits_mul_inv, mul_one]

theorem diagUnitsConjAlgEquiv_toLinearMap_apply (d : n → Aˣ) (X : Matrix n n A) (a b : n) :
    (diagUnitsConjAlgEquiv (K := K) d).toLinearMap X a b
      = (d a : A) * X a b * (((d b)⁻¹ : Aˣ) : A) := by
  show (Matrix.diagonal (fun a => (d a : A)) * X *
      Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A))) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diagUnitsConjAlgEquiv_symm_apply (d : n → Aˣ) (X : Matrix n n A) (a b : n) :
    (diagUnitsConjAlgEquiv (K := K) d).symm X a b
      = (((d a)⁻¹ : Aˣ) : A) * X a b * (d b : A) := by
  show (Matrix.diagonal (fun a => (((d a)⁻¹ : Aˣ) : A)) * X *
      Matrix.diagonal (fun a => (d a : A))) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

end DiagConj

/-! ### The odd-unit collapse isomorphism (deferred from M9-1c) -/

section OddCollapse

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A] (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-- The diagonal of units realizing the odd-unit collapse: `1` on the first `p` slots, the odd
unit `w` on the last `q`. -/
def oddDiag (p q : ℕ) (w : Aˣ) : Fin p ⊕ Fin q → Aˣ :=
  Sum.elim (fun _ => 1) (fun _ => w)

@[simp] private theorem oddDiag_inl (p q : ℕ) (w : Aˣ) (a : Fin p) :
    oddDiag p q w (Sum.inl a) = 1 := rfl

@[simp] private theorem oddDiag_inr (p q : ℕ) (w : Aˣ) (a : Fin q) :
    oddDiag p q w (Sum.inr a) = w := rfl

@[simp] private theorem sumParity_inl' (p q : ℕ) (a : Fin p) :
    sumParity p q (Sum.inl a) = 0 := rfl

@[simp] private theorem sumParity_inr' (p q : ℕ) (a : Fin q) :
    sumParity p q (Sum.inr a) = 1 := rfl

private theorem zmod2_i11 : ∀ i : ZMod 2, i + 1 + 1 = i := by decide +revert

/-- Conjugation by `oddDiag` carries the checkerboard grading of `M_{p|q}(A)` onto the
constant-`i` condition (the grading of `M_{p+q|0}(A)`, before reindexing): entrywise, the four
checkerboard blocks all land in the *same* degree `i`, since the odd unit `w` (degree `1`) and
its homogeneous inverse (`Bimod.isUnit_inv_mem`, degree `1` again since `ZMod 2` is `2`-torsion)
absorb exactly the parity shift each off-diagonal block carries. -/
theorem diagUnitsConjAlgEquiv_map_matrixGradingA (p q : ℕ) {w : A} (hw1 : w ∈ 𝒜 1)
    (hw : IsUnit w) (i : ZMod 2) :
    (matrixGradingA (sumParity p q) 𝒜 i).map
        (diagUnitsConjAlgEquiv (K := K) (oddDiag p q hw.unit)).toLinearMap
      = matrixGradingA (fun _ : Fin p ⊕ Fin q => (0 : ZMod 2)) 𝒜 i := by
  have hwinv1 : (((hw.unit⁻¹ : Aˣ) : A)) ∈ 𝒜 1 := Bimod.isUnit_inv_mem hw1 hw.unit hw.unit_spec
  ext N
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨X, hX, rfl⟩
    intro a b
    rw [diagUnitsConjAlgEquiv_toLinearMap_apply, show i + (0 : ZMod 2) + 0 = i from by
      rw [add_zero, add_zero]]
    rcases a with a | a <;> rcases b with b | b
    · have hXab := hX (Sum.inl a) (Sum.inl b)
      simp only [sumParity_inl', add_zero] at hXab
      simpa using hXab
    · have hXab := hX (Sum.inl a) (Sum.inr b)
      simp only [sumParity_inl', sumParity_inr', add_zero] at hXab
      have h2 := SetLike.mul_mem_graded hXab hwinv1
      rw [zmod2_i11] at h2
      simpa using h2
    · have hXab := hX (Sum.inr a) (Sum.inl b)
      simp only [sumParity_inl', sumParity_inr', add_zero] at hXab
      have h2 := SetLike.mul_mem_graded hw1 hXab
      rw [show (1 : ZMod 2) + (i + 1) = i from by
        rw [← add_assoc, add_comm (1 : ZMod 2) i, zmod2_i11]] at h2
      simpa using h2
    · have hXab := hX (Sum.inr a) (Sum.inr b)
      simp only [sumParity_inr'] at hXab
      rw [zmod2_i11] at hXab
      have h2 := SetLike.mul_mem_graded (SetLike.mul_mem_graded hw1 hXab) hwinv1
      rw [show (1 : ZMod 2) + i + 1 = i from by
        rw [add_comm (1 : ZMod 2) i]; exact zmod2_i11 i] at h2
      simpa using h2
  · intro hN
    refine ⟨(diagUnitsConjAlgEquiv (K := K) (oddDiag p q hw.unit)).symm N, ?_, ?_⟩
    · intro a b
      rw [diagUnitsConjAlgEquiv_symm_apply]
      have hNab := hN a b
      rw [add_zero, add_zero] at hNab
      rcases a with a | a <;> rcases b with b | b
      · simpa using hNab
      · simp only [oddDiag_inl, oddDiag_inr, sumParity_inl', sumParity_inr', add_zero,
          Units.val_one, inv_one, one_mul]
        exact SetLike.mul_mem_graded hNab hw1
      · simp only [oddDiag_inl, oddDiag_inr, sumParity_inl', sumParity_inr', add_zero,
          Units.val_one, mul_one, show i + 1 = (1 : ZMod 2) + i from add_comm i 1]
        exact SetLike.mul_mem_graded hwinv1 hNab
      · simp only [oddDiag_inr, sumParity_inr',
          show i + 1 + 1 = (1 : ZMod 2) + i + 1 from by rw [add_comm (1 : ZMod 2) i]]
        exact SetLike.mul_mem_graded (SetLike.mul_mem_graded hwinv1 hNab) hw1
    · exact (diagUnitsConjAlgEquiv (K := K) (oddDiag p q hw.unit)).apply_symm_apply N

private theorem sumParity_zero_right (m : ℕ) (x : Fin m ⊕ Fin 0) :
    sumParity m 0 x = 0 := by
  rcases x with x | x
  · rfl
  · exact x.elim0

/-- The index bijection realizing the odd-unit collapse: `Fin p ⊕ Fin q ≃ Fin (p+q) ⊕ Fin 0`
(the `Fin q`-tail is absorbed into the `p+q` block; the `Fin 0` factor is empty). -/
def oddCollapseIndexEquiv (p q : ℕ) : Fin p ⊕ Fin q ≃ Fin (p + q) ⊕ Fin 0 :=
  finSumFinEquiv.trans (Equiv.sumEmpty (Fin (p + q)) (Fin 0)).symm

/-- **The odd-unit collapse** (M9-2, deferred from `Superfusion.Gauge.SizeRigidity`, M9-1c): an
odd unit `w` of `P` collapses the matrix stabilization `M_{p|q}(P)` onto the purely-`(p+q)`-sized
`M_{p+q|0}(P)`, via conjugation by the diagonal matrix with `1` in the first `p` slots and `w` in
the last `q` (`diagUnitsConjAlgEquiv`), followed by the reindexing `oddCollapseIndexEquiv`. -/
noncomputable def matrixSuperOddCollapse {K : Type*} [Field K] (P : SuperAlgebra K) (p q : ℕ)
    {w : P.carrier} (hw1 : w ∈ P.grading 1) (hw : IsUnit w) :
    SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper (p + q) 0) :=
  ⟨(diagUnitsConjAlgEquiv (K := K) (oddDiag p q hw.unit)).trans
      (Matrix.reindexAlgEquiv K P.carrier (oddCollapseIndexEquiv p q)),
    fun i => by
      show (matrixGradingA (sumParity p q) P.grading i).map
          ((Matrix.reindexAlgEquiv K P.carrier (oddCollapseIndexEquiv p q)).toLinearMap.comp
            (diagUnitsConjAlgEquiv (K := K) (oddDiag p q hw.unit)).toLinearMap)
        = matrixGradingA (sumParity (p + q) 0) P.grading i
      rw [Submodule.map_comp, diagUnitsConjAlgEquiv_map_matrixGradingA P.grading p q hw1 hw i,
        reindexAlgEquiv_map_matrixGradingA P.grading (fun _ => (0 : ZMod 2))
          (sumParity (p + q) 0) (oddCollapseIndexEquiv p q)
          (fun a => (sumParity_zero_right (p + q) _).symm) i]⟩

end OddCollapse

/-! ### The `DivisionFusionGauge` structure -/

universe u v w

/-- **The skeletal fusion data of a division gauge** (M9-2): a general group `G`
(`[AddGroup G]`, matching `stdTower`/`stdFuse`'s native `ZMod 8` convention), a family of
central super division representatives `D_a`, and size-tagged fusion isomorphisms
`φ_{a,b} : D_a ᵍ⊗ D_b ≅ M_{σ(a,b)}(D_{a+b})`.  No coherence is imposed on `φ`: its failure to
satisfy the pentagon is exactly the `(p, χ)` data measured downstream.  No section condition
`[D_a] = a` is imposed either — that is meaningful only once `G` is specialized to a
Brauer–Wall group (the later `DBWGauge`). -/
structure DivisionFusionGauge (K : Type u) [Field K] [Invertible (2 : K)] (G : Type v)
    [AddGroup G] where
  /-- The representative super division algebra at each skeleton index. -/
  D : G → SuperAlgebra.{u, w} K
  /-- Each representative is supercentral (§2.1). -/
  central : ∀ a, IsSuperCentral (D a).grading
  /-- Each representative is graded-simple (§2.1); together with `central` this is central
  simplicity, matching `PentagonParity`'s per-object hypotheses.  Not derived from `division`
  (that a super division algebra is graded-simple is unproved in this codebase). -/
  gradedSimple : ∀ a, IsGradedSimple (D a).grading
  /-- Each representative is a super division algebra (§2.1): every nonzero homogeneous
  element is a unit. -/
  division : ∀ a, Bimod.IsSuperDivision (D a).grading
  /-- Each representative is nontrivial, needed for `Bimod.finrank_D_pos`
  (`Superfusion.Gauge.SuperDivisionModule`) downstream. -/
  nontriv : ∀ a, Nontrivial (D a).carrier
  /-- Each representative is finite-dimensional over `K`. -/
  findim : ∀ a, FiniteDimensional K (D a).carrier
  /-- The matrix sizes `σ(a,b) = (p, q)` of the fusion isomorphism at `(a, b)`: *data*, not
  derived, exactly mirroring `stdFuse`'s `fuseSize`. -/
  size : G → G → ℕ × ℕ
  /-- **The fusion isomorphisms** `φ_{a,b}`, with *no* imposed coherence: `D_a ᵍ⊗ D_b ≅
  M_{σ(a,b)}(D_{a+b})`, spelled exactly as `stdFuse`'s target so the concrete `ℤ/8` instance
  (M9-4) is a literal fit. -/
  fuse : ∀ a b, SuperAlgEquiv ((D a).gtensor (D b))
    ((D (a + b)).matrixSuper (size a b).1 (size a b).2)

namespace DivisionFusionGauge

variable {K : Type u} [Field K] [Invertible (2 : K)] {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

/-! ### Derived basics -/

/-- **Total-size multiplicativity**: the fusion isomorphism transports `K`-dimension, giving
`finrank K (D a) * finrank K (D b) = (p+q)² · finrank K (D (a+b))` for `(p, q) = size a b`.
Route: the type-synonym identification `GradedTensorProduct.of` transports the ordinary
tensor-product finrank formula (`Module.finrank_tensorProduct`) across `gtensor`; the fusion
equivalence transports it onto the matrix side (`finrank_matrixSuper`,
`Superfusion.Gauge.SizeRigidity`). -/
theorem finrank_fuse (a b : G) :
    finrank K (Γ.D a).carrier * finrank K (Γ.D b).carrier
      = ((Γ.size a b).1 + (Γ.size a b).2) * ((Γ.size a b).1 + (Γ.size a b).2)
          * finrank K (Γ.D (a + b)).carrier := by
  haveI := Γ.findim a
  haveI := Γ.findim b
  have h1 : finrank K ((Γ.D a).gtensor (Γ.D b)).carrier
      = finrank K (Γ.D a).carrier * finrank K (Γ.D b).carrier := by
    show finrank K ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) = _
    rw [← (GradedTensorProduct.of K (Γ.D a).grading (Γ.D b).grading).finrank_eq]
    exact Module.finrank_tensorProduct
  have h2 := (Γ.fuse a b).toAlgEquiv.toLinearEquiv.finrank_eq
  rw [finrank_matrixSuper, h1] at h2
  exact h2

/-- **Total-size positivity**: `σ(a,b) = (p,q)` always has `p + q ≠ 0`.  If `p + q = 0` the
`finrank_fuse` identity would force `finrank K (D a) * finrank K (D b) = 0`, contradicting
`Bimod.finrank_D_pos` on both (nontrivial, finite-dimensional) factors. -/
theorem size_pos (a b : G) : (Γ.size a b).1 + (Γ.size a b).2 ≠ 0 := by
  intro h
  haveI := Γ.nontriv a
  haveI := Γ.nontriv b
  haveI := Γ.findim a
  haveI := Γ.findim b
  have hfr := Γ.finrank_fuse a b
  rw [h, zero_mul, zero_mul] at hfr
  exact (Nat.mul_ne_zero (Bimod.finrank_D_pos).ne' (Bimod.finrank_D_pos).ne') hfr

/-- **Size normalization**: the "even part dominates" convention on sizes, `q ≤ p` for
every `σ(a,b) = (p, q)`.  This presentation convention is unrelated to normalization at
the monoidal unit; see `DivisionFusionGauge.UnitalNormalization`. -/
def IsSizeNormalized : Prop := ∀ a b, (Γ.size a b).2 ≤ (Γ.size a b).1

end DivisionFusionGauge

/-! ### Size-composition normalization preservation -/

/-- **Pure `ℕ`-arithmetic composition-preserves-normalization fact**: `(p - q)(p' - q') ≥ 0`,
in cross-multiplied form.  This is exactly the fact needed for the composite size
`(p'*p + q'*q, p'*q + q'*p)` of `matrixSuperComp`/`collapseIndexEquiv`
(`Superfusion.Super.BWTransitivity`) to stay normalized when its two factors are — the
size-composition normalization preservation needed for later route-size coherence. -/
theorem size_compose_normalized {p q p' q' : ℕ} (hpq : q ≤ p) (hpq' : q' ≤ p') :
    p' * q + q' * p ≤ p' * p + q' * q := by
  obtain ⟨d, hd⟩ := Nat.le.dest hpq
  obtain ⟨d', hd'⟩ := Nat.le.dest hpq'
  subst hd hd'
  nlinarith [Nat.zero_le (d * d')]

end Superfusion
