/-
Superfusion / Gauge / RealGauge

Milestone M9-4 of the intrinsic gauge track: **the `ℝ` instance** — registering
the concrete tower `(ZMod 8, stdTower, stdFuse)` as a `DivisionFusionGauge ℝ (ZMod 8)`
(`Superfusion.Gauge.FusionGauge`).

**THE KEY FINDING of this round.**  The `central`, `gradedSimple`, `findim`, `nontriv`
fields of `DivisionFusionGauge` are already landed theorems (`stdTower_isSuperCentral`,
`stdTower_isGradedSimple`, and the `FiniteDimensional`/`Nontrivial` instances of
`Superfusion.Super.TowerStd`).  The one genuinely new obligation was **super-division**
of the eight towers, `Bimod.IsSuperDivision (stdTower a).grading` for `a : ZMod 8`.

Investigating this obligation reveals that **the concrete towers `stdTower a` are NOT all
super division algebras**: the classical fact "the eight Brauer–Wall division
representatives" and "the literal `2^n`-dimensional iterated odd-double tower
`divisionTower 1 n`" *coincide only for `n ≤ 3`*.  Concretely:

* `n = 0, 1, 2` are super division over **any** field with the relevant `ε ≠ 0`
  (`divisionTower_isSuperDivision_zero`, `_one`), and `n = 1, 2` over `ℝ` specifically via
  an explicit "sum of squares" invertibility argument (`divisionTower_isSuperDivision_one`,
  `divisionTower_isSuperDivision_two`, both `ε = 1`).
* `n = 4` is **not** super division, and neither is any `n ≥ 4`: the existing certificate
  `Superfusion.Super.QuaternionTower.towerFourQuatSuper : divisionTower 1 4 ≅ M_{1|1}(ℍ)`
  transports the matrix idempotent `E = diag(1, 0)` (nonzero, even, `E² = E ≠ 1`, hence a
  zero divisor, hence *not* a unit) back to a homogeneous non-unit of `divisionTower 1 4`
  (`divisionTower_not_isSuperDivision_four`).  A short general lemma
  (`homogeneousIdempotent_persists`) then **propagates this witness forward along the
  tower's own graded structure** — the map `a ↦ mk a 0` embeds `divisionTower ε n` into
  `divisionTower ε (n+1)` as a graded subalgebra, carrying nonzero-idempotent-`≠1` witnesses
  forward — giving **`divisionTower 1 n` not super division for every `n ≥ 4`** in one shot
  (`divisionTower_not_isSuperDivision_of_ge_four`), with no need for separate certificates at
  `n = 5, 6, 7`.  Since `stdTower a = divisionTower 1 a.val` and `a.val ≤ 7` always, this
  settles the question at `a.val ∈ {4, 5, 6, 7}` uniformly
  (`stdTower_not_isSuperDivision_of_val_ge_four`).

  Dimension-counting sanity check: the classical eight super division representatives of
  `BW(ℝ) ≅ ℤ/8` have dimensions `1, 2, 4, 8, 8, 4, 2, 1` (or a permutation thereof, per sign
  convention) — bounded by `8` — while the *tower* `divisionTower 1 n` has dimension `2ⁿ`,
  growing without bound; the two can only coincide while `2ⁿ ≤ 8`, i.e. `n ≤ 3`.  So this
  finding was to be expected on dimension grounds alone, and the quaternion certificate
  pins the failure at exactly `n = 4` (matching `[D₁]⁴ = [ℍ]` in the Brauer–Wall relation,
  `Superfusion.Super.QuaternionTower.isBWEquivalent_tower_four_quaternion`).

* `n = 3` (`a.val = 3`) is **left open this round**.  By-hand investigation (the classical
  "reversal norm" `rev(x) · x` argument, built recursively alongside the odd-double
  induction — route (a)/(b) of the task guidance) strongly suggests `divisionTower 1 3` *is*
  super division: the reversal-norm computation was verified by hand through the `n = 2 → 3`
  step (the first step where the base algebra `divisionTower 1 2` is non-commutative, so the
  cross-term cancellation is a genuine, non-formal identity, not a low-dimensional
  coincidence) and gives a positive sum-of-four-squares norm.  Formalizing this cleanly
  — either by building a reusable "graded reversal / Clifford-conjugation" antiautomorphism
  with a norm-multiplicativity lemma (route (a): no such machinery exists in the repo; "real
  work" per the task's own assessment), or by a direct 8-dimensional coordinate computation
  — is deferred to a follow-up round.  **No `sorry` is introduced for this**: the `a.val = 3`
  case is simply not stated as a theorem here.

**Consequence for this round's deliverable.**  Since `stdTower` is *not* super division at
every index (`a.val = 3` open, `a.val ≥ 4` refuted), `stdTower`/`stdFuse` **cannot** be
assembled into a `DivisionFusionGauge ℝ (ZMod 8)` as originally hoped — `division` is a
*field* of that structure, required for *every* `a : ZMod 8`.  Building the actual
`realGauge : DivisionFusionGauge ℝ (ZMod 8)` needs the **true** division representatives
`D_a` for `a.val ≥ 4` (smaller than the tower — e.g. the quaternion-matrix quotient
structure suggested by `towerFourQuatSuper` itself) together with *new* fusion isomorphisms
`D_a ᵍ⊗ D_b ≅ M_{σ(a,b)}(D_{a+b})` relating them back to the towers.  Constructing those
representatives and their fusion data is genuinely new work, deferred to a follow-up
milestone (M9-4b/c per the task's own naming).  This file's deliverable is therefore the
**division/non-division determination** above, together with the general-purpose lemmas
(`isUnit_of_conj_eq_algebraMap`, `homogeneousIdempotent_persists`) that a follow-up round can
reuse.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.GaugePentagon
import Superfusion.Super.TowerStd
import Superfusion.Super.QuaternionTower

namespace Superfusion

/-! ### A general unit criterion: `x` with a "conjugate" `y` satisfying two-sided
`x * y = y * x = algebraMap c`, `c ≠ 0`, is a unit. -/

/-- If `x` has a **conjugate** `y` with `y * x = x * y = algebraMap K A c` for a nonzero scalar
`c`, then `x` is a unit, with inverse `c⁻¹ • y`.  The special case `y = x` is the familiar
"a square equal to a nonzero scalar is a unit" fact; the general two-element form is what the
Clifford-style "reversal norm" argument produces (`rev x * x = x * rev x = N(x)`, `N(x) ≠ 0`
for `x ≠ 0`). -/
theorem isUnit_of_conj_eq_algebraMap {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {x y : A} {c : K} (hc : c ≠ 0) (h1 : y * x = algebraMap K A c)
    (h2 : x * y = algebraMap K A c) : IsUnit x := by
  refine ⟨⟨x, c⁻¹ • y, ?_, ?_⟩, rfl⟩
  · show x * (c⁻¹ • y) = 1
    rw [Algebra.mul_smul_comm, h2, Algebra.smul_def, ← map_mul, mul_comm c⁻¹ c,
      mul_inv_cancel₀ hc, map_one]
  · show (c⁻¹ • y) * x = 1
    rw [Algebra.smul_mul_assoc, h1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one]

/-- Specialization to `y = x`: a homogeneous element whose square is a nonzero scalar is a
unit. -/
theorem isUnit_of_sq_eq_algebraMap {K A : Type*} [Field K] [Ring A] [Algebra K A] {x : A}
    {c : K} (hc : c ≠ 0) (hx : x * x = algebraMap K A c) : IsUnit x :=
  isUnit_of_conj_eq_algebraMap hc hx hx

/-! ### Floor `0`: the base field is super division (already landed). -/

theorem divisionTower_isSuperDivision_zero {K : Type*} [Field K] :
    Bimod.IsSuperDivision (divisionTower (1 : K) 0).grading := by
  rw [divisionTower_zero]
  exact Bimod.IsSuperDivision.base

/-! ### Floor `1`: `K[θ]`, `θ² = ε ≠ 0`, is super division over any field. -/

section FloorOne

variable {K : Type*} [Field K] (ε : K)

private theorem mk_p_zero_mul_mk_p_zero (p p' : K) :
    OddDouble.mk (evenGrading K K) ε p 0 * OddDouble.mk (evenGrading K K) ε p' 0
      = OddDouble.mk (evenGrading K K) ε (p * p') 0 := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem mk_zero_q_mul_mk_zero_q (q q' : K) :
    OddDouble.mk (evenGrading K K) ε 0 q * OddDouble.mk (evenGrading K K) ε 0 q'
      = OddDouble.mk (evenGrading K K) ε (ε * (q * q')) 0 := by
  rw [OddDouble.mk_mul_mk, parityMap_of_mem_zero (evenGrading K K) (Submodule.mem_top (x := q'))]
  simp [smul_eq_mul]

private theorem mk_p_zero_mul_mk_zero_q (p q : K) :
    OddDouble.mk (evenGrading K K) ε p 0 * OddDouble.mk (evenGrading K K) ε 0 q
      = OddDouble.mk (evenGrading K K) ε 0 (p * q) := by
  rw [OddDouble.mk_mul_mk]; simp

private theorem mk_zero_q_mul_mk_p_zero (q p : K) :
    OddDouble.mk (evenGrading K K) ε 0 q * OddDouble.mk (evenGrading K K) ε p 0
      = OddDouble.mk (evenGrading K K) ε 0 (q * p) := by
  rw [OddDouble.mk_mul_mk, parityMap_of_mem_zero (evenGrading K K) (Submodule.mem_top (x := p))]
  simp

private theorem eq_mk_p_zero_of_mem_grading_zero {x : OddDouble (evenGrading K K) ε}
    (hx : x ∈ OddDouble.grading (evenGrading K K) ε 0) :
    x = OddDouble.mk (evenGrading K K) ε (OddDouble.p1 (evenGrading K K) ε x) 0 := by
  obtain ⟨-, h2⟩ := (OddDouble.mem_grading (evenGrading K K) ε).mp hx
  rw [zero_add, evenGrading_one, Submodule.mem_bot] at h2
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading K K) ε x]
  rw [h2]

private theorem eq_mk_zero_q_of_mem_grading_one {x : OddDouble (evenGrading K K) ε}
    (hx : x ∈ OddDouble.grading (evenGrading K K) ε 1) :
    x = OddDouble.mk (evenGrading K K) ε 0 (OddDouble.p2 (evenGrading K K) ε x) := by
  obtain ⟨h1, -⟩ := (OddDouble.mem_grading (evenGrading K K) ε).mp hx
  rw [evenGrading_one, Submodule.mem_bot] at h1
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading K K) ε x]
  rw [h1]

/-- **Floor `1` is super division** over any field: even homogeneous elements are scalars
(units, since `K` is a field), odd homogeneous elements `b·θ` square to the scalar `ε·b²`
(nonzero since `ε ≠ 0` and `K` has no zero divisors), hence are units. -/
theorem divisionTower_isSuperDivision_one (hε : ε ≠ 0) :
    Bimod.IsSuperDivision (divisionTower ε 1).grading := by
  show Bimod.IsSuperDivision (OddDouble.grading (evenGrading K K) ε)
  intro i x hx hx0
  rcases zmod2_cases i with hi | hi <;> subst hi
  · have hxeq := eq_mk_p_zero_of_mem_grading_zero ε hx
    have hp0 : OddDouble.p1 (evenGrading K K) ε x ≠ 0 := by
      intro h
      exact hx0 (by rw [hxeq, h]; exact OddDouble.ext _ _ (by simp) (by simp))
    rw [hxeq]
    exact (isUnit_iff_ne_zero.mpr hp0).map (algebraMap K (OddDouble (evenGrading K K) ε))
  · have hxeq := eq_mk_zero_q_of_mem_grading_one ε hx
    have hq0 : OddDouble.p2 (evenGrading K K) ε x ≠ 0 := by
      intro h
      exact hx0 (by rw [hxeq, h]; exact OddDouble.ext _ _ (by simp) (by simp))
    refine isUnit_of_sq_eq_algebraMap
      (mul_ne_zero hε (mul_ne_zero hq0 hq0)) ?_
    rw [hxeq]
    exact mk_zero_q_mul_mk_zero_q ε _ _

end FloorOne

/-! ### Floor `2` over `ℝ`: a sum-of-two-squares invertibility argument. -/

section FloorTwo

private theorem mk_zero_zero {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) :
    OddDouble.mk 𝒜 ε 0 0 = 0 :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

private theorem mk_eq_zero_iff {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) (a b : A) :
    OddDouble.mk 𝒜 ε a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => ⟨by simpa using congrArg (OddDouble.p1 𝒜 ε) h,
      by simpa using congrArg (OddDouble.p2 𝒜 ε) h⟩,
    fun ⟨ha, hb⟩ => by rw [ha, hb]; exact mk_zero_zero 𝒜 ε⟩

private theorem mk_add_mk {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) (a b a' b' : A) :
    OddDouble.mk 𝒜 ε a b + OddDouble.mk 𝒜 ε a' b' = OddDouble.mk 𝒜 ε (a + a') (b + b') :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

private theorem algebraMap_real_eq_mk (ε c : ℝ) :
    algebraMap ℝ (OddDouble (evenGrading ℝ ℝ) ε) c = OddDouble.mk (evenGrading ℝ ℝ) ε c 0 :=
  OddDouble.ext _ _ (by simp) (by simp)

private theorem algebraMap_real_eq_mk2 (c : ℝ) :
    algebraMap ℝ (OddDouble (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)) c
      = OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)
          (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) c 0) 0 :=
  OddDouble.ext _ _ (by rw [OddDouble.p1_algebraMap]; exact algebraMap_real_eq_mk 1 c) (by simp)

private theorem parityMap_mk_p_zero (p : ℝ) :
    parityMap (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ))
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) p 0)
      = OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) p 0 :=
  parityMap_of_mem_zero _ (OddDouble.mk_mem_grading _ _ Submodule.mem_top (Submodule.zero_mem _))

private theorem parityMap_mk_zero_q (q : ℝ) :
    parityMap (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ))
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 q)
      = OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 (-q) := by
  rw [parityMap_of_mem_one _
    (OddDouble.mk_mem_grading _ _ (Submodule.zero_mem _) Submodule.mem_top)]
  exact OddDouble.ext _ _ (by simp) (by simp)

/-- **Floor `2` is super division over `ℝ`**: a homogeneous element of `divisionTower 1 2`
decomposes (via floor `1`'s scalar coordinatization) into a pair of real numbers, and its
Clifford-conjugate product is the positive scalar sum of their squares.  The floor is fully
unfolded (`(divisionTower 1 1).grading = OddDouble.grading (evenGrading ℝ ℝ) 1`, etc.) at the
top via `show`, so all subsequent term-level reasoning happens at a single, consistent
`OddDouble`-level type throughout (avoiding the recurring `divisionTower`-vs-`OddDouble`
instance-path mismatches that plague naive unfolding mid-proof). -/
theorem divisionTower_isSuperDivision_two :
    Bimod.IsSuperDivision (divisionTower (1 : ℝ) 2).grading := by
  show Bimod.IsSuperDivision
    (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ))
  intro i x hx hx0
  obtain ⟨ha, hb⟩ :=
    (OddDouble.mem_grading (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)).mp hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · -- even: x = mk a b, a ∈ floor1-even (a = mk p 0), b ∈ floor1-odd (b = mk 0 q)
    set p := OddDouble.p1 (evenGrading ℝ ℝ) (1 : ℝ)
      (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x) with hpdef
    set q := OddDouble.p2 (evenGrading ℝ ℝ) (1 : ℝ)
      (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x) with hqdef
    have hxeq : x = OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) p 0)
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 q) := by
      conv_lhs =>
        rw [← OddDouble.mk_p1_p2 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x]
      rw [eq_mk_p_zero_of_mem_grading_zero (1 : ℝ) ha,
        eq_mk_zero_q_of_mem_grading_one (1 : ℝ) hb]
    have hpq0 : p ≠ 0 ∨ q ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx0
      rw [hxeq, hcon.1, hcon.2]
      simp only [mk_zero_zero]
    have hc : (p * p + q * q) ≠ 0 := fun h => hpq0.elim
      (fun hp => hp (by nlinarith [sq_nonneg q])) (fun hq => hq (by nlinarith [sq_nonneg p]))
    rw [hxeq]
    refine isUnit_of_conj_eq_algebraMap (y := OddDouble.mk
        (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) p 0)
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 (-q))) hc ?_ ?_
    · rw [algebraMap_real_eq_mk2, OddDouble.mk_mul_mk, parityMap_mk_zero_q, parityMap_mk_p_zero,
        mk_p_zero_mul_mk_p_zero, mk_zero_q_mul_mk_zero_q, mk_p_zero_mul_mk_zero_q,
        mk_zero_q_mul_mk_p_zero, one_smul, mk_add_mk, mk_add_mk]
      congr 1
      · congr 1 <;> ring
      · rw [mk_eq_zero_iff]; exact ⟨by ring, by ring⟩
    · rw [algebraMap_real_eq_mk2, OddDouble.mk_mul_mk, parityMap_mk_zero_q, parityMap_mk_p_zero,
        mk_p_zero_mul_mk_p_zero, mk_zero_q_mul_mk_zero_q, mk_p_zero_mul_mk_zero_q,
        mk_zero_q_mul_mk_p_zero, one_smul, mk_add_mk, mk_add_mk]
      congr 1
      · congr 1 <;> ring
      · rw [mk_eq_zero_iff]; exact ⟨by ring, by ring⟩
  · -- odd: x = mk a b, a ∈ floor1-odd (a = mk 0 a'), b ∈ floor1-even (b = mk b' 0)
    rw [show (1 : ZMod 2) + 1 = 0 from by decide] at hb
    set a' := OddDouble.p2 (evenGrading ℝ ℝ) (1 : ℝ)
      (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x) with hadef
    set b' := OddDouble.p1 (evenGrading ℝ ℝ) (1 : ℝ)
      (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x) with hbdef
    have hxeq : x = OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ)
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) 0 a')
        (OddDouble.mk (evenGrading ℝ ℝ) (1 : ℝ) b' 0) := by
      conv_lhs =>
        rw [← OddDouble.mk_p1_p2 (OddDouble.grading (evenGrading ℝ ℝ) (1 : ℝ)) (1 : ℝ) x]
      rw [eq_mk_zero_q_of_mem_grading_one (1 : ℝ) ha,
        eq_mk_p_zero_of_mem_grading_zero (1 : ℝ) hb]
    have hab0 : a' ≠ 0 ∨ b' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx0
      rw [hxeq, hcon.1, hcon.2]
      simp only [mk_zero_zero]
    have hc : (a' * a' + b' * b') ≠ 0 := fun h => hab0.elim
      (fun ha' => ha' (by nlinarith [sq_nonneg b'])) (fun hb' => hb' (by nlinarith [sq_nonneg a']))
    rw [hxeq]
    refine isUnit_of_sq_eq_algebraMap hc ?_
    rw [algebraMap_real_eq_mk2, OddDouble.mk_mul_mk, parityMap_mk_p_zero, parityMap_mk_zero_q,
      mk_zero_q_mul_mk_zero_q, mk_p_zero_mul_mk_p_zero, mk_zero_q_mul_mk_p_zero,
      mk_p_zero_mul_mk_zero_q, one_smul, mk_add_mk, mk_add_mk]
    congr 1
    · congr 1 <;> ring
    · rw [mk_eq_zero_iff]; exact ⟨by ring, by ring⟩

end FloorTwo

/-! ### Floors `≥ 4`: not super division, via a persisting idempotent witness. -/

section HighFloors

open Quaternion

variable {K : Type*} [Field K] {ε : K}

/-- The graded embedding `divisionTower ε n → divisionTower ε (n + 1)`, `a ↦ mk a 0`: it is
injective, sends `1 ↦ 1`, and is multiplicative (immediate from `OddDouble.mk_mul_mk`, the
`ε`-term dropping since the second coordinate is `0`). -/
private theorem mk_embed_mul {n : ℕ} (a a' : (divisionTower ε n).carrier) :
    OddDouble.mk (divisionTower ε n).grading ε a 0
      * OddDouble.mk (divisionTower ε n).grading ε a' 0
      = OddDouble.mk (divisionTower ε n).grading ε (a * a') 0 := by
  rw [OddDouble.mk_mul_mk]; simp

/-- **A homogeneous idempotent `≠ 0, 1` persists forward through the tower**: if some floor
`n` has a nonzero, non-unital idempotent of a fixed degree `i`, so does every higher floor
`m ≥ n` (same degree `i`), via the graded embedding `a ↦ mk a 0` iterated `m - n` times. Any
such witness shows the floor is *not* super division (an idempotent `e ≠ 0, 1` is never a
unit: `e * e = e` forces `e = 1` by cancellation). -/
theorem homogeneousIdempotent_persists {n : ℕ} {i : ZMod 2} {e : (divisionTower ε n).carrier}
    (hei : e ∈ (divisionTower ε n).grading i) (he2 : e * e = e) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    ∀ m, n ≤ m → ∃ e' : (divisionTower ε m).carrier,
      e' ∈ (divisionTower ε m).grading i ∧ e' * e' = e' ∧ e' ≠ 0 ∧ e' ≠ 1 := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨e, hei, he2, he0, he1⟩
  | succ m _ ih =>
      obtain ⟨e', hei', he2', he0', he1'⟩ := ih
      refine ⟨OddDouble.mk (divisionTower ε m).grading ε e' 0, ?_, ?_, ?_, ?_⟩
      · exact OddDouble.mk_mem_grading _ _ hei' (Submodule.zero_mem _)
      · show OddDouble.mk (divisionTower ε m).grading ε e' 0
            * OddDouble.mk (divisionTower ε m).grading ε e' 0
          = OddDouble.mk (divisionTower ε m).grading ε e' 0
        rw [mk_embed_mul, he2']
      · show (OddDouble.mk (divisionTower ε m).grading ε e' 0 :
            OddDouble (divisionTower ε m).grading ε) ≠ 0
        intro h
        exact he0' (by simpa using congrArg (OddDouble.p1 (divisionTower ε m).grading ε) h)
      · show (OddDouble.mk (divisionTower ε m).grading ε e' 0 :
            OddDouble (divisionTower ε m).grading ε) ≠ 1
        intro h
        exact he1' (by simpa using congrArg (OddDouble.p1 (divisionTower ε m).grading ε) h)

/-- An idempotent that is also a unit is `1` (cancel `e` from `e * e = e = e * 1` by
multiplying by its inverse). -/
private theorem eq_one_of_isUnit_of_sq_eq_self {A : Type*} [Ring A] {e : A} (he2 : e * e = e)
    (heu : IsUnit e) : e = 1 := by
  obtain ⟨u, hu⟩ := heu
  rw [← hu]
  have hu2 : (u : A) * (u : A) = (u : A) := by rw [hu]; exact he2
  have h3 := congrArg (fun z => (↑u⁻¹ : A) * z) hu2
  simp only [← mul_assoc, Units.inv_mul, one_mul] at h3
  exact h3

/-- **The floor-`4` idempotent witness**: transporting the matrix idempotent
`diag(1, 0) ∈ M_{1|1}(ℍ[K])` back along `Superfusion.Super.QuaternionTower.towerFourQuatSuper`
gives a nonzero, `≠ 1`, even idempotent of `divisionTower 1 4`. -/
theorem floorFourIdempotentWitness (K : Type*) [Field K] [Invertible (2 : K)] :
    ∃ e : (divisionTower (1 : K) 4).carrier, e ∈ (divisionTower (1 : K) 4).grading 0 ∧
      e * e = e ∧ e ≠ 0 ∧ e ≠ 1 := by
  set E : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℍ[K] :=
    Matrix.diagonal (Sum.elim (fun _ => (1 : ℍ[K])) (fun _ => 0)) with hEdef
  have hE2 : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    cases a <;> simp
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    simp [hEdef] at this
  have hE1 : E ≠ 1 := by
    intro h
    have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
    simp [hEdef] at this
  have hEmem : E ∈ matrixGradingA (sumParity 1 1) (evenGrading K ℍ[K]) 0 := by
    rw [mem_matrixGradingA]
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · have hab : a = b := Subsingleton.elim a b
      subst hab
      rw [hEdef, Matrix.diagonal_apply_eq]
      simp [sumParity]
    · rw [hEdef, Matrix.diagonal_apply_ne _ (by simp : (Sum.inl a : Fin 1 ⊕ Fin 1) ≠ Sum.inr b)]
      exact zero_mem _
    · rw [hEdef, Matrix.diagonal_apply_ne _ (by simp : (Sum.inr a : Fin 1 ⊕ Fin 1) ≠ Sum.inl b)]
      exact zero_mem _
    · rw [hEdef]
      by_cases hab : a = b
      · subst hab; rw [Matrix.diagonal_apply_eq]; exact zero_mem _
      · rw [Matrix.diagonal_apply_ne _ (by simp [hab])]; exact zero_mem _
  set f := (towerFourQuatSuper K).symm.toAlgEquiv with hfdef
  refine ⟨f E, ?_, ?_, ?_, ?_⟩
  · rw [hfdef, ← (towerFourQuatSuper K).symm.map_grading 0]
    exact Submodule.mem_map.mpr ⟨E, hEmem, rfl⟩
  · rw [← map_mul]
    exact congrArg f hE2
  · intro h
    exact hE0 (f.injective (h.trans (map_zero f).symm))
  · intro h
    exact hE1 (f.injective (h.trans (map_one f).symm))

/-- **Floor `4` is not super division**. -/
theorem divisionTower_not_isSuperDivision_four {K : Type*} [Field K] [Invertible (2 : K)] :
    ¬ Bimod.IsSuperDivision (divisionTower (1 : K) 4).grading := by
  intro hdiv
  obtain ⟨e, hem, he2, he0, he1⟩ := floorFourIdempotentWitness K
  exact he1 (eq_one_of_isUnit_of_sq_eq_self he2 (hdiv hem he0))

/-- **Every floor `n ≥ 4` is not super division**: the idempotent witness at floor `4`
(`floorFourIdempotentWitness`) propagates forward via `homogeneousIdempotent_persists`. -/
theorem divisionTower_not_isSuperDivision_of_ge_four {K : Type*} [Field K] [Invertible (2 : K)]
    {n : ℕ} (hn : 4 ≤ n) : ¬ Bimod.IsSuperDivision (divisionTower (1 : K) n).grading := by
  intro hdiv
  obtain ⟨e, hem, he2, he0, he1⟩ := floorFourIdempotentWitness K
  obtain ⟨e', hem', he2', he0', he1'⟩ :=
    homogeneousIdempotent_persists hem he2 he0 he1 n hn
  exact he1' (eq_one_of_isUnit_of_sq_eq_self he2' (hdiv hem' he0'))

end HighFloors

/-! ### The `stdTower` (`ZMod 8`) classification, over `ℝ` -/

noncomputable instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

/-- **`stdTower a` is super division for `a.val ≤ 2`**: `stdTower a = divisionTower 1 a.val`,
and floors `0, 1, 2` are super division (`divisionTower_isSuperDivision_zero`, `_one`,
`_two`). -/
theorem stdTower_isSuperDivision (a : ZMod 8) (h : a.val ≤ 2) :
    Bimod.IsSuperDivision (stdTower (K := ℝ) a).grading := by
  show Bimod.IsSuperDivision (divisionTower (1 : ℝ) a.val).grading
  have h0 : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
  rcases h0 with h0 | h0 | h0
  · rw [h0]; exact divisionTower_isSuperDivision_zero
  · rw [h0]; exact divisionTower_isSuperDivision_one 1 one_ne_zero
  · rw [h0]; exact divisionTower_isSuperDivision_two

/-- **`stdTower a` is NOT super division for `a.val ≥ 4`**: since `a.val ≤ 7` always
(`a : ZMod 8`), this settles `a.val ∈ {4, 5, 6, 7}` uniformly via
`divisionTower_not_isSuperDivision_of_ge_four`. -/
theorem stdTower_not_isSuperDivision_of_val_ge_four (a : ZMod 8) (h : 4 ≤ a.val) :
    ¬ Bimod.IsSuperDivision (stdTower (K := ℝ) a).grading := by
  show ¬ Bimod.IsSuperDivision (divisionTower (1 : ℝ) a.val).grading
  exact divisionTower_not_isSuperDivision_of_ge_four h

end Superfusion
