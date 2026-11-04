/-
Superfusion / Gauge / RealReps

Milestone M9-4b-i of the intrinsic gauge track: **the eight real super
division representatives and their division proofs** (Table 1 of the
paper, `docs/paper-tables-extract.md`).

Three deliverables:

1. The `ε = -1` floors `1, 2, 3` of the division tower are super division
   over `ℝ` (`divisionTower_neg_isSuperDivision_one/_two/_three`).  The
   route is a **general lemma** (`isSuperDivision_of_evenDivision_oddUnit`):
   a superalgebra whose even part is a division ring and which has *some*
   odd unit is automatically super division (the odd unit's inverse
   trades any nonzero odd element for a nonzero even one, via
   `Bimod.isUnit_inv_mem`).  Combined with a direct "conjugate norm"
   computation (`E_mul_E`, `O_mul_O`) this closes not only the `ε = -1`
   floors but, uniformly, **every floor `n ≤ 3` at every `ε ≠ 0`** —
   in particular it retroactively closes the `ε = 1, n = 3` case left
   open by `Superfusion.Gauge.RealGauge` (`divisionTower_pos_isSuperDivision_three`).
2. `quatEvenSuper`: the purely even quaternion superalgebra (`D₄` of the
   table), reusing `Superfusion.Super.QuaternionTower.SuperAlgebra.quaternion`,
   with its division/central/simple/findim/nontriv bundle.
3. `realRep : ZMod 8 → SuperAlgebra ℝ`, the eight-representative family,
   with `realRep_isSuperDivision`.

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealGauge
import Superfusion.Super.QuaternionTower

namespace Superfusion

open Quaternion

/-! ### A general lemma: even division + one odd unit ⟹ super division -/

/-- **If the even part of a superalgebra is a division ring and some odd
element is a unit, the whole superalgebra is super division.**  Given a
nonzero odd `x`, write `x = u • z` with `z = u⁻¹ x` even (`u⁻¹` is odd
again, `Bimod.isUnit_inv_mem`); `z ≠ 0` since `x ≠ 0`, hence a unit by
hypothesis, hence `x = u * z` is a unit. -/
theorem isSuperDivision_of_evenDivision_oddUnit {K D : Type*} [Field K] [Ring D]
    [Algebra K D] {𝒟 : ZMod 2 → Submodule K D} [GradedAlgebra 𝒟]
    (h0 : ∀ x : D, x ∈ 𝒟 0 → x ≠ 0 → IsUnit x) {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) : Bimod.IsSuperDivision 𝒟 := by
  intro i x hx hx0
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact h0 x hx hx0
  · set v := ((hu.unit⁻¹ : Dˣ) : D) with hv
    have hv1 : v ∈ 𝒟 1 := Bimod.isUnit_inv_mem hu1 hu.unit hu.unit_spec
    have huv : u * v = 1 := by
      have h2 := hu.unit.mul_inv
      rwa [hu.unit_spec] at h2
    set z := v * x with hzdef
    have hz1 : z ∈ 𝒟 0 := by
      have h := SetLike.mul_mem_graded hv1 hx
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
    have huz : u * z = x := by rw [hzdef, ← mul_assoc, huv, one_mul]
    have hzne : z ≠ 0 := fun h => hx0 (by rw [← huz, h, mul_zero])
    have hzu : IsUnit z := h0 z hz1 hzne
    rw [← huz]
    exact hu.mul hzu

/-! ### Floor `1`, `ε = -1` -/

/-- **Floor `1` at `ε = -1` is super division over `ℝ`**: an instance of
the field-generic `divisionTower_isSuperDivision_one`. -/
theorem divisionTower_neg_isSuperDivision_one :
    Bimod.IsSuperDivision (divisionTower (-1 : ℝ) 1).grading :=
  divisionTower_isSuperDivision_one (-1 : ℝ) (by norm_num)

/-! ### Shared machinery for floors `2` and `3`, uniform over `ε ≠ 0`

Both floors are handled by a single **conjugate-norm computation**: an
element `x` of floor `n` decomposes (recursively, via floors `n - 1` and
`n - 2`) into two "shapes" — `E ε p q` (even, `p + q·(e₁e₂)`-like) and
`O ε r s` (odd, `r·e₁ + s·e₂`-like) — and the multiplication table on
these shapes (`E_mul_E`, `E_mul_O`, `O_mul_E`, `O_mul_O`) is *ε-uniform*:
every norm that appears is a sum of squares scaled by `ε²`, hence
positive whenever `ε ≠ 0`, over `ℝ`. -/

section Machinery

/-- The floor-`1` multiplication table, in raw real coordinates
(`K[θ]`, `θ² = ε`). -/
private theorem floor1_mul (ε p q p' q' : ℝ) :
    OddDouble.mk (evenGrading ℝ ℝ) ε p q * OddDouble.mk (evenGrading ℝ ℝ) ε p' q'
      = OddDouble.mk (evenGrading ℝ ℝ) ε (p * p' + ε * (q * q')) (p * q' + q * p') := by
  rw [OddDouble.mk_mul_mk, parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top,
    parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, smul_eq_mul]

/-- The base parity map (`evenGrading`) is the identity. -/
private theorem parityMap_evenGrading (x : ℝ) : parityMap (evenGrading ℝ ℝ) x = x :=
  parityMap_of_mem_zero _ Submodule.mem_top

/-- Floor `1`'s own parity map fixes the even shape `mk p 0`. -/
private theorem parityMap_mk_p_zero (ε p : ℝ) :
    parityMap (OddDouble.grading (evenGrading ℝ ℝ) ε) (OddDouble.mk (evenGrading ℝ ℝ) ε p 0)
      = OddDouble.mk (evenGrading ℝ ℝ) ε p 0 :=
  parityMap_of_mem_zero _ (OddDouble.mk_mem_grading _ _ Submodule.mem_top (Submodule.zero_mem _))

/-- Floor `1`'s own parity map negates the odd shape `mk 0 q`. -/
private theorem parityMap_mk_zero_q (ε q : ℝ) :
    parityMap (OddDouble.grading (evenGrading ℝ ℝ) ε) (OddDouble.mk (evenGrading ℝ ℝ) ε 0 q)
      = OddDouble.mk (evenGrading ℝ ℝ) ε 0 (-q) := by
  rw [parityMap_of_mem_one _ (OddDouble.mk_mem_grading _ _ (Submodule.zero_mem _) Submodule.mem_top)]
  exact OddDouble.ext _ _ (by simp) (by simp)

/-- Componentwise addition of `mk`'s (generic, any base superalgebra). -/
private theorem mk_add_mk {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) (a b a' b' : A) :
    OddDouble.mk 𝒜 ε a b + OddDouble.mk 𝒜 ε a' b' = OddDouble.mk 𝒜 ε (a + a') (b + b') :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

/-- Componentwise negation of `mk`'s. -/
private theorem neg_mk {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) (a b : A) :
    -(OddDouble.mk 𝒜 ε a b) = OddDouble.mk 𝒜 ε (-a) (-b) :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

/-- Componentwise scalar multiplication of `mk`'s. -/
private theorem mk_smul {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε c : K) (a b : A) :
    c • OddDouble.mk 𝒜 ε a b = OddDouble.mk 𝒜 ε (c • a) (c • b) :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

/-- `mk 0 0 = 0` (generic). -/
private theorem mk_zero_zero {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K) :
    OddDouble.mk 𝒜 ε 0 0 = 0 :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

/-- `algebraMap` unfolds to `mk (algebraMap _) 0` (generic, any level). -/
private theorem algebraMap_eq_mk {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε r : K) :
    algebraMap K (OddDouble 𝒜 ε) r = OddDouble.mk 𝒜 ε (algebraMap K A r) 0 :=
  OddDouble.ext 𝒜 ε (by simp) (by simp)

/-- The real scalar `c` sits inside floor `2` as `mk (mk c 0) 0`. -/
private theorem algebraMap_floor2_eq (ε c : ℝ) :
    algebraMap ℝ (OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) c
      = OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) ε) ε
          (OddDouble.mk (evenGrading ℝ ℝ) ε c 0) 0 := by
  rw [algebraMap_eq_mk (OddDouble.grading (evenGrading ℝ ℝ) ε) ε c,
    algebraMap_eq_mk (evenGrading ℝ ℝ) ε c, Algebra.algebraMap_self_apply]

/-- The real scalar `c` sits inside floor `3` as `mk (mk (mk c 0) 0) 0`. -/
private theorem algebraMap_floor3_eq (ε c : ℝ) :
    algebraMap ℝ (OddDouble (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε) c
      = OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
          (OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) ε) ε
            (OddDouble.mk (evenGrading ℝ ℝ) ε c 0) 0) 0 := by
  rw [algebraMap_eq_mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε c,
    algebraMap_floor2_eq]

/-- The "even shape" of floor `2`: `p + q·(e₁e₂)`. -/
private noncomputable def E (ε p q : ℝ) : OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε :=
  OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) ε) ε
    (OddDouble.mk (evenGrading ℝ ℝ) ε p 0) (OddDouble.mk (evenGrading ℝ ℝ) ε 0 q)

/-- The "odd shape" of floor `2`: `r·e₁ + s·e₂`. -/
private noncomputable def O (ε r s : ℝ) : OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε :=
  OddDouble.mk (OddDouble.grading (evenGrading ℝ ℝ) ε) ε
    (OddDouble.mk (evenGrading ℝ ℝ) ε 0 r) (OddDouble.mk (evenGrading ℝ ℝ) ε s 0)

private theorem E_mem_zero (ε p q : ℝ) :
    E ε p q ∈ OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε 0 := by
  simp only [E]
  exact OddDouble.mk_mem_grading _ _
    (OddDouble.mk_mem_grading _ _ Submodule.mem_top (Submodule.zero_mem _))
    (OddDouble.mk_mem_grading _ _ (Submodule.zero_mem _) Submodule.mem_top)

private theorem O_mem_one (ε r s : ℝ) :
    O ε r s ∈ OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε 1 := by
  simp only [O]
  exact OddDouble.mk_mem_grading _ _
    (OddDouble.mk_mem_grading _ _ (Submodule.zero_mem _) Submodule.mem_top)
    (OddDouble.mk_mem_grading _ _ Submodule.mem_top (Submodule.zero_mem _))

private theorem E_zero_zero (ε : ℝ) : E ε 0 0 = 0 := by
  simp only [E, mk_zero_zero]

private theorem O_zero_zero (ε : ℝ) : O ε 0 0 = 0 := by
  simp only [O, mk_zero_zero]

private theorem E_eq_zero_iff (ε p q : ℝ) : E ε p q = 0 ↔ p = 0 ∧ q = 0 := by
  simp only [E]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrArg (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) h
      simp only [OddDouble.p1_mk, map_zero] at h1
      have h2 := congrArg (OddDouble.p1 (evenGrading ℝ ℝ) ε) h1
      simpa using h2
    · have h1 := congrArg (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) h
      simp only [OddDouble.p2_mk, map_zero] at h1
      have h2 := congrArg (OddDouble.p2 (evenGrading ℝ ℝ) ε) h1
      simpa using h2
  · rintro ⟨hp, hq⟩
    simp [hp, hq, mk_zero_zero]

private theorem O_eq_zero_iff (ε r s : ℝ) : O ε r s = 0 ↔ r = 0 ∧ s = 0 := by
  simp only [O]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrArg (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) h
      simp only [OddDouble.p1_mk, map_zero] at h1
      have h2 := congrArg (OddDouble.p2 (evenGrading ℝ ℝ) ε) h1
      simpa using h2
    · have h1 := congrArg (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) h
      simp only [OddDouble.p2_mk, map_zero] at h1
      have h2 := congrArg (OddDouble.p1 (evenGrading ℝ ℝ) ε) h1
      simpa using h2
  · rintro ⟨hr, hs⟩
    simp [hr, hs, mk_zero_zero]

/-- `E ε p q * E ε p' q' = E ε (p p' - ε² q q') (p q' + q p')`. -/
private theorem E_mul_E (ε p q p' q' : ℝ) :
    E ε p q * E ε p' q' = E ε (p * p' - ε * ε * (q * q')) (p * q' + q * p') := by
  simp only [E]
  refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_mk_zero_q, parityMap_mk_p_zero] <;>
    refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_evenGrading, smul_eq_mul, map_add, map_smul] <;>
    ring

/-- `E ε p q * O ε r' s' = O ε (p r' + ε q s') (p s' - ε q r')`. -/
private theorem E_mul_O (ε p q r' s' : ℝ) :
    E ε p q * O ε r' s' = O ε (p * r' + ε * (q * s')) (p * s' - ε * (q * r')) := by
  simp only [E, O]
  refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_mk_zero_q, parityMap_mk_p_zero] <;>
    refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_evenGrading, smul_eq_mul, map_add, map_smul] <;>
    ring

/-- `O ε r s * E ε p' q' = O ε (r p' - ε s q') (ε r q' + s p')`. -/
private theorem O_mul_E (ε r s p' q' : ℝ) :
    O ε r s * E ε p' q' = O ε (r * p' - ε * (s * q')) (ε * (r * q') + s * p') := by
  simp only [O, E]
  refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_mk_zero_q, parityMap_mk_p_zero] <;>
    refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_evenGrading, smul_eq_mul, map_add, map_smul] <;>
    ring

/-- `O ε r s * O ε r' s' = E ε (ε (r r' + s s')) (r s' - s r')`. -/
private theorem O_mul_O (ε r s r' s' : ℝ) :
    O ε r s * O ε r' s' = E ε (ε * (r * r' + s * s')) (r * s' - s * r') := by
  simp only [O, E]
  refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_mk_p_zero, parityMap_mk_zero_q] <;>
    refine OddDouble.ext _ _ ?_ ?_ <;>
    simp only [OddDouble.p1_mul, OddDouble.p2_mul, OddDouble.p1_mk, OddDouble.p2_mk,
      parityMap_evenGrading, smul_eq_mul, map_add, map_smul] <;>
    ring

/-! ### Membership → shape conversion, and the `algebraMap`/parity facts needed for floor `3` -/

private theorem eq_mk_p_zero_of_mem_grading_zero {ε : ℝ} {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 0) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε (OddDouble.p1 (evenGrading ℝ ℝ) ε x) 0 := by
  obtain ⟨-, h2⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [zero_add, evenGrading_one, Submodule.mem_bot] at h2
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h2]

private theorem eq_mk_zero_q_of_mem_grading_one {ε : ℝ} {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 1) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε 0 (OddDouble.p2 (evenGrading ℝ ℝ) ε x) := by
  obtain ⟨h1, -⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [evenGrading_one, Submodule.mem_bot] at h1
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h1]

private theorem eq_E_of_mem_grading_zero {ε : ℝ}
    {A : OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε}
    (hA : A ∈ OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε 0) :
    ∃ p q, A = E ε p q := by
  obtain ⟨h1, h2⟩ := (OddDouble.mem_grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε).mp hA
  rw [zero_add] at h2
  refine ⟨OddDouble.p1 (evenGrading ℝ ℝ) ε (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε A),
    OddDouble.p2 (evenGrading ℝ ℝ) ε (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε A), ?_⟩
  simp only [E]
  conv_lhs => rw [← OddDouble.mk_p1_p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε A]
  congr 1
  · exact eq_mk_p_zero_of_mem_grading_zero h1
  · exact eq_mk_zero_q_of_mem_grading_one h2

private theorem eq_O_of_mem_grading_one {ε : ℝ}
    {B : OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε}
    (hB : B ∈ OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε 1) :
    ∃ r s, B = O ε r s := by
  obtain ⟨h1, h2⟩ := (OddDouble.mem_grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε).mp hB
  rw [show (1 : ZMod 2) + 1 = 0 from by decide] at h2
  refine ⟨OddDouble.p2 (evenGrading ℝ ℝ) ε (OddDouble.p1 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε B),
    OddDouble.p1 (evenGrading ℝ ℝ) ε (OddDouble.p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε B), ?_⟩
  simp only [O]
  conv_lhs => rw [← OddDouble.mk_p1_p2 (OddDouble.grading (evenGrading ℝ ℝ) ε) ε B]
  congr 1
  · exact eq_mk_zero_q_of_mem_grading_one h1
  · exact eq_mk_p_zero_of_mem_grading_zero h2

private theorem E_c_zero_eq_algebraMap (ε c : ℝ) :
    E ε c 0 = algebraMap ℝ (OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) c := by
  simp only [E, mk_zero_zero]
  exact (algebraMap_floor2_eq ε c).symm

private theorem parityMap_E_mem_zero (ε p q : ℝ) :
    parityMap (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) (E ε p q) = E ε p q :=
  parityMap_of_mem_zero _ (E_mem_zero ε p q)

private theorem parityMap_O_mem_one (ε r s : ℝ) :
    parityMap (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) (O ε r s)
      = -(O ε r s) :=
  parityMap_of_mem_one _ (O_mem_one ε r s)

private theorem E_add_E (ε p q p' q' : ℝ) : E ε p q + E ε p' q' = E ε (p + p') (q + q') := by
  simp only [E, mk_add_mk, add_zero]

private theorem O_add_O (ε r s r' s' : ℝ) : O ε r s + O ε r' s' = O ε (r + r') (s + s') := by
  simp only [O, mk_add_mk, add_zero]

private theorem E_smul (ε c p q : ℝ) : c • E ε p q = E ε (c * p) (c * q) := by
  simp only [E, mk_smul, smul_eq_mul, mul_zero]

private theorem O_neg (ε r s : ℝ) : -(O ε r s) = O ε (-r) (-s) := by
  simp only [O, neg_mk, neg_zero]

/-- `algebraMap` unfolds one level into floor `3`, exposing the shape `E`. -/
private theorem algebraMap_floor3_eq' (ε c : ℝ) :
    algebraMap ℝ (OddDouble (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε) c
      = OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
          (E ε c 0) 0 := by
  rw [algebraMap_eq_mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε c,
    ← E_c_zero_eq_algebraMap]

/-! ### The conjugate-norm identity at floor `3`: `X · X̄ = X̄ · X = p² + ε²(q² + r² + s²)` -/

private theorem X_mul_Xbar (ε p q r s : ℝ) :
    OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
        (E ε p q) (O ε r s)
      * OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
        (E ε p (-q)) (-(O ε r s))
      = algebraMap ℝ (OddDouble (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε)
          (p * p + ε * ε * (q * q + r * r + s * s)) := by
  refine OddDouble.ext _ _ ?_ ?_
  · simp only [algebraMap_floor3_eq', OddDouble.p1_mul, OddDouble.p1_mk,
      OddDouble.p2_mk, map_neg, parityMap_O_mem_one, neg_neg]
    rw [E_mul_E, O_mul_O, E_smul, E_add_E]
    congr 1 <;> ring
  · simp only [algebraMap_floor3_eq', OddDouble.p2_mul, OddDouble.p1_mk,
      OddDouble.p2_mk, parityMap_E_mem_zero]
    rw [mul_neg, E_mul_O, O_mul_E, O_neg, O_add_O, ← O_zero_zero ε]
    congr 1 <;> ring

private theorem Xbar_mul_X (ε p q r s : ℝ) :
    OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
        (E ε p (-q)) (-(O ε r s))
      * OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
        (E ε p q) (O ε r s)
      = algebraMap ℝ (OddDouble (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε)
          (p * p + ε * ε * (q * q + r * r + s * s)) := by
  refine OddDouble.ext _ _ ?_ ?_
  · simp only [algebraMap_floor3_eq', OddDouble.p1_mul, OddDouble.p1_mk,
      OddDouble.p2_mk, parityMap_O_mem_one, neg_mul_neg]
    rw [E_mul_E, O_mul_O, E_smul, E_add_E]
    congr 1 <;> ring
  · simp only [algebraMap_floor3_eq', OddDouble.p2_mul, OddDouble.p1_mk,
      OddDouble.p2_mk, parityMap_E_mem_zero]
    rw [neg_mul, E_mul_O, O_mul_E, O_neg, O_add_O, ← O_zero_zero ε]
    congr 1 <;> ring

end Machinery

/-! ### Floor `2`, uniform over `ε ≠ 0`: super division over `ℝ` -/

/-- **Floor `2` is super division over `ℝ` for every `ε ≠ 0`** (not just `ε = ±1`): the
"complex-like" norm `p² + ε²q²` on the even part and `ε(a'² + b'²)` on the odd part are
both positive whenever the source is nonzero. -/
theorem divisionTower_isSuperDivision_two_of_ne_zero {ε : ℝ} (hε : ε ≠ 0) :
    Bimod.IsSuperDivision (divisionTower ε 2).grading := by
  show Bimod.IsSuperDivision (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
  intro i x hx hx0
  rcases zmod2_cases i with hi | hi <;> subst hi
  · obtain ⟨p, q, hxeq⟩ := eq_E_of_mem_grading_zero hx
    have hpq0 : p ≠ 0 ∨ q ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (by rw [hxeq, hcon.1, hcon.2, E_zero_zero])
    have hc : p * p + ε * ε * (q * q) ≠ 0 := by
      have hεε : 0 < ε * ε := mul_self_pos.mpr hε
      rcases hpq0 with hp | hq
      · have hpp : 0 < p * p := mul_self_pos.mpr hp
        nlinarith [mul_nonneg hεε.le (mul_self_nonneg q)]
      · have hqq : 0 < q * q := mul_self_pos.mpr hq
        nlinarith [mul_self_nonneg p, mul_pos hεε hqq]
    rw [hxeq]
    refine isUnit_of_conj_eq_algebraMap (y := E ε p (-q)) hc ?_ ?_
    · rw [E_mul_E, ← E_c_zero_eq_algebraMap]
      congr 1 <;> ring
    · rw [E_mul_E, ← E_c_zero_eq_algebraMap]
      congr 1 <;> ring
  · obtain ⟨r, s, hxeq⟩ := eq_O_of_mem_grading_one hx
    have hrs0 : r ≠ 0 ∨ s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (by rw [hxeq, hcon.1, hcon.2, O_zero_zero])
    have hc : ε * (r * r + s * s) ≠ 0 := by
      apply mul_ne_zero hε
      rcases hrs0 with hr | hs
      · have hrr : 0 < r * r := mul_self_pos.mpr hr
        nlinarith [mul_self_nonneg s]
      · have hss : 0 < s * s := mul_self_pos.mpr hs
        nlinarith [mul_self_nonneg r]
    rw [hxeq]
    refine isUnit_of_sq_eq_algebraMap hc ?_
    rw [O_mul_O, ← E_c_zero_eq_algebraMap]
    congr 1
    ring

theorem divisionTower_neg_isSuperDivision_two :
    Bimod.IsSuperDivision (divisionTower (-1 : ℝ) 2).grading :=
  divisionTower_isSuperDivision_two_of_ne_zero (by norm_num)

/-! ### Floor `3`, uniform over `ε ≠ 0`: super division over `ℝ`

The even part is a division ring via the conjugate norm `X · X̄ = p² + ε²(q² + r² + s²)`
(`X_mul_Xbar`, `Xbar_mul_X`); the top generator is an odd unit (`gen² = algebraMap ε`,
`ε ≠ 0`).  The general lemma `isSuperDivision_of_evenDivision_oddUnit` combines them —
**uniformly in the sign of `ε`**, closing both `ε = -1` and the previously-open `ε = 1`
case of `Superfusion.Gauge.RealGauge`. -/

/-- The even part of floor `3` is a division ring, for every `ε ≠ 0`. -/
theorem divisionTower_isSuperDivision_three_even_of_ne_zero {ε : ℝ} (hε : ε ≠ 0) :
    ∀ x : OddDouble (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε,
      x ∈ OddDouble.grading
        (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε 0 →
      x ≠ 0 → IsUnit x := by
  intro x hx hx0
  obtain ⟨ha, hb⟩ := (OddDouble.mem_grading
    (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε).mp hx
  rw [zero_add] at hb
  obtain ⟨p, q, hAeq⟩ := eq_E_of_mem_grading_zero ha
  obtain ⟨r, s, hBeq⟩ := eq_O_of_mem_grading_one hb
  have hxeq' : x = OddDouble.mk (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε
      (E ε p q) (O ε r s) := by
    conv_lhs => rw [← OddDouble.mk_p1_p2
      (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε x]
    rw [hAeq, hBeq]
  have hpqrs0 : p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0 ∨ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hp, hq, hr, hs⟩ := hcon
    exact hx0 (by rw [hxeq', hp, hq, hr, hs, E_zero_zero, O_zero_zero, mk_zero_zero])
  have hc : p * p + ε * ε * (q * q + r * r + s * s) ≠ 0 := by
    have hεε : 0 < ε * ε := mul_self_pos.mpr hε
    rcases hpqrs0 with hp | hq | hr | hs
    · have : 0 < p * p := mul_self_pos.mpr hp
      nlinarith [mul_nonneg hεε.le (add_nonneg (add_nonneg (mul_self_nonneg q)
        (mul_self_nonneg r)) (mul_self_nonneg s))]
    · have : 0 < q * q := mul_self_pos.mpr hq
      nlinarith [mul_self_nonneg p, mul_self_nonneg r, mul_self_nonneg s,
        mul_pos hεε this]
    · have : 0 < r * r := mul_self_pos.mpr hr
      nlinarith [mul_self_nonneg p, mul_self_nonneg q, mul_self_nonneg s,
        mul_pos hεε this]
    · have : 0 < s * s := mul_self_pos.mpr hs
      nlinarith [mul_self_nonneg p, mul_self_nonneg q, mul_self_nonneg r,
        mul_pos hεε this]
  rw [hxeq']
  exact isUnit_of_conj_eq_algebraMap hc (Xbar_mul_X ε p q r s) (X_mul_Xbar ε p q r s)

/-- **Floor `3` is super division over `ℝ` for every `ε ≠ 0`.** -/
theorem divisionTower_isSuperDivision_three_of_ne_zero {ε : ℝ} (hε : ε ≠ 0) :
    Bimod.IsSuperDivision (divisionTower ε 3).grading := by
  show Bimod.IsSuperDivision
    (OddDouble.grading (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε)
  refine isSuperDivision_of_evenDivision_oddUnit
    (fun x hx hx0 => divisionTower_isSuperDivision_three_even_of_ne_zero hε x hx hx0)
    (OddDouble.gen_mem_grading (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε) ?_
  exact isUnit_of_sq_eq_algebraMap hε
    (OddDouble.gen_mul_gen (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) ε)

theorem divisionTower_neg_isSuperDivision_three :
    Bimod.IsSuperDivision (divisionTower (-1 : ℝ) 3).grading :=
  divisionTower_isSuperDivision_three_of_ne_zero (by norm_num)

/-- **Closes the previously-open `ε = 1, n = 3` case** flagged in
`Superfusion.Gauge.RealGauge`: `divisionTower 1 3` is super division after all, via the
`ε`-uniform conjugate-norm argument (the classical "reversal norm", made concrete through
the shapes `E`/`O`). -/
theorem divisionTower_pos_isSuperDivision_three :
    Bimod.IsSuperDivision (divisionTower (1 : ℝ) 3).grading :=
  divisionTower_isSuperDivision_three_of_ne_zero one_ne_zero

/-! ### `D₄`: the purely even quaternion superalgebra

Reuses `Superfusion.Super.QuaternionTower.SuperAlgebra.quaternion`, already landed as the
target of `towerFourQuatSuper` (`[D₁]⁴ = [ℍ]`).  Being purely even makes super division and
graded simplicity nearly free (`evenGrading`'s super-center is the ordinary center,
`IsSimpleRing` transfers from `DivisionRing`); the one genuine computation is that the
center of `ℍ[ℝ]` is exactly the scalars. -/

/-- `D₄` (Table 1): the quaternions, purely even. -/
noncomputable def quatEvenSuper : SuperAlgebra ℝ := SuperAlgebra.quaternion ℝ

theorem quatEvenSuper_isSuperDivision : Bimod.IsSuperDivision quatEvenSuper.grading := by
  show Bimod.IsSuperDivision (evenGrading ℝ ℍ[ℝ])
  intro i x hx hx0
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact isUnit_iff_ne_zero.mpr hx0
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    exact absurd hx hx0

/-- The commutator of a quaternion with `i` and with `j` forces the `j`, `k` and `i`
components to vanish, leaving a scalar. -/
private theorem quat_center_scalar {p q r s : ℝ}
    (hi : (⟨p, q, r, s⟩ : ℍ[ℝ]) * (⟨0, 1, 0, 0⟩ : ℍ[ℝ])
      = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨p, q, r, s⟩)
    (hj : (⟨p, q, r, s⟩ : ℍ[ℝ]) * (⟨0, 0, 1, 0⟩ : ℍ[ℝ])
      = (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨p, q, r, s⟩) :
    q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_mul_mk] at hi hj
  have hi' := QuaternionAlgebra.ext_iff.mp hi
  have hj' := QuaternionAlgebra.ext_iff.mp hj
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hj'.2.2.2]
  · nlinarith [hi'.2.2.2]
  · nlinarith [hi'.2.2.1]

theorem quatEvenSuper_isSuperCentral : IsSuperCentral quatEvenSuper.grading := by
  show IsSuperCentral (evenGrading ℝ ℍ[ℝ])
  constructor
  rw [superCenter_evenGrading]
  rintro a ha
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff] at ha
  obtain ⟨p, q, r, s⟩ := a
  obtain ⟨hq, hr, hs⟩ := quat_center_scalar (ha _).symm (ha _).symm
  subst hq; subst hr; subst hs
  refine Submodule.mem_one.mpr ⟨p, ?_⟩
  apply QuaternionAlgebra.ext <;> simp [Algebra.algebraMap_eq_smul_one]

theorem quatEvenSuper_isGradedSimple : IsGradedSimple quatEvenSuper.grading := by
  show IsGradedSimple (evenGrading ℝ ℍ[ℝ])
  haveI : IsSimpleRing ℍ[ℝ] := DivisionRing.isSimpleRing ℍ[ℝ]
  exact isGradedSimple_of_isSimpleRing _

noncomputable instance : FiniteDimensional ℝ quatEvenSuper.carrier :=
  inferInstanceAs (FiniteDimensional ℝ ℍ[ℝ])

instance : Nontrivial quatEvenSuper.carrier :=
  inferInstanceAs (Nontrivial ℍ[ℝ])

theorem quatEvenSuper_finrank : Module.finrank ℝ quatEvenSuper.carrier = 4 :=
  Quaternion.finrank_eq_four

/-! ### The eight-representative family (Table 1) -/

/-- The repo correspondence: `Cl_{0,n} = divisionTower (-1) n` (`n = 1, 2, 3`), the purely
even `ℍ` at `4`, and `Cl_{n,0} = divisionTower 1 (8 - a)` for `a ≥ 5` (indices spelled
directly, `a = 5, 6, 7 ↦ n = 3, 2, 1`). -/
noncomputable def realRepAux : ℕ → SuperAlgebra ℝ
  | 0 => SuperAlgebra.base ℝ
  | 1 => divisionTower (-1 : ℝ) 1
  | 2 => divisionTower (-1 : ℝ) 2
  | 3 => divisionTower (-1 : ℝ) 3
  | 4 => quatEvenSuper
  | 5 => divisionTower (1 : ℝ) 3
  | 6 => divisionTower (1 : ℝ) 2
  | _ => divisionTower (1 : ℝ) 1

/-- **The eight real super division representatives** (Table 1). -/
noncomputable def realRep (a : ZMod 8) : SuperAlgebra ℝ := realRepAux a.val

/-- **Every `realRep a` is super division.** -/
theorem realRep_isSuperDivision (a : ZMod 8) :
    Bimod.IsSuperDivision (realRep a).grading := by
  show Bimod.IsSuperDivision (realRepAux a.val).grading
  have h8 : a.val < 8 := ZMod.val_lt a
  set n := a.val with hn
  interval_cases n <;> simp only [realRepAux]
  · exact divisionTower_isSuperDivision_zero
  · exact divisionTower_neg_isSuperDivision_one
  · exact divisionTower_neg_isSuperDivision_two
  · exact divisionTower_neg_isSuperDivision_three
  · exact quatEvenSuper_isSuperDivision
  · exact divisionTower_pos_isSuperDivision_three
  · exact divisionTower_isSuperDivision_two_of_ne_zero one_ne_zero
  · exact divisionTower_isSuperDivision_one (1 : ℝ) one_ne_zero

theorem realRep_isSuperCentral (a : ZMod 8) : IsSuperCentral (realRep a).grading := by
  show IsSuperCentral (realRepAux a.val).grading
  have h8 : a.val < 8 := ZMod.val_lt a
  set n := a.val with hn
  interval_cases n <;> simp only [realRepAux]
  · exact base_isSuperCentral
  · exact divisionTower_isSuperCentral (ε := (-1 : ℝ)) (by norm_num) 1
  · exact divisionTower_isSuperCentral (ε := (-1 : ℝ)) (by norm_num) 2
  · exact divisionTower_isSuperCentral (ε := (-1 : ℝ)) (by norm_num) 3
  · exact quatEvenSuper_isSuperCentral
  · exact divisionTower_isSuperCentral (ε := (1 : ℝ)) one_ne_zero 3
  · exact divisionTower_isSuperCentral (ε := (1 : ℝ)) one_ne_zero 2
  · exact divisionTower_isSuperCentral (ε := (1 : ℝ)) one_ne_zero 1

theorem realRep_isGradedSimple (a : ZMod 8) : IsGradedSimple (realRep a).grading := by
  show IsGradedSimple (realRepAux a.val).grading
  have h8 : a.val < 8 := ZMod.val_lt a
  set n := a.val with hn
  interval_cases n <;> simp only [realRepAux]
  · exact base_isGradedSimple
  · exact divisionTower_isGradedSimple (ε := (-1 : ℝ)) (by norm_num) 1
  · exact divisionTower_isGradedSimple (ε := (-1 : ℝ)) (by norm_num) 2
  · exact divisionTower_isGradedSimple (ε := (-1 : ℝ)) (by norm_num) 3
  · exact quatEvenSuper_isGradedSimple
  · exact divisionTower_isGradedSimple (ε := (1 : ℝ)) one_ne_zero 3
  · exact divisionTower_isGradedSimple (ε := (1 : ℝ)) one_ne_zero 2
  · exact divisionTower_isGradedSimple (ε := (1 : ℝ)) one_ne_zero 1

theorem realRep_finiteDimensional (a : ZMod 8) :
    FiniteDimensional ℝ (realRep a).carrier := by
  show FiniteDimensional ℝ (realRepAux a.val).carrier
  have h8 : a.val < 8 := ZMod.val_lt a
  set n := a.val with hn
  interval_cases n <;> simp only [realRepAux]
  · exact Module.Finite.self ℝ
  · exact divisionTower_finite (-1 : ℝ) 1
  · exact divisionTower_finite (-1 : ℝ) 2
  · exact divisionTower_finite (-1 : ℝ) 3
  · exact inferInstanceAs (FiniteDimensional ℝ quatEvenSuper.carrier)
  · exact divisionTower_finite (1 : ℝ) 3
  · exact divisionTower_finite (1 : ℝ) 2
  · exact divisionTower_finite (1 : ℝ) 1

theorem realRep_nontrivial (a : ZMod 8) : Nontrivial (realRep a).carrier := by
  show Nontrivial (realRepAux a.val).carrier
  have h8 : a.val < 8 := ZMod.val_lt a
  set n := a.val with hn
  interval_cases n <;> simp only [realRepAux]
  · exact inferInstanceAs (Nontrivial ℝ)
  · exact divisionTower_nontrivial (-1 : ℝ) 1
  · exact divisionTower_nontrivial (-1 : ℝ) 2
  · exact divisionTower_nontrivial (-1 : ℝ) 3
  · exact inferInstanceAs (Nontrivial quatEvenSuper.carrier)
  · exact divisionTower_nontrivial (1 : ℝ) 3
  · exact divisionTower_nontrivial (1 : ℝ) 2
  · exact divisionTower_nontrivial (1 : ℝ) 1

end Superfusion
