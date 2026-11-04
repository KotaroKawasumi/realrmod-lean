/-
Superfusion / Gauge / RealClassification

Milestones C2+C3 of the intrinsic gauge track: **the classification of
real central super division algebras**, using the freshly-landed
Frobenius theorem (`Superfusion.Gauge.Frobenius2`).  The goal, worked out
stage by stage, each a stopping milestone:

* **C2** (`superAlgEquiv_of_odd_eq_bot`): the purely even case — if
  `S.grading 1 = ⊥`, then `S ≅ realRep 0` or `S ≅ realRep 4` (as graded
  algebras). **Done.**
* **C3a**: the odd case's `𝒟 0`-analysis — general `ZMod 2`-grading facts
  (`sup_grade_eq_top`/`inf_grade_eq_bot`/`finrank_eq_add_of_grading`), `𝒟 0`
  as a finite-dimensional division ring (`divisionRingGradeZero`, ready for
  `Frobenius.frobenius_trichotomy`), and the supercentral-detection lemma
  (`eq_algebraMap_of_central_zero_commute_odd`): an even element central in
  `𝒟 0` *and* commuting with a fixed odd unit is forced to be a real scalar.
  **Done.**
* **C3b**: the case tree on `𝒟 0 ≅ ℝ`, `ℂ`, `ℍ`, landing in the four
  remaining `realRep`s.
  - The `𝒟 0 ≅ ℝ` branch (`superAlgEquiv_of_gradeZero_real`, landing in
    `realRep 1`/`realRep 7`) is **done**: `𝒟 0` is forced to be exactly the
    scalars, `u²` a nonzero real rescaled to `±1`, and `OddDouble.lift` plus
    graded-simple injectivity/a `finrank` count assemble the graded
    isomorphism.
  - The `𝒟 0 ≅ ℂ` branch (target `realRep 2`/`realRep 6`) and the `𝒟 0 ≅ ℍ`
    branch (target `realRep 3`/`realRep 5`, which additionally needs a
    Skolem–Noether-flavored "every `ℝ`-automorphism of `ℍ[ℝ]` is inner" fact
    not otherwise present in the repository) are **not attempted** in this
    pass — genuinely open, not stubbed with `sorry` anywhere in this file.
* **C4** (assembly, `real_superDivision_classification`, and the
  `realGauge.IsCanonical`/`DBW ℝ` payoff corollaries): **not attempted**,
  blocked on the `ℂ`/`ℍ` branches of C3b above.

Design record: docs/super-track-design.md (M9 sections).
-/
import Superfusion.Gauge.Frobenius2
import Superfusion.Gauge.SuperDivisionBasic
import Superfusion.Gauge.RealReps
import Superfusion.Super.EvenGrading
import Superfusion.Super.OddDoubleLift
import Superfusion.Super.GradedTransfer

namespace Superfusion

open Quaternion

/-! ## C2: the purely even case -/

section EvenCase

variable {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D}

/-- **The bridge lemma**: if the odd part of a superalgebra is trivial, the even part is
everything.  Every `x : D` splits as `evenPart 𝒟 x + oddPart 𝒟 x` with the second summand
forced to `0` by `𝒟 1 = ⊥`. -/
theorem evenGrading_zero_eq_top [GradedAlgebra 𝒟] (h1 : 𝒟 1 = ⊥) : 𝒟 0 = ⊤ := by
  apply top_unique
  intro x _
  have hsplit := evenPart_add_oddPart 𝒟 x
  have hodd0 : oddPart 𝒟 x = 0 := by
    have hmem := oddPart_mem 𝒟 x
    rw [h1] at hmem
    exact hmem
  rw [hodd0, add_zero] at hsplit
  rw [← hsplit]
  exact evenPart_mem 𝒟 x

/-- **`D` is a division ring** when the even part is everything and `D` is super division:
every nonzero element is even, hence a unit. -/
@[implicit_reducible]
noncomputable def divisionRingOfEvenTop [GradedAlgebra 𝒟] (hdiv : Bimod.IsSuperDivision 𝒟)
    (h0 : 𝒟 0 = ⊤) [Nontrivial D] [FiniteDimensional ℝ D] : DivisionRing D := by
  haveI : NoZeroDivisors D := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · have ha0 : a ∈ 𝒟 0 := by rw [h0]; exact Submodule.mem_top
      have hau : IsUnit a := hdiv ha0 ha
      exact Or.inr (hau.mul_right_eq_zero.mp hab)
  haveI : IsDomain D := NoZeroDivisors.to_isDomain D
  exact divisionRingOfFiniteDimensional ℝ D

/-- **Supercentrality of a purely even superalgebra is ordinary centrality**: if `𝒟 0 = ⊤`
and `IsSuperCentral 𝒟`, the ordinary center of `D` is exactly `ℝ · 1`. -/
theorem isCentral_of_superCentral_even [GradedAlgebra 𝒟] [IsSuperCentral 𝒟] (h0 : 𝒟 0 = ⊤) :
    Algebra.IsCentral ℝ D where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have hxc : IsSupercentral 𝒟 0 x := by
      intro j b _
      simpa using (hx b).symm
    have hx0 : x ∈ 𝒟 0 := by rw [h0]; exact Submodule.mem_top
    have hxone : x ∈ (1 : Submodule ℝ D) := mem_one_of_isSupercentral 𝒟 hx0 hxc
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hxone
    exact Algebra.mem_bot.mpr ⟨y, hy⟩

end EvenCase

/-! ### Identifying `realRep 0`, `realRep 4` with the base/quaternion models -/

private theorem realRep_zero_eq : realRep (0 : ZMod 8) = SuperAlgebra.base ℝ := rfl

private theorem realRep_four_eq : realRep (4 : ZMod 8) = quatEvenSuper := rfl

/-- **C2 — the purely even case.** If `S.grading 1 = ⊥`, then `S` is graded-isomorphic to
`realRep 0` (`≅ ℝ`) or `realRep 4` (`≅ ℍ[ℝ]`).  Route: `𝒟 0 = ⊤` (`evenGrading_zero_eq_top`)
makes `S.carrier` an ordinary finite-dimensional central division ring over `ℝ`
(`divisionRingOfEvenTop`, `isCentral_of_superCentral_even`), so `frobenius_central` applies;
the resulting `AlgEquiv` is automatically graded since `Submodule.map` of `⊤`/`⊥` under a
bijective map stays `⊤`/`⊥`. -/
theorem superAlgEquiv_of_odd_eq_bot (S : SuperAlgebra.{0, 0} ℝ) [IsSuperCentral S.grading]
    (hdiv : Bimod.IsSuperDivision S.grading) [FiniteDimensional ℝ S.carrier]
    [Nontrivial S.carrier] (h1 : S.grading 1 = ⊥) :
    Nonempty (SuperAlgEquiv S (realRep 0)) ∨ Nonempty (SuperAlgEquiv S (realRep 4)) := by
  have h0 : S.grading 0 = ⊤ := evenGrading_zero_eq_top h1
  letI : DivisionRing S.carrier := divisionRingOfEvenTop hdiv h0
  haveI : Algebra.IsCentral ℝ S.carrier := isCentral_of_superCentral_even h0
  have hgrad : ∀ (T : SuperAlgebra ℝ) (φ : S.carrier ≃ₐ[ℝ] T.carrier),
      T.grading 0 = ⊤ → T.grading 1 = ⊥ →
      ∀ i, (S.grading i).map φ.toLinearMap = T.grading i := by
    intro T φ hT0 hT1 i
    rcases zmod2_cases i with hi | hi <;> subst hi
    · rw [h0, hT0, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr φ.surjective
    · rw [h1, hT1]
      exact Submodule.map_bot _
  rcases Frobenius.frobenius_central S.carrier with h | h
  · obtain ⟨φ⟩ := h
    refine Or.inl ⟨realRep_zero_eq ▸ ⟨φ, ?_⟩⟩
    exact hgrad (SuperAlgebra.base ℝ) φ rfl rfl
  · obtain ⟨φ⟩ := h
    refine Or.inr ⟨realRep_four_eq ▸ ⟨φ, ?_⟩⟩
    exact hgrad quatEvenSuper φ rfl rfl

/-! ## C3a: the odd case's `𝒟 0`-analysis -/

section OddCase

variable {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D} [GradedAlgebra 𝒟]

/-- **The two grade pieces span everything** (general, no odd-unit hypothesis needed): every
`x` splits as `evenPart 𝒟 x + oddPart 𝒟 x`. -/
theorem sup_grade_eq_top : 𝒟 0 ⊔ 𝒟 1 = ⊤ := by
  apply top_unique
  intro x _
  rw [← evenPart_add_oddPart 𝒟 x]
  exact Submodule.add_mem_sup (evenPart_mem 𝒟 x) (oddPart_mem 𝒟 x)

/-- **The two grade pieces meet trivially** (general). -/
theorem inf_grade_eq_bot : 𝒟 0 ⊓ 𝒟 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hx0, hx1⟩
  rw [Submodule.mem_bot, ← oddPart_of_mem_one 𝒟 hx1, oddPart_of_mem_zero 𝒟 hx0]

/-- **`finrank` splits additively across a `ZMod 2` grading** (general): combines
`sup_grade_eq_top`/`inf_grade_eq_bot` with the standard submodule dimension formula. -/
theorem finrank_eq_add_of_grading [FiniteDimensional ℝ D] :
    Module.finrank ℝ D = Module.finrank ℝ (𝒟 0) + Module.finrank ℝ (𝒟 1) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (𝒟 0) (𝒟 1)
  rw [sup_grade_eq_top, inf_grade_eq_bot, finrank_top, finrank_bot, add_zero] at h
  exact h

/-- **`𝒟 0` is a finite-dimensional division ring** when `D` is super division: every nonzero
even element is a unit (in `D`), and inverses of even elements stay even
(`Bimod.isUnit_inv_mem`, folded into `hdiv` restricted to degree `0`). -/
@[implicit_reducible]
noncomputable def divisionRingGradeZero (hdiv : Bimod.IsSuperDivision 𝒟) [Nontrivial D]
    [FiniteDimensional ℝ D] : DivisionRing (𝒟 0) := by
  haveI : Nontrivial (𝒟 0) :=
    ⟨⟨0, Submodule.zero_mem _⟩, ⟨1, SetLike.one_mem_graded 𝒟⟩,
      fun h => (one_ne_zero (α := D)) (Subtype.ext_iff.mp h).symm⟩
  haveI : NoZeroDivisors (𝒟 0) := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · have ha0 : (a : D) ≠ 0 := fun h => ha (Subtype.ext h)
      have hau : IsUnit (a : D) := hdiv a.2 ha0
      have habD : (a : D) * (b : D) = 0 := congrArg Subtype.val hab
      exact Or.inr (Subtype.ext (hau.mul_right_eq_zero.mp habD))
  haveI : IsDomain (𝒟 0) := NoZeroDivisors.to_isDomain _
  exact divisionRingOfFiniteDimensional ℝ (𝒟 0)

/-- **The supercentral-detection lemma**: an even element `z` that commutes with all of
`𝒟 0` and with a fixed odd unit `u` is supercentral, hence (given `IsSuperCentral 𝒟`) a real
scalar.  Route: testing supercommutation against `j = 0` is the commuting-with-`𝒟 0` hypothesis
directly; testing against `j = 1` reduces (writing `b = u * (u⁻¹ * b)` for `b ∈ 𝒟 1`, `u⁻¹ * b
∈ 𝒟 0` by `Bimod.isUnit_inv_mem`) to the `z`-commutes-with-`u` hypothesis together with the
`𝒟 0`-commuting hypothesis applied to `u⁻¹ * b`. -/
theorem eq_algebraMap_of_central_zero_commute_odd [IsSuperCentral 𝒟] {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) {z : D} (hz0 : z ∈ 𝒟 0) (hzc : ∀ d ∈ 𝒟 0, z * d = d * z)
    (hzu : z * u = u * z) : ∃ r : ℝ, z = algebraMap ℝ D r := by
  set v := ((hu.unit⁻¹ : Dˣ) : D) with hv
  have hv1 : v ∈ 𝒟 1 := Bimod.isUnit_inv_mem hu1 hu.unit hu.unit_spec
  have huv : u * v = 1 := by
    have h2 := hu.unit.mul_inv
    rwa [hu.unit_spec] at h2
  have hsc : IsSupercentral 𝒟 0 z := by
    intro j b hb
    rcases zmod2_cases j with hj | hj <;> subst hj
    · simpa using hzc b hb
    · have hvb0 : v * b ∈ 𝒟 0 := by
        have h := SetLike.mul_mem_graded hv1 hb
        rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
      have hbeq : b = u * (v * b) := by rw [← mul_assoc, huv, one_mul]
      have hcomm : z * (u * (v * b)) = (u * (v * b)) * z := by
        calc z * (u * (v * b)) = (z * u) * (v * b) := by rw [mul_assoc]
          _ = (u * z) * (v * b) := by rw [hzu]
          _ = u * (z * (v * b)) := by rw [mul_assoc]
          _ = u * ((v * b) * z) := by rw [hzc _ hvb0]
          _ = u * (v * b) * z := (mul_assoc u (v * b) z).symm
      simp only [zero_mul, sgn_zero, Units.val_one, one_smul]
      calc z * b = z * (u * (v * b)) := by rw [← hbeq]
        _ = (u * (v * b)) * z := hcomm
        _ = b * z := by rw [← hbeq]
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp (mem_one_of_isSupercentral 𝒟 hz0 hsc)
  exact ⟨y, hy.symm⟩

end OddCase

/-! ## C3b — the `𝒟 0 ≅ ℝ` branch: `realRep 1`, `realRep 7`

`𝒟 0 ≅ ℝ` forces `𝒟 0` to be *exactly* the scalars (a `finrank`-`1` submodule containing
them); `u² ∈ 𝒟 0` is then a nonzero real scalar `c`, and rescaling `u` by `|c|^{-1/2}`
normalizes `u² = ±1`.  The resulting pair `(1, u)` is exactly the presentation of floor `1`
of the division tower, and the `OddDouble` universal property (`OddDouble.lift`) turns this
into an algebra map `divisionTower ε 1 →ₐ[ℝ] D`; it is bijective by the graded-simple
injectivity transfer (`injective_of_isGradedSimple`) together with a `finrank` count
(`finrank_eq_add_of_grading` gives `finrank D = 2`, matching `divisionTower_finrank`). -/

section RealBranch

variable {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D} [GradedAlgebra 𝒟]

/-- **`𝒟 0` is exactly the scalars** when `finrank ℝ (𝒟 0) = 1`: combines the (always true)
inclusion `(1 : Submodule) ≤ 𝒟 0` with `Submodule.eq_of_le_of_finrank_eq`. -/
theorem grade_zero_eq_one_of_finrank_eq_one [Nontrivial D] [FiniteDimensional ℝ D]
    (h1 : Module.finrank ℝ (𝒟 0) = 1) : 𝒟 0 = (1 : Submodule ℝ D) := by
  have hle : (1 : Submodule ℝ D) ≤ 𝒟 0 := by
    rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
    exact SetLike.one_mem_graded 𝒟
  have hfr : Module.finrank ℝ (1 : Submodule ℝ D) = Module.finrank ℝ (𝒟 0) := by
    rw [Submodule.one_eq_span, finrank_span_singleton (one_ne_zero (α := D)), h1]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm

/-- The scalar embedding is homogeneous of degree `0` (general, no odd-unit hypothesis
needed). -/
theorem isHomogeneousHom_ofId : IsHomogeneousHom (evenGrading ℝ ℝ) 𝒟 (Algebra.ofId ℝ D) := by
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · show algebraMap ℝ D x ∈ 𝒟 0
    exact algebraMap_mem_grade_zero 𝒟 x
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    subst hx
    show algebraMap ℝ D 0 ∈ 𝒟 1
    rw [map_zero]
    exact zero_mem _

/-- **The `𝒟 0 ≅ ℝ` branch**: given an odd unit `u` and an abstract algebra iso `𝒟 0 ≅ ℝ`,
the bundled superalgebra `⟨D, 𝒟⟩` is graded-isomorphic to `divisionTower ε 1` for `ε = 1` or
`ε = -1` (the sign of `u²` after normalization).  Route: `𝒟 0 = 1` (the scalars, from
`grade_zero_eq_one_of_finrank_eq_one`) puts `u² = algebraMap c` for a nonzero real `c`;
rescaling `u` by `(√|c|)⁻¹` normalizes `u² = algebraMap ε`; `OddDouble.lift` (with the scalar
embedding and the rescaled `u`) then gives an algebra map `divisionTower ε 1 →ₐ[ℝ] D`, bijective
by graded-simple injectivity (`injective_of_isGradedSimple`) plus a `finrank` count
(`finrank_eq_add_of_grading` gives `finrank D = 2 = finrank (divisionTower ε 1)`). -/
theorem nonempty_superAlgEquiv_divisionTower_one_of_gradeZero_real [Nontrivial D]
    [FiniteDimensional ℝ D] {u : D} (hu1 : u ∈ 𝒟 1) (hu : IsUnit u)
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower ε 1)) := by
  have h0 : Module.finrank ℝ (𝒟 0 : Submodule ℝ D) = 1 := by
    rw [φ.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hz0eq : 𝒟 0 = (1 : Submodule ℝ D) := grade_zero_eq_one_of_finrank_eq_one h0
  have h1eq : Module.finrank ℝ (𝒟 1 : Submodule ℝ D) = 1 := by
    rw [← Bimod.oddUnit_finrank_eq hu1 hu, h0]
  obtain ⟨husq0, husqU⟩ := Bimod.oddUnit_sq_even_unit hu1 hu
  rw [hz0eq] at husq0
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp husq0
  have hcne : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact husqU.ne_zero hc.symm
  have hfinD : Module.finrank ℝ D = 2 := by
    rw [finrank_eq_add_of_grading (𝒟 := 𝒟), h0, h1eq]
  -- The common construction, given the normalized odd unit `u'` with `u' * u' = algebraMap ε`.
  have key : ∀ ε : ℝ, ε ≠ 0 → ∀ u' : D, u' ∈ 𝒟 1 → IsUnit u' →
      u' * u' = algebraMap ℝ D ε →
      Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower ε 1)) := by
    intro ε hεne u' hu'1 hu' hu'sq
    set f : ℝ →ₐ[ℝ] D := Algebra.ofId ℝ D with hfdef
    have hsq : u' * u' = algebraMap ℝ D ε := hu'sq
    have hconj : ∀ a : ℝ, u' * f a = f (parityMap (evenGrading ℝ ℝ) a) * u' := by
      intro a
      rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, hfdef, Algebra.ofId_apply]
      exact (Algebra.commutes a u').symm
    set ψ : OddDouble (evenGrading ℝ ℝ) ε →ₐ[ℝ] D := OddDouble.lift (evenGrading ℝ ℝ) ε f u' hsq hconj
      with hψdef
    have hψhom : IsHomogeneousHom (OddDouble.grading (evenGrading ℝ ℝ) ε) 𝒟 ψ :=
      OddDouble.lift_isHomogeneous (evenGrading ℝ ℝ) ε f u' hsq hconj 𝒟 isHomogeneousHom_ofId hu'1
    haveI : IsGradedSimple (OddDouble.grading (evenGrading ℝ ℝ) ε) :=
      divisionTower_isGradedSimple (K := ℝ) hεne 1
    have hinj : Function.Injective ψ :=
      injective_of_isGradedSimple (OddDouble.grading (evenGrading ℝ ℝ) ε) 𝒟 ψ hψhom
    have heq : Module.finrank ℝ (OddDouble (evenGrading ℝ ℝ) ε) = Module.finrank ℝ D := by
      rw [show Module.finrank ℝ (OddDouble (evenGrading ℝ ℝ) ε)
          = Module.finrank ℝ (divisionTower ε 1).carrier from rfl,
        divisionTower_finrank ε 1, pow_one, hfinD]
    have hbij : Function.Bijective ψ :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := ψ.toLinearMap) heq).mp hinj⟩
    have hgrad : ∀ i, (OddDouble.grading (evenGrading ℝ ℝ) ε i).map ψ.toLinearMap = 𝒟 i :=
      map_grading_of_bijective (OddDouble.grading (evenGrading ℝ ℝ) ε) 𝒟 ψ hψhom hbij
    exact ⟨(⟨AlgEquiv.ofBijective ψ hbij, hgrad⟩ :
      SuperAlgEquiv (divisionTower ε 1) (⟨D, 𝒟⟩ : SuperAlgebra ℝ)).symm⟩
  rcases lt_or_gt_of_ne hcne with hcneg | hcpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    set s := Real.sqrt (-c) with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    set r := s⁻¹ with hrdef
    have hrne : r ≠ 0 := inv_ne_zero hspos.ne'
    refine key (-1) (by norm_num) (r • u) (Submodule.smul_mem _ r hu1)
      (by rw [Algebra.smul_def]
          exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu) ?_
    have hmul : (r • u) * (r • u) = (r * r) • (u * u) := by rw [smul_mul_smul_comm]
    rw [hmul, ← hc, Algebra.smul_def, ← map_mul]
    congr 1
    have hss : s * s = -c := Real.mul_self_sqrt (by linarith)
    rw [hrdef]
    field_simp
    linarith [hss]
  · refine ⟨1, Or.inl rfl, ?_⟩
    set s := Real.sqrt c with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr hcpos
    set r := s⁻¹ with hrdef
    have hrne : r ≠ 0 := inv_ne_zero hspos.ne'
    refine key 1 one_ne_zero (r • u) (Submodule.smul_mem _ r hu1)
      (by rw [Algebra.smul_def]
          exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu) ?_
    have hmul : (r • u) * (r • u) = (r * r) • (u * u) := by rw [smul_mul_smul_comm]
    rw [hmul, ← hc, Algebra.smul_def, ← map_mul]
    congr 1
    have hss : s * s = c := Real.mul_self_sqrt hcpos.le
    rw [hrdef]
    field_simp
    linarith [hss]

private theorem realRep_one_eq : realRep (1 : ZMod 8) = divisionTower (-1 : ℝ) 1 := rfl

private theorem realRep_seven_eq : realRep (7 : ZMod 8) = divisionTower (1 : ℝ) 1 := rfl

/-- **C3b — the `𝒟 0 ≅ ℝ` branch, bundled.** If `S.grading 0 ≅ ℝ` (witnessed abstractly by
`φ`) and `u` is an odd unit, `S` is graded-isomorphic to `realRep 7` (`u² = 1` after
normalization, `Cl_{1,0}`) or `realRep 1` (`u² = -1`, `Cl_{0,1}`). -/
theorem superAlgEquiv_of_gradeZero_real (S : SuperAlgebra.{0, 0} ℝ) [Nontrivial S.carrier]
    [FiniteDimensional ℝ S.carrier] {u : S.carrier} (hu1 : u ∈ S.grading 1) (hu : IsUnit u)
    (φ : (S.grading 0 : Submodule ℝ S.carrier) ≃ₐ[ℝ] ℝ) :
    Nonempty (SuperAlgEquiv S (realRep 7)) ∨ Nonempty (SuperAlgEquiv S (realRep 1)) := by
  obtain ⟨ε, hε, ⟨Φ⟩⟩ := nonempty_superAlgEquiv_divisionTower_one_of_gradeZero_real hu1 hu φ
  rcases hε with rfl | rfl
  · exact Or.inl ⟨realRep_seven_eq ▸ Φ⟩
  · exact Or.inr ⟨realRep_one_eq ▸ Φ⟩

end RealBranch

end Superfusion
