import Superfusion.Gauge.RealClassification
import Superfusion.Gauge.RealCanonical
import Superfusion.Super.SkolemNoetherIso

namespace Superfusion

open Quaternion Complex

/-! ## Shared machinery: transporting conjugation by an odd unit through an abstract
`𝒟 0 ≅ K` isomorphism -/

section GradeZeroConj

variable {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D} [GradedAlgebra 𝒟]

/-- The canonical embedding of the grade-`0` piece into the ambient ring: every field is `rfl`,
since `SetLike.GradeZero`'s ring/algebra structure on `𝒟 0` literally *is* ambient arithmetic. -/
noncomputable def gradeZeroEmbed : (𝒟 0 : Submodule ℝ D) →ₐ[ℝ] D where
  toFun x := (x : D)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Conjugation by a two-sided-invertible odd pair `(u, v)` (`u * v = v * u = 1`), restricted
to the grade-`0` piece: `x ↦ u * x * v`, landing back in grade `0` since `1 + 0 + 1 = 0`. -/
noncomputable def conjGradeZero {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) :
    (𝒟 0 : Submodule ℝ D) →ₐ[ℝ] (𝒟 0 : Submodule ℝ D) where
  toFun x := ⟨u * (x : D) * v, by
    have h := SetLike.mul_mem_graded (SetLike.mul_mem_graded hu1 x.2) hv1
    rwa [show (1 : ZMod 2) + 0 + 1 = 0 from by decide] at h⟩
  map_one' := by
    apply Subtype.ext
    show u * (1 : D) * v = 1
    rw [mul_one, huv]
  map_mul' x y := by
    apply Subtype.ext
    show u * ((x : D) * (y : D)) * v = (u * (x : D) * v) * (u * (y : D) * v)
    rw [show (u * (x : D) * v) * (u * (y : D) * v) = u * (x : D) * (v * u) * (y : D) * v by
      noncomm_ring, hvu]
    noncomm_ring
  map_zero' := by apply Subtype.ext; show u * (0 : D) * v = 0; rw [mul_zero, zero_mul]
  map_add' x y := by
    apply Subtype.ext
    show u * ((x : D) + (y : D)) * v = u * (x : D) * v + u * (y : D) * v
    noncomm_ring
  commutes' r := by
    apply Subtype.ext
    show u * (algebraMap ℝ D r) * v = algebraMap ℝ D r
    rw [← Algebra.commutes r u, mul_assoc, huv, mul_one]

theorem conjGradeZero_comp {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) :
    (conjGradeZero hv1 hu1 hvu huv).comp (conjGradeZero hu1 hv1 huv hvu) = AlgHom.id ℝ _ := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  show v * (u * (x : D) * v) * u = (x : D)
  rw [show v * (u * (x : D) * v) * u = (v * u) * (x : D) * (v * u) by noncomm_ring, hvu, one_mul,
    mul_one]

theorem conjGradeZero_surjective {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) :
    Function.Surjective (conjGradeZero hu1 hv1 huv hvu) := by
  intro y
  refine ⟨conjGradeZero hv1 hu1 hvu huv y, ?_⟩
  have h := congrArg (fun f => f y) (conjGradeZero_comp hv1 hu1 hvu huv)
  simpa using h

/-- Transport an automorphism, given as an abstract iso `φ : 𝒟 0 ≃ₐ[ℝ] K`, into an algebra map
`K →ₐ[ℝ] K`. -/
noncomputable def transportAut {K : Type*} [Ring K] [Algebra ℝ K]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] K) {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) : K →ₐ[ℝ] K :=
  φ.toAlgHom.comp ((conjGradeZero hu1 hv1 huv hvu).comp φ.symm.toAlgHom)

/-- Unfolding `transportAut` on a point: `rfl`, but stated as a lemma so `rw` can fire on it
without fighting the `AlgHom`-vs-`AlgEquiv` coercion mismatch left by unfolding the `.comp`
chain directly. -/
theorem transportAut_apply {K : Type*} [Ring K] [Algebra ℝ K]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] K) {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) (x : K) :
    transportAut φ hu1 hv1 huv hvu x = φ (conjGradeZero hu1 hv1 huv hvu (φ.symm x)) := rfl

theorem transportAut_surjective {K : Type*} [Ring K] [Algebra ℝ K]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] K) {u v : D} (hu1 : u ∈ 𝒟 1) (hv1 : v ∈ 𝒟 1)
    (huv : u * v = 1) (hvu : v * u = 1) :
    Function.Surjective (transportAut φ hu1 hv1 huv hvu) :=
  φ.surjective.comp ((conjGradeZero_surjective hu1 hv1 huv hvu).comp φ.symm.surjective)

end GradeZeroConj

/-- Any algebra endomorphism of a purely-even-graded algebra is automatically homogeneous
(for its own `evenGrading`, both source and target). -/
private theorem isHomogeneousHom_evenGrading_self {A : Type*} [Ring A] [Algebra ℝ A]
    (f : A →ₐ[ℝ] A) : IsHomogeneousHom (evenGrading ℝ A) (evenGrading ℝ A) f := by
  intro i x hx
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact Submodule.mem_top
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    subst hx
    rw [map_zero, evenGrading_one]
    exact Submodule.zero_mem _

/-! ## The `𝒟 0 ≅ ℂ` branch: `realRep 2`, `realRep 6`

Aut_ℝ(ℂ) = {id, conj} (`Complex.real_algHom_eq_id_or_conj`, ready-made in Mathlib); the `id` case
is excluded by a supercentral-detection contradiction, leaving `conj`, which produces two
anticommuting odd generators `e₁ = u`, `e₂ = w * u` (`w` the image of `I`) presenting `S` as the
two-fold odd double `divisionTower ε 2`. -/

section ComplexBranch

/-! ### `floor 1`'s own grading, in `mk`-shape (mirrors the private lemmas of `RealFuse2`) -/

private theorem floor1_eq_mk_p_zero_of_mem_zero {ε : ℝ} {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 0) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε (OddDouble.p1 (evenGrading ℝ ℝ) ε x) 0 := by
  obtain ⟨-, h2⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [show (0 : ZMod 2) + 1 = 1 from by decide, evenGrading_one, Submodule.mem_bot] at h2
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h2]

private theorem floor1_eq_mk_zero_q_of_mem_one {ε : ℝ} {x : OddDouble (evenGrading ℝ ℝ) ε}
    (hx : x ∈ OddDouble.grading (evenGrading ℝ ℝ) ε 1) :
    x = OddDouble.mk (evenGrading ℝ ℝ) ε 0 (OddDouble.p2 (evenGrading ℝ ℝ) ε x) := by
  obtain ⟨h1, -⟩ := (OddDouble.mem_grading (evenGrading ℝ ℝ) ε).mp hx
  rw [evenGrading_one, Submodule.mem_bot] at h1
  conv_lhs => rw [← OddDouble.mk_p1_p2 (evenGrading ℝ ℝ) ε x]
  rw [h1]

/-- **Reduction of the `hconj` hypothesis of `OddDouble.lift` to the two homogeneous cases**:
if `γ` commutes with the image of the even part and anticommutes with the image of the odd
part, it satisfies the full `parityMap`-twisted commutation on every element. -/
private theorem hconj_of_grade_cases {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
    [Ring C] [Algebra K C] {𝒜 : ZMod 2 → Submodule K A} [GradedAlgebra 𝒜] {f : A →ₐ[K] C} {γ : C}
    (heven : ∀ a, a ∈ 𝒜 0 → γ * f a = f a * γ)
    (hodd : ∀ a, a ∈ 𝒜 1 → γ * f a = -(f a * γ)) (a : A) :
    γ * f a = f (parityMap 𝒜 a) * γ := by
  conv_lhs => rw [← evenPart_add_oddPart 𝒜 a]
  rw [map_add, mul_add, heven _ (evenPart_mem 𝒜 a), hodd _ (oddPart_mem 𝒜 a),
    parityMap_apply, map_sub, sub_mul]
  abel

/-- **The `𝒟 0 ≅ ℂ` branch, generic form.** Given a normalized odd unit `u'` (`u'² =
algebraMap ε`, `ε ≠ 0`) and an abstract iso `φ : 𝒟 0 ≃ₐ[ℝ] ℂ`, the bundled superalgebra
`⟨D, 𝒟⟩` is graded-isomorphic to `divisionTower ε 2`. Route: `σ := transportAut φ` is an
`ℝ`-algebra endomorphism of `ℂ`, so `σ = id` or `σ = conj`
(`Complex.real_algHom_eq_id_or_conj`); `σ = id` is excluded (it would force the image `w` of `I`
to be a real scalar, by `eq_algebraMap_of_central_zero_commute_odd`, contradicting `I ∉ ℝ`);
`σ = conj` gives `u' * w = -(w * u')`, and `e₁ := u'`, `e₂ := w * u'` present `⟨D,𝒟⟩` via two
iterated `OddDouble.lift`s (floor `1`, then floor `2`). -/
private theorem key_complex {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D}
    [GradedAlgebra 𝒟] [IsSuperCentral 𝒟] [Nontrivial D] [FiniteDimensional ℝ D]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] ℂ) (ε : ℝ) (hεne : ε ≠ 0) (u' : D) (hu'1 : u' ∈ 𝒟 1)
    (hu' : IsUnit u') (hu'sq : u' * u' = algebraMap ℝ D ε) :
    Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower ε 2)) := by
  set v' := ((hu'.unit⁻¹ : Dˣ) : D) with hv'
  have hv'1 : v' ∈ 𝒟 1 := Bimod.isUnit_inv_mem hu'1 hu'.unit hu'.unit_spec
  have hu'v' : u' * v' = 1 := by have h2 := hu'.unit.mul_inv; rwa [hu'.unit_spec] at h2
  have hv'u' : v' * u' = 1 := by have h2 := hu'.unit.inv_mul; rwa [hu'.unit_spec] at h2
  set σ : ℂ →ₐ[ℝ] ℂ := transportAut φ hu'1 hv'1 hu'v' hv'u' with hσdef
  set w : (𝒟 0 : Submodule ℝ D) := φ.symm Complex.I with hwdef
  have hD0comm : ∀ x y : (𝒟 0 : Submodule ℝ D), x * y = y * x := by
    intro x y; apply φ.injective; rw [map_mul, map_mul, mul_comm]
  rcases Complex.real_algHom_eq_id_or_conj σ with hid | hconjc
  · exfalso
    have hcomm0 : ∀ x : (𝒟 0 : Submodule ℝ D), conjGradeZero hu'1 hv'1 hu'v' hv'u' x = x := by
      intro x
      apply φ.injective
      have h := congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f (φ x)) hid
      rw [hσdef, transportAut_apply, AlgEquiv.symm_apply_apply] at h
      simpa using h
    have hzu : u' * (w : D) = (w : D) * u' := by
      have h := hcomm0 w
      have h' : u' * (w : D) * v' = (w : D) := congrArg Subtype.val h
      have h2 : u' * (w : D) * (v' * u') = (w : D) * u' := by rw [← mul_assoc, h']
      rwa [mul_assoc, hv'u', mul_one] at h2
    have hzc : ∀ d ∈ 𝒟 0, (w : D) * d = d * (w : D) := by
      intro d hd
      exact congrArg Subtype.val (hD0comm w ⟨d, hd⟩)
    obtain ⟨r, hr⟩ := eq_algebraMap_of_central_zero_commute_odd hu'1 hu' w.2 hzc hzu.symm
    have hwr : w = algebraMap ℝ (𝒟 0 : Submodule ℝ D) r := by
      apply Subtype.coe_injective
      show (w : D) = _
      rw [hr]; rfl
    have : Complex.I = (r : ℂ) := by
      rw [hwdef] at hwr
      have := congrArg φ hwr
      rwa [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at this
    have himeq := congrArg Complex.im this
    simp at himeq
  · have hgen : ∀ x : (𝒟 0 : Submodule ℝ D),
        φ (conjGradeZero hu'1 hv'1 hu'v' hv'u' x) = Complex.conjAe (φ x) := by
      intro x
      have h1 := congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f (φ x)) hconjc
      rw [hσdef, transportAut_apply, AlgEquiv.symm_apply_apply] at h1
      exact h1
    have hφw : φ w = Complex.I := by rw [hwdef]; exact φ.apply_symm_apply _
    have h : φ (conjGradeZero hu'1 hv'1 hu'v' hv'u' w) = -Complex.I := by
      rw [hgen w, hφw, Complex.conjAe_coe, Complex.conj_I]
    have hzu : u' * (w : D) = -((w : D) * u') := by
      have h2 : conjGradeZero hu'1 hv'1 hu'v' hv'u' w = -w := by
        apply φ.injective
        rw [map_neg, hφw]; exact h
      have h3 : u' * (w : D) * v' = -(w : D) := congrArg Subtype.val h2
      have h4 : u' * (w : D) * (v' * u') = -(w : D) * u' := by rw [← mul_assoc, h3]
      rwa [mul_assoc, hv'u', mul_one, neg_mul] at h4
    -- raw (unfolded) facts about `w`, `u'`, established before `e₂` is introduced (so `set`
    -- below folds them cleanly into `e₂`-form).
    have hbase_raw : (w : D) * u' * u' = -(u' * ((w : D) * u')) := by
      linear_combination (norm := noncomm_ring) hzu * u'
    have hwsq0 : w * w = -1 := by
      apply φ.injective
      rw [map_mul, hφw, Complex.I_mul_I, map_neg, map_one]
    have hwsqD : (w : D) * (w : D) = -1 := congrArg Subtype.val hwsq0
    have hsq_raw : (w : D) * u' * ((w : D) * u') = algebraMap ℝ D ε := by
      have step : (w : D) * u' * ((w : D) * u') = -(((w : D) * (w : D)) * (u' * u')) := by
        linear_combination (norm := noncomm_ring) (w : D) * hzu * u'
      rw [step, hwsqD, hu'sq, neg_one_mul, neg_neg]
    set f₀ : ℝ →ₐ[ℝ] D := Algebra.ofId ℝ D with hf₀def
    have hf₀hom : IsHomogeneousHom (evenGrading ℝ ℝ) 𝒟 f₀ := isHomogeneousHom_ofId
    have hconj_u' : ∀ a : ℝ, u' * f₀ a = f₀ (parityMap (evenGrading ℝ ℝ) a) * u' := by
      intro a
      rw [parityMap_of_mem_zero (evenGrading ℝ ℝ) Submodule.mem_top, hf₀def, Algebra.ofId_apply]
      exact (Algebra.commutes a u').symm
    set floor1embed := OddDouble.lift (evenGrading ℝ ℝ) ε f₀ u' hu'sq hconj_u' with hfloor1def
    have hfloor1hom : IsHomogeneousHom (OddDouble.grading (evenGrading ℝ ℝ) ε) 𝒟 floor1embed :=
      OddDouble.lift_isHomogeneous (evenGrading ℝ ℝ) ε f₀ u' hu'sq hconj_u' 𝒟 hf₀hom hu'1
    set e₂ : D := (w : D) * u' with he₂def
    have he₂mem : e₂ ∈ 𝒟 1 := by
      have h := SetLike.mul_mem_graded w.2 hu'1
      rwa [zero_add] at h
    have hbase : e₂ * u' = -(u' * e₂) := hbase_raw
    have he₂sq : e₂ * e₂ = algebraMap ℝ D ε := hsq_raw
    clear_value e₂
    have hconj_e₂ : ∀ x : OddDouble (evenGrading ℝ ℝ) ε,
        e₂ * floor1embed x = floor1embed (parityMap (OddDouble.grading (evenGrading ℝ ℝ) ε) x)
          * e₂ := by
      refine hconj_of_grade_cases ?_ ?_
      · intro a ha
        have ha' := floor1_eq_mk_p_zero_of_mem_zero ha
        rw [ha', hfloor1def, OddDouble.lift_inl, hf₀def, Algebra.ofId_apply]
        exact (Algebra.commutes _ _).symm
      · intro a ha
        have ha' := floor1_eq_mk_zero_q_of_mem_one ha
        rw [ha', hfloor1def, OddDouble.lift_mk, map_zero, zero_add, hf₀def,
          Algebra.ofId_apply]
        set p := OddDouble.p2 (evenGrading ℝ ℝ) ε a
        calc e₂ * (algebraMap ℝ D p * u') = (e₂ * algebraMap ℝ D p) * u' := by rw [mul_assoc]
          _ = (algebraMap ℝ D p * e₂) * u' := by rw [Algebra.commutes]
          _ = algebraMap ℝ D p * (e₂ * u') := by rw [mul_assoc]
          _ = algebraMap ℝ D p * (-(u' * e₂)) := by rw [hbase]
          _ = -(algebraMap ℝ D p * (u' * e₂)) := by rw [mul_neg]
          _ = -((algebraMap ℝ D p * u') * e₂) := by rw [mul_assoc]
    haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    haveI : IsGradedSimple (evenGrading ℝ ℝ) := base_isGradedSimple
    haveI hGS1 : IsGradedSimple (OddDouble.grading (evenGrading ℝ ℝ) ε) :=
      OddDouble.isGradedSimple (evenGrading ℝ ℝ) ε hεne
    haveI hGS2 : IsGradedSimple (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε) :=
      OddDouble.isGradedSimple (OddDouble.grading (evenGrading ℝ ℝ) ε) ε hεne
    set ψ := OddDouble.lift (OddDouble.grading (evenGrading ℝ ℝ) ε) ε floor1embed e₂ he₂sq
      hconj_e₂ with hψdef
    have hψhom : IsHomogeneousHom (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
        𝒟 ψ :=
      OddDouble.lift_isHomogeneous (OddDouble.grading (evenGrading ℝ ℝ) ε) ε floor1embed e₂ he₂sq
        hconj_e₂ 𝒟 hfloor1hom he₂mem
    have hinj : Function.Injective ψ :=
      injective_of_isGradedSimple (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
        𝒟 ψ hψhom
    have hfinD0 : Module.finrank ℝ (𝒟 0 : Submodule ℝ D) = 2 := by
      rw [φ.toLinearEquiv.finrank_eq, Complex.finrank_real_complex]
    have hfinD1 : Module.finrank ℝ (𝒟 1 : Submodule ℝ D) = 2 := by
      rw [← Bimod.oddUnit_finrank_eq hu'1 hu', hfinD0]
    have hfinD : Module.finrank ℝ D = 4 := by
      rw [finrank_eq_add_of_grading (𝒟 := 𝒟), hfinD0, hfinD1]
    have heq : Module.finrank ℝ (OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
        = Module.finrank ℝ D := by
      rw [show Module.finrank ℝ (OddDouble (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
          = Module.finrank ℝ (divisionTower ε 2).carrier from rfl,
        divisionTower_finrank, hfinD]
      norm_num
    have hbij : Function.Bijective ψ :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := ψ.toLinearMap) heq).mp hinj⟩
    have hgrad : ∀ i, ((OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε i)).map
        ψ.toLinearMap = 𝒟 i :=
      map_grading_of_bijective (OddDouble.grading (OddDouble.grading (evenGrading ℝ ℝ) ε) ε)
        𝒟 ψ hψhom hbij
    exact ⟨(⟨AlgEquiv.ofBijective ψ hbij, hgrad⟩ :
      SuperAlgEquiv (divisionTower ε 2) (⟨D, 𝒟⟩ : SuperAlgebra ℝ)).symm⟩

/-- **The `𝒟 0 ≅ ℂ` branch.** Given an odd unit `u` and an abstract algebra iso
`𝒟 0 ≅ ℂ`, the bundled superalgebra `⟨D, 𝒟⟩` is graded-isomorphic to `divisionTower (-1) 2`
(`ε < 0`) or `divisionTower 1 2` (`ε > 0`), where `ε` is the sign of `u²`. Route: `u * u` is a
nonzero real scalar `c` by centrality (`𝒟 0`, being commutative — a copy of `ℂ` — makes `u*u`
supercentral for free, no case split on `σ` needed for this step), and rescaling normalizes
`u² = algebraMap ε`, `ε = ±1`, feeding `key_complex`. -/
theorem nonempty_superAlgEquiv_divisionTower_two_of_gradeZero_complex
    {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D} [GradedAlgebra 𝒟]
    [IsSuperCentral 𝒟] [Nontrivial D] [FiniteDimensional ℝ D] {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] ℂ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower ε 2)) := by
  obtain ⟨husq0, husqU⟩ := Bimod.oddUnit_sq_even_unit hu1 hu
  have hD0comm : ∀ x y : (𝒟 0 : Submodule ℝ D), x * y = y * x := by
    intro x y; apply φ.injective; rw [map_mul, map_mul, mul_comm]
  have hzc : ∀ d ∈ 𝒟 0, (u * u) * d = d * (u * u) := by
    intro d hd
    exact congrArg Subtype.val (hD0comm ⟨u * u, husq0⟩ ⟨d, hd⟩)
  obtain ⟨c, hc⟩ :=
    eq_algebraMap_of_central_zero_commute_odd hu1 hu husq0 hzc (mul_assoc u u u)
  have hcne : c ≠ 0 := fun h => by rw [h, map_zero] at hc; exact husqU.ne_zero hc
  rcases lt_or_gt_of_ne hcne with hcneg | hcpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    set s := Real.sqrt (-c) with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    set r := s⁻¹ with hrdef
    have hrne : r ≠ 0 := inv_ne_zero hspos.ne'
    refine key_complex φ (-1) (by norm_num) (r • u) (Submodule.smul_mem _ r hu1)
      (by rw [Algebra.smul_def]
          exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu) ?_
    have hmul : (r • u) * (r • u) = (r * r) • (u * u) := by rw [smul_mul_smul_comm]
    rw [hmul, hc, Algebra.smul_def, ← map_mul]
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
    refine key_complex φ 1 one_ne_zero (r • u) (Submodule.smul_mem _ r hu1)
      (by rw [Algebra.smul_def]
          exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu) ?_
    have hmul : (r • u) * (r • u) = (r * r) • (u * u) := by rw [smul_mul_smul_comm]
    rw [hmul, hc, Algebra.smul_def, ← map_mul]
    congr 1
    have hss : s * s = c := Real.mul_self_sqrt hcpos.le
    rw [hrdef]
    field_simp
    linarith [hss]

private theorem realRep_two_eq : realRep (2 : ZMod 8) = divisionTower (-1 : ℝ) 2 := rfl

private theorem realRep_six_eq : realRep (6 : ZMod 8) = divisionTower (1 : ℝ) 2 := rfl

/-- **C3b — the `𝒟 0 ≅ ℂ` branch, bundled.** If `S.grading 0 ≅ ℂ` (witnessed abstractly by
`φ`) and `u` is an odd unit, `S` is graded-isomorphic to `realRep 2` (`u² < 0`, `Cl_{0,2}`) or
`realRep 6` (`u² > 0`, `Cl_{2,0}`). -/
theorem superAlgEquiv_of_gradeZero_complex (S : SuperAlgebra.{0, 0} ℝ) [IsSuperCentral S.grading]
    [Nontrivial S.carrier] [FiniteDimensional ℝ S.carrier] {u : S.carrier} (hu1 : u ∈ S.grading 1)
    (hu : IsUnit u) (φ : (S.grading 0 : Submodule ℝ S.carrier) ≃ₐ[ℝ] ℂ) :
    Nonempty (SuperAlgEquiv S (realRep 2)) ∨ Nonempty (SuperAlgEquiv S (realRep 6)) := by
  obtain ⟨ε, hε, ⟨Φ⟩⟩ := nonempty_superAlgEquiv_divisionTower_two_of_gradeZero_complex hu1 hu φ
  rcases hε with rfl | rfl
  · exact Or.inr ⟨realRep_six_eq ▸ Φ⟩
  · exact Or.inl ⟨realRep_two_eq ▸ Φ⟩

end ComplexBranch

/-! ## The `𝒟 0 ≅ ℍ` branch: `realRep 3`, `realRep 5`

**The Skolem–Noether shortcut.** `𝒟 0 ≅ ℍ` is *not* commutative, so the `𝒟 0 ≅ ℂ` branch's
direct centrality argument for "`u` commutes with `𝒟 0`" no longer applies. Instead: transport
"conjugation by `u`" through `φ` into an `ℝ`-algebra endomorphism `σ' : ℍ →ₐ[ℝ] ℍ`
(`transportAut`, shared machinery); since `quatEvenSuper` (`ℍ`, purely even) is supercentral,
graded-simple, and finite-dimensional, the repo's own super Skolem–Noether
(`superSkolemNoether_exists_of_surjective`, at even parity where the Koszul sign collapses)
produces an intertwiner `t : ℍ`, a unit, with `σ'(b) * t = t * b` for all `b : ℍ`. Pulling `t`
back through `φ` gives an even unit `T ∈ 𝒟 0` implementing the *same* conjugation as `u` does on
`𝒟 0`; replacing `u` by `u' := T⁻¹ * u` (an odd unit again) makes conjugation by `u'` the
*identity* on `𝒟 0` — after which the argument is a copy of the `ℂ`-branch's `id` case (now
productive, not a contradiction): `u'` commutes with all of `𝒟 0`, `u'²` is a real scalar by
`eq_algebraMap_of_central_zero_commute_odd`, and after rescaling, the map `ℍ → D` sends `1 ↦ u'`
generators onto `S`, presenting it as `ℍ.oddDouble δ`, identified with `divisionTower (-δ) 3`
(`realRep 3`/`realRep 5`) via the already-landed `cliffThetaEquiv`. -/

section QuaternionBranch

/-- **The final assembly step of the `ℍ`-branch**: given an *already normalized* odd unit `u''`
(`u''² = algebraMap δ`, `δ² = 1`) commuting with all of `𝒟 0`, build the two-generator map
`ℍ → D` (quaternion part into `𝒟 0` via `φ.symm`, the Clifford generator to `u''`) via
`OddDouble.lift` on `quatEvenSuper.grading`, get bijectivity by graded simplicity plus a
`finrank` count (`8 = 8`), and compose with the landed `cliffThetaEquiv`. -/
private theorem key_quaternion_finish {D : Type*} [Ring D] [Algebra ℝ D]
    {𝒟 : ZMod 2 → Submodule ℝ D} [GradedAlgebra 𝒟] [Nontrivial D] [FiniteDimensional ℝ D]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] ℍ[ℝ]) (δ : ℝ) (hδsq : δ * δ = 1) {u'' : D}
    (hu''1 : u'' ∈ 𝒟 1) (hu'' : IsUnit u'') (hu''sq : u'' * u'' = algebraMap ℝ D δ)
    (hu''commD0 : ∀ x ∈ 𝒟 0, u'' * x = x * u'') :
    Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower (-δ) 3)) := by
  have hδne : δ ≠ 0 := fun h => by rw [h, mul_zero] at hδsq; exact zero_ne_one hδsq
  set f : ℍ[ℝ] →ₐ[ℝ] D := gradeZeroEmbed.comp φ.symm.toAlgHom with hfdef
  have hfmem : ∀ a : ℍ[ℝ], f a ∈ 𝒟 0 := fun a => (φ.symm a).2
  have hconj : ∀ a : ℍ[ℝ], u'' * f a = f (parityMap quatEvenSuper.grading a) * u'' := by
    intro a
    show u'' * f a = f (parityMap (evenGrading ℝ ℍ[ℝ]) a) * u''
    rw [parityMap_of_mem_zero (evenGrading ℝ ℍ[ℝ]) Submodule.mem_top, hu''commD0 (f a) (hfmem a)]
  set θ := OddDouble.lift quatEvenSuper.grading δ f u'' hu''sq hconj with hθdef
  have hfhom : IsHomogeneousHom quatEvenSuper.grading 𝒟 f := by
    intro i x hx
    rcases zmod2_cases i with hi | hi <;> subst hi
    · exact hfmem x
    · rw [show (quatEvenSuper.grading 1 : Submodule ℝ ℍ[ℝ]) = ⊥ from rfl,
        Submodule.mem_bot] at hx
      subst hx
      rw [map_zero]
      exact zero_mem _
  have hθhom : IsHomogeneousHom (OddDouble.grading quatEvenSuper.grading δ) 𝒟 θ :=
    OddDouble.lift_isHomogeneous quatEvenSuper.grading δ f u'' hu''sq hconj 𝒟 hfhom hu''1
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  haveI : IsGradedSimple quatEvenSuper.grading := quatEvenSuper_isGradedSimple
  haveI : IsGradedSimple (OddDouble.grading quatEvenSuper.grading δ) :=
    OddDouble.isGradedSimple quatEvenSuper.grading δ hδne
  have hinj : Function.Injective θ :=
    injective_of_isGradedSimple (OddDouble.grading quatEvenSuper.grading δ) 𝒟 θ hθhom
  have hfinD0 : Module.finrank ℝ (𝒟 0 : Submodule ℝ D) = 4 := by
    rw [φ.toLinearEquiv.finrank_eq, Quaternion.finrank_eq_four]
  have hfinD1 : Module.finrank ℝ (𝒟 1 : Submodule ℝ D) = 4 := by
    rw [← Bimod.oddUnit_finrank_eq hu''1 hu'', hfinD0]
  have hfinD : Module.finrank ℝ D = 8 := by
    rw [finrank_eq_add_of_grading (𝒟 := 𝒟), hfinD0, hfinD1]
  have heq : Module.finrank ℝ (OddDouble quatEvenSuper.grading δ) = Module.finrank ℝ D := by
    rw [show Module.finrank ℝ (OddDouble quatEvenSuper.grading δ)
        = Module.finrank ℝ (ℍ[ℝ] × ℍ[ℝ]) from rfl,
      Module.finrank_prod, Quaternion.finrank_eq_four, hfinD]
  have hbij : Function.Bijective θ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := θ.toLinearMap) heq).mp hinj⟩
  have hgrad : ∀ i, ((OddDouble.grading quatEvenSuper.grading δ) i).map θ.toLinearMap = 𝒟 i :=
    map_grading_of_bijective (OddDouble.grading quatEvenSuper.grading δ) 𝒟 θ hθhom hbij
  obtain ⟨Ψ⟩ : Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (quatEvenSuper.oddDouble δ)) :=
    ⟨(⟨AlgEquiv.ofBijective θ hbij, hgrad⟩ :
      SuperAlgEquiv (quatEvenSuper.oddDouble δ) (⟨D, 𝒟⟩ : SuperAlgebra ℝ)).symm⟩
  have hbridge : SuperAlgEquiv (quatEvenSuper.oddDouble δ) (quatEvenSuper.oddDouble (-(-δ))) :=
    oddDouble_congr_eps (show δ = -(-δ) from by ring)
  have hclifford : SuperAlgEquiv (quatEvenSuper.oddDouble (-(-δ))) (divisionTower (-δ) 3) :=
    cliffThetaEquiv (-δ) (by rw [neg_mul_neg]; exact hδsq)
  exact ⟨Ψ.trans (hbridge.trans hclifford)⟩

/-- **The `𝒟 0 ≅ ℍ` branch, generic form.** Given an odd unit `u` and an abstract algebra iso
`φ : 𝒟 0 ≃ₐ[ℝ] ℍ[ℝ]`, the bundled superalgebra `⟨D, 𝒟⟩` is graded-isomorphic to
`divisionTower (-δ) 3` for `δ = ±1`, the (normalized) sign of the replacement odd unit's
square. -/
private theorem key_quaternion {D : Type*} [Ring D] [Algebra ℝ D] {𝒟 : ZMod 2 → Submodule ℝ D}
    [GradedAlgebra 𝒟] [IsSuperCentral 𝒟] [Nontrivial D] [FiniteDimensional ℝ D]
    (φ : (𝒟 0 : Submodule ℝ D) ≃ₐ[ℝ] ℍ[ℝ]) {u : D} (hu1 : u ∈ 𝒟 1) (hu : IsUnit u) :
    ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧
      Nonempty (SuperAlgEquiv (⟨D, 𝒟⟩ : SuperAlgebra ℝ) (divisionTower (-δ) 3)) := by
  set v := ((hu.unit⁻¹ : Dˣ) : D) with hv
  have hv1 : v ∈ 𝒟 1 := Bimod.isUnit_inv_mem hu1 hu.unit hu.unit_spec
  have huv : u * v = 1 := by have h2 := hu.unit.mul_inv; rwa [hu.unit_spec] at h2
  have hvu : v * u = 1 := by have h2 := hu.unit.inv_mul; rwa [hu.unit_spec] at h2
  set σ' : ℍ[ℝ] →ₐ[ℝ] ℍ[ℝ] := transportAut φ hu1 hv1 huv hvu with hσdef
  haveI : IsSuperCentral (evenGrading ℝ ℍ[ℝ]) := quatEvenSuper_isSuperCentral
  haveI : IsGradedSimple (evenGrading ℝ ℍ[ℝ]) := quatEvenSuper_isGradedSimple
  obtain ⟨p, t, htp, htu, hint⟩ := superSkolemNoether_exists_of_surjective (evenGrading ℝ ℍ[ℝ])
    (evenGrading ℝ ℍ[ℝ]) (AlgHom.id ℝ ℍ[ℝ]) σ' (isHomogeneousHom_evenGrading_self _)
    (isHomogeneousHom_evenGrading_self _) Function.surjective_id
    (transportAut_surjective φ hu1 hv1 huv hvu)
  have hgen : ∀ b : ℍ[ℝ], σ' b * t = t * b := by
    intro b
    have h := hint (j := 0) (b := b) Submodule.mem_top
    rwa [zero_mul, sgn_zero, Units.val_one, one_smul, AlgHom.id_apply] at h
  have htne : t ≠ 0 := htu.ne_zero
  set T0 : (𝒟 0 : Submodule ℝ D) := φ.symm t with hT0def
  set Tinv0 : (𝒟 0 : Submodule ℝ D) := φ.symm t⁻¹ with hTinv0def
  have hT0Tinv0 : T0 * Tinv0 = 1 := by
    apply φ.injective
    rw [map_mul, hT0def, hTinv0def, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      mul_inv_cancel₀ htne, map_one]
  have hTinv0T0 : Tinv0 * T0 = 1 := by
    apply φ.injective
    rw [map_mul, hT0def, hTinv0def, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      inv_mul_cancel₀ htne, map_one]
  have hφT0 : φ T0 = t := by rw [hT0def]; exact φ.apply_symm_apply _
  have hgenx : ∀ x : (𝒟 0 : Submodule ℝ D),
      conjGradeZero hu1 hv1 huv hvu x = T0 * x * Tinv0 := by
    intro x
    apply φ.injective
    rw [map_mul, map_mul, hφT0, hTinv0def, AlgEquiv.apply_symm_apply]
    have h1 := hgen (φ x)
    rw [hσdef, transportAut_apply, AlgEquiv.symm_apply_apply] at h1
    rw [← h1, mul_assoc, mul_inv_cancel₀ htne, mul_one]
  set T : D := (T0 : D) with hTdef
  set Tinv : D := (Tinv0 : D) with hTinvdef
  have hTmem : T ∈ 𝒟 0 := T0.2
  have hTinvmem : Tinv ∈ 𝒟 0 := Tinv0.2
  have hTTinv : T * Tinv = 1 := congrArg Subtype.val hT0Tinv0
  have hTinvT : Tinv * T = 1 := congrArg Subtype.val hTinv0T0
  set u' : D := Tinv * u with hu'def
  set v' : D := v * T with hv'def
  have hu'1 : u' ∈ 𝒟 1 := by
    have h := SetLike.mul_mem_graded hTinvmem hu1
    rwa [zero_add] at h
  have hv'1 : v' ∈ 𝒟 1 := by
    have h := SetLike.mul_mem_graded hv1 hTmem
    rwa [add_zero] at h
  have hu'v' : u' * v' = 1 := by
    rw [hu'def, hv'def, show Tinv * u * (v * T) = Tinv * (u * v) * T by noncomm_ring, huv,
      mul_one, hTinvT]
  have hv'u' : v' * u' = 1 := by
    rw [hv'def, hu'def, show v * T * (Tinv * u) = v * (T * Tinv) * u by noncomm_ring, hTTinv,
      mul_one, hvu]
  have hu' : IsUnit u' := ⟨⟨u', v', hu'v', hv'u'⟩, rfl⟩
  have hfix : ∀ x ∈ 𝒟 0, u' * x * v' = x := by
    intro x hx
    have hD : u * x * v = T * x * Tinv := congrArg Subtype.val (hgenx ⟨x, hx⟩)
    rw [hu'def, hv'def, show Tinv * u * x * (v * T) = Tinv * (u * x * v) * T by noncomm_ring, hD,
      show Tinv * (T * x * Tinv) * T = (Tinv * T) * x * (Tinv * T) by noncomm_ring, hTinvT,
      one_mul, mul_one]
  clear_value T Tinv u' v'
  have hu'commD0 : ∀ x ∈ 𝒟 0, u' * x = x * u' := by
    intro x hx
    have h2 : u' * x * (v' * u') = x * u' := by rw [← mul_assoc, hfix x hx]
    rwa [mul_assoc, hv'u', mul_one] at h2
  obtain ⟨hu'sq0, hu'squ⟩ := Bimod.oddUnit_sq_even_unit hu'1 hu'
  have hzc : ∀ d ∈ 𝒟 0, (u' * u') * d = d * (u' * u') := by
    intro d hd
    calc (u' * u') * d = u' * (u' * d) := by rw [mul_assoc]
      _ = u' * (d * u') := by rw [hu'commD0 d hd]
      _ = (u' * d) * u' := by rw [mul_assoc]
      _ = (d * u') * u' := by rw [hu'commD0 d hd]
      _ = d * (u' * u') := by rw [mul_assoc]
  obtain ⟨c, hc⟩ :=
    eq_algebraMap_of_central_zero_commute_odd hu'1 hu' hu'sq0 hzc (mul_assoc u' u' u')
  have hcne : c ≠ 0 := fun h => by rw [h, map_zero] at hc; exact hu'squ.ne_zero hc
  rcases lt_or_gt_of_ne hcne with hcneg | hcpos
  · -- `δ = -1`
    set s := Real.sqrt (-c) with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    set r := s⁻¹ with hrdef
    have hrne : r ≠ 0 := inv_ne_zero hspos.ne'
    set u'' : D := r • u' with hu''def
    have hu''1 : u'' ∈ 𝒟 1 := Submodule.smul_mem _ r hu'1
    have hu'' : IsUnit u'' := by
      rw [hu''def, Algebra.smul_def]
      exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu'
    have hu''sq : u'' * u'' = algebraMap ℝ D (-1) := by
      have hmul : u'' * u'' = (r * r) • (u' * u') := by rw [hu''def, smul_mul_smul_comm]
      rw [hmul, hc, Algebra.smul_def, ← map_mul]
      congr 1
      have hss : s * s = -c := Real.mul_self_sqrt (by linarith)
      rw [hrdef]; field_simp; linarith [hss]
    have hu''commD0 : ∀ x ∈ 𝒟 0, u'' * x = x * u'' := by
      intro x hx
      rw [hu''def, smul_mul_assoc, mul_smul_comm, hu'commD0 x hx]
    exact ⟨(-1 : ℝ), Or.inr rfl,
      key_quaternion_finish φ (-1 : ℝ) (by norm_num) hu''1 hu'' hu''sq hu''commD0⟩
  · -- `δ = 1`
    set s := Real.sqrt c with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr hcpos
    set r := s⁻¹ with hrdef
    have hrne : r ≠ 0 := inv_ne_zero hspos.ne'
    set u'' : D := r • u' with hu''def
    have hu''1 : u'' ∈ 𝒟 1 := Submodule.smul_mem _ r hu'1
    have hu'' : IsUnit u'' := by
      rw [hu''def, Algebra.smul_def]
      exact ((isUnit_iff_ne_zero.mpr hrne).map (algebraMap ℝ D)).mul hu'
    have hu''sq : u'' * u'' = algebraMap ℝ D 1 := by
      have hmul : u'' * u'' = (r * r) • (u' * u') := by rw [hu''def, smul_mul_smul_comm]
      rw [hmul, hc, Algebra.smul_def, ← map_mul]
      congr 1
      have hss : s * s = c := Real.mul_self_sqrt hcpos.le
      rw [hrdef]; field_simp; linarith [hss]
    have hu''commD0 : ∀ x ∈ 𝒟 0, u'' * x = x * u'' := by
      intro x hx
      rw [hu''def, smul_mul_assoc, mul_smul_comm, hu'commD0 x hx]
    exact ⟨(1 : ℝ), Or.inl rfl,
      key_quaternion_finish φ (1 : ℝ) (by norm_num) hu''1 hu'' hu''sq hu''commD0⟩

private theorem realRep_three_eq : realRep (3 : ZMod 8) = divisionTower (-1 : ℝ) 3 := rfl

private theorem realRep_five_eq : realRep (5 : ZMod 8) = divisionTower (1 : ℝ) 3 := rfl

/-- **C3b — the `𝒟 0 ≅ ℍ` branch, bundled.** If `S.grading 0 ≅ ℍ[ℝ]` (witnessed abstractly by
`φ`) and `u` is an odd unit, `S` is graded-isomorphic to `realRep 3` (`Cl_{0,3}`) or `realRep 5`
(`Cl_{3,0}`). -/
theorem superAlgEquiv_of_gradeZero_quaternion (S : SuperAlgebra.{0, 0} ℝ)
    [IsSuperCentral S.grading] [Nontrivial S.carrier] [FiniteDimensional ℝ S.carrier]
    {u : S.carrier} (hu1 : u ∈ S.grading 1) (hu : IsUnit u)
    (φ : (S.grading 0 : Submodule ℝ S.carrier) ≃ₐ[ℝ] ℍ[ℝ]) :
    Nonempty (SuperAlgEquiv S (realRep 3)) ∨ Nonempty (SuperAlgEquiv S (realRep 5)) := by
  obtain ⟨δ, hδ, ⟨Φ⟩⟩ := key_quaternion φ hu1 hu
  rcases hδ with rfl | rfl
  · exact Or.inl ⟨realRep_three_eq ▸ Φ⟩
  · have heq : (-(-1 : ℝ)) = (1 : ℝ) := by norm_num
    have Φ' : SuperAlgEquiv S (divisionTower (1 : ℝ) 3) := heq ▸ Φ
    exact Or.inr ⟨realRep_five_eq ▸ Φ'⟩

end QuaternionBranch

/-! ## C4: the classification theorem, and the `realGauge`/`DBW ℝ` payoffs

Assembly: purely-even splits into `{0, 4}` (`superAlgEquiv_of_odd_eq_bot`, landed); with an odd
unit, `𝒟 0` is a finite-dimensional division ring (`divisionRingGradeZero`), classified by
Frobenius' trichotomy (`Frobenius.frobenius_trichotomy`) into `ℝ`, `ℂ`, `ℍ`, landing via the
three branches above in `{1, 7}`, `{2, 6}`, `{3, 5}` respectively — covering all eight classes
of `ZMod 8`. -/

section Classification

/-- **C4 — the real central super division classification theorem.** Every
finite-dimensional, nontrivial, supercentral super *division* algebra `S` over `ℝ` is
graded-isomorphic to one of the eight `realRep a` (`a : ZMod 8`, Table 1). -/
theorem real_superDivision_classification (S : SuperAlgebra.{0, 0} ℝ) [IsSuperCentral S.grading]
    (hdiv : Bimod.IsSuperDivision S.grading) [FiniteDimensional ℝ S.carrier]
    [Nontrivial S.carrier] : ∃ a : ZMod 8, Nonempty (SuperAlgEquiv S (realRep a)) := by
  rcases hdiv.dichotomy with h1 | ⟨u, hu1, hu⟩
  · rcases superAlgEquiv_of_odd_eq_bot S hdiv h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨4, h⟩
  · letI : DivisionRing (S.grading 0 : Submodule ℝ S.carrier) := divisionRingGradeZero hdiv
    rcases Frobenius.frobenius_trichotomy (S.grading 0 : Submodule ℝ S.carrier) with h | h | h
    · obtain ⟨φ⟩ := h
      rcases superAlgEquiv_of_gradeZero_real S hu1 hu φ with h' | h'
      · exact ⟨7, h'⟩
      · exact ⟨1, h'⟩
    · obtain ⟨φ⟩ := h
      rcases superAlgEquiv_of_gradeZero_complex S hu1 hu φ with h' | h'
      · exact ⟨2, h'⟩
      · exact ⟨6, h'⟩
    · obtain ⟨φ⟩ := h
      rcases superAlgEquiv_of_gradeZero_quaternion S hu1 hu φ with h' | h'
      · exact ⟨3, h'⟩
      · exact ⟨5, h'⟩

/-- **`realGauge` is canonical**: its Brauer–Wall class map is injective (landed,
`realGauge_bwClass_injective`) with range *exactly* `DBW ℝ` — the missing surjectivity
hypothesis of `realGauge_isCanonical_of_surjective` is now supplied by
`real_superDivision_classification`: every division-representable class has a super division
witness `D`, classified as `D ≅ realRep a` for some `a`, and Brauer–Wall classes are invariant
under `SuperAlgEquiv` (`IsBWEquivalent.of_superAlgEquiv`, `BWMonoid.mk_eq_mk_iff`). -/
theorem realGauge_isCanonical : realGauge.IsCanonical := by
  apply realGauge_isCanonical_of_surjective
  rintro x ⟨D, hc, _hgs, hf, hn, hdiv, hval⟩
  haveI := hc
  haveI := hf
  haveI := hn
  obtain ⟨a, ⟨Φ⟩⟩ := real_superDivision_classification D hdiv
  refine ⟨a, ?_⟩
  apply Units.ext
  rw [DivisionFusionGauge.bwClass_val]
  haveI := realRep_finiteDimensional a
  haveI := realRep_nontrivial a
  show BWMonoid.mk (realRep a) = x.val
  rw [← hval]
  exact (BWMonoid.mk_eq_mk_iff.mpr (IsBWEquivalent.of_superAlgEquiv Φ)).symm

/-- **The division-representable Brauer–Wall classes of `ℝ` are exactly the range of
`realGauge.bwClass`**, both inclusions now available from `realGauge_isCanonical`. -/
theorem DBW_real_eq_range : DBW ℝ = Set.range realGauge.bwClass :=
  realGauge_isCanonical.2.symm

/-- **The finale**: the division-representable Brauer–Wall classes of `ℝ` form a set in
bijection with `ZMod 8` (a group of order `8`, generated by the class of `Cl_{1,0}`), realized
by the eight `realRep` representatives via `realGauge.bwClass`. -/
noncomputable def zmod8_equiv_DBW_real : ZMod 8 ≃ ↥(DBW ℝ) :=
  (Equiv.ofInjective realGauge.bwClass realGauge_bwClass_injective).trans
    (Equiv.setCongr DBW_real_eq_range.symm)

end Classification

end Superfusion
