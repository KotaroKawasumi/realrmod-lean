/-
Superfusion / Gauge / SuperDivisionBasic

Milestone M9-1a: the opening round of the **intrinsic gauge track**
(general-`K` `(G, D_a, φ)` framework, §2.1-2.2).  This file develops the
basic theory of the project-local super-division predicate
`IsSuperDivision` (`Superfusion.Bimod.ColumnSimple`, reused verbatim,
not redefined):

* the purely even base `SuperAlgebra.base K` is super division
  (`IsSuperDivision.base`);
* super division is preserved by the super-opposite construction
  (`IsSuperDivision.sop`);
* super division is preserved by the ordinary multiplicative opposite
  (`isSuperDivision_opGrading`), the unsigned bridge for right modules;
* **the type dichotomy** driving the whole gauge classification: a
  super division algebra is either purely even (`𝒟 1 = ⊥`) or has an
  odd unit (`IsSuperDivision.dichotomy`);
* the structural consequences of an odd unit — left multiplication is
  a `K`-linear equivalence swapping the two grade components
  (`oddUnit_mulEquiv`, with the `finrank` corollary
  `oddUnit_finrank_eq`), and its square is an even unit
  (`oddUnit_sq_even_unit`).

The key technical lemma feeding both `IsSuperDivision.sop` and the
odd-unit consequences is `isUnit_inv_mem`: in a `ZMod 2`-graded ring,
the (two-sided, ring-theoretic) inverse of a homogeneous unit is again
homogeneous, of the *same* degree (`ZMod 2` being `2`-torsion, "same
degree" is also "opposite degree").  This is a general graded-ring
fact, not special to super division algebras, and is proved once by a
grade-component cancellation argument, mirroring the sign-free
`columnBimodule_irreducible` argument of `ColumnSimple.lean`.

Design record: docs/super-track-design.md (M7d-5c-adjacent sections).
-/
import Superfusion.Bimod.ColumnSimple
import Superfusion.Super.DivisionTower
import Superfusion.Super.PlainOpposite
import Superfusion.Super.SuperOpposite

namespace Superfusion

namespace Bimod

variable {K : Type*} [Field K]

/-! ### The purely even base case -/

/-- The purely even base superalgebra is a super division algebra: in a
field every nonzero scalar is a unit, and the odd part is trivial so the
odd case is vacuous. -/
theorem IsSuperDivision.base : IsSuperDivision (SuperAlgebra.base K).grading := by
  show IsSuperDivision (evenGrading K K)
  intro i x hx hx0
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact isUnit_iff_ne_zero.mpr hx0
  · rw [evenGrading_one, Submodule.mem_bot] at hx
    exact absurd hx hx0

variable {D : Type*} [Ring D] [Algebra K D] {𝒟 : ZMod 2 → Submodule K D}

/-- Specialization of `IsSuperDivision` to the even part. -/
theorem IsSuperDivision.isUnit_of_mem_zero (h : IsSuperDivision 𝒟) {x : D}
    (hx : x ∈ 𝒟 0) (hx0 : x ≠ 0) : IsUnit x := h hx hx0

/-- Specialization of `IsSuperDivision` to the odd part. -/
theorem IsSuperDivision.isUnit_of_mem_one (h : IsSuperDivision 𝒟) {x : D}
    (hx : x ∈ 𝒟 1) (hx0 : x ≠ 0) : IsUnit x := h hx hx0

/-- **The type dichotomy** (§2.2): a super division algebra is either
purely even, or it has an odd unit.  Nearly definitional: if `𝒟 1 ≠ ⊥`
a nonzero `u ∈ 𝒟 1` exists, and `h` makes it a unit. -/
theorem IsSuperDivision.dichotomy (h : IsSuperDivision 𝒟) :
    𝒟 1 = ⊥ ∨ ∃ u : D, u ∈ 𝒟 1 ∧ IsUnit u := by
  rcases eq_or_ne (𝒟 1) ⊥ with h1 | h1
  · exact Or.inl h1
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    exact Or.inr ⟨u, hu, h hu hu0⟩

/-- If the odd part is trivial, no odd element is a unit (in a
nontrivial ring): the purely-even case of the dichotomy really is
purely even. -/
theorem no_odd_unit_of_bot [Nontrivial D] (h1 : 𝒟 1 = ⊥) {x : D}
    (hx : x ∈ 𝒟 1) (hu : IsUnit x) : False := by
  rw [h1, Submodule.mem_bot] at hx
  exact hu.ne_zero hx

/-! ### Homogeneous units have homogeneous inverses -/

private theorem zmod2_add_self' : ∀ i : ZMod 2, i + i = 0 := by decide

private theorem zmod2_add_succ_self' : ∀ i : ZMod 2, i + (i + 1) = 1 := by decide

private theorem modProj_add_modProj_succ {M : Type*} [AddCommGroup M]
    [Module K M] (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
    (i : ZMod 2) (m : M) : modProj ℳ i m + modProj ℳ (i + 1) m = m := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · simpa using modProj_zero_add_modProj_one ℳ m
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm]
    exact modProj_zero_add_modProj_one ℳ m

/-- **A homogeneous unit's inverse is homogeneous, of the same degree**
(`ZMod 2` is `2`-torsion, so "same" is also "opposite"): a general
graded-ring fact, proved by a grade-component cancellation argument and
not special to super division algebras. -/
theorem isUnit_inv_mem [GradedAlgebra 𝒟] {i : ZMod 2} {x : D} (hx : x ∈ 𝒟 i)
    (u : Dˣ) (hux : (u : D) = x) : ((u⁻¹ : Dˣ) : D) ∈ 𝒟 i := by
  set z := ((u⁻¹ : Dˣ) : D) with hz
  have hxz : x * z = 1 := hux ▸ u.mul_inv
  have hzx : z * x = 1 := hux ▸ u.inv_mul
  have hsplit := modProj_add_modProj_succ 𝒟 i z
  have hmem0 : x * modProj 𝒟 i z ∈ 𝒟 0 := by
    have h := SetLike.mul_mem_graded hx (modProj_mem 𝒟 i z)
    rwa [zmod2_add_self' i] at h
  have hmem1 : x * modProj 𝒟 (i + 1) z ∈ 𝒟 1 := by
    have h := SetLike.mul_mem_graded hx (modProj_mem 𝒟 (i + 1) z)
    rwa [zmod2_add_succ_self' i] at h
  have hsum : x * modProj 𝒟 i z + x * modProj 𝒟 (i + 1) z = 1 := by
    rw [← mul_add, hsplit, hxz]
  have e1 : x * modProj 𝒟 (i + 1) z = 0 := by
    have h := congrArg (modProj 𝒟 1) hsum
    rwa [map_add, modProj_of_mem_ne 𝒟 hmem0 (by decide), modProj_of_mem 𝒟 hmem1,
      zero_add, modProj_of_mem_ne 𝒟 (SetLike.one_mem_graded 𝒟) (by decide)] at h
  have hz1 : modProj 𝒟 (i + 1) z = 0 := by
    have h : z * (x * modProj 𝒟 (i + 1) z) = z * 0 := by rw [e1]
    rwa [← mul_assoc, hzx, one_mul, mul_zero] at h
  rw [← hsplit, hz1, add_zero]
  exact modProj_mem 𝒟 i z

/-! ### The super-opposite preserves super division -/

/-- **Super division is preserved by the super-opposite construction.**
The super-opposite's grading is the same underlying submodules with a
signed multiplication (`SuperOpposite.lean`); a nonzero homogeneous
element is a unit there because it is a unit in the original ring with
a homogeneous inverse (`isUnit_inv_mem`), the sign correction
(`op_mul_op_of_mem`) being itself an invertible scalar (`±1`). -/
theorem IsSuperDivision.sop [GradedAlgebra 𝒟] (h : IsSuperDivision 𝒟) :
    IsSuperDivision (SuperOp.grading 𝒟) := by
  intro i x hx hx0
  have ha : SuperOp.unop 𝒟 x ∈ 𝒟 i := (SuperOp.mem_grading_iff 𝒟 i x).mp hx
  have ha0 : SuperOp.unop 𝒟 x ≠ 0 := fun h0 =>
    hx0 (by rw [← SuperOp.op_unop 𝒟 x, h0, map_zero])
  obtain ⟨u, hu⟩ := h ha ha0
  have hz : ((u⁻¹ : Dˣ) : D) ∈ 𝒟 i := isUnit_inv_mem ha u hu
  have hzx0 : ((u⁻¹ : Dˣ) : D) * SuperOp.unop 𝒟 x = 1 := by rw [← hu]; exact u.inv_mul
  have hx0z : SuperOp.unop 𝒟 x * ((u⁻¹ : Dˣ) : D) = 1 := by rw [← hu]; exact u.mul_inv
  have hux : SuperOp.op 𝒟 (SuperOp.unop 𝒟 x) = x := SuperOp.op_unop 𝒟 x
  have hxr : x * SuperOp.op 𝒟 ((u⁻¹ : Dˣ) : D)
      = ((sgn (i * i) : ℤˣ) : ℤ) • (1 : SuperOp 𝒟) := by
    rw [← hux, SuperOp.op_mul_op_of_mem 𝒟 ha hz, hzx0, SuperOp.op_one]
  have hxl : SuperOp.op 𝒟 ((u⁻¹ : Dˣ) : D) * x
      = ((sgn (i * i) : ℤˣ) : ℤ) • (1 : SuperOp 𝒟) := by
    rw [← hux, SuperOp.op_mul_op_of_mem 𝒟 hz ha, hx0z, SuperOp.op_one]
  rcases zmod2_cases i with hi | hi <;> subst hi
  · simp only [zero_mul, sgn_zero, Units.val_one, one_smul] at hxr hxl
    exact ⟨⟨x, SuperOp.op 𝒟 ((u⁻¹ : Dˣ) : D), hxr, hxl⟩, rfl⟩
  · simp only [one_mul, sgn_one, units_sign_eq, Units.val_neg, Units.val_one,
      neg_smul, one_smul] at hxr hxl
    refine ⟨⟨x, -(SuperOp.op 𝒟 ((u⁻¹ : Dˣ) : D)), ?_, ?_⟩, rfl⟩
    · rw [mul_neg, hxr, neg_neg]
    · rw [neg_mul, hxl, neg_neg]

/-! ### Consequences of an odd unit -/

/-- **Left multiplication by an odd unit swaps the two grade
components.**  A `K`-linear equivalence `𝒟 0 ≃ₗ[K] 𝒟 1`; its inverse is
left multiplication by `u⁻¹`, which is odd again by `isUnit_inv_mem`. -/
noncomputable def oddUnit_mulEquiv [GradedAlgebra 𝒟] {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) : (𝒟 0) ≃ₗ[K] (𝒟 1) := by
  have hv1 : ((hu.unit⁻¹ : Dˣ) : D) ∈ 𝒟 1 := isUnit_inv_mem hu1 hu.unit hu.unit_spec
  refine LinearEquiv.ofLinear
    (LinearMap.codRestrict (𝒟 1) ((LinearMap.mulLeft K u).domRestrict (𝒟 0)) ?_)
    (LinearMap.codRestrict (𝒟 0)
      ((LinearMap.mulLeft K ((hu.unit⁻¹ : Dˣ) : D)).domRestrict (𝒟 1)) ?_)
    ?_ ?_
  · intro x
    have h := SetLike.mul_mem_graded hu1 x.2
    rwa [add_zero] at h
  · intro y
    have h := SetLike.mul_mem_graded hv1 y.2
    rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
  · apply LinearMap.ext
    intro y
    apply Subtype.ext
    show u * (((hu.unit⁻¹ : Dˣ) : D) * (y : D)) = (y : D)
    have hcancel : u * ((hu.unit⁻¹ : Dˣ) : D) = 1 := by
      have h := hu.unit.mul_inv
      rwa [hu.unit_spec] at h
    rw [← mul_assoc, hcancel, one_mul]
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    show ((hu.unit⁻¹ : Dˣ) : D) * (u * (x : D)) = (x : D)
    have hcancel : ((hu.unit⁻¹ : Dˣ) : D) * u = 1 := by
      have h := hu.unit.inv_mul
      rwa [hu.unit_spec] at h
    rw [← mul_assoc, hcancel, one_mul]

/-- The two grade components of a superalgebra with an odd unit have
equal dimension (no finiteness hypothesis needed: `LinearEquiv.finrank_eq`
holds unconditionally, both sides collapsing to `0` in the infinite
case). -/
theorem oddUnit_finrank_eq [GradedAlgebra 𝒟] {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) : Module.finrank K (𝒟 0) = Module.finrank K (𝒟 1) :=
  (oddUnit_mulEquiv hu1 hu).finrank_eq

/-- The square of an odd unit is an even unit. -/
theorem oddUnit_sq_even_unit [GradedAlgebra 𝒟] {u : D} (hu1 : u ∈ 𝒟 1)
    (hu : IsUnit u) : u * u ∈ 𝒟 0 ∧ IsUnit (u * u) := by
  refine ⟨?_, hu.mul hu⟩
  have h := SetLike.mul_mem_graded hu1 hu1
  rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h

end Bimod

/-- Super division is preserved by the ordinary multiplicative opposite.

Unlike the super-opposite, the plain opposite introduces no Koszul sign:
homogeneous units transfer directly through `op` and `unop`. -/
theorem isSuperDivision_opGrading
    {K : Type*} [Field K]
    {D : Type*} [Ring D] [Algebra K D]
    (𝒟 : ZMod 2 → Submodule K D)
    (hdiv : Bimod.IsSuperDivision 𝒟) :
    Bimod.IsSuperDivision (opGrading 𝒟) := by
  intro i x hx hx0
  have ha : MulOpposite.unop x ∈ 𝒟 i :=
    (mem_opGrading_iff 𝒟).mp hx
  have ha0 : MulOpposite.unop x ≠ 0 := fun h0 =>
    hx0 (by rw [← MulOpposite.op_unop x, h0, MulOpposite.op_zero])
  have hu : IsUnit (MulOpposite.unop x) := hdiv ha ha0
  rw [← MulOpposite.op_unop x]
  exact hu.op

end Superfusion
