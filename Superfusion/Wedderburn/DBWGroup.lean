/-
Superfusion / Wedderburn / DBWGroup

Milestone M10-6, the final round of the graded Wedderburn arc: **the `DBW(K)`
group law for a general field**.

`Superfusion.Gauge.DBW` left `DBW.MulClosed` — the mini-Wedderburn target —
deliberately unproved for a general field `K`, landing it only at `K = ℝ`
(`Superfusion.Gauge.DBWRealGroup`, via the completed real classification,
*without* appeal to the general theorem).  This file closes that gap using
the graded Wedderburn theorem (`Superfusion.Wedderburn.MatrixRealization`)
and the converse of Wall's criterion (`Superfusion.Wedderburn.AzumayaConverse`).

**Contents.**

* `exists_division_of_gtensor`: the tensor-of-divisions Wedderburn
  corollary — the graded tensor product of two central-simple,
  finite-dimensional, nontrivial super *division* algebras is again
  super-Azumaya (Wall's criterion forward direction on each factor, then
  closure under `ᵍ⊗`), hence central and graded-simple (the converse of
  Wall's criterion); `graded_wedderburn` then produces a super division
  algebra `D₃` and `p q : ℕ` with `p + q ≠ 0` realizing it as
  `M_{p|q}(D₃)`, and `D₃` inherits all six DBW witness fields (centrality
  descends from the matrix stabilization via the P-twist, graded
  simplicity is automatic for a super division algebra).
* `DBW_mulClosed`: `DBW.MulClosed` for a *general* field `K` — unfold
  membership on both sides to representatives, multiply via
  `BWMonoid.mk_mul`, and apply the corollary above.
* `DBWSubgroup`: `DBW K` packaged as a subgroup of `BW K`, for a general
  field `K`, generalizing the landed `DBWRealSubgroup`.
* `DBWSubgroup_real_eq`: the general construction specializes to
  `DBWRealSubgroup` at `K = ℝ` (both are literally built from the same
  carrier `DBW ℝ`, so the identification of subgroup structures is `rfl`
  by proof irrelevance of the closure fields).

**What remains open.** With this file, `DBW K` is a group for *every*
field `K` with `2` invertible — the "one irreducible core" of the M9
design dialogue is closed. The further statement `BW K = DBW K` (every
Brauer–Wall class has a division-algebra representative, i.e. every unit
of the class monoid `BWMonoid K` has an Azumaya representative) is a
genuinely separate theorem: it is the *converse* of the fact that Azumaya
classes are units (`BW.ofAzumaya`), asking that an **arbitrary**
representative of an invertible class can be replaced by one that is
graded-simple. `graded_wedderburn` cannot be invoked directly on such a
representative because it takes `IsGradedSimple` as a *hypothesis*, and a
generic quotient representative of a unit's class carries no such
structure a priori (the representative is produced by `Quotient.out`/
`Quotient.exists_rep`, with no control over its internal structure beyond
finite-dimensionality and nontriviality). Establishing `BW K = DBW K` in
general needs an independent structure-theoretic argument (reducing an
arbitrary finite-dimensional representative via its own Wedderburn/Jacobson
radical theory before the graded machinery applies), which is not carried
out here; this file lands the group law (`DBWSubgroup`) only.

Update (M10-7): `BW K = DBW K` is now closed in `Wedderburn/BWEqualsDBW.lean`.
-/
import Superfusion.Wedderburn.MatrixRealization
import Superfusion.Wedderburn.AzumayaConverse
import Superfusion.Super.WallFactor
import Superfusion.Gauge.DBWRealGroup

namespace Superfusion

/-! ### Deliverable 1: division ⊗ division ⇒ `M_{p|q}(division)` -/

section TensorDivision

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- **The tensor-of-divisions Wedderburn corollary** (M10-6, deliverable 1). The graded tensor
product of two central-simple, finite-dimensional, nontrivial super *division* algebras
`D₁ D₂` is again super-Azumaya (`isSuperAzumaya_of_central_simple` on each factor, then
`isSuperAzumaya_tensorGrading` for closure under `ᵍ⊗`), hence central
(`isSuperCentral_of_isSuperAzumaya`) and graded-simple (`isGradedSimple_of_isSuperAzumaya`);
`graded_wedderburn` realizes it as `M_{p|q}(D₃)` for a super division algebra `D₃`
(`p + q ≠ 0`), which inherits all six DBW witness fields: graded simplicity is automatic for
a super division algebra (`IsSuperDivision.isGradedSimple`), and centrality transports from the
tensor product onto the matrix stabilization (`isSuperCentral_of_equiv`) and then descends to
`D₃` itself via the P-twist (`isSuperCentral_of_matrixSuper`, using `p + q ≠ 0`). -/
theorem exists_division_of_gtensor (D₁ D₂ : SuperAlgebra.{u, u} K)
    [hc1 : IsSuperCentral D₁.grading] [hs1 : IsGradedSimple D₁.grading]
    [hf1 : FiniteDimensional K D₁.carrier] [hn1 : Nontrivial D₁.carrier]
    (_hdiv1 : Bimod.IsSuperDivision D₁.grading)
    [hc2 : IsSuperCentral D₂.grading] [hs2 : IsGradedSimple D₂.grading]
    [hf2 : FiniteDimensional K D₂.carrier] [hn2 : Nontrivial D₂.carrier]
    (_hdiv2 : Bimod.IsSuperDivision D₂.grading) :
    ∃ (D₃ : SuperAlgebra.{u, u} K) (p q : ℕ), p + q ≠ 0 ∧
      IsSuperCentral D₃.grading ∧ IsGradedSimple D₃.grading ∧
      ∃ (hf3 : FiniteDimensional K D₃.carrier) (hn3 : Nontrivial D₃.carrier),
      Bimod.IsSuperDivision D₃.grading ∧
        haveI := hf3; haveI := hn3; BWMonoid.mk D₃ = BWMonoid.mk (D₁.gtensor D₂) := by
  haveI hA1 : IsSuperAzumaya D₁.grading := isSuperAzumaya_of_central_simple D₁.grading
  haveI hA2 : IsSuperAzumaya D₂.grading := isSuperAzumaya_of_central_simple D₂.grading
  haveI hAtensor : IsSuperAzumaya (D₁.gtensor D₂).grading :=
    isSuperAzumaya_tensorGrading D₁.grading D₂.grading
  haveI hAcentral : IsSuperCentral (D₁.gtensor D₂).grading :=
    isSuperCentral_of_isSuperAzumaya (D₁.gtensor D₂).grading
  haveI hAsimple : IsGradedSimple (D₁.gtensor D₂).grading :=
    isGradedSimple_of_isSuperAzumaya (D₁.gtensor D₂).grading
  obtain ⟨D₃, p, q, hpq, hdiv3, hfin3, hnontriv3, ⟨θ⟩⟩ :=
    graded_wedderburn (D₁.gtensor D₂)
  haveI := hfin3
  haveI := hnontriv3
  have hsimple3 : IsGradedSimple D₃.grading := IsSuperDivision.isGradedSimple hdiv3
  haveI hcentralMatrix : IsSuperCentral (D₃.matrixSuper p q).grading :=
    isSuperCentral_of_equiv (D₁.gtensor D₂).grading (D₃.matrixSuper p q).grading
      θ.toAlgEquiv θ.map_grading
  have hcentral3 : IsSuperCentral D₃.grading := isSuperCentral_of_matrixSuper D₃ p q hpq
  exact ⟨D₃, p, q, hpq, hcentral3, hsimple3, hfin3, hnontriv3, hdiv3,
    BWMonoid.mk_eq_mk_iff.mpr (IsBWEquivalent.of_matrixSuper hpq θ).symm⟩

end TensorDivision

/-! ### Deliverable 2: `DBW.MulClosed` for a general field -/

section MulClosed

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **`DBW(K)` is multiplicatively closed, for a general field `K`** (M10-6, deliverable 2):
unfold membership of `x` and `y` to central-simple division representatives `D₁`, `D₂`; the
product `x * y` has value `mk D₁ * mk D₂ = mk (D₁ ᵍ⊗ D₂)` (`BWMonoid.mk_mul`), which is the class
of the division representative `D₃` produced by `exists_division_of_gtensor`. -/
theorem DBW_mulClosed : DBW.MulClosed (K := K) := by
  intro x y hx hy
  obtain ⟨D₁, hc1, hs1, hf1, hn1, hdiv1, hval1⟩ := hx
  obtain ⟨D₂, hc2, hs2, hf2, hn2, hdiv2, hval2⟩ := hy
  haveI := hc1
  haveI := hs1
  haveI := hf1
  haveI := hn1
  haveI := hc2
  haveI := hs2
  haveI := hf2
  haveI := hn2
  obtain ⟨D₃, p, q, hpq, hc3, hs3, hf3, hn3, hdiv3, hmk⟩ :=
    exists_division_of_gtensor D₁ D₂ hdiv1 hdiv2
  have hxy : (x * y).val = BWMonoid.mk (D₁.gtensor D₂) := by
    show x.val * y.val = BWMonoid.mk (D₁.gtensor D₂)
    rw [← hval1, ← hval2]
    exact BWMonoid.mk_mul D₁ D₂
  refine ⟨D₃, hc3, hs3, hf3, hn3, hdiv3, ?_⟩
  haveI := hf3
  haveI := hn3
  rw [hxy]
  exact hmk

end MulClosed

/-! ### Deliverable 3: `DBW(K)` as a subgroup of `BW(K)`, for a general field -/

section Subgroup

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **`DBW(K)`, packaged as a subgroup of `BW(K)`, for a general field `K`** (M10-6,
deliverable 3): the three closure properties (`DBW.one_mem`, `DBW_mulClosed`, `DBW.inv_mem`),
mirroring `DBWRealSubgroup` (`Superfusion.Gauge.DBWRealGroup`) verbatim, generalized away from
`K = ℝ`. -/
noncomputable def DBWSubgroup : Subgroup (BW K) where
  carrier := DBW K
  one_mem' := DBW.one_mem
  mul_mem' hx hy := DBW_mulClosed K _ _ hx hy
  inv_mem' hx := DBW.inv_mem hx

end Subgroup

/-! ### Deliverable 4: compatibility with the `K = ℝ` precedent -/

/-- **Compatibility**: the general construction specializes to `DBWRealSubgroup` at `K = ℝ`.
Both subgroups are built from the identical carrier `DBW ℝ`; the closure fields (`one_mem'`,
`mul_mem'`, `inv_mem'`) are propositions, hence equal by proof irrelevance, so the two
`Subgroup`-bundles coincide definitionally. -/
theorem DBWSubgroup_real_eq : DBWSubgroup ℝ = DBWRealSubgroup := rfl

end Superfusion
