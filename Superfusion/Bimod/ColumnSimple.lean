/-
Superfusion / Bimod / ColumnSimple

Milestone M8a-6b: **irreducibility of the column bimodule** (§4.1:
"It is irreducible").  Over a *super division algebra* — a superalgebra
whose nonzero homogeneous elements are units — the column bimodule has
no homogeneous sub-bimodules besides `⊥` and `⊤`:

given a nonzero homogeneous sub-bimodule element `w`, some component
`w k₀` is a nonzero homogeneous element of `D`, hence a unit; acting on
the right by its inverse normalizes that component to `1`, and then a
single matrix (the target column placed in column `k₀`) reaches any
vector.  The Koszul sign never enters: the argument uses only the
sign-free actions.

The super-division predicate `IsSuperDivision` is project-local (no
such notion exists in mathlib or the parent track); the standard tower
fibers `D_a` satisfy it — that instantiation belongs to the `B_L`
milestones.
-/
import Superfusion.Bimod.ColumnBimod

namespace Superfusion

namespace Bimod

variable {K : Type*} [CommRing K]
variable {D : Type*} [Ring D] [Algebra K D]

/-- A superalgebra is a **super division algebra** if every nonzero
homogeneous element is a unit (§2.1). -/
def IsSuperDivision (𝒟 : ZMod 2 → Submodule K D) : Prop :=
  ∀ ⦃i : ZMod 2⦄ ⦃x : D⦄, x ∈ 𝒟 i → x ≠ 0 → IsUnit x

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (γ : n → ZMod 2) (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]

/-- Any column with an invertible entry generates everything: the
matrix with the target column placed in column `k₀` maps it there. -/
private theorem column_reach {w : n → D} {k₀ : n} (hw : w k₀ = 1)
    (z : n → D) :
    (Matrix.of fun j k => if k = k₀ then z j else 0) • w = z := by
  funext j
  rw [Matrix.smul_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [show (fun k => (if k = k₀ then z j else 0) * w k)
      = fun k => if k = k₀ then z j * w k else 0 from by
      funext k
      by_cases hk : k = k₀ <;> simp [hk]]
  rw [Finset.sum_ite_eq' Finset.univ k₀ (fun k => z j * w k)]
  simp [hw]

/-- **The column bimodule is irreducible** over a super division
algebra: a homogeneous submodule of the column space stable under the
left matrix action and the right coefficient action is `⊥` or `⊤`. -/
theorem columnBimodule_irreducible (hdiv : IsSuperDivision 𝒟)
    (p : Submodule K (n → D))
    (hL : ∀ (X : Matrix n n D), ∀ v ∈ p, X • v ∈ p)
    (hR : ∀ (d : D), ∀ v ∈ p, MulOpposite.op d • v ∈ p)
    (hHom : p.IsHomogeneous (columnGrading γ 𝒟)) :
    p = ⊥ ∨ p = ⊤ := by
  by_cases hp : p = ⊥
  · exact Or.inl hp
  refine Or.inr ?_
  -- a nonzero element, then a nonzero homogeneous element
  obtain ⟨v, hvp, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hcomp : ∃ i : ZMod 2, modProj (columnGrading γ 𝒟) i v ≠ 0 := by
    by_contra h
    push Not at h
    refine hv ?_
    rw [← modProj_zero_add_modProj_one (columnGrading γ 𝒟) v, h 0, h 1,
      add_zero]
  obtain ⟨i, hwi⟩ := hcomp
  set w := modProj (columnGrading γ 𝒟) i v with hw
  have hwp : w ∈ p := by
    rw [hw, modProj_apply]
    exact hHom i hvp
  have hwmem : w ∈ columnGrading γ 𝒟 i :=
    modProj_mem (columnGrading γ 𝒟) i v
  -- a nonzero component, hence a homogeneous unit
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, w k₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hwi (funext h)
  obtain ⟨u, hu⟩ := hdiv (hwmem k₀) hk₀
  -- normalize the component to 1 by the right action
  set w' := MulOpposite.op ((u⁻¹ : Dˣ) : D) • w with hw'
  have hw'p : w' ∈ p := hR _ w hwp
  have hw'k₀ : w' k₀ = 1 := by
    rw [hw']
    show w k₀ * ((u⁻¹ : Dˣ) : D) = 1
    rw [← hu]
    exact u.mul_inv
  -- reach any vector by one matrix
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  rw [← column_reach hw'k₀ z]
  exact hL _ w' hw'p

end Bimod

end Superfusion
