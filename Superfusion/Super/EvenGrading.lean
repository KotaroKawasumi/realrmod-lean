/-
Superfusion / Super / EvenGrading

The purely even grading on an ordinary algebra: `𝒜 0 = ⊤`, `𝒜 1 = ⊥`.
This is the underlying construction of the paper's purely even embedding
`Br(K) → BW(K)` (§2.1, §8), and it doubles as a sanity anchor for the
supercenter: for the even grading, the supercenter coincides with the
ordinary center (`superCenter_evenGrading`), so our Koszul-sign definitions
degenerate correctly on ungraded algebras.
-/
import Superfusion.Super.Basic

namespace Superfusion

variable (K : Type*) [CommRing K] (A : Type*) [Ring A] [Algebra K A]

/-- The purely even grading: everything in degree `0`. -/
def evenGrading : ZMod 2 → Submodule K A := fun i => if i = 0 then ⊤ else ⊥

@[simp] theorem evenGrading_zero : evenGrading K A 0 = ⊤ := rfl

@[simp] theorem evenGrading_one : evenGrading K A 1 = ⊥ := rfl

theorem mem_evenGrading_zero (a : A) : a ∈ evenGrading K A 0 :=
  Submodule.mem_top

instance : GradedAlgebra (evenGrading K A) where
  one_mem := Submodule.mem_top
  mul_mem {i j} a b ha hb := by
    rcases zmod2_cases i with hi | hi <;> rcases zmod2_cases j with hj | hj <;>
      subst hi <;> subst hj <;>
      simp_all [evenGrading, Submodule.mem_bot]
  decompose' := fun a =>
    DirectSum.of (fun i => evenGrading K A i) 0 ⟨a, mem_evenGrading_zero K A a⟩
  left_inv a := by rw [DirectSum.coeAddMonoidHom_of]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        exact map_zero _
    | of i b =>
        rcases zmod2_cases i with hi | hi <;> subst hi
        · rw [DirectSum.coeAddMonoidHom_of]
        · have hb : b = 0 := Subtype.ext ((Submodule.mem_bot K).mp b.2)
          subst hb
          rw [map_zero, map_zero]
          exact map_zero _
    | add x y hx hy =>
        beta_reduce
        have hxy :
            (⟨(DirectSum.coeAddMonoidHom (evenGrading K A)) x
                + (DirectSum.coeAddMonoidHom (evenGrading K A)) y,
              mem_evenGrading_zero K A _⟩ : ↥(evenGrading K A 0)) =
            ⟨_, mem_evenGrading_zero K A
                ((DirectSum.coeAddMonoidHom (evenGrading K A)) x)⟩
              + ⟨_, mem_evenGrading_zero K A
                ((DirectSum.coeAddMonoidHom (evenGrading K A)) y)⟩ := rfl
        rw [map_add, hxy, map_add]
        exact congrArg₂ (· + ·) hx hy

/-- For the purely even grading the supercenter is the ordinary center:
the Koszul-sign definitions degenerate correctly on ungraded algebras. -/
theorem superCenter_evenGrading :
    superCenter (evenGrading K A) =
      Subalgebra.toSubmodule (Subalgebra.center K A) := by
  apply le_antisymm
  · rw [superCenter, sup_le_iff]
    constructor
    · rintro a ⟨-, ha⟩
      rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
      intro b
      have := ha 0 b (mem_evenGrading_zero K A b)
      simpa using this.symm
    · rintro a ⟨ha, -⟩
      rw [evenGrading_one, Submodule.mem_bot] at ha
      subst ha
      exact Submodule.zero_mem _
  · intro a ha
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff] at ha
    refine le_sup_left (α := Submodule K A) ?_
    refine ⟨mem_evenGrading_zero K A a, fun j b hb => ?_⟩
    rcases zmod2_cases j with hj | hj <;> subst hj
    · simpa using (ha b).symm
    · rw [evenGrading_one, Submodule.mem_bot] at hb
      subst hb
      simp

end Superfusion
