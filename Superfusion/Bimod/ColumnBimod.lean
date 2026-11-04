/-
Superfusion / Bimod / ColumnBimod

Milestone M8a-6a: **the graded column bimodule**.  For a superalgebra
`D` and a parity function `γ : n → ZMod 2`, the column space `n → D`
carries

* the left action of the matrix superalgebra `M_γ(D)`
  (mathlib's `mulVec` module structure),
* the right action of `D` (entrywise, the `Pi` module over `Dᵐᵒᵖ`),
* the **column grading**: `v` is homogeneous of degree `i` iff
  `v k ∈ 𝒟 (i + γ k)` for all `k` (entrywise masks, the
  `matrixGradingA` pattern),

and the two actions are graded and strictly commute — the column space
is a super `(M_γ(D), D)`-bimodule in the sense of M8a-1
(`columnActionHom` certifies the full package).  This is the paper's
column bimodule `C_{a,b} = K^{p|q} ⊗ D_{a+b}` (§4.1) with the left
action *before* transport along the table isomorphism `φ_{a,b}`;
irreducibility is the next milestone.
-/
import Superfusion.Bimod.Basic
import Superfusion.Super.MatrixSuperCoeff
import Mathlib.LinearAlgebra.Matrix.Action
import Superfusion.Bimod.GradedModule

namespace Superfusion

namespace Bimod

variable {K : Type*} [CommRing K]
variable {D : Type*} [Ring D] [Algebra K D]
variable {n : Type*}
variable (γ : n → ZMod 2) (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒟]

private theorem zmod2_col_cancel :
    ∀ i i' c : ZMod 2, i ≠ i' → i + c ≠ i' + c := by decide

private theorem zmod2_col_mul :
    ∀ i j x z : ZMod 2, (i + x + z) + (j + z) = (i + j) + x := by
  decide +revert

private theorem zmod2_col_right :
    ∀ i j x : ZMod 2, (j + x) + i = (i + j) + x := by decide +revert

/-! ### The column grading -/

/-- The column grading on `n → D`: degree-`i` vectors have their `k`
component in `𝒟 (i + γ k)`. -/
def columnGrading (i : ZMod 2) : Submodule K (n → D) where
  carrier := {v | ∀ k, v k ∈ 𝒟 (i + γ k)}
  zero_mem' _ := zero_mem _
  add_mem' {u v} hu hv k := by
    rw [Pi.add_apply]
    exact add_mem (hu k) (hv k)
  smul_mem' c v hv k := by
    rw [Pi.smul_apply]
    exact Submodule.smul_mem _ _ (hv k)

omit [GradedAlgebra 𝒟] in
theorem mem_columnGrading {i : ZMod 2} {v : n → D} :
    v ∈ columnGrading γ 𝒟 i ↔ ∀ k, v k ∈ 𝒟 (i + γ k) :=
  Iff.rfl

omit [GradedAlgebra 𝒟] in
/-- Homogeneous single-entry columns. -/
theorem single_mem_columnGrading [DecidableEq n] {i : ZMod 2} {j : n} {d : D}
    (hd : d ∈ 𝒟 (i + γ j)) : Pi.single j d ∈ columnGrading γ 𝒟 i := by
  intro k
  rcases eq_or_ne k j with hk | hk
  · subst hk
    rw [Pi.single_eq_same]
    exact hd
  · rw [Pi.single_eq_of_ne hk]
    exact zero_mem _

/-! ### Masks and the decomposition -/

/-- The degree-`i` mask: project every component onto its relevant
graded piece. -/
noncomputable def colMask (i : ZMod 2) : (n → D) →ₗ[K] (n → D) where
  toFun v := fun k => modProj 𝒟 (i + γ k) (v k)
  map_add' u v := funext fun k => by
    show modProj 𝒟 (i + γ k) ((u + v) k) = _
    rw [Pi.add_apply, map_add]
    rfl
  map_smul' c v := funext fun k => by
    show modProj 𝒟 (i + γ k) ((c • v) k) = _
    rw [Pi.smul_apply, map_smul]
    rfl

theorem colMask_apply (i : ZMod 2) (v : n → D) (k : n) :
    colMask γ 𝒟 i v k = modProj 𝒟 (i + γ k) (v k) := rfl

theorem colMask_mem (i : ZMod 2) (v : n → D) :
    colMask γ 𝒟 i v ∈ columnGrading γ 𝒟 i := fun k =>
  modProj_mem 𝒟 (i + γ k) (v k)

theorem colMask_of_mem {i : ZMod 2} {v : n → D}
    (hv : v ∈ columnGrading γ 𝒟 i) : colMask γ 𝒟 i v = v :=
  funext fun k => modProj_of_mem 𝒟 (hv k)

theorem colMask_of_mem_ne {i i' : ZMod 2} {v : n → D}
    (hv : v ∈ columnGrading γ 𝒟 i) (hii' : i ≠ i') :
    colMask γ 𝒟 i' v = 0 :=
  funext fun k =>
    modProj_of_mem_ne 𝒟 (hv k) (zmod2_col_cancel i i' (γ k) hii')

theorem colMask_zero_add_colMask_one (v : n → D) :
    colMask γ 𝒟 0 v + colMask γ 𝒟 1 v = v := by
  funext k
  rw [Pi.add_apply, colMask_apply, colMask_apply]
  rcases zmod2_cases (γ k) with hk | hk <;> rw [hk]
  · rw [show (0 : ZMod 2) + 0 = 0 from by decide,
      show (1 : ZMod 2) + 0 = 1 from by decide,
      modProj_zero_add_modProj_one]
  · rw [show (0 : ZMod 2) + 1 = 1 from by decide,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_comm,
      modProj_zero_add_modProj_one]

/-- The degree-`i` mask, corestricted to the layer. -/
noncomputable def colMaskInto (i : ZMod 2) :
    (n → D) →ₗ[K] columnGrading γ 𝒟 i :=
  LinearMap.codRestrict (columnGrading γ 𝒟 i) (colMask γ 𝒟 i)
    (colMask_mem γ 𝒟 i)

/-- **The column space of a superalgebra is decomposed.** -/
noncomputable instance : DirectSum.Decomposition (columnGrading γ 𝒟) where
  decompose' v :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(columnGrading γ 𝒟 i)) 0
        (colMaskInto γ 𝒟 0 v)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(columnGrading γ 𝒟 i)) 1
        (colMaskInto γ 𝒟 1 v)
  left_inv v := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact colMask_zero_add_colMask_one γ 𝒟 v
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        rw [map_zero]
        beta_reduce
        rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | of i b =>
        rcases zmod2_cases i with hi | hi <;> subst hi
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : colMaskInto γ 𝒟 0 (b : n → D) = b :=
            Subtype.ext (colMask_of_mem γ 𝒟 b.2)
          have h2 : colMaskInto γ 𝒟 1 (b : n → D) = 0 :=
            Subtype.ext (colMask_of_mem_ne γ 𝒟 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : colMaskInto γ 𝒟 0 (b : n → D) = 0 :=
            Subtype.ext (colMask_of_mem_ne γ 𝒟 b.2 (by decide))
          have h2 : colMaskInto γ 𝒟 1 (b : n → D) = b :=
            Subtype.ext (colMask_of_mem γ 𝒟 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-! ### The two actions are graded -/

variable [Fintype n] [DecidableEq n]

/-- The left action of the matrix superalgebra on the column space is
graded. -/
instance : SetLike.GradedSMul (matrixGradingA γ 𝒟) (columnGrading γ 𝒟) where
  smul_mem {i j} X v hX hv := by
    rw [vadd_eq_add]
    intro k
    rw [show (X • v) k = Finset.sum Finset.univ fun l => X k l * v l from by
      rw [Matrix.smul_eq_mulVec]
      simp only [Matrix.mulVec, dotProduct]]
    refine Submodule.sum_mem _ fun l _ => ?_
    have h := SetLike.mul_mem_graded (hX k l) (hv l)
    rwa [zmod2_col_mul] at h

/-- The graded left action, as a directly applicable lemma (for
transport to type synonyms without instance search). -/
theorem columnGrading_smul_mem {i j : ZMod 2} {X : Matrix n n D}
    {v : n → D} (hX : X ∈ matrixGradingA γ 𝒟 i)
    (hv : v ∈ columnGrading γ 𝒟 j) :
    X • v ∈ columnGrading γ 𝒟 (i + j) := by
  have h := SetLike.GradedSMul.smul_mem hX hv
  rwa [vadd_eq_add] at h

/-- The right action of the coefficients on the column space is
graded. -/
instance : GradedRightSMul 𝒟 (columnGrading γ 𝒟) where
  smul_mem {i j} d v hd hv := by
    intro k
    rw [show (MulOpposite.op d • v) k = v k * d from rfl]
    have h := SetLike.mul_mem_graded (hv k) hd
    rwa [zmod2_col_right] at h

/-! ### The super-bimodule package -/

/-- **The column space is a super `(M_γ(D), D)`-bimodule**: the two
graded actions assemble into the enveloping-algebra action of M8a-1.
(The instantiation certifies that the whole unbundled package —
actions, strict commutation, towers, gradings — is in place.) -/
noncomputable def columnActionHom :
    Envelope (matrixGradingA γ 𝒟) 𝒟 →ₐ[K] Module.End K (n → D) :=
  actionHom (matrixGradingA γ 𝒟) 𝒟 (columnGrading γ 𝒟)

end Bimod

end Superfusion
