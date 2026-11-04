/-
Superfusion / Super / GradedEnd

Milestone M7f-1e: **the endomorphism algebra of a graded algebra is a
graded algebra** —

  `endGrading 𝒜 i = {f : End K A | ∀ j, f (𝒜 j) ⊆ 𝒜 (j + i)}`,

with the `GradedAlgebra` instance built from the mask projections
`f ↦ proj_{j+i} ∘ f ∘ proj_j` (the `EvenGrading`/`TensorGrading`
pattern; no finiteness needed since the index is `ZMod 2`).

The Wall map `superMulLeftRight : A ᵍ⊗ Aˢᵒᵖ → End K A` is a map of
*graded* algebras for this grading (M7f-2), and the graded
`End(A) ᵍ⊗ End(B) → End(A ⊗ B)` (M7f-1f) has this as its target
grading — together these make the Wall-map factorization
(super-Azumaya `ᵍ⊗`-closure) expressible.
-/
import Superfusion.Super.TensorGrading

namespace Superfusion

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

private theorem zmod2_end_one : ∀ i i' : ZMod 2, i ≠ i' → 1 + i ≠ 1 + i' := by
  decide

private theorem zmod2_end_mul : ∀ k j i : ZMod 2,
    (k + j) + i = k + (i + j) := by
  decide

/-! ### The grading -/

/-- The parity grading on the endomorphism algebra: degree `i` maps
shift every grade by `i`. -/
def endGrading (i : ZMod 2) : Submodule K (Module.End K A) where
  carrier := {f | ∀ (j : ZMod 2), ∀ x ∈ 𝒜 j, f x ∈ 𝒜 (j + i)}
  zero_mem' := fun j x _ => by
    rw [LinearMap.zero_apply]
    exact zero_mem _
  add_mem' {f g} hf hg := fun j x hx => by
    rw [LinearMap.add_apply]
    exact add_mem (hf j x hx) (hg j x hx)
  smul_mem' c f hf := fun j x hx => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (hf j x hx)

omit [GradedAlgebra 𝒜] in
theorem mem_endGrading {i : ZMod 2} {f : Module.End K A} :
    f ∈ endGrading 𝒜 i ↔ ∀ (j : ZMod 2), ∀ x ∈ 𝒜 j, f x ∈ 𝒜 (j + i) :=
  Iff.rfl

/-! ### Masks and the decomposition -/

/-- The degree-`i` mask on endomorphisms:
`f ↦ proj_i ∘ f ∘ proj_0 + proj_{1+i} ∘ f ∘ proj_1`. -/
noncomputable def endMask (i : ZMod 2) :
    Module.End K A →ₗ[K] Module.End K A where
  toFun f := gradeProj 𝒜 (0 + i) ∘ₗ f ∘ₗ gradeProj 𝒜 0
    + gradeProj 𝒜 (1 + i) ∘ₗ f ∘ₗ gradeProj 𝒜 1
  map_add' f g := by
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' c f := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp,
      RingHom.id_apply, smul_add]

theorem endMask_apply (i : ZMod 2) (f : Module.End K A) (x : A) :
    endMask 𝒜 i f x
      = gradeProj 𝒜 (0 + i) (f (gradeProj 𝒜 0 x))
        + gradeProj 𝒜 (1 + i) (f (gradeProj 𝒜 1 x)) := rfl

theorem endMask_mem (i : ZMod 2) (f : Module.End K A) :
    endMask 𝒜 i f ∈ endGrading 𝒜 i := by
  intro j x hx
  rw [endMask_apply]
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [gradeProj_of_mem 𝒜 hx, gradeProj_of_mem_ne 𝒜 hx (by decide),
      map_zero, map_zero, add_zero]
    exact gradeProj_mem 𝒜 (0 + i) _
  · rw [gradeProj_of_mem 𝒜 hx, gradeProj_of_mem_ne 𝒜 hx (by decide),
      map_zero, map_zero, zero_add]
    exact gradeProj_mem 𝒜 (1 + i) _

theorem endMask_of_mem {i : ZMod 2} {f : Module.End K A}
    (hf : f ∈ endGrading 𝒜 i) : endMask 𝒜 i f = f := by
  refine LinearMap.ext fun x => ?_
  rw [endMask_apply]
  conv_rhs => rw [← gradeProj_zero_add_gradeProj_one 𝒜 x, map_add]
  rw [gradeProj_of_mem 𝒜 (hf 0 _ (gradeProj_mem 𝒜 0 x)),
    gradeProj_of_mem 𝒜 (hf 1 _ (gradeProj_mem 𝒜 1 x))]

theorem endMask_of_mem_ne {i i' : ZMod 2} {f : Module.End K A}
    (hf : f ∈ endGrading 𝒜 i) (hii' : i ≠ i') :
    endMask 𝒜 i' f = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [endMask_apply,
    gradeProj_of_mem_ne 𝒜 (hf 0 _ (gradeProj_mem 𝒜 0 x))
      (fun h => hii' (by rwa [zero_add, zero_add] at h)),
    gradeProj_of_mem_ne 𝒜 (hf 1 _ (gradeProj_mem 𝒜 1 x))
      (zmod2_end_one i i' hii'),
    add_zero, LinearMap.zero_apply]

theorem endMask_zero_add_endMask_one (f : Module.End K A) :
    endMask 𝒜 0 f + endMask 𝒜 1 f = f := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.add_apply, endMask_apply, endMask_apply]
  rw [show (0 : ZMod 2) + 0 = 0 from by decide,
    show (1 : ZMod 2) + 0 = 1 from by decide,
    show (0 : ZMod 2) + 1 = 1 from by decide,
    show (1 : ZMod 2) + 1 = 0 from by decide]
  rw [add_add_add_comm, gradeProj_zero_add_gradeProj_one,
    add_comm (gradeProj 𝒜 1 (f (gradeProj 𝒜 1 x))) (gradeProj 𝒜 0 (f (gradeProj 𝒜 1 x))),
    gradeProj_zero_add_gradeProj_one, ← map_add,
    gradeProj_zero_add_gradeProj_one]

/-- The degree-`i` mask, corestricted to the layer. -/
noncomputable def endMaskInto (i : ZMod 2) :
    Module.End K A →ₗ[K] endGrading 𝒜 i :=
  LinearMap.codRestrict (endGrading 𝒜 i) (endMask 𝒜 i)
    (endMask_mem 𝒜 i)

noncomputable instance : DirectSum.Decomposition (endGrading 𝒜) where
  decompose' f :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(endGrading 𝒜 i)) 0
        (endMaskInto 𝒜 0 f)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(endGrading 𝒜 i)) 1
        (endMaskInto 𝒜 1 f)
  left_inv f := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact endMask_zero_add_endMask_one 𝒜 f
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
          have h1 : endMaskInto 𝒜 0 (b : Module.End K A) = b :=
            Subtype.ext (endMask_of_mem 𝒜 b.2)
          have h2 : endMaskInto 𝒜 1 (b : Module.End K A) = 0 :=
            Subtype.ext (endMask_of_mem_ne 𝒜 b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : endMaskInto 𝒜 0 (b : Module.End K A) = 0 :=
            Subtype.ext (endMask_of_mem_ne 𝒜 b.2 (by decide))
          have h2 : endMaskInto 𝒜 1 (b : Module.End K A) = b :=
            Subtype.ext (endMask_of_mem 𝒜 b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-! ### The graded monoid structure -/

instance : SetLike.GradedMonoid (endGrading 𝒜) where
  one_mem := fun j x hx => by
    rw [show ((1 : Module.End K A) x) = x from rfl]
    rwa [show j + (0 : ZMod 2) = j from by rw [add_zero]]
  mul_mem {i j} f g hf hg := fun k x hx => by
    rw [show ((f * g) x) = f (g x) from rfl]
    have h := hf (k + j) (g x) (hg k x hx)
    rwa [zmod2_end_mul] at h

/-- **The endomorphism algebra of a graded algebra is a graded
algebra** (M7f-1e): degree-`i` endomorphisms shift every grade by
`i`. -/
noncomputable instance endGradedAlgebra :
    GradedAlgebra (endGrading 𝒜) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

/-! ### Basic membership API -/

theorem lmul_mem_endGrading {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    Algebra.lmul K A a ∈ endGrading 𝒜 i := by
  intro j x hx
  rw [show (Algebra.lmul K A a) x = a * x from rfl]
  have h := SetLike.mul_mem_graded ha hx
  rwa [show i + j = j + i from by rw [add_comm]] at h

end Superfusion
