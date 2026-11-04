/-
Superfusion / Super / OddDouble

Milestone M7c-1: the **odd-double induction step**.

Given a superalgebra `(A, 𝒜)` and `ε : K`, the odd double
`OddDouble 𝒜 ε = A ⊕ A·g` adjoins an odd element `g` with

  `g² = ε`,   `g a g⁻¹ = J a`  (the parity involution),

realized explicitly on `A × A` with multiplication
  `(a, b)(c, d) = (a c + ε (b · Jd), a d + b · Jc)`.
This is the explicit model of the graded tensor product
`A ᵍ⊗ D_ε` (`D_ε = AdjoinOdd ε` from M7a); the identification with
mathlib's `GradedTensorProduct` is M7c-2.

Main results:

* `OddDouble` is a superalgebra (grading `(OddDouble)ᵢ = 𝒜ᵢ × 𝒜ᵢ₊₁`);
* **central simplicity is preserved** (field base, `2` invertible,
  `ε ≠ 0`): `isSuperCentral`, `isGradedSimple`, `isSuperAzumaya`.

Iterating from `K` builds the standard super division algebras `D_n`
(`n ∈ ℤ/8` over `ℝ`), the Clifford algebras of diagonal quadratic
forms — without ever needing tensor-product simplicity, associativity
of `ᵍ⊗`, or a Clifford basis.

The proofs are coordinate versions of the M4 arguments: for graded
simplicity, the combinations `x·g ∓ g·x` isolate the two coordinates of
a homogeneous ideal element (the `J`-conjugation trick), reducing to
graded simplicity of `A`; for supercentrality, testing against `A ⊕ 0`
reduces to the supercenter of `A`, and testing against `g` kills the
remaining coefficient.
-/
import Superfusion.Super.WallProof
import Superfusion.Super.ParityInvolution

namespace Superfusion

section CommRingBase

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]

/-- `A ⊕ A·g` with `g` odd, `g² = ε` and `g a g⁻¹ = J a`: the explicit
model of `A ᵍ⊗ D_ε`. -/
@[nolint unusedArguments]
def OddDouble (𝒜 : ZMod 2 → Submodule K A) (ε : K) : Type _ :=
  letI := 𝒜; letI := ε; A × A

namespace OddDouble

variable (𝒜 : ZMod 2 → Submodule K A) (ε : K)

instance : AddCommGroup (OddDouble 𝒜 ε) := inferInstanceAs (AddCommGroup (A × A))

instance : Module K (OddDouble 𝒜 ε) := inferInstanceAs (Module K (A × A))

instance [Nontrivial A] : Nontrivial (OddDouble 𝒜 ε) :=
  inferInstanceAs (Nontrivial (A × A))

instance [Module.Finite K A] : Module.Finite K (OddDouble 𝒜 ε) :=
  inferInstanceAs (Module.Finite K (A × A))

/-- The element `a + b·g`. -/
def mk (a b : A) : OddDouble 𝒜 ε := ((a, b) : A × A)

/-- The coefficient of `1`. -/
def p1 : OddDouble 𝒜 ε →ₗ[K] A := LinearMap.fst K A A

/-- The coefficient of `g`. -/
def p2 : OddDouble 𝒜 ε →ₗ[K] A := LinearMap.snd K A A

@[simp] theorem p1_mk (a b : A) : p1 𝒜 ε (mk 𝒜 ε a b) = a := rfl

@[simp] theorem p2_mk (a b : A) : p2 𝒜 ε (mk 𝒜 ε a b) = b := rfl

theorem ext {x y : OddDouble 𝒜 ε} (h1 : p1 𝒜 ε x = p1 𝒜 ε y)
    (h2 : p2 𝒜 ε x = p2 𝒜 ε y) : x = y :=
  Prod.ext h1 h2

theorem mk_p1_p2 (x : OddDouble 𝒜 ε) : mk 𝒜 ε (p1 𝒜 ε x) (p2 𝒜 ε x) = x := rfl

instance : One (OddDouble 𝒜 ε) := ⟨mk 𝒜 ε 1 0⟩

@[simp] theorem p1_one : p1 𝒜 ε (1 : OddDouble 𝒜 ε) = 1 := rfl

@[simp] theorem p2_one : p2 𝒜 ε (1 : OddDouble 𝒜 ε) = 0 := rfl

/-- The adjoined odd generator. -/
def gen : OddDouble 𝒜 ε := mk 𝒜 ε 0 1

@[simp] theorem p1_gen : p1 𝒜 ε (gen 𝒜 ε) = 0 := rfl

@[simp] theorem p2_gen : p2 𝒜 ε (gen 𝒜 ε) = 1 := rfl

variable [GradedAlgebra 𝒜]

noncomputable instance : Mul (OddDouble 𝒜 ε) :=
  ⟨fun x y => mk 𝒜 ε
    (p1 𝒜 ε x * p1 𝒜 ε y + ε • (p2 𝒜 ε x * parityMap 𝒜 (p2 𝒜 ε y)))
    (p1 𝒜 ε x * p2 𝒜 ε y + p2 𝒜 ε x * parityMap 𝒜 (p1 𝒜 ε y))⟩

@[simp] theorem p1_mul (x y : OddDouble 𝒜 ε) :
    p1 𝒜 ε (x * y) =
      p1 𝒜 ε x * p1 𝒜 ε y + ε • (p2 𝒜 ε x * parityMap 𝒜 (p2 𝒜 ε y)) := rfl

@[simp] theorem p2_mul (x y : OddDouble 𝒜 ε) :
    p2 𝒜 ε (x * y) =
      p1 𝒜 ε x * p2 𝒜 ε y + p2 𝒜 ε x * parityMap 𝒜 (p1 𝒜 ε y) := rfl

theorem mk_mul_mk (a b c d : A) :
    mk 𝒜 ε a b * mk 𝒜 ε c d =
      mk 𝒜 ε (a * c + ε • (b * parityMap 𝒜 d))
        (a * d + b * parityMap 𝒜 c) :=
  ext 𝒜 ε (by simp) (by simp)

noncomputable instance instMonoid : Monoid (OddDouble 𝒜 ε) where
  one_mul x := ext 𝒜 ε (by simp) (by simp)
  mul_one x := ext 𝒜 ε (by simp) (by simp [parityMap_one])
  mul_assoc x y z :=
    ext 𝒜 ε
      (by
        simp only [p1_mul, p2_mul, map_add, parityMap_mul,
          parityMap_parityMap, mul_add, add_mul, smul_add, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel)
      (by
        simp only [p1_mul, p2_mul, map_add, map_smul, parityMap_mul,
          parityMap_parityMap, mul_add, add_mul, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel)

noncomputable instance instRing : Ring (OddDouble 𝒜 ε) where
  left_distrib x y z :=
    ext 𝒜 ε
      (by simp only [p1_mul, map_add, mul_add, smul_add]; abel)
      (by simp only [p2_mul, map_add, mul_add]; abel)
  right_distrib x y z :=
    ext 𝒜 ε
      (by simp only [p1_mul, map_add, add_mul, smul_add]; abel)
      (by simp only [p2_mul, map_add, add_mul]; abel)
  zero_mul x := ext 𝒜 ε (by simp) (by simp)
  mul_zero x := ext 𝒜 ε (by simp) (by simp)

/-- The scalar inclusion `K →+* OddDouble 𝒜 ε`. -/
noncomputable def algebraMapAux : K →+* OddDouble 𝒜 ε where
  toFun r := mk 𝒜 ε (algebraMap K A r) 0
  map_one' := ext 𝒜 ε (by simp) (by simp)
  map_mul' r s := ext 𝒜 ε (by simp) (by simp)
  map_zero' := ext 𝒜 ε (by simp) (by simp)
  map_add' r s := ext 𝒜 ε (by simp) (by simp)

noncomputable instance instAlgebra : Algebra K (OddDouble 𝒜 ε) where
  algebraMap := algebraMapAux 𝒜 ε
  commutes' r x :=
    ext 𝒜 ε
      (by simp [algebraMapAux, ← Algebra.commutes r (p1 𝒜 ε x)])
      (by simp [algebraMapAux, parityMap_algebraMap,
        ← Algebra.commutes r (p2 𝒜 ε x)])
  smul_def' r x :=
    ext 𝒜 ε
      (by simp [algebraMapAux, Algebra.smul_def])
      (by simp [algebraMapAux, Algebra.smul_def])

@[simp] theorem p1_algebraMap (r : K) :
    p1 𝒜 ε (algebraMap K (OddDouble 𝒜 ε) r) = algebraMap K A r := rfl

@[simp] theorem p2_algebraMap (r : K) :
    p2 𝒜 ε (algebraMap K (OddDouble 𝒜 ε) r) = 0 := rfl

/-- The defining relation `g² = ε`. -/
theorem gen_mul_gen : gen 𝒜 ε * gen 𝒜 ε = algebraMap K (OddDouble 𝒜 ε) ε :=
  ext 𝒜 ε (by simp [parityMap_one, Algebra.algebraMap_eq_smul_one]) (by simp)

/-! ### The grading -/

/-- The grading `(OddDouble 𝒜 ε)ᵢ = 𝒜ᵢ × 𝒜ᵢ₊₁`. -/
def grading : ZMod 2 → Submodule K (OddDouble 𝒜 ε) := fun i =>
  (𝒜 i).prod (𝒜 (i + 1))

theorem mem_grading {i : ZMod 2} {x : OddDouble 𝒜 ε} :
    x ∈ grading 𝒜 ε i ↔ p1 𝒜 ε x ∈ 𝒜 i ∧ p2 𝒜 ε x ∈ 𝒜 (i + 1) :=
  Iff.rfl

theorem mk_mem_grading {i : ZMod 2} {a b : A} (ha : a ∈ 𝒜 i)
    (hb : b ∈ 𝒜 (i + 1)) : mk 𝒜 ε a b ∈ grading 𝒜 ε i :=
  (mem_grading 𝒜 ε).mpr ⟨ha, hb⟩

theorem gen_mem_grading : gen 𝒜 ε ∈ grading 𝒜 ε 1 :=
  (mem_grading 𝒜 ε).mpr ⟨zero_mem _, SetLike.one_mem_graded 𝒜⟩

private theorem idx1 : ∀ i j : ZMod 2, i + 1 + (j + 1) = i + j := by decide

private theorem idx2 : ∀ i j : ZMod 2, i + (j + 1) = i + j + 1 := by decide

private theorem idx3 : ∀ i j : ZMod 2, i + 1 + j = i + j + 1 := by decide

instance : SetLike.GradedMonoid (grading 𝒜 ε) where
  one_mem := (mem_grading 𝒜 ε).mpr
    ⟨SetLike.one_mem_graded 𝒜, zero_mem _⟩
  mul_mem {i j} x y hx hy := by
    obtain ⟨hx1, hx2⟩ := (mem_grading 𝒜 ε).mp hx
    obtain ⟨hy1, hy2⟩ := (mem_grading 𝒜 ε).mp hy
    refine (mem_grading 𝒜 ε).mpr ⟨?_, ?_⟩
    · rw [p1_mul]
      refine add_mem (SetLike.mul_mem_graded hx1 hy1)
        (Submodule.smul_mem _ _ ?_)
      have h := SetLike.mul_mem_graded hx2 (parityMap_mem 𝒜 hy2)
      rwa [idx1] at h
    · rw [p2_mul]
      refine add_mem ?_ ?_
      · have h := SetLike.mul_mem_graded hx1 hy2
        rwa [idx2] at h
      · have h := SetLike.mul_mem_graded hx2 (parityMap_mem 𝒜 hy1)
        rwa [idx3] at h

/-- The pair `(a, b)` as an element of the odd double, `K`-linearly. -/
def ofPair : (A × A) ≃ₗ[K] OddDouble 𝒜 ε := LinearEquiv.refl K (A × A)

/-- Projection onto the even layer. -/
noncomputable def evenInto : OddDouble 𝒜 ε →ₗ[K] grading 𝒜 ε 0 :=
  LinearMap.codRestrict (grading 𝒜 ε 0)
    ((ofPair 𝒜 ε).toLinearMap.comp
      (((evenPart 𝒜).comp (p1 𝒜 ε)).prod ((oddPart 𝒜).comp (p2 𝒜 ε))))
    fun _ => (mem_grading 𝒜 ε).mpr ⟨evenPart_mem 𝒜 _, oddPart_mem 𝒜 _⟩

/-- Projection onto the odd layer. -/
noncomputable def oddInto : OddDouble 𝒜 ε →ₗ[K] grading 𝒜 ε 1 :=
  LinearMap.codRestrict (grading 𝒜 ε 1)
    ((ofPair 𝒜 ε).toLinearMap.comp
      (((oddPart 𝒜).comp (p1 𝒜 ε)).prod ((evenPart 𝒜).comp (p2 𝒜 ε))))
    fun _ => (mem_grading 𝒜 ε).mpr ⟨oddPart_mem 𝒜 _, evenPart_mem 𝒜 _⟩

@[simp] theorem evenInto_coe (x : OddDouble 𝒜 ε) :
    (evenInto 𝒜 ε x : OddDouble 𝒜 ε) =
      mk 𝒜 ε (evenPart 𝒜 (p1 𝒜 ε x)) (oddPart 𝒜 (p2 𝒜 ε x)) := rfl

@[simp] theorem oddInto_coe (x : OddDouble 𝒜 ε) :
    (oddInto 𝒜 ε x : OddDouble 𝒜 ε) =
      mk 𝒜 ε (oddPart 𝒜 (p1 𝒜 ε x)) (evenPart 𝒜 (p2 𝒜 ε x)) := rfl

private theorem split (x : OddDouble 𝒜 ε) :
    mk 𝒜 ε (evenPart 𝒜 (p1 𝒜 ε x)) (oddPart 𝒜 (p2 𝒜 ε x))
      + mk 𝒜 ε (oddPart 𝒜 (p1 𝒜 ε x)) (evenPart 𝒜 (p2 𝒜 ε x)) = x := by
  refine ext 𝒜 ε ?_ ?_
  · simp only [map_add, p1_mk]
    exact evenPart_add_oddPart 𝒜 _
  · simp only [map_add, p2_mk]
    rw [add_comm]
    exact evenPart_add_oddPart 𝒜 _

noncomputable instance : DirectSum.Decomposition (grading 𝒜 ε) where
  decompose' x :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(grading 𝒜 ε i)) 0 (evenInto 𝒜 ε x)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(grading 𝒜 ε i)) 1 (oddInto 𝒜 ε x)
  left_inv x := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of,
      evenInto_coe, oddInto_coe]
    exact split 𝒜 ε x
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
          obtain ⟨hb1, hb2⟩ := (mem_grading 𝒜 ε).mp b.2
          have h1 : evenInto 𝒜 ε (b : OddDouble 𝒜 ε) = b :=
            Subtype.ext (ext 𝒜 ε
              (by simp [evenPart_of_mem_zero 𝒜 hb1])
              (by simp [oddPart_of_mem_one 𝒜 hb2]))
          have h2 : oddInto 𝒜 ε (b : OddDouble 𝒜 ε) = 0 :=
            Subtype.ext (ext 𝒜 ε
              (by simp [oddPart_of_mem_zero 𝒜 hb1])
              (by simp [evenPart_of_mem_one 𝒜 hb2]))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          obtain ⟨hb1, hb2⟩ := (mem_grading 𝒜 ε).mp b.2
          have h1 : evenInto 𝒜 ε (b : OddDouble 𝒜 ε) = 0 :=
            Subtype.ext (ext 𝒜 ε
              (by simp [evenPart_of_mem_one 𝒜 hb1])
              (by simp [oddPart_of_mem_zero 𝒜 hb2]))
          have h2 : oddInto 𝒜 ε (b : OddDouble 𝒜 ε) = b :=
            Subtype.ext (ext 𝒜 ε
              (by simp [oddPart_of_mem_one 𝒜 hb1])
              (by simp [evenPart_of_mem_zero 𝒜 hb2]))
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-- The odd double of a superalgebra is a superalgebra. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading 𝒜 ε) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

/-! ### Graded components, explicitly -/

theorem decompose_zero_coe (x : OddDouble 𝒜 ε) :
    ((DirectSum.decompose (grading 𝒜 ε) x 0 : grading 𝒜 ε 0) :
      OddDouble 𝒜 ε) =
      mk 𝒜 ε (evenPart 𝒜 (p1 𝒜 ε x)) (oddPart 𝒜 (p2 𝒜 ε x)) := by
  have hmem0 : mk 𝒜 ε (evenPart 𝒜 (p1 𝒜 ε x)) (oddPart 𝒜 (p2 𝒜 ε x)) ∈
      grading 𝒜 ε 0 :=
    (mem_grading 𝒜 ε).mpr ⟨evenPart_mem 𝒜 _, oddPart_mem 𝒜 _⟩
  have hmem1 : mk 𝒜 ε (oddPart 𝒜 (p1 𝒜 ε x)) (evenPart 𝒜 (p2 𝒜 ε x)) ∈
      grading 𝒜 ε 1 :=
    (mem_grading 𝒜 ε).mpr ⟨oddPart_mem 𝒜 _, evenPart_mem 𝒜 _⟩
  conv_lhs => rw [← split 𝒜 ε x]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_same _ hmem0,
    DirectSum.decompose_of_mem_ne _ hmem1 (by decide : (1 : ZMod 2) ≠ 0),
    add_zero]

theorem decompose_one_coe (x : OddDouble 𝒜 ε) :
    ((DirectSum.decompose (grading 𝒜 ε) x 1 : grading 𝒜 ε 1) :
      OddDouble 𝒜 ε) =
      mk 𝒜 ε (oddPart 𝒜 (p1 𝒜 ε x)) (evenPart 𝒜 (p2 𝒜 ε x)) := by
  have hmem0 : mk 𝒜 ε (evenPart 𝒜 (p1 𝒜 ε x)) (oddPart 𝒜 (p2 𝒜 ε x)) ∈
      grading 𝒜 ε 0 :=
    (mem_grading 𝒜 ε).mpr ⟨evenPart_mem 𝒜 _, oddPart_mem 𝒜 _⟩
  have hmem1 : mk 𝒜 ε (oddPart 𝒜 (p1 𝒜 ε x)) (evenPart 𝒜 (p2 𝒜 ε x)) ∈
      grading 𝒜 ε 1 :=
    (mem_grading 𝒜 ε).mpr ⟨oddPart_mem 𝒜 _, evenPart_mem 𝒜 _⟩
  conv_lhs => rw [← split 𝒜 ε x]
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_ne _ hmem0 (by decide : (0 : ZMod 2) ≠ 1),
    DirectSum.decompose_of_mem_same _ hmem1, zero_add]

end OddDouble

end CommRingBase

/-! ### The induction step: central simplicity is preserved -/

namespace OddDouble

section Field

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜] (ε : K)

/-- Supercentrality is preserved by the odd double (field base, `2`
invertible, `ε ≠ 0`). -/
theorem isSuperCentral [Invertible (2 : K)] [IsSuperCentral 𝒜]
    (hε : ε ≠ 0) : IsSuperCentral (grading 𝒜 ε) := by
  constructor
  have layer : ∀ (i : ZMod 2) (z : OddDouble 𝒜 ε),
      z ∈ grading 𝒜 ε i → IsSupercentral (grading 𝒜 ε) i z →
      z ∈ (1 : Submodule K (OddDouble 𝒜 ε)) := by
    intro i z hz hzc
    obtain ⟨hz1, hz2⟩ := (mem_grading 𝒜 ε).mp hz
    -- testing against `A ⊕ 0`: both coordinates are supercentral in `A`
    have hp1 : IsSupercentral 𝒜 i (p1 𝒜 ε z) := by
      intro j c hc
      have h := hzc j (mk 𝒜 ε c 0) (mk_mem_grading 𝒜 ε hc (zero_mem _))
      have h1 : p1 𝒜 ε (z * mk 𝒜 ε c 0) =
          ((sgn (i * j) : ℤˣ) : ℤ) • p1 𝒜 ε (mk 𝒜 ε c 0 * z) := by
        rw [h, map_zsmul]
      simpa using h1
    have hp2 : IsSupercentral 𝒜 (i + 1) (p2 𝒜 ε z) := by
      intro j c hc
      have h := hzc j (mk 𝒜 ε c 0) (mk_mem_grading 𝒜 ε hc (zero_mem _))
      have h2 : p2 𝒜 ε (z * mk 𝒜 ε c 0) =
          ((sgn (i * j) : ℤˣ) : ℤ) • p2 𝒜 ε (mk 𝒜 ε c 0 * z) := by
        rw [h, map_zsmul]
      simp only [p2_mul, p1_mk, p2_mk, mul_zero, zero_mul, zero_add,
        add_zero] at h2
      rcases zmod2_cases j with hj | hj <;> subst hj
      · rw [parityMap_of_mem_zero 𝒜 hc] at h2
        simpa using h2
      · rw [parityMap_of_mem_one 𝒜 hc, mul_neg] at h2
        have h3 : p2 𝒜 ε z * c =
            -(((sgn (i * 1) : ℤˣ) : ℤ) • (c * p2 𝒜 ε z)) := by
          rw [← h2, neg_neg]
        rw [h3, ← neg_zsmul]
        congr 1
        rcases zmod2_cases i with hi | hi <;> subst hi <;>
          simp [show ((1 : ZMod 2) + 1) = 0 by decide]
    -- so both coordinates are scalars
    have hs1 : p1 𝒜 ε z ∈ (1 : Submodule K A) :=
      mem_one_of_isSupercentral 𝒜 hz1 hp1
    have hs2 : p2 𝒜 ε z ∈ (1 : Submodule K A) :=
      mem_one_of_isSupercentral 𝒜 hz2 hp2
    rcases zmod2_cases i with hi | hi <;> subst hi
    · -- even case: the odd coordinate is a scalar in `𝒜 1`, hence `0`
      obtain ⟨μ, hμ⟩ := Submodule.mem_one.mp hs2
      have hz2' : p2 𝒜 ε z ∈ 𝒜 0 := by
        rw [← hμ]
        exact algebraMap_mem_grade_zero 𝒜 μ
      have hz20 : p2 𝒜 ε z = 0 :=
        eq_zero_of_mem_zero_of_mem_one 𝒜 hz2' hz2
      obtain ⟨lam, hlam⟩ := Submodule.mem_one.mp hs1
      exact Submodule.mem_one.mpr
        ⟨lam, ext 𝒜 ε (by simpa using hlam) (by simp [hz20])⟩
    · -- odd case: the even coordinate vanishes, and testing against `g`
      -- kills the odd one
      obtain ⟨lam, hlam⟩ := Submodule.mem_one.mp hs1
      have hz1' : p1 𝒜 ε z ∈ 𝒜 0 := by
        rw [← hlam]
        exact algebraMap_mem_grade_zero 𝒜 lam
      have hz10 : p1 𝒜 ε z = 0 :=
        eq_zero_of_mem_zero_of_mem_one 𝒜 hz1' hz1
      -- p2 z is an even scalar
      obtain ⟨μ, hμ⟩ := Submodule.mem_one.mp hs2
      have h := hzc 1 (gen 𝒜 ε) (gen_mem_grading 𝒜 ε)
      have h1 : p1 𝒜 ε (z * gen 𝒜 ε) =
          ((sgn ((1 : ZMod 2) * 1) : ℤˣ) : ℤ) • p1 𝒜 ε (gen 𝒜 ε * z) := by
        rw [h, map_zsmul]
      simp only [p1_mul, p1_gen, p2_gen, mul_zero, zero_mul, zero_add,
        mul_one, parityMap_one] at h1
      rw [show parityMap 𝒜 (p2 𝒜 ε z) = p2 𝒜 ε z by
          rw [← hμ, parityMap_algebraMap]] at h1
      simp only [one_mul] at h1
      -- h1 : ε • p2 z = -(ε • p2 z)
      have h2 : ((2 : K) * ε) • p2 𝒜 ε z = 0 := by
        have hthis : ε • p2 𝒜 ε z = -(ε • p2 𝒜 ε z) := by
          simpa using h1
        rw [two_mul, add_smul]
        nth_rewrite 1 [hthis]
        abel
      have hz20 : p2 𝒜 ε z = 0 := by
        rcases smul_eq_zero.mp h2 with h | h
        · exact absurd h (mul_ne_zero (Invertible.ne_zero (2 : K)) hε)
        · exact h
      refine Submodule.mem_one.mpr ⟨0, ?_⟩
      rw [map_zero]
      exact (ext 𝒜 ε (by simp [hz10]) (by simp [hz20])).symm
  rw [superCenter, sup_le_iff]
  exact ⟨fun z hz => layer 0 z hz.1 hz.2, fun z hz => layer 1 z hz.1 hz.2⟩

/-- Graded simplicity is preserved by the odd double (field base, `2`
invertible, `ε ≠ 0`).  The combinations `x·g ∓ g·x` isolate the two
coordinates of a homogeneous ideal element. -/
theorem isGradedSimple [Invertible (2 : K)] [IsGradedSimple 𝒜]
    (hε : ε ≠ 0) : IsGradedSimple (grading 𝒜 ε) := by
  constructor
  intro I hI
  rw [or_iff_not_imp_left]
  intro hne
  -- the coordinate ideal
  set N : TwoSidedIdeal A := TwoSidedIdeal.mk' {c : A | mk 𝒜 ε c 0 ∈ I}
    (by
      show mk 𝒜 ε 0 0 ∈ I
      have : mk 𝒜 ε 0 0 = 0 := ext 𝒜 ε (by simp) (by simp)
      rw [this]
      exact I.zero_mem)
    (fun {c c'} hc hc' => by
      show mk 𝒜 ε (c + c') 0 ∈ I
      have : mk 𝒜 ε (c + c') 0 = mk 𝒜 ε c 0 + mk 𝒜 ε c' 0 :=
        ext 𝒜 ε (by simp) (by simp)
      rw [this]
      exact I.add_mem hc hc')
    (fun {c} hc => by
      show mk 𝒜 ε (-c) 0 ∈ I
      have : mk 𝒜 ε (-c) 0 = -mk 𝒜 ε c 0 := ext 𝒜 ε (by simp) (by simp)
      rw [this]
      exact I.neg_mem hc)
    (fun {u c} hc => by
      show mk 𝒜 ε (u * c) 0 ∈ I
      have : mk 𝒜 ε (u * c) 0 = mk 𝒜 ε u 0 * mk 𝒜 ε c 0 :=
        ext 𝒜 ε (by simp) (by simp)
      rw [this]
      exact I.mul_mem_left _ _ hc)
    (fun {c v} hc => by
      show mk 𝒜 ε (c * v) 0 ∈ I
      have : mk 𝒜 ε (c * v) 0 = mk 𝒜 ε c 0 * mk 𝒜 ε v 0 :=
        ext 𝒜 ε (by simp) (by simp)
      rw [this]
      exact I.mul_mem_right _ _ hc) with hNdef
  have memN : ∀ c : A, c ∈ N ↔ mk 𝒜 ε c 0 ∈ I := by
    intro c
    rw [hNdef, TwoSidedIdeal.mem_mk']
    rfl
  -- N is closed under K-scalars with invertible scalar cancellation
  have smulN : ∀ (κ : K) (c : A), κ ≠ 0 → κ • c ∈ N → c ∈ N := by
    intro κ c hκ hc
    have : c = algebraMap K A κ⁻¹ * (κ • c) := by
      rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hκ, one_smul]
    rw [this]
    exact N.mul_mem_left _ _ hc
  -- N is homogeneous
  have hN : TwoSidedIdeal.IsHomogeneous 𝒜 N := by
    intro c hc i
    have h := hI (mk 𝒜 ε c 0) ((memN c).mp hc) i
    rcases zmod2_cases i with hi | hi <;> subst hi
    · rw [decompose_zero_coe] at h
      simp only [p1_mk, p2_mk, map_zero] at h
      exact (memN _).mpr h
    · rw [decompose_one_coe] at h
      simp only [p1_mk, p2_mk, map_zero] at h
      exact (memN _).mpr h
  -- both coordinates of a homogeneous ideal element land in N
  have key : ∀ (y : OddDouble 𝒜 ε) (i : ZMod 2), y ∈ I → y ∈ grading 𝒜 ε i →
      p1 𝒜 ε y ∈ N ∧ p2 𝒜 ε y ∈ N := by
    intro y i hyI hyg
    obtain ⟨hy1, hy2⟩ := (mem_grading 𝒜 ε).mp hyg
    have hyg' : y * gen 𝒜 ε ∈ I := I.mul_mem_right _ _ hyI
    have hgy' : gen 𝒜 ε * y ∈ I := I.mul_mem_left _ _ hyI
    have hxg : y * gen 𝒜 ε = mk 𝒜 ε (ε • p2 𝒜 ε y) (p1 𝒜 ε y) :=
      ext 𝒜 ε (by simp [parityMap_one]) (by simp)
    rcases zmod2_cases i with hi | hi <;> subst hi
    · -- even: J(p1 y) = p1 y, J(p2 y) = -(p2 y)
      have hgx : gen 𝒜 ε * y = mk 𝒜 ε (-(ε • p2 𝒜 ε y)) (p1 𝒜 ε y) := by
        refine ext 𝒜 ε ?_ ?_
        · simp [parityMap_of_mem_one 𝒜 hy2]
        · simp [parityMap_of_mem_zero 𝒜 hy1]
      have hb : p2 𝒜 ε y ∈ N := by
        have hdiff : y * gen 𝒜 ε - gen 𝒜 ε * y =
            mk 𝒜 ε (((2 : K) * ε) • p2 𝒜 ε y) 0 := by
          rw [hxg, hgx]
          refine ext 𝒜 ε ?_ ?_
          · simp only [map_sub, p1_mk, sub_neg_eq_add, two_mul, add_smul]
          · simp
        have := I.sub_mem hyg' hgy'
        rw [hdiff] at this
        exact smulN _ _ (mul_ne_zero (Invertible.ne_zero (2 : K)) hε)
          ((memN _).mpr this)
      have ha : p1 𝒜 ε y ∈ N := by
        have hsum : y * gen 𝒜 ε + gen 𝒜 ε * y =
            mk 𝒜 ε 0 ((2 : K) • p1 𝒜 ε y) := by
          rw [hxg, hgx]
          refine ext 𝒜 ε ?_ ?_
          · simp
          · simp only [map_add, p2_mk, two_smul]
        have hmem := I.add_mem hyg' hgy'
        rw [hsum] at hmem
        -- swap the coordinates with another right multiplication by g
        have hswap : mk 𝒜 ε 0 ((2 : K) • p1 𝒜 ε y) * gen 𝒜 ε =
            mk 𝒜 ε ((ε * 2) • p1 𝒜 ε y) 0 := by
          refine ext 𝒜 ε ?_ ?_
          · simp [parityMap_one, smul_smul]
          · simp
        have hmem2 := I.mul_mem_right _ (gen 𝒜 ε) hmem
        rw [hswap] at hmem2
        exact smulN _ _ (mul_ne_zero hε (Invertible.ne_zero (2 : K)))
          ((memN _).mpr hmem2)
      exact ⟨ha, hb⟩
    · -- odd: J(p1 y) = -(p1 y), J(p2 y) = p2 y
      have hgx : gen 𝒜 ε * y = mk 𝒜 ε (ε • p2 𝒜 ε y) (-(p1 𝒜 ε y)) := by
        refine ext 𝒜 ε ?_ ?_
        · simp [parityMap_of_mem_zero 𝒜 hy2]
        · simp [parityMap_of_mem_one 𝒜 hy1]
      have hb : p2 𝒜 ε y ∈ N := by
        have hsum : y * gen 𝒜 ε + gen 𝒜 ε * y =
            mk 𝒜 ε (((2 : K) * ε) • p2 𝒜 ε y) 0 := by
          rw [hxg, hgx]
          refine ext 𝒜 ε ?_ ?_
          · simp only [map_add, p1_mk, two_mul, add_smul]
          · simp
        have := I.add_mem hyg' hgy'
        rw [hsum] at this
        exact smulN _ _ (mul_ne_zero (Invertible.ne_zero (2 : K)) hε)
          ((memN _).mpr this)
      have ha : p1 𝒜 ε y ∈ N := by
        have hdiff : y * gen 𝒜 ε - gen 𝒜 ε * y =
            mk 𝒜 ε 0 ((2 : K) • p1 𝒜 ε y) := by
          rw [hxg, hgx]
          refine ext 𝒜 ε ?_ ?_
          · simp
          · simp only [map_sub, p2_mk, sub_neg_eq_add, two_smul]
        have hmem := I.sub_mem hyg' hgy'
        rw [hdiff] at hmem
        have hswap : mk 𝒜 ε 0 ((2 : K) • p1 𝒜 ε y) * gen 𝒜 ε =
            mk 𝒜 ε ((ε * 2) • p1 𝒜 ε y) 0 := by
          refine ext 𝒜 ε ?_ ?_
          · simp [parityMap_one, smul_smul]
          · simp
        have hmem2 := I.mul_mem_right _ (gen 𝒜 ε) hmem
        rw [hswap] at hmem2
        exact smulN _ _ (mul_ne_zero hε (Invertible.ne_zero (2 : K)))
          ((memN _).mpr hmem2)
      exact ⟨ha, hb⟩
  -- extract a nonzero element and conclude
  have hex : ∃ x, x ∈ I ∧ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine SetLike.ext fun y => ?_
    rw [TwoSidedIdeal.mem_bot (OddDouble 𝒜 ε)]
    exact ⟨fun hy => hcon y hy, fun hy => hy ▸ I.zero_mem⟩
  obtain ⟨x, hxI, hx0⟩ := hex
  have hc0 := hI x hxI 0
  have hc1 := hI x hxI 1
  have hk0 := key _ 0 hc0 (SetLike.coe_mem _)
  have hk1 := key _ 1 hc1 (SetLike.coe_mem _)
  rcases IsGradedSimple.eq_bot_or_eq_top N hN with hbot | htop
  · -- all four coordinates vanish, contradicting x ≠ 0
    exfalso
    apply hx0
    have z1 := hk0.1
    have z2 := hk0.2
    have z3 := hk1.1
    have z4 := hk1.2
    rw [hbot, TwoSidedIdeal.mem_bot A] at z1 z2 z3 z4
    rw [decompose_zero_coe] at z1 z2
    rw [decompose_one_coe] at z3 z4
    simp only [p1_mk, p2_mk] at z1 z2 z3 z4
    rw [← split 𝒜 ε x, z1, z2, z3, z4]
    refine ext 𝒜 ε ?_ ?_ <;> simp
  · have h1 : (1 : OddDouble 𝒜 ε) ∈ I := by
      have : (1 : A) ∈ N := htop ▸ TwoSidedIdeal.mem_top A
      exact (memN 1).mp this
    refine SetLike.ext fun y => ?_
    refine ⟨fun _ => TwoSidedIdeal.mem_top (OddDouble 𝒜 ε), fun _ => ?_⟩
    have := I.mul_mem_left y _ h1
    rwa [mul_one] at this

/-- **The odd-double induction step** (M7c-1): adjoining an odd square
root of `ε ≠ 0` preserves central simplicity; with M4's Wall criterion,
the odd double of a finite-dimensional central simple superalgebra is
super-Azumaya. -/
theorem isSuperAzumaya [Invertible (2 : K)] [IsSuperCentral 𝒜]
    [IsGradedSimple 𝒜] [FiniteDimensional K A] [Nontrivial A]
    (hε : ε ≠ 0) : IsSuperAzumaya (grading 𝒜 ε) := by
  haveI := isSuperCentral 𝒜 ε hε
  haveI := isGradedSimple 𝒜 ε hε
  exact isSuperAzumaya_of_central_simple (grading 𝒜 ε)

end Field

end OddDouble

end Superfusion
