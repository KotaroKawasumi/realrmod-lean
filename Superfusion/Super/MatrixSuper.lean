/-
Superfusion / Super / MatrixSuper

Milestone M7d-1: **matrix superalgebras are central simple**.

For an index parity `π : n → ZMod 2`, the matrix algebra `Matrix n n K`
is graded by `(matrixGrading π K)ᵢ = {M | M a b ≠ 0 → π a + π b = i}`;
the choice `n = Fin p ⊕ Fin q`, `π = Sum.elim 0 1` (`sumParity`) is the
matrix superalgebra `M_{p|q}(K) = End(K^{p|q})`.

Main results (field base):

* `matrixGradedAlgebra` — the parity grading is a superalgebra
  structure (absent from mathlib);
* `isGradedSimple_matrix` — free from `IsSimpleRing.matrix` (M7d
  inventory) through `isGradedSimple_of_isSimpleRing`;
* `isSuperCentral_matrix` — even supercentral elements commute with
  both parities, hence are central, hence scalar
  (`Algebra.IsCentral.matrix`); odd supercentral elements commute with
  the even units `single a a 1`, hence are diagonal, and odd diagonals
  vanish;
* `isSuperAzumaya_matrix` — Wall's criterion (M4).

These are the BW-trivial central simple superalgebras: the targets of
the Brauer–Wall equivalence (`thm:bw-periodicity`), and in particular
of the certificate route `D₁^{⊗̂8} ≅ M_{8|8}(ℝ)` (M7d-3 of the design
record).
-/
import Superfusion.Super.WallProof
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Algebra.Central.Matrix

namespace Superfusion

section CommRingBase

variable {n : Type*}

private theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by decide +revert

private theorem zmod2_mid (x z y : ZMod 2) : (x + z) + (z + y) = x + y := by
  decide +revert

variable (π : n → ZMod 2) (K : Type*) [CommRing K]

/-- The parity grading on a matrix algebra: degree `i` matrices are
supported on entries `(a, b)` with `π a + π b = i`. -/
def matrixGrading (i : ZMod 2) : Submodule K (Matrix n n K) where
  carrier := {M | ∀ a b, π a + π b ≠ i → M a b = 0}
  zero_mem' _ _ _ := rfl
  add_mem' {M N} hM hN a b h := by
    rw [Matrix.add_apply, hM a b h, hN a b h, add_zero]
  smul_mem' c M hM a b h := by
    rw [Matrix.smul_apply, hM a b h, smul_zero]

theorem mem_matrixGrading {i : ZMod 2} {M : Matrix n n K} :
    M ∈ matrixGrading π K i ↔ ∀ a b, π a + π b ≠ i → M a b = 0 :=
  Iff.rfl

/-- The mask onto the degree-`i` entries, linearly. -/
def matrixMask (i : ZMod 2) : Matrix n n K →ₗ[K] Matrix n n K where
  toFun M := Matrix.of fun a b => if π a + π b = i then M a b else 0
  map_add' M N := by
    ext a b
    by_cases h : π a + π b = i <;> simp [h]
  map_smul' c M := by
    ext a b
    by_cases h : π a + π b = i <;> simp [h]

theorem matrixMask_apply (i : ZMod 2) (M : Matrix n n K) (a b : n) :
    matrixMask π K i M a b = if π a + π b = i then M a b else 0 := rfl

theorem matrixMask_mem (i : ZMod 2) (M : Matrix n n K) :
    matrixMask π K i M ∈ matrixGrading π K i := by
  intro a b h
  rw [matrixMask_apply, if_neg h]

theorem matrixMask_of_mem {i : ZMod 2} {M : Matrix n n K}
    (hM : M ∈ matrixGrading π K i) : matrixMask π K i M = M := by
  ext a b
  rw [matrixMask_apply]
  by_cases h : π a + π b = i
  · rw [if_pos h]
  · rw [if_neg h, hM a b h]

theorem matrixMask_of_mem_ne {i j : ZMod 2} {M : Matrix n n K}
    (hM : M ∈ matrixGrading π K i) (hij : i ≠ j) :
    matrixMask π K j M = 0 := by
  ext a b
  rw [matrixMask_apply]
  by_cases h : π a + π b = j
  · rw [if_pos h, hM a b (h ▸ hij ∘ Eq.symm)]
    · rfl
  · rw [if_neg h]
    rfl

theorem matrixMask_add_matrixMask (M : Matrix n n K) :
    matrixMask π K 0 M + matrixMask π K 1 M = M := by
  ext a b
  rw [Matrix.add_apply, matrixMask_apply, matrixMask_apply]
  rcases zmod2_cases (π a + π b) with h | h <;>
    simp [h]

variable [Fintype n] [DecidableEq n]

instance : SetLike.GradedMonoid (matrixGrading π K) where
  one_mem a b h := by
    by_cases hab : a = b
    · subst hab
      exact absurd (zmod2_add_self (π a)) h
    · exact Matrix.one_apply_ne hab
  mul_mem {i j} M N hM hN := by
    intro a b h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : π a + π c = i
    · have h2 : π c + π b ≠ j := fun h2 => h (by rw [← h1, ← h2, zmod2_mid])
      rw [hN c b h2, mul_zero]
    · rw [hM a c h1, zero_mul]

/-- The degree-`i` projection, corestricted to the layer. -/
def matrixMaskInto (i : ZMod 2) :
    Matrix n n K →ₗ[K] matrixGrading π K i :=
  LinearMap.codRestrict (matrixGrading π K i) (matrixMask π K i)
    (matrixMask_mem π K i)

instance : DirectSum.Decomposition (matrixGrading π K) where
  decompose' M :=
    DirectSum.lof K (ZMod 2) (fun i => ↥(matrixGrading π K i)) 0
        (matrixMaskInto π K 0 M)
      + DirectSum.lof K (ZMod 2) (fun i => ↥(matrixGrading π K i)) 1
        (matrixMaskInto π K 1 M)
  left_inv M := by
    rw [map_add, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    exact matrixMask_add_matrixMask π K M
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
          have h1 : matrixMaskInto π K 0 (b : Matrix n n K) = b :=
            Subtype.ext (matrixMask_of_mem π K b.2)
          have h2 : matrixMaskInto π K 1 (b : Matrix n n K) = 0 :=
            Subtype.ext (matrixMask_of_mem_ne π K b.2 (by decide))
          rw [h1, h2, map_zero, add_zero, DirectSum.lof_eq_of]
        · rw [DirectSum.coeAddMonoidHom_of]
          beta_reduce
          have h1 : matrixMaskInto π K 0 (b : Matrix n n K) = 0 :=
            Subtype.ext (matrixMask_of_mem_ne π K b.2 (by decide))
          have h2 : matrixMaskInto π K 1 (b : Matrix n n K) = b :=
            Subtype.ext (matrixMask_of_mem π K b.2)
          rw [h1, h2, map_zero, zero_add, DirectSum.lof_eq_of]
    | add x y hx hy =>
        rw [map_add]
        beta_reduce
        rw [map_add, map_add, map_add, map_add, add_add_add_comm]
        exact congrArg₂ (· + ·) hx hy

/-- The parity grading makes the matrix algebra a superalgebra. -/
instance matrixGradedAlgebra : GradedAlgebra (matrixGrading π K) where
  toGradedMonoid := inferInstance
  toDecomposition := inferInstance

end CommRingBase

/-! ### Central simplicity -/

section Field

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (π : n → ZMod 2) (K : Type*) [Field K]

/-- Matrix superalgebras are graded-simple — free from the simplicity of
matrix rings. -/
theorem isGradedSimple_matrix [Nonempty n] :
    IsGradedSimple (matrixGrading π K) :=
  isGradedSimple_of_isSimpleRing _

/-- Matrix superalgebras are supercentral: the supercenter is `K·1`. -/
theorem isSuperCentral_matrix : IsSuperCentral (matrixGrading π K) := by
  constructor
  have layer : ∀ (i : ZMod 2) (z : Matrix n n K),
      z ∈ matrixGrading π K i → IsSupercentral (matrixGrading π K) i z →
      z ∈ (1 : Submodule K (Matrix n n K)) := by
    intro i z hz hzc
    rcases zmod2_cases i with hi | hi <;> subst hi
    · -- even: commutes with both parities, hence central, hence scalar
      have hcomm : ∀ X : Matrix n n K, X * z = z * X := by
        intro X
        have h0 := hzc 0 (evenPart (matrixGrading π K) X)
          (evenPart_mem (matrixGrading π K) X)
        have h1 := hzc 1 (oddPart (matrixGrading π K) X)
          (oddPart_mem (matrixGrading π K) X)
        simp only [mul_zero, zero_mul, sgn_zero, Units.val_one, one_smul]
          at h0 h1
        calc X * z
            = evenPart (matrixGrading π K) X * z
              + oddPart (matrixGrading π K) X * z := by
              rw [← add_mul, evenPart_add_oddPart]
          _ = z * evenPart (matrixGrading π K) X
              + z * oddPart (matrixGrading π K) X := by rw [← h0, ← h1]
          _ = z * X := by rw [← mul_add, evenPart_add_oddPart]
      have hcen : z ∈ Subalgebra.center K (Matrix n n K) :=
        Subalgebra.mem_center_iff.mpr hcomm
      haveI : Algebra.IsCentral K K :=
        ⟨fun x _ => Algebra.mem_bot.mpr ⟨x, rfl⟩⟩
      have hbot : z ∈ (⊥ : Subalgebra K (Matrix n n K)) :=
        Algebra.IsCentral.out hcen
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hbot
      exact Submodule.mem_one.mpr ⟨c, hc⟩
    · -- odd: commuting with the even units forces diagonal support,
      -- and odd diagonals vanish
      have hdiag : ∀ a x : n, x ≠ a → z x a = 0 := by
        intro a x hxa
        have hEmem : Matrix.single a a (1 : K) ∈ matrixGrading π K 0 := by
          intro x' y' h
          by_cases hx : a = x' ∧ a = y'
          · exfalso
            obtain ⟨rfl, rfl⟩ := hx
            exact h (zmod2_add_self (π a))
          · simp [Matrix.single, hx]
        have h := hzc 0 (Matrix.single a a 1) hEmem
        simp only [mul_zero, sgn_zero, Units.val_one, one_smul] at h
        have hentry : (z * Matrix.single a a (1 : K)) x a
            = (Matrix.single a a (1 : K) * z) x a := by rw [h]
        simpa [hxa] using hentry
      have hzero : z = 0 := by
        ext x y
        by_cases hxy : x = y
        · subst hxy
          refine hz x x ?_
          rw [zmod2_add_self]
          decide
        · exact hdiag y x hxy
      rw [hzero]
      exact zero_mem _
  rw [superCenter, sup_le_iff]
  exact ⟨fun z hz => layer 0 z hz.1 hz.2, fun z hz => layer 1 z hz.1 hz.2⟩

/-- **Matrix superalgebras are super-Azumaya** (M7d-1): the BW-trivial
central simple superalgebras. -/
theorem isSuperAzumaya_matrix [Nonempty n] [Invertible (2 : K)] :
    IsSuperAzumaya (matrixGrading π K) := by
  haveI := isSuperCentral_matrix π K
  haveI := isGradedSimple_matrix π K
  exact isSuperAzumaya_of_central_simple _

end Field

/-! ### `M_{p|q}` -/

/-- The index parity of `K^{p|q}`: the first block even, the second
odd. -/
def sumParity (p q : ℕ) : Fin p ⊕ Fin q → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- `M_{p|q}(K)`, the endomorphism superalgebra of `K^{p|q}`, is a
central simple superalgebra whenever `p + q ≠ 0`. -/
theorem isSuperAzumaya_sumParity (p q : ℕ) (K : Type*) [Field K]
    [Invertible (2 : K)] [Nonempty (Fin p ⊕ Fin q)] :
    IsSuperAzumaya (matrixGrading (sumParity p q) K) :=
  isSuperAzumaya_matrix _ K

end Superfusion
