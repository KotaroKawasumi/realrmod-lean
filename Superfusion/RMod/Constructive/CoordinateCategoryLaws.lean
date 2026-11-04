import Superfusion.RMod.Constructive.CoordinateCore
import Superfusion.GaugeChi.RouteMatrixProto

/-!
# Category laws for the constructive coordinate core

The declarations in `CoordinateCore` are executable data.  This file is the
separate proof layer: it compares the frozen coordinate multiplication with
the semantic real division algebras, and then proves the additive, scalar,
category, and grading laws for atomic and matrix morphisms.
-/

set_option autoImplicit false

namespace Superfusion
namespace RModCoordinate

namespace Coeff

@[ext]
theorem ext {a : ZMod 8} {x y : Coeff a} (h : ∀ i, x i = y i) : x = y :=
  funext h

@[simp] theorem zero_apply (a : ZMod 8) (i) : zero a i = 0 := rfl
@[simp] theorem add_apply (a : ZMod 8) (x y : Coeff a) (i) :
    add a x y i = x i + y i := rfl
@[simp] theorem neg_apply (a : ZMod 8) (x : Coeff a) (i) :
    neg a x i = -x i := rfl
@[simp] theorem smul_apply (a : ZMod 8) (r : ℝ) (x : Coeff a) (i) :
    smul a r x i = r * x i := rfl
@[simp] theorem component_apply (a : ZMod 8) (d : ZMod 2) (x : Coeff a) (i) :
    component a d x i = if realRepBasisParity a i = d then x i else 0 := rfl

@[simp]
theorem mul_zero (a : ZMod 8) (x : Coeff a) : mul a x (zero a) = zero a := by
  ext k
  simp [mul, zero]

@[simp]
theorem zero_mul (a : ZMod 8) (x : Coeff a) : mul a (zero a) x = zero a := by
  ext k
  simp [mul, zero]

@[simp]
theorem component_zero (a : ZMod 8) (d : ZMod 2) :
    component a d (zero a) = zero a := by
  ext i
  simp [component, zero]

/-- Proof-only interpretation of a coordinate vector in the corresponding
real division algebra. -/
noncomputable def semantic (a : ZMod 8) :
    Coeff a ≃ₗ[ℝ] (realRep a).carrier :=
  (realRepBasis a).equivFun.symm

@[simp]
theorem semantic_zero (a : ZMod 8) : semantic a (zero a) = 0 := by
  exact (semantic a).map_zero

@[simp]
theorem semantic_add (a : ZMod 8) (x y : Coeff a) :
    semantic a (add a x y) = semantic a x + semantic a y := by
  exact (semantic a).map_add x y

@[simp]
theorem semantic_neg (a : ZMod 8) (x : Coeff a) :
    semantic a (neg a x) = -semantic a x := by
  exact (semantic a).map_neg x

@[simp]
theorem semantic_smul (a : ZMod 8) (r : ℝ) (x : Coeff a) :
    semantic a (smul a r x) = r • semantic a x := by
  exact (semantic a).map_smul r x

/-- Reindex a finite sum by the involutive signed-xor multiplication index. -/
private theorem reindex_mulIdx (a : ZMod 8)
    (i : Fin (realRepDim a.val))
    {M : Type*} [AddCommMonoid M]
    (F : Fin (realRepDim a.val) → M) :
    ∑ j, F j = ∑ k, F (realRepMulIdx a i k) := by
  let e : Fin (realRepDim a.val) ≃ Fin (realRepDim a.val) :=
    { toFun := realRepMulIdx a i
      invFun := realRepMulIdx a i
      left_inv := realRepMulIdx_involutive a i
      right_inv := realRepMulIdx_involutive a i }
  exact (Equiv.sum_comp e F).symm

/-- Frozen signed-xor convolution agrees with multiplication in `realRep a`.
This is used only for proofs; executable multiplication remains `Coeff.mul`. -/
theorem semantic_mul (a : ZMod 8) (x y : Coeff a) :
    semantic a (mul a x y) = semantic a x * semantic a y := by
  classical
  simp only [semantic, Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_mul_sum]
  symm
  rw [Finset.sum_congr rfl (fun i _ => reindex_mulIdx a i
    (fun j => (x i • realRepBasis a i) * (y j • realRepBasis a j)))]
  have hterm : ∀ (i k : Fin (realRepDim a.val)),
      (x i • realRepBasis a i) *
          (y (realRepMulIdx a i k) •
            realRepBasis a (realRepMulIdx a i k)) =
        (x i * y (realRepMulIdx a i k) *
            (realRepMulSign a i (realRepMulIdx a i k) : ℝ)) •
          realRepBasis a k := by
    intro i k
    rw [smul_mul_assoc, mul_smul_comm, realRepBasis_mul,
      smul_smul, smul_smul, realRepMulIdx_involutive]
  rw [Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun k _ => hterm i k))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  rfl

@[simp]
theorem semantic_one (a : ZMod 8) : semantic a (one a) = 1 := by
  classical
  let i0 : Fin (realRepDim a.val) := ⟨0, realRepDim_pos a.val⟩
  simp only [semantic, Module.Basis.equivFun_symm_apply]
  rw [Fintype.sum_eq_single i0]
  · simp [one, i0, GaugeChi.realRepBasis_zero]
  · intro b hb
    have hb0 : b.val ≠ 0 := by
      intro h
      apply hb
      exact Fin.ext h
    simp [one, hb0]

theorem add_assoc (a : ZMod 8) (x y z : Coeff a) :
    add a (add a x y) z = add a x (add a y z) := by
  ext i
  exact _root_.add_assoc _ _ _

theorem add_comm (a : ZMod 8) (x y : Coeff a) : add a x y = add a y x := by
  ext i
  exact _root_.add_comm _ _

@[simp]
theorem zero_add (a : ZMod 8) (x : Coeff a) : add a (zero a) x = x := by
  ext i
  simp [add, zero]

@[simp]
theorem add_zero (a : ZMod 8) (x : Coeff a) : add a x (zero a) = x := by
  ext i
  simp [add, zero]

@[simp]
theorem neg_add (a : ZMod 8) (x : Coeff a) : add a (neg a x) x = zero a := by
  ext i
  simp [add, neg, zero]

@[simp]
theorem add_neg (a : ZMod 8) (x : Coeff a) : add a x (neg a x) = zero a := by
  ext i
  simp [add, neg, zero]

theorem mul_assoc (a : ZMod 8) (x y z : Coeff a) :
    mul a (mul a x y) z = mul a x (mul a y z) := by
  apply (semantic a).injective
  simp [semantic_mul, _root_.mul_assoc]

@[simp]
theorem one_mul (a : ZMod 8) (x : Coeff a) : mul a (one a) x = x := by
  apply (semantic a).injective
  simp [semantic_mul]

@[simp]
theorem mul_one (a : ZMod 8) (x : Coeff a) : mul a x (one a) = x := by
  apply (semantic a).injective
  simp [semantic_mul]

theorem mul_add (a : ZMod 8) (x y z : Coeff a) :
    mul a x (add a y z) = add a (mul a x y) (mul a x z) := by
  apply (semantic a).injective
  simp [semantic_mul, _root_.mul_add]

theorem add_mul (a : ZMod 8) (x y z : Coeff a) :
    mul a (add a x y) z = add a (mul a x z) (mul a y z) := by
  apply (semantic a).injective
  simp [semantic_mul, _root_.add_mul]

@[simp]
theorem one_smul (a : ZMod 8) (x : Coeff a) : smul a 1 x = x := by
  ext i
  simp [smul]

theorem mul_smul (a : ZMod 8) (r s : ℝ) (x : Coeff a) :
    smul a (r * s) x = smul a r (smul a s x) := by
  ext i
  exact _root_.mul_assoc _ _ _

theorem add_smul (a : ZMod 8) (r s : ℝ) (x : Coeff a) :
    smul a (r + s) x = add a (smul a r x) (smul a s x) := by
  ext i
  exact _root_.add_mul _ _ _

theorem smul_add (a : ZMod 8) (r : ℝ) (x y : Coeff a) :
    smul a r (add a x y) = add a (smul a r x) (smul a r y) := by
  ext i
  exact _root_.mul_add _ _ _

@[simp]
theorem zero_smul (a : ZMod 8) (x : Coeff a) : smul a 0 x = zero a := by
  ext i
  simp [smul, zero]

@[simp]
theorem smul_zero (a : ZMod 8) (r : ℝ) : smul a r (zero a) = zero a := by
  ext i
  simp [smul, zero]

theorem smul_mul (a : ZMod 8) (r : ℝ) (x y : Coeff a) :
    mul a (smul a r x) y = smul a r (mul a x y) := by
  apply (semantic a).injective
  simp [semantic_mul, Algebra.smul_mul_assoc]

theorem mul_smul_right (a : ZMod 8) (r : ℝ) (x y : Coeff a) :
    mul a x (smul a r y) = smul a r (mul a x y) := by
  apply (semantic a).injective
  simp [semantic_mul, Algebra.mul_smul_comm]

/-! ## Coordinate grading -/

set_option maxHeartbeats 1000000

/-- The signed-xor product index has the sum of the input parities. -/
theorem basisParity_mulIdx (a : ZMod 8)
    (i j : Fin (realRepDim a.val)) :
    realRepBasisParity a (realRepMulIdx a i j) =
      realRepBasisParity a i + realRepBasisParity a j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

/-- Basis index zero is even at every label. -/
theorem basisParity_of_val_zero (a : ZMod 8)
    (i : Fin (realRepDim a.val)) (hi : i.val = 0) :
    realRepBasisParity a i = 0 := by
  have hidx : realRepMulIdx a i i = i := by
    apply Fin.ext
    rw [realRepMulIdx_eq_xor, hi]
    rfl
  have hp := basisParity_mulIdx a i i
  rw [hidx] at hp
  have hp' : (0 : ZMod 2) + realRepBasisParity a i =
      realRepBasisParity a i + realRepBasisParity a i := by
    simpa using hp
  exact (add_right_cancel hp').symm

set_option maxHeartbeats 200000

/-- No element of `ZMod 2` is fixed by translation by one. -/
private theorem ne_add_one (d : ZMod 2) : d ≠ d + 1 := by
  intro h
  have h' : d + 0 = d + 1 := by simpa using h
  have : (0 : ZMod 2) = 1 := add_left_cancel h'
  exact zero_ne_one this

/-- Every element of `ZMod 2` is its own additive inverse. -/
theorem add_self_eq_zero (d : ZMod 2) : d + d = 0 := by
  fin_cases d <;> rfl

theorem memGrade_zero (a : ZMod 8) (d : ZMod 2) : MemGrade a d (zero a) := by
  intro i _
  rfl

theorem memGrade_add (a : ZMod 8) (d : ZMod 2) {x y : Coeff a}
    (hx : MemGrade a d x) (hy : MemGrade a d y) :
    MemGrade a d (add a x y) := by
  intro i hi
  simp [add, hx i hi, hy i hi]

theorem memGrade_neg (a : ZMod 8) (d : ZMod 2) {x : Coeff a}
    (hx : MemGrade a d x) : MemGrade a d (neg a x) := by
  intro i hi
  simp [neg, hx i hi]

theorem memGrade_smul (a : ZMod 8) (d : ZMod 2) (r : ℝ) {x : Coeff a}
    (hx : MemGrade a d x) : MemGrade a d (smul a r x) := by
  intro i hi
  simp [smul, hx i hi]

theorem component_add (a : ZMod 8) (d : ZMod 2) (x y : Coeff a) :
    component a d (add a x y) =
      add a (component a d x) (component a d y) := by
  ext i
  by_cases h : realRepBasisParity a i = d <;> simp [component, add, h]

theorem component_neg (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    component a d (neg a x) = neg a (component a d x) := by
  ext i
  by_cases h : realRepBasisParity a i = d <;> simp [component, neg, h]

theorem component_smul (a : ZMod 8) (d : ZMod 2) (r : ℝ) (x : Coeff a) :
    component a d (smul a r x) = smul a r (component a d x) := by
  ext i
  by_cases h : realRepBasisParity a i = d <;> simp [component, smul, h]

theorem component_memGrade (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    MemGrade a d (component a d x) := by
  intro i hi
  simp [component, hi]

theorem component_eq_self_iff (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    component a d x = x ↔ MemGrade a d x := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [component, hi] using this.symm
  · intro h
    ext i
    by_cases hi : realRepBasisParity a i = d
    · simp [component, hi]
    · simp [component, hi, h i hi]

theorem component_idem (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    component a d (component a d x) = component a d x :=
  (component_eq_self_iff a d _).2 (component_memGrade a d x)

theorem component_complement (a : ZMod 8) (d : ZMod 2) (x : Coeff a) :
    add a (component a d x) (component a (d + 1) x) = x := by
  ext i
  by_cases hi : realRepBasisParity a i = d
  · have hi' : realRepBasisParity a i ≠ d + 1 := by
      rw [hi]
      exact ne_add_one d
    simp [add, component, hi, hi']
  · have hi' : realRepBasisParity a i = d + 1 := by
      generalize realRepBasisParity a i = e at hi ⊢
      fin_cases d <;> fin_cases e <;> simp_all <;> rfl
    simp [add, component, hi, hi']

theorem memGrade_disjoint (a : ZMod 8) (d : ZMod 2) {x : Coeff a}
    (hd : MemGrade a d x) (hd' : MemGrade a (d + 1) x) :
    x = zero a := by
  ext i
  by_cases hi : realRepBasisParity a i = d
  · apply hd' i
    rw [hi]
    exact ne_add_one d
  · exact hd i hi

theorem memGrade_one (a : ZMod 8) : MemGrade a 0 (one a) := by
  intro i hi
  by_cases h0 : i.val = 0
  · exact (hi (basisParity_of_val_zero a i h0)).elim
  · simp [one, h0]

theorem memGrade_mul (a : ZMod 8) (d e : ZMod 2) {x y : Coeff a}
    (hx : MemGrade a d x) (hy : MemGrade a e y) :
    MemGrade a (d + e) (mul a x y) := by
  intro k hk
  apply Finset.sum_eq_zero
  intro i _
  let j := realRepMulIdx a i k
  have hparity : realRepBasisParity a k =
      realRepBasisParity a i + realRepBasisParity a j := by
    simpa [j, realRepMulIdx_involutive] using basisParity_mulIdx a i j
  by_cases hi : realRepBasisParity a i = d
  · by_cases hj : realRepBasisParity a j = e
    · exfalso
      apply hk
      rw [hparity, hi, hj]
    · simp [mul, j, hy j hj]
  · simp [mul, hx i hi]

end Coeff

end RModCoordinate
end Superfusion
