import RMod.BrundanEllis.StackingReferenceCommutorRightLinear
import Superfusion.RMod.FromRawDCT.Core

/-! Matrices of actual reference morphisms at a fixed Brauer--Wall label.
A right-module matrix acts by the same left coefficient multiplications as
composition in the raw reference category. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- A finite family of parity shifts at one fixed label. -/
def rowObject {n : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) : Obj :=
  ⟨n, fun i => (a, p i)⟩

/-- Coefficient matrices use target rows and source columns. -/
def rowHom {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    Hom realDData (rowObject a p) (rowObject a q) :=
  fun i j => AtomHom.ofLabelEq rfl (M j i)

@[simp] theorem rowHom_coeff {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (M : Matrix (Fin m) (Fin n) (Coeff a)) (i : Fin n) (j : Fin m) :
    (rowHom a p q M i j).coeff rfl = M j i := AtomHom.coeff_ofLabelEq rfl _

/-- Reading the actual atomic coefficients recovers the entire matrix. -/
theorem rowHom_injective {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Function.Injective (rowHom a p q) := by
  intro M N h
  funext j i
  have he := congrArg (fun f => (f i j).coeff rfl) h
  with_unfolding_all simpa only [rowHom_coeff] using he

/-- The corresponding operator on the free right module. -/
def rowOperator {n m : ℕ} (a : ZMod 8) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a) :=
  LinearMap.pi fun j => ∑ i : Fin n, (coefficientLeft a (M j i)).comp (LinearMap.proj i)

@[simp] theorem rowOperator_apply {n m : ℕ} (a : ZMod 8) (M : Matrix (Fin m) (Fin n) (Coeff a))
    (v : Fin n → Coeff a) (j : Fin m) :
    rowOperator a M v j = ∑ i : Fin n, Coeff.mul a (M j i) (v i) := by
  simp only [rowOperator, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, coefficientLeft]
  rfl

/-- A row coefficient is obtained by evaluating on the corresponding unit vector. -/
theorem rowOperator_unit {n m : ℕ} (a : ZMod 8) (M : Matrix (Fin m) (Fin n) (Coeff a))
    (i : Fin n) (j : Fin m) :
    rowOperator a M (Pi.single i (Coeff.one a)) j = M j i := by
  rw [rowOperator_apply]
  have hz (x : Coeff a) : Coeff.mul a x 0 = 0 := by with_unfolding_all exact Coeff.mul_zero a x
  simp only [Pi.single_apply, apply_ite, hz, Coeff.mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The free-module action detects equality of coefficient matrices. -/
theorem rowOperator_injective {n m : ℕ} (a : ZMod 8) :
    Function.Injective (@rowOperator n m a) := by
  intro M N h
  funext j i
  have he := congrArg (fun f : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a) =>
    f (Pi.single i (Coeff.one a)) j) h
  simpa only [rowOperator_unit] using he

/-- Product uses the stored division-algebra multiplication, not pointwise multiplication. -/
def rowProduct {n m l : ℕ} (a : ZMod 8)
    (N : Matrix (Fin l) (Fin m) (Coeff a)) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    Matrix (Fin l) (Fin n) (Coeff a) :=
  fun k i => ∑ j : Fin m, Coeff.mul a (N k j) (M j i)

/-- Composition of free-module operators is coefficient matrix multiplication. -/
theorem rowOperator_comp {n m l : ℕ} (a : ZMod 8)
    (N : Matrix (Fin l) (Fin m) (Coeff a)) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    (rowOperator a N).comp (rowOperator a M) = rowOperator a (rowProduct a N M) := by
  apply LinearMap.ext
  intro v
  funext k
  apply (Coeff.semantic a).injective
  simp only [LinearMap.comp_apply, rowOperator_apply, rowProduct, map_sum, Coeff.semantic_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Reading a coefficient commutes with the fixed-order raw finite sum. -/
theorem atom_finSum_coeff (a : ZMod 8) (p q : ZMod 2) {n : ℕ}
    (f : Fin n → AtomHom realDData (a, p) (a, q)) :
    @Eq (Coeff a) ((AtomHom.finSum n f).coeff rfl) (∑ i, (f i).coeff rfl) := by
  induction n with
  | zero => simp [AtomHom.finSum, AtomHom.coeff_zero]; rfl
  | succ n ih =>
    rw [AtomHom.finSum, AtomHom.coeff_add, ih, Fin.sum_univ_castSucc]
    rfl

/-- The same coefficient product is composition in the actual raw category. -/
theorem rowHom_comp {n m l : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (r : Fin l → ZMod 2) (N : Matrix (Fin l) (Fin m) (Coeff a))
    (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    Hom.comp (rowHom a p q M) (rowHom a q r N) = rowHom a p r (rowProduct a N M) := by
  funext i k
  apply AtomHom.ext_same_label
  with_unfolding_all
    rw [Hom.comp, atom_finSum_coeff]
    simp only [rowHom_coeff, AtomHom.coeff_comp_same_label, rowProduct]
    rfl

/-- Matrix support in one degree is exactly the condition on the raw morphism. -/
theorem rowHom_grade {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (M : Matrix (Fin m) (Fin n) (Coeff a)) (d : ZMod 2)
    (h : ∀ i j, (realDData.algebra a).MemGrade (d + p i + q j) (M j i)) :
    Hom.MemGrade (dD := realDData) d (rowHom a p q M) := by
  intro i j hij
  simpa only [rowHom, rowObject, Obj.atom, Atom.label, Atom.shift,
    AtomHom.coeff_ofLabelEq] using h i j

/-- The unit matrix has the actual algebra unit on its diagonal. -/
def rowIdentity (a : ZMod 8) (n : ℕ) : Matrix (Fin n) (Fin n) (Coeff a) :=
  fun j i => if i = j then Coeff.one a else 0

@[simp] theorem rowOperator_identity (a : ZMod 8) (n : ℕ) :
    rowOperator a (rowIdentity a n) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext j
  rw [rowOperator_apply]
  have hz (x : Coeff a) : Coeff.mul a 0 x = 0 := by
    with_unfolding_all exact Coeff.zero_mul a x
  change (∑ i, Coeff.mul a (if i = j then Coeff.one a else 0) (v i)) = v j
  rw [Finset.sum_eq_single j]
  · simp only [if_true, Coeff.one_mul]
  · intro i hi hij
    rw [if_neg hij, hz]
  · simp

@[simp] theorem rowHom_identity {n : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) :
    rowHom a p p (rowIdentity a n) = Hom.id realDData (rowObject a p) := by
  funext i j
  by_cases h : i = j
  · subst j
    apply AtomHom.ext_same_label
    with_unfolding_all
      simp only [rowHom_coeff, rowIdentity, Hom.id, dite_true, if_true]
      change Coeff.one a = (AtomHom.id realDData (a, p i)).coeff rfl
      rw [AtomHom.coeff_id]
      rfl
  · apply AtomHom.ext_same_label
    simp only [rowHom_coeff, rowIdentity, if_neg h, Hom.id, dif_neg h]
    rfl

/-- The free right action, using the stored division algebra. -/
def rowRight {n : ℕ} (a : ZMod 8) (v : Fin n → Coeff a) (x : Coeff a) : Fin n → Coeff a :=
  fun i => Coeff.mul a (v i) x

/-- Every right-linear operator is determined by its values on row units. -/
def rowMatrixOf {n m : ℕ} (a : ZMod 8)
    (F : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a)) : Matrix (Fin m) (Fin n) (Coeff a) :=
  fun j i => F (Pi.single i (Coeff.one a)) j

private theorem row_unit_expansion {n : ℕ} (a : ZMod 8) (v : Fin n → Coeff a) :
    v = ∑ i : Fin n, rowRight a (Pi.single i (Coeff.one a)) (v i) := by
  funext j
  have hz (x : Coeff a) : Coeff.mul a 0 x = 0 := by
    with_unfolding_all exact Coeff.zero_mul a x
  simp only [Finset.sum_apply, rowRight, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp only [if_true, Coeff.one_mul]
  · intro i hi hij
    rw [if_neg (Ne.symm hij), hz]
  · simp

/-- Right linearity is sufficient; no choice of a matrix presentation is assumed. -/
theorem rowOperator_matrixOf {n m : ℕ} (a : ZMod 8)
    (F : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a))
    (hF : ∀ v x, F (rowRight a v x) = rowRight a (F v) x) :
    rowOperator a (rowMatrixOf a F) = F := by
  apply LinearMap.ext
  intro v
  have hf : F v = ∑ i : Fin n, rowRight a (F (Pi.single i (Coeff.one a))) (v i) := by
    conv_lhs => rw [row_unit_expansion a v, map_sum]
    simp only [hF]
  rw [hf]
  funext j
  simp only [rowOperator_apply, rowMatrixOf, Finset.sum_apply, rowRight]

/-- An invertible right-linear operator has a right-linear inverse. -/
theorem rowEquiv_symm_right {n m : ℕ} (a : ZMod 8)
    (F : (Fin n → Coeff a) ≃ₗ[ℝ] (Fin m → Coeff a))
    (hF : ∀ v x, F (rowRight a v x) = rowRight a (F v) x) (v : Fin m → Coeff a) (x : Coeff a) :
    F.symm (rowRight a v x) = rowRight a (F.symm v) x := by
  apply F.injective
  rw [LinearEquiv.apply_symm_apply, hF, LinearEquiv.apply_symm_apply]

/-- The forward and inverse operators give actual mutually inverse raw morphisms. -/
theorem rowHom_equiv_inverse {n m : ℕ} (a : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (F : (Fin n → Coeff a) ≃ₗ[ℝ] (Fin m → Coeff a))
    (hF : ∀ v x, F (rowRight a v x) = rowRight a (F v) x) :
    Hom.comp (rowHom a p q (rowMatrixOf a F.toLinearMap))
        (rowHom a q p (rowMatrixOf a F.symm.toLinearMap)) = Hom.id realDData (rowObject a p) ∧
      Hom.comp (rowHom a q p (rowMatrixOf a F.symm.toLinearMap))
        (rowHom a p q (rowMatrixOf a F.toLinearMap)) = Hom.id realDData (rowObject a q) := by
  have hs := rowEquiv_symm_right a F hF
  constructor
  · rw [rowHom_comp, ← rowHom_identity]
    apply congrArg (rowHom a p p)
    apply rowOperator_injective a
    rw [← rowOperator_comp, rowOperator_matrixOf a _ hF, rowOperator_matrixOf a _ hs,
      rowOperator_identity]
    apply LinearMap.ext
    exact F.symm_apply_apply
  · rw [rowHom_comp, ← rowHom_identity]
    apply congrArg (rowHom a q q)
    apply rowOperator_injective a
    rw [← rowOperator_comp, rowOperator_matrixOf a _ hF, rowOperator_matrixOf a _ hs,
      rowOperator_identity]
    apply LinearMap.ext
    exact F.apply_symm_apply

end RMod.BrundanEllis.Stacking.ReferenceCommutor
