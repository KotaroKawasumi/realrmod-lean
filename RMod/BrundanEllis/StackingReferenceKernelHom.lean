import RMod.BrundanEllis.StackingReferenceRowHom
import RMod.BrundanEllis.StackingReferenceInverseNormalization

/-! The normalized division-module exchange gives invertible homogeneous
morphisms between the actual reference row objects. This step keeps the
right algebra action and the source/target parity shifts explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Homogeneity of a vector in a finite direct sum of shifted right modules. -/
def RowGrade {n : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (d : ZMod 2)
    (v : Fin n → Coeff a) : Prop :=
  ∀ i, (realDData.algebra a).MemGrade (d + p i) (v i)

/-- The unit of the i-th summand has its declared parity. -/
theorem rowUnit_grade {n : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (i : Fin n) :
    RowGrade a p (p i) (Pi.single i (Coeff.one a)) := by
  intro j
  by_cases h : j = i
  · subst j
    simp only [Pi.single_eq_same, CharTwo.add_self_eq_zero]
    exact (realDLaws.algebra_laws a).one_mem
  · rw [Pi.single_eq_of_ne h]
    exact (realDLaws.algebra_laws a).component_zero _

/-- A homogeneous module operator gives a homogeneous morphism of row objects. -/
theorem rowHom_matrixOf_grade {n m : ℕ} (a : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (F : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a)) (d : ZMod 2)
    (hF : ∀ k v, RowGrade a p k v → RowGrade a q (k + d) (F v)) :
    Hom.MemGrade (dD := realDData) d (rowHom a p q (rowMatrixOf a F)) := by
  apply rowHom_grade
  intro i j
  have h := hF (p i) (Pi.single i (Coeff.one a)) (rowUnit_grade a p i) j
  simpa only [rowMatrixOf, add_comm (p i) d] using h

/-- The parity of a row in the shifted reference fusion kernel. -/
def kernelRowParity (a b : ZMod 8) (i : FusionTable.Index a b) : ZMod 2 :=
  FusionTable.indexParity a b i + shiftNu realComputableNuBeta.data a b

/-- The row-object grading is the stored reference-kernel grading. -/
theorem kernelGrade_rowGrade (a b : ZMod 8) (d : ZMod 2) (v : RealCCarrier a b) :
    realComputableShiftedRawDCT.data.C.MemGrade a b d v ↔
      RowGrade (a + b) (kernelRowParity a b) d v := by
  change (fun i => Coeff.component (a + b)
    ((d + shiftNu realComputableNuBeta.data a b) + FusionTable.indexParity a b i) (v i)) = v ↔ _
  constructor
  · intro h i
    simpa only [SuperAlgebraData.MemGrade, realDData, coordinateSuperAlgebraData,
      kernelRowParity, add_assoc, add_comm, add_left_comm] using congrFun h i
  · intro h
    funext i
    simpa only [SuperAlgebraData.MemGrade, realDData, coordinateSuperAlgebraData,
      RowGrade, kernelRowParity, add_assoc, add_comm, add_left_comm] using h i

/-- Cast only the endpoint algebra, retaining the order of the target rows. -/
def kernelTargetCast (a b : ZMod 8) :
    RealCCarrier b a ≃ₗ[ℝ] (FusionTable.Index b a → Coeff (a + b)) :=
  LinearEquiv.piCongrRight fun _ => coefficientCast (add_comm b a)

/-- View both sides of the exchange over exactly the same endpoint algebra. -/
def commonKernelEquiv (a b : ZMod 8) :
    RealCCarrier a b ≃ₗ[ℝ] (FusionTable.Index b a → Coeff (a + b)) :=
  (normalizedKernelEquiv a b).trans (kernelTargetCast a b)

@[simp] theorem commonKernelEquiv_apply (a b : ZMod 8) (v : RealCCarrier a b)
    (i : FusionTable.Index b a) :
    commonKernelEquiv a b v i = coefficientCast (add_comm b a) (normalizedKernelEquiv a b v i) := rfl

/-- Endpoint transport preserves the actual graded subspaces. -/
theorem coefficientCast_grade {a b : ZMod 8} (h : a = b) (d : ZMod 2) (x : Coeff a)
    (hx : (realDData.algebra a).MemGrade d x) :
    (realDData.algebra b).MemGrade d (coefficientCast h x) := by
  cases h
  exact hx

theorem commonKernelEquiv_grade (a b : ZMod 8) (d : ZMod 2) (v : RealCCarrier a b)
    (hv : RowGrade (a + b) (kernelRowParity a b) d v) :
    RowGrade (a + b) (kernelRowParity b a) (d + degree a b) (commonKernelEquiv a b v) := by
  have h := (kernelGrade_rowGrade b a _ _).mp
    (normalizedKernelEquiv_grade a b v ((kernelGrade_rowGrade a b _ _).mpr hv))
  intro i
  exact coefficientCast_grade (add_comm b a) _ _ (h i)

theorem commonKernelEquiv_right (a b : ZMod 8) (v : RealCCarrier a b) (x : Coeff (a + b)) :
    commonKernelEquiv a b (rowRight (a + b) v x) =
      rowRight (a + b) (commonKernelEquiv a b v) x := by
  funext i
  change coefficientCast (add_comm b a)
    (normalizedKernelEquiv a b (realCRight a b v x) i) = _
  rw [normalizedKernelEquiv_right_linear]
  change coefficientCast (add_comm b a)
    (Coeff.mul (b + a) (normalizedKernelEquiv a b v i) (coefficientCast (add_comm a b) x)) = _
  rw [coefficientCast_mul, coefficientCast_trans]
  rfl


/-- The inverse equality transport preserves the same homogeneous subspace. -/
theorem coefficientCast_symm_grade {a b : ZMod 8} (h : a = b) (d : ZMod 2) (x : Coeff b)
    (hx : (realDData.algebra b).MemGrade d x) :
    (realDData.algebra a).MemGrade d ((coefficientCast h).symm x) := by
  cases h
  exact hx

theorem commonKernelEquiv_symm_grade (a b : ZMod 8) (d : ZMod 2)
    (v : FusionTable.Index b a → Coeff (a + b))
    (hv : RowGrade (a + b) (kernelRowParity b a) d v) :
    RowGrade (a + b) (kernelRowParity a b) (d + degree a b) ((commonKernelEquiv a b).symm v) := by
  apply (kernelGrade_rowGrade a b _ _).mp
  apply normalizedKernelEquiv_symm_grade
  apply (kernelGrade_rowGrade b a _ _).mpr
  intro i
  exact coefficientCast_symm_grade (add_comm b a) _ _ (hv i)

/-- Actual homogeneous raw morphism induced by the normalized exchange. -/
def kernelHom (a b : ZMod 8) :
    Hom realDData (rowObject (a + b) (kernelRowParity a b))
      (rowObject (a + b) (kernelRowParity b a)) :=
  rowHom (a + b) (kernelRowParity a b) (kernelRowParity b a)
    (rowMatrixOf (a + b) (commonKernelEquiv a b).toLinearMap)

/-- Its actual raw inverse, read from the inverse right-linear operator. -/
def kernelInv (a b : ZMod 8) :
    Hom realDData (rowObject (a + b) (kernelRowParity b a))
      (rowObject (a + b) (kernelRowParity a b)) :=
  rowHom (a + b) (kernelRowParity b a) (kernelRowParity a b)
    (rowMatrixOf (a + b) (commonKernelEquiv a b).symm.toLinearMap)

theorem kernelHom_grade (a b : ZMod 8) : Hom.MemGrade (degree a b) (kernelHom a b) :=
  rowHom_matrixOf_grade (a + b) _ _ _ _ (commonKernelEquiv_grade a b)

theorem kernelInv_grade (a b : ZMod 8) : Hom.MemGrade (degree a b) (kernelInv a b) :=
  rowHom_matrixOf_grade (a + b) _ _ _ _ (commonKernelEquiv_symm_grade a b)

theorem kernelHom_inverse (a b : ZMod 8) :
    Hom.comp (kernelHom a b) (kernelInv a b) =
        Hom.id realDData (rowObject (a + b) (kernelRowParity a b)) ∧
      Hom.comp (kernelInv a b) (kernelHom a b) =
        Hom.id realDData (rowObject (a + b) (kernelRowParity b a)) :=
  rowHom_equiv_inverse (a + b) _ _ (commonKernelEquiv a b) (commonKernelEquiv_right a b)

/-- Odd types really require an odd exchange. -/
example : Hom.MemGrade 1 (kernelHom 1 1) := kernelHom_grade 1 1

/-- An odd/even pair has even exchange, and its inverse is an actual raw morphism. -/
example : Hom.comp (kernelHom 1 4) (kernelInv 1 4) =
    Hom.id realDData (rowObject (1 + 4) (kernelRowParity 1 4)) :=
  (kernelHom_inverse 1 4).1

end RMod.BrundanEllis.Stacking.ReferenceCommutor
