import RMod.BrundanEllis.StackingReferenceNormalization

/-! Properties of the inverse normalized exchange, needed when the chosen
exterior comparison uses the opposite crossing orientation. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

/-- Equality transports of coefficient algebras compose without a new choice. -/
theorem coefficientCast_trans {a b c : ZMod 8} (h : a = b) (k : b = c) (x : Coeff a) :
    coefficientCast k (coefficientCast h x) = coefficientCast (h.trans k) x := by
  cases h
  cases k
  rfl

/-- The inverse normalized exchange has the same signed input naturality. -/
theorem normalizedKernelEquiv_symm_naturality (a b : ZMod 8) {i j : ZMod 2}
    (x : Coeff a) (y : Coeff b)
    (hx : (realDData.algebra a).MemGrade i x) (hy : (realDData.algebra b).MemGrade j y)
    (v : RealCCarrier b a) :
    (normalizedKernelEquiv a b).symm (leftOperator b a y x v) =
      paritySign (degree a b * (i + j) + i * j) •
        leftOperator a b x y ((normalizedKernelEquiv a b).symm v) := by
  apply (normalizedKernelEquiv a b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, normalizedKernelEquiv_naturality a b x y hx hy,
    LinearEquiv.apply_symm_apply, smul_smul, shiftParitySign_mul_self, one_smul]

/-- The inverse exchange also respects the actual endpoint right action. -/
theorem normalizedKernelEquiv_symm_right_linear (a b : ZMod 8) (v : RealCCarrier b a)
    (x : Coeff (b + a)) :
    (normalizedKernelEquiv a b).symm (realCRight b a v x) =
      realCRight a b ((normalizedKernelEquiv a b).symm v) (coefficientCast (add_comm b a) x) := by
  apply (normalizedKernelEquiv a b).injective
  rw [LinearEquiv.apply_symm_apply, normalizedKernelEquiv_right_linear,
    LinearEquiv.apply_symm_apply, coefficientCast_trans]
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
