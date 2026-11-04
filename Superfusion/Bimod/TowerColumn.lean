/-
Superfusion / Bimod / TowerColumn

Milestone M8a-7c-2: **the concrete column bimodules of the standard
tower** — the paper's `C_{a,b}` (§4.1).  For `a b : ZMod 8`,

  `TowerColumn K a b := (Fin p ⊕ Fin q) → T_{a+b}`,

the column space of the fused matrix superalgebra
`M_{p|q}(T_{a+b})` (with `(p,q) = fuseSize a b`), carrying

* the right `T_{a+b}`-action (coefficientwise, from M8a-6a),
* the left `(T_a ⊗̂ T_b)`-action, pulled back from the matrix action
  along the table isomorphism `stdFuse a b` (M7d-5b),
* the two **slot actions** of `T_a` and `T_b` (through
  `includeLeft`/`includeRight`), which supercommute
  (`TowerColumn.superCommSMul` via M8a-7c-1) — the input for the
  signed middle action when this column is the second factor of a
  `B_L`-type fusion,

all graded for the column grading (gradedness of the pullbacks comes
from `SuperAlgEquiv.map_grading`).  All structure is declared as
instances on the dedicated type synonym; the index patterns
(`a`-slot / `b`-slot / full ᵍ⊗ / coefficients) are syntactically
distinct, so no diamonds arise in the generic development.
-/
import Superfusion.Bimod.ColumnSimple
import Superfusion.Bimod.GtensorSlots
import Superfusion.Super.TowerStd

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]

/-- The index type of the fused matrix superalgebra. -/
abbrev fuseIdx (a b : ZMod 8) : Type :=
  Fin (fuseSize a b).1 ⊕ Fin (fuseSize a b).2

/-- Its parity function. -/
abbrev fuseParity (a b : ZMod 8) : fuseIdx a b → ZMod 2 :=
  sumParity (fuseSize a b).1 (fuseSize a b).2

/-- **The tower column bimodule** `C_{a,b}` (§4.1): the column space of
the fused matrix superalgebra. -/
def TowerColumn (a b : ZMod 8) : Type _ :=
  fuseIdx a b → (stdTower (K := K) (a + b)).carrier

namespace TowerColumn

variable (a b : ZMod 8)

noncomputable instance : AddCommGroup (TowerColumn K a b) :=
  inferInstanceAs
    (AddCommGroup (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

noncomputable instance : Module K (TowerColumn K a b) :=
  inferInstanceAs
    (Module K (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

/-- The left action of the fused matrix superalgebra (`mulVec`). -/
noncomputable instance : Module
    ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).carrier
    (TowerColumn K a b) :=
  inferInstanceAs
    (Module (Matrix (fuseIdx a b) (fuseIdx a b)
        (stdTower (K := K) (a + b)).carrier)
      (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

/-- The matrix action in its raw spelling (both spellings are the same
instance; registered separately for instance search). -/
noncomputable instance : Module
    (Matrix (fuseIdx a b) (fuseIdx a b) (stdTower (K := K) (a + b)).carrier)
    (TowerColumn K a b) :=
  inferInstanceAs
    (Module (Matrix (fuseIdx a b) (fuseIdx a b)
        (stdTower (K := K) (a + b)).carrier)
      (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

/-- The right action of the coefficients. -/
noncomputable instance : Module ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ
    (TowerColumn K a b) :=
  inferInstanceAs
    (Module ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ
      (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

instance : IsScalarTower K ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ
    (TowerColumn K a b) :=
  inferInstanceAs
    (IsScalarTower K ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ
      (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

/-- The column grading of `C_{a,b}`. -/
noncomputable abbrev grading : ZMod 2 → Submodule K (TowerColumn K a b) :=
  columnGrading (fuseParity a b) (stdTower (K := K) (a + b)).grading

noncomputable instance : DirectSum.Decomposition (grading K a b) :=
  inferInstanceAs (DirectSum.Decomposition
    (columnGrading (fuseParity a b) (stdTower (K := K) (a + b)).grading))

/-- The right coefficient action is graded (from M8a-6a). -/
instance : GradedRightSMul (stdTower (K := K) (a + b)).grading
    (grading K a b) :=
  inferInstanceAs (GradedRightSMul (stdTower (K := K) (a + b)).grading
    (columnGrading (fuseParity a b) (stdTower (K := K) (a + b)).grading))

/-! ### The pulled-back left actions -/

/-- The left `(T_a ⊗̂ T_b)`-action, through the table isomorphism. -/
noncomputable instance : Module
    ((stdTower (K := K) a).gtensor (stdTower b)).carrier
    (TowerColumn K a b) :=
  Module.compHom _ ((stdFuse (K := K) a b).toAlgEquiv.toAlgHom.toRingHom)

theorem gtensor_smul_def
    (w : ((stdTower (K := K) a).gtensor (stdTower b)).carrier)
    (v : TowerColumn K a b) :
    w • v = ((stdFuse (K := K) a b).toAlgEquiv w) • v := rfl

/-- Bridge: the `(T_a ⊗̂ T_b)`-action in the raw ᵍ⊗ spelling. -/
noncomputable instance : Module
    ((stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)
    (TowerColumn K a b) :=
  inferInstanceAs (Module
    ((stdTower (K := K) a).gtensor (stdTower b)).carrier
    (TowerColumn K a b))

/-- The `a`-slot action of `T_a` (through `x ↦ x ᵍ⊗ 1` and the table
isomorphism). -/
noncomputable instance : Module (stdTower (K := K) a).carrier
    (TowerColumn K a b) :=
  Module.compHom _
    (((stdFuse (K := K) a b).toAlgEquiv.toAlgHom.comp
      (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading)).toRingHom)

theorem lslot_smul_def (x : (stdTower (K := K) a).carrier)
    (v : TowerColumn K a b) :
    x • v = ((stdFuse (K := K) a b).toAlgEquiv
      (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading x)) • v := rfl

/-- The `b`-slot action of `T_b` (through `y ↦ 1 ᵍ⊗ y`). -/
noncomputable instance : Module (stdTower (K := K) b).carrier
    (TowerColumn K a b) :=
  Module.compHom _
    (((stdFuse (K := K) a b).toAlgEquiv.toAlgHom.comp
      (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading)).toRingHom)

theorem rslot_smul_def (y : (stdTower (K := K) b).carrier)
    (v : TowerColumn K a b) :
    y • v = ((stdFuse (K := K) a b).toAlgEquiv
      (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading y)) • v := rfl

/-- **The two slot actions supercommute** (via M8a-7c-1) — the
`SuperCommSMul` input of the signed middle action. -/
theorem superCommSMul :
    SuperCommSMul (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading (TowerColumn K a b) :=
  fun _ _ _ _ hx hc n =>
    superCommSMul_of_algHom (stdTower (K := K) a).grading
      (stdTower (K := K) b).grading
      (stdFuse (K := K) a b).toAlgEquiv.toAlgHom hx hc n

/-- Bridge: the matrix action is graded over the synonym (the
`ColumnBimod` instance, transported along the definitional equality of
carriers). -/
noncomputable instance : SetLike.GradedSMul
    (matrixGradingA (fuseParity a b) (stdTower (K := K) (a + b)).grading)
    (grading K a b) :=
  inferInstanceAs (SetLike.GradedSMul
    (matrixGradingA (fuseParity a b) (stdTower (K := K) (a + b)).grading)
    (columnGrading (fuseParity a b) (stdTower (K := K) (a + b)).grading))

/-! ### Gradedness and commutation of the pulled-back actions -/

/-- Transport of matrix membership along the table isomorphism. -/
theorem stdFuse_mem_matrixGrading {i : ZMod 2}
    {w : ((stdTower (K := K) a).gtensor (stdTower b)).carrier}
    (hw : w ∈ ((stdTower (K := K) a).gtensor (stdTower b)).grading i) :
    (stdFuse (K := K) a b).toAlgEquiv w
      ∈ matrixGradingA (fuseParity a b)
          (stdTower (K := K) (a + b)).grading i := by
  have h := Submodule.mem_map_of_mem
    (f := (stdFuse (K := K) a b).toAlgEquiv.toLinearMap) hw
  rwa [(stdFuse (K := K) a b).map_grading i] at h

/-- The full `(T_a ⊗̂ T_b)`-action is graded. -/
instance : SetLike.GradedSMul
    ((stdTower (K := K) a).gtensor (stdTower b)).grading
    (grading K a b) where
  smul_mem {i j} w v hw hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (fuseParity a b)
      (stdTower (K := K) (a + b)).grading
      (stdFuse_mem_matrixGrading K a b hw) hv

/-- The `a`-slot action is graded. -/
instance : SetLike.GradedSMul (stdTower (K := K) a).grading
    (grading K a b) where
  smul_mem {i j} x v hx hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (fuseParity a b)
      (stdTower (K := K) (a + b)).grading
      (stdFuse_mem_matrixGrading K a b
        (includeLeft_mem_tensorGrading _ _ hx)) hv

/-- The `b`-slot action is graded. -/
instance : SetLike.GradedSMul (stdTower (K := K) b).grading
    (grading K a b) where
  smul_mem {i j} y v hy hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (fuseParity a b)
      (stdTower (K := K) (a + b)).grading
      (stdFuse_mem_matrixGrading K a b
        (includeRight_mem_tensorGrading _ _ hy)) hv

/-- Bridge: commutation and tower for the bundled matrix spelling. -/
noncomputable instance : SMulCommClass
    ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).carrier
    ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ (TowerColumn K a b) :=
  inferInstanceAs (SMulCommClass
    (Matrix (fuseIdx a b) (fuseIdx a b) (stdTower (K := K) (a + b)).carrier)
    ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ
    (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

noncomputable instance : IsScalarTower K
    ((stdTower (K := K) (a + b)).matrixSuper (fuseSize a b).1
      (fuseSize a b).2).carrier (TowerColumn K a b) :=
  inferInstanceAs (IsScalarTower K
    (Matrix (fuseIdx a b) (fuseIdx a b) (stdTower (K := K) (a + b)).carrier)
    (fuseIdx a b → (stdTower (K := K) (a + b)).carrier))

/-- The pulled-back actions strictly commute with the coefficient
action (sign-free bimodule axioms). -/
instance : SMulCommClass
    ((stdTower (K := K) a).gtensor (stdTower b)).carrier
    ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ (TowerColumn K a b) where
  smul_comm w d v := smul_comm
    (((stdFuse (K := K) a b).toAlgEquiv w :
      Matrix (fuseIdx a b) (fuseIdx a b)
        (stdTower (K := K) (a + b)).carrier)) d
    (v : fuseIdx a b → (stdTower (K := K) (a + b)).carrier)

instance : SMulCommClass (stdTower (K := K) a).carrier
    ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ (TowerColumn K a b) where
  smul_comm x d v := smul_comm
    (((stdFuse (K := K) a b).toAlgEquiv
      (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading x) :
      Matrix (fuseIdx a b) (fuseIdx a b)
        (stdTower (K := K) (a + b)).carrier)) d
    (v : fuseIdx a b → (stdTower (K := K) (a + b)).carrier)

instance : SMulCommClass (stdTower (K := K) b).carrier
    ((stdTower (K := K) (a + b)).carrier)ᵐᵒᵖ (TowerColumn K a b) where
  smul_comm y d v := smul_comm
    (((stdFuse (K := K) a b).toAlgEquiv
      (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading y) :
      Matrix (fuseIdx a b) (fuseIdx a b)
        (stdTower (K := K) (a + b)).carrier)) d
    (v : fuseIdx a b → (stdTower (K := K) (a + b)).carrier)

instance : IsScalarTower K
    ((stdTower (K := K) a).gtensor (stdTower b)).carrier
    (TowerColumn K a b) where
  smul_assoc k w v := by
    rw [gtensor_smul_def, map_smul]
    exact smul_assoc k _ _

noncomputable instance : IsScalarTower K
    ((stdTower (K := K) a).grading ᵍ⊗[K] (stdTower (K := K) b).grading)
    (TowerColumn K a b) :=
  inferInstanceAs (IsScalarTower K
    ((stdTower (K := K) a).gtensor (stdTower b)).carrier
    (TowerColumn K a b))


instance : IsScalarTower K (stdTower (K := K) a).carrier
    (TowerColumn K a b) where
  smul_assoc k x v := by
    show (GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading (k • x)) • v
      = k • ((GradedTensorProduct.includeLeft (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading x) • v)
    rw [map_smul]
    exact smul_assoc k (GradedTensorProduct.includeLeft
      (stdTower (K := K) a).grading (stdTower (K := K) b).grading x) v

instance : IsScalarTower K (stdTower (K := K) b).carrier
    (TowerColumn K a b) where
  smul_assoc k y v := by
    show (GradedTensorProduct.includeRight (stdTower (K := K) a).grading
        (stdTower (K := K) b).grading (k • y)) • v
      = k • ((GradedTensorProduct.includeRight (stdTower (K := K) a).grading
          (stdTower (K := K) b).grading y) • v)
    rw [map_smul]
    exact smul_assoc k (GradedTensorProduct.includeRight
      (stdTower (K := K) a).grading (stdTower (K := K) b).grading y) v

end TowerColumn

end Bimod

end Superfusion
