import Superfusion.RMod.FromRawDCT.Category
import Superfusion.RMod.RawDCT.Shift

/-!
# Tensor data from a raw binary kernel

This abstract file defines tensor data, its laws, and the completed tensor
structure on the finite coordinate envelope.  The canonical executable
construction depends only on `DData` and `CData`; ternary connector data is
irrelevant to the tensor bifunctor itself.

The parity of a tensor summand is the stored `dC.rowParity`, and its
coefficient map is the stored `dC.leftCoeff`.  In particular, no separate
`nu`, `beta`, or concrete real table is applied here.

The only additional signs are those forced by the parity shifts attached to
the source and target atoms.  They are expressed through `routeRowTwist` on
the two input coefficients and one scalar Koszul sign.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Abstract tensor structure -/

/-- Executable tensor operations on the finite envelope determined by `dD`.

No coherence proof and no associator or unit data is stored here. -/
structure TensorData (dD : DData) where
  tensorObj : Obj → Obj → Obj
  tensorHom : {X₁ Y₁ X₂ Y₂ : Obj} →
    Hom dD X₁ Y₁ → Hom dD X₂ Y₂ →
      Hom dD (tensorObj X₁ X₂) (tensorObj Y₁ Y₂)

/-- The seven laws saying that the stored operations form a real-linear
graded tensor bifunctor with the super interchange sign. -/
structure TensorLaws (dD : DData) (_hD : DLaws dD)
    (d : TensorData dD) : Prop where
  tensor_grade : ∀ {X₁ Y₁ X₂ Y₂ a b}
    (f : Hom dD X₁ Y₁) (g : Hom dD X₂ Y₂),
    Hom.MemGrade a f → Hom.MemGrade b g →
      Hom.MemGrade (a + b) (d.tensorHom f g)
  tensor_id : ∀ X Y,
    d.tensorHom (Hom.id dD X) (Hom.id dD Y) =
      Hom.id dD (d.tensorObj X Y)
  tensor_add_left : ∀ {X₁ Y₁ X₂ Y₂}
    (f f' : Hom dD X₁ Y₁) (g : Hom dD X₂ Y₂),
    d.tensorHom (Hom.add f f') g =
      Hom.add (d.tensorHom f g) (d.tensorHom f' g)
  tensor_add_right : ∀ {X₁ Y₁ X₂ Y₂}
    (f : Hom dD X₁ Y₁) (g g' : Hom dD X₂ Y₂),
    d.tensorHom f (Hom.add g g') =
      Hom.add (d.tensorHom f g) (d.tensorHom f g')
  tensor_smul_left : ∀ {X₁ Y₁ X₂ Y₂} (r : ℝ)
    (f : Hom dD X₁ Y₁) (g : Hom dD X₂ Y₂),
    d.tensorHom (Hom.smul r f) g = Hom.smul r (d.tensorHom f g)
  tensor_smul_right : ∀ {X₁ Y₁ X₂ Y₂} (r : ℝ)
    (f : Hom dD X₁ Y₁) (g : Hom dD X₂ Y₂),
    d.tensorHom f (Hom.smul r g) = Hom.smul r (d.tensorHom f g)
  super_interchange : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ b c}
    (f : Hom dD Y₁ Z₁) (g : Hom dD Y₂ Z₂)
    (h : Hom dD X₁ Y₁) (k : Hom dD X₂ Y₂),
    Hom.MemGrade b g → Hom.MemGrade c h →
      Hom.comp (d.tensorHom h k) (d.tensorHom f g) =
        Hom.smul ((-1 : ℝ) ^ (b * c).val)
          (d.tensorHom (Hom.comp h f) (Hom.comp k g))

/-- Completed tensor structure over a completed coefficient algebra family. -/
structure Tensor (D : D) where
  data : TensorData D.data
  laws : TensorLaws D.data D.laws data

namespace Tensor

/-! ## Canonical tensor summands -/

/-- The provenance of one summand in the tensor of two finite objects.

This is a dependent product rather than a new record: it consists only of
the left object index, the right object index, and one stored row of the
corresponding raw fusion kernel. -/
abbrev Slot (dD : DData) (dC : CData dD) (X Y : Obj) :=
  (i : Fin X.size) ×
    (j : Fin Y.size) ×
      dC.Index (X.atom i).label (Y.atom j).label

namespace Slot

def left {dD : DData} {dC : CData dD} {X Y : Obj}
    (q : Slot dD dC X Y) : Fin X.size :=
  q.1

def right {dD : DData} {dC : CData dD} {X Y : Obj}
    (q : Slot dD dC X Y) : Fin Y.size :=
  q.2.1

def fusion {dD : DData} {dC : CData dD} {X Y : Obj}
    (q : Slot dD dC X Y) :
    dC.Index (X.atom q.left).label (Y.atom q.right).label :=
  q.2.2

end Slot

/-- Canonical lexicographic enumeration of tensor summands. -/
def slots (dD : DData) (dC : CData dD) (X Y : Obj) :
    List (Slot dD dC X Y) :=
  (List.ofFn fun i : Fin X.size => i).sigma fun i =>
    (List.ofFn fun j : Fin Y.size => j).sigma fun j =>
      List.ofFn fun r : dC.Index (X.atom i).label (Y.atom j).label => r

/-- Every tensor slot occurs exactly once in the canonical enumeration. -/
theorem slots_nodup (dD : DData) (dC : CData dD) (X Y : Obj) :
    (slots dD dC X Y).Nodup := by
  unfold slots
  apply (List.nodup_ofFn.mpr Function.injective_id).sigma
  intro i
  apply (List.nodup_ofFn.mpr Function.injective_id).sigma
  intro j
  exact List.nodup_ofFn.mpr Function.injective_id

/-- The atom carried by one tensor slot.

The raw kernel row parity is already the shifted parity when `dC` is a
shifted raw DCT, so it is inserted exactly once. -/
def slotAtom (dD : DData) (dC : CData dD) (X Y : Obj)
    (q : Slot dD dC X Y) : Atom :=
  ((X.atom q.left).label + (Y.atom q.right).label,
    (X.atom q.left).shift + (Y.atom q.right).shift +
      dC.rowParity (X.atom q.left).label (Y.atom q.right).label q.fusion)

/-- Tensor product of finite coordinate objects. -/
def obj (dD : DData) (dC : CData dD) (X Y : Obj) : Obj :=
  ⟨(slots dD dC X Y).length,
    fun q => slotAtom dD dC X Y ((slots dD dC X Y).get q)⟩

/-! ## Tensor coefficients -/

/-- One coefficient of the tensor of two atomic morphisms.

Here `s` is the parity shift of the left source atom, while `t` and `t'`
are the shifts of the right source and target atoms.  The endpoint-shift
formula contributes only

`(-1)^(s * (t + t'))`, `J^(t')` on the left coefficient, and `J^s` on the
right coefficient.

The stored `dC.leftCoeff` is then evaluated exactly once. -/
def coefficient (dD : DData) (dC : CData dD) (a b : ZMod 8)
    (s t t' : ZMod 2) (source target : dC.Index a b)
    (f : (dD.algebra a).carrier) (g : (dD.algebra b).carrier) :
    (dD.algebra (a + b)).carrier :=
  (dD.algebra (a + b)).smul (RawDCT.paritySign (s * (t + t')))
    (dC.leftCoeff a b target source
      (RawDCT.routeRowTwist dD a t' f)
      (RawDCT.routeRowTwist dD b s g))

/-! ### Consequences of the stored binary-kernel laws -/

/- The following proof-only instances expose the additive operations of one
raw coefficient algebra.  They are used solely to evaluate a finite row
basis and add no data to the tensor construction. -/

private instance tensorRawZero (d : SuperAlgebraData ℝ) : Zero d.carrier :=
  ⟨d.zero⟩

private instance tensorRawAdd (d : SuperAlgebraData ℝ) : Add d.carrier :=
  ⟨d.add⟩

private instance tensorRawNeg (d : SuperAlgebraData ℝ) : Neg d.carrier :=
  ⟨d.neg⟩

private instance tensorRawScalar (d : SuperAlgebraData ℝ) : SMul ℝ d.carrier :=
  ⟨d.smul⟩

@[implicit_reducible]
private def tensorRawAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier where
  add_assoc := h.add_assoc
  zero_add := h.zero_add
  add_zero := h.add_zero
  neg_add_cancel := h.neg_add
  add_comm := h.add_comm
  sub := fun x y => d.add x (d.neg y)
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

@[implicit_reducible]
private def tensorRawModule (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) :
    letI := tensorRawAddCommGroup d h
    Module ℝ d.carrier := by
  letI := tensorRawAddCommGroup d h
  exact
    { one_smul := h.one_smul
      mul_smul := h.smul_assoc
      smul_add := h.smul_add
      smul_zero := h.smul_zero
      add_smul := h.add_smul
      zero_smul := h.zero_smul }

private theorem rawMulZero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    d.mul x d.zero = d.zero := by
  letI := tensorRawAddCommGroup d h
  let v := d.mul x d.zero
  have hm := h.mul_add x d.zero d.zero
  rw [h.zero_add] at hm
  change v = d.add v v at hm
  apply add_left_cancel (a := v)
  change d.add v v = d.add v d.zero
  rw [← hm, h.add_zero]

/-- A coordinate sum supported on one fusion row evaluates to that row. -/
private theorem rawFinSum_mul_single (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {m : ℕ} (source : Fin m)
    (f : Fin m → d.carrier) :
    CData.rawFinSum d (fun r =>
      d.mul (f r) (if r = source then d.one else d.zero)) = f source := by
  letI := tensorRawAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn fun r =>
    d.mul (f r) (if r = source then d.one else d.zero)).sum = f source
  rw [List.sum_ofFn]
  classical
  simp only [apply_ite, rawMulZero d h, h.mul_one]
  change (∑ r, if r = source then f r else (0 : d.carrier)) = f source
  simp

private theorem rawFinSum_smul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {m : ℕ} (q : ℝ) (f : Fin m → d.carrier) :
    CData.rawFinSum d (fun i => d.smul q (f i)) =
      d.smul q (CData.rawFinSum d f) := by
  letI := tensorRawAddCommGroup d h
  letI := tensorRawModule d h
  unfold CData.rawFinSum
  change (List.ofFn (fun i => q • f i)).sum = q • (List.ofFn f).sum
  rw [List.sum_ofFn, List.sum_ofFn, Finset.smul_sum]

/-- The module vector with coefficient one at exactly one fusion row. -/
private def kernelRowBasis (dD : DData) (dC : CData dD)
    (a b : ZMod 8) (source : dC.Index a b) : dC.carrier a b :=
  dC.ofCoord a b fun r =>
    if r = source then (dD.algebra (a + b)).one
    else (dD.algebra (a + b)).zero

private theorem kernelRowBasis_toCoord (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (source : dC.Index a b) :
    dC.toCoord a b (kernelRowBasis dD dC a b source) = fun r =>
      if r = source then (dD.algebra (a + b)).one
      else (dD.algebra (a + b)).zero := by
  exact hC.toCoord_ofCoord a b _

/-- Evaluating the action on a row basis recovers one stored coefficient. -/
private theorem leftCoeff_on_rowBasis (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.toCoord a b
        (dC.left a b x y (kernelRowBasis dD dC a b source)) target =
      dC.leftCoeff a b target source x y := by
  rw [hC.toCoord_left,
    kernelRowBasis_toCoord dD hD dC hC]
  exact rawFinSum_mul_single (dD.algebra (a + b))
    (hD.algebra_laws (a + b)) source
    (fun r => dC.leftCoeff a b target r x y)

private theorem leftCoeff_add_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x x' : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).add x x') y =
      (dD.algebra (a + b)).add
        (dC.leftCoeff a b target source x y)
        (dC.leftCoeff a b target source x' y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_add_left a b x x' y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_add] at h
  change dC.leftCoeff a b target source ((dD.algebra a).add x x') y =
    (dD.algebra (a + b)).add
      (dC.toCoord a b (dC.left a b x y m) target)
      (dC.toCoord a b (dC.left a b x' y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC,
    leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_add_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b)
    (x : (dD.algebra a).carrier) (y y' : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source x ((dD.algebra b).add y y') =
      (dD.algebra (a + b)).add
        (dC.leftCoeff a b target source x y)
        (dC.leftCoeff a b target source x y') := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_add_right a b x y y' m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_add] at h
  change dC.leftCoeff a b target source x ((dD.algebra b).add y y') =
    (dD.algebra (a + b)).add
      (dC.toCoord a b (dC.left a b x y m) target)
      (dC.toCoord a b (dC.left a b x y' m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC,
    leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_smul_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b) (r : ℝ)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).smul r x) y =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source x y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_smul_left a b r x y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_smul] at h
  change dC.leftCoeff a b target source ((dD.algebra a).smul r x) y =
    (dD.algebra (a + b)).smul r
      (dC.toCoord a b (dC.left a b x y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

private theorem leftCoeff_smul_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b) (r : ℝ)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source x ((dD.algebra b).smul r y) =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source x y) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_smul_right a b r x y m)
  rw [leftCoeff_on_rowBasis dD hD dC hC, hC.toCoord_smul] at h
  change dC.leftCoeff a b target source x ((dD.algebra b).smul r y) =
    (dD.algebra (a + b)).smul r
      (dC.toCoord a b (dC.left a b x y m) target) at h
  rw [leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

/-- The action of two algebra units is the identity matrix in the stored
fusion-row basis. -/
private theorem leftCoeff_one (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (target source : dC.Index a b) :
    dC.leftCoeff a b target source
        (dD.algebra a).one (dD.algebra b).one =
      if target = source then (dD.algebra (a + b)).one
      else (dD.algebra (a + b)).zero := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_one a b m)
  rw [leftCoeff_on_rowBasis dD hD dC hC,
    kernelRowBasis_toCoord dD hD dC hC] at h
  exact h

private theorem routeRowTwist_add_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2)
    (x y : (dD.algebra a).carrier) :
    RawDCT.routeRowTwist dD a p ((dD.algebra a).add x y) =
      (dD.algebra a).add (RawDCT.routeRowTwist dD a p x)
        (RawDCT.routeRowTwist dD a p y) :=
  RawDCT.routeRowTwist_add (dD.algebra a) (hD.algebra_laws a) p x y

private theorem routeRowTwist_smul_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) (r : ℝ)
    (x : (dD.algebra a).carrier) :
    RawDCT.routeRowTwist dD a p ((dD.algebra a).smul r x) =
      (dD.algebra a).smul r (RawDCT.routeRowTwist dD a p x) :=
  RawDCT.routeRowTwist_smul (dD.algebra a) (hD.algebra_laws a) p r x

private theorem routeRowTwist_memGrade_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    (dD.algebra a).MemGrade i (RawDCT.routeRowTwist dD a p x) :=
  RawDCT.routeRowTwist_memGrade
    (dD.algebra a) (hD.algebra_laws a) p i x hx

private theorem routeRowTwist_of_memGrade_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    RawDCT.routeRowTwist dD a p x =
      (dD.algebra a).smul (RawDCT.paritySign (p * i)) x :=
  RawDCT.routeRowTwist_of_memGrade
    (dD.algebra a) (hD.algebra_laws a) p i x hx

/-- Changing the twist exponent on a homogeneous coefficient contributes
the sign of the difference, which equals the sum in `ZMod 2`. -/
private theorem routeRowTwist_change_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (p q i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    RawDCT.routeRowTwist dD a p x =
      (dD.algebra a).smul (RawDCT.paritySign ((p + q) * i))
        (RawDCT.routeRowTwist dD a q x) := by
  rw [routeRowTwist_of_memGrade_at dD hD a p i x hx,
    routeRowTwist_of_memGrade_at dD hD a q i x hx,
    ← (hD.algebra_laws a).smul_assoc]
  congr 1
  rw [← RawDCT.shiftParitySign_add]
  congr 1
  calc
    p * i = p * i + 0 := (add_zero _).symm
    _ = p * i + (q * i + q * i) := by rw [ZModModule.add_self]
    _ = (p + q) * i + q * i := by ring

private theorem routeRowTwist_mul_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (p : ZMod 2) (x y : (dD.algebra a).carrier) :
    RawDCT.routeRowTwist dD a p ((dD.algebra a).mul x y) =
      (dD.algebra a).mul (RawDCT.routeRowTwist dD a p x)
        (RawDCT.routeRowTwist dD a p y) :=
  RawDCT.routeRowTwist_mul
    (dD.algebra a) (hD.algebra_laws a) p x y

private theorem routeRowTwist_one_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) :
    RawDCT.routeRowTwist dD a p (dD.algebra a).one =
      (dD.algebra a).one :=
  RawDCT.routeRowTwist_one (dD.algebra a) (hD.algebra_laws a) p

/-- The coefficient formula is homogeneous in the two input coefficients,
with the source and target row parities contributing to its degree. -/
theorem coefficient_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b) (i j : ZMod 2)
    (f : (dD.algebra a).carrier) (g : (dD.algebra b).carrier)
    (hf : (dD.algebra a).MemGrade i f)
    (hg : (dD.algebra b).MemGrade j g) :
    (dD.algebra (a + b)).MemGrade
      (i + j + dC.rowParity a b source + dC.rowParity a b target)
      (coefficient dD dC a b s t t' source target f g) := by
  have hf' := routeRowTwist_memGrade_at dD hD a t' i f hf
  have hg' := routeRowTwist_memGrade_at dD hD b s j g hg
  have hc := RawDCT.leftCoeff_memGrade dD hD dC hC
    a b target source i j
    (RawDCT.routeRowTwist dD a t' f)
    (RawDCT.routeRowTwist dD b s g) hf' hg'
  unfold coefficient
  unfold SuperAlgebraData.MemGrade at hc ⊢
  rw [(hD.algebra_laws (a + b)).component_smul, hc]

/-- Tensor coefficients are additive in the first input. -/
theorem coefficient_add_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b)
    (f f' : (dD.algebra a).carrier) (g : (dD.algebra b).carrier) :
    coefficient dD dC a b s t t' source target
        ((dD.algebra a).add f f') g =
      (dD.algebra (a + b)).add
        (coefficient dD dC a b s t t' source target f g)
        (coefficient dD dC a b s t t' source target f' g) := by
  unfold coefficient
  rw [routeRowTwist_add_at dD hD,
    leftCoeff_add_left dD hD dC hC,
    (hD.algebra_laws (a + b)).smul_add]

/-- Tensor coefficients are additive in the second input. -/
theorem coefficient_add_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b)
    (f : (dD.algebra a).carrier) (g g' : (dD.algebra b).carrier) :
    coefficient dD dC a b s t t' source target f
        ((dD.algebra b).add g g') =
      (dD.algebra (a + b)).add
        (coefficient dD dC a b s t t' source target f g)
        (coefficient dD dC a b s t t' source target f g') := by
  unfold coefficient
  rw [routeRowTwist_add_at dD hD,
    leftCoeff_add_right dD hD dC hC,
    (hD.algebra_laws (a + b)).smul_add]

/-- Tensor coefficients commute with scalar multiplication in the first
input. -/
theorem coefficient_smul_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b) (r : ℝ)
    (f : (dD.algebra a).carrier) (g : (dD.algebra b).carrier) :
    coefficient dD dC a b s t t' source target
        ((dD.algebra a).smul r f) g =
      (dD.algebra (a + b)).smul r
        (coefficient dD dC a b s t t' source target f g) := by
  unfold coefficient
  rw [routeRowTwist_smul_at dD hD,
    leftCoeff_smul_left dD hD dC hC]
  let sign := RawDCT.paritySign (s * (t + t'))
  let z := dC.leftCoeff a b target source
    (RawDCT.routeRowTwist dD a t' f)
    (RawDCT.routeRowTwist dD b s g)
  change (dD.algebra (a + b)).smul sign
      ((dD.algebra (a + b)).smul r z) =
    (dD.algebra (a + b)).smul r
      ((dD.algebra (a + b)).smul sign z)
  rw [← (hD.algebra_laws (a + b)).smul_assoc,
    ← (hD.algebra_laws (a + b)).smul_assoc, mul_comm]

/-- Tensor coefficients commute with scalar multiplication in the second
input. -/
theorem coefficient_smul_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b) (r : ℝ)
    (f : (dD.algebra a).carrier) (g : (dD.algebra b).carrier) :
    coefficient dD dC a b s t t' source target f
        ((dD.algebra b).smul r g) =
      (dD.algebra (a + b)).smul r
        (coefficient dD dC a b s t t' source target f g) := by
  unfold coefficient
  rw [routeRowTwist_smul_at dD hD,
    leftCoeff_smul_right dD hD dC hC]
  let sign := RawDCT.paritySign (s * (t + t'))
  let z := dC.leftCoeff a b target source
    (RawDCT.routeRowTwist dD a t' f)
    (RawDCT.routeRowTwist dD b s g)
  change (dD.algebra (a + b)).smul sign
      ((dD.algebra (a + b)).smul r z) =
    (dD.algebra (a + b)).smul r
      ((dD.algebra (a + b)).smul sign z)
  rw [← (hD.algebra_laws (a + b)).smul_assoc,
    ← (hD.algebra_laws (a + b)).smul_assoc, mul_comm]

/-- A zero first input gives a zero tensor coefficient. -/
theorem coefficient_zero_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b) (g : (dD.algebra b).carrier) :
    coefficient dD dC a b s t t' source target (dD.algebra a).zero g =
      (dD.algebra (a + b)).zero := by
  calc
    _ = coefficient dD dC a b s t t' source target
        ((dD.algebra a).smul 0 (dD.algebra a).one) g := by
      rw [(hD.algebra_laws a).zero_smul]
    _ = (dD.algebra (a + b)).smul 0
        (coefficient dD dC a b s t t' source target
          (dD.algebra a).one g) :=
      coefficient_smul_left dD hD dC hC _ _ _ _ _ _ _ _ _ _
    _ = _ := (hD.algebra_laws (a + b)).zero_smul _

/-- A zero second input gives a zero tensor coefficient. -/
theorem coefficient_zero_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t t' : ZMod 2)
    (source target : dC.Index a b) (f : (dD.algebra a).carrier) :
    coefficient dD dC a b s t t' source target f (dD.algebra b).zero =
      (dD.algebra (a + b)).zero := by
  calc
    _ = coefficient dD dC a b s t t' source target f
        ((dD.algebra b).smul 0 (dD.algebra b).one) := by
      rw [(hD.algebra_laws b).zero_smul]
    _ = (dD.algebra (a + b)).smul 0
        (coefficient dD dC a b s t t' source target f
          (dD.algebra b).one) :=
      coefficient_smul_right dD hD dC hC _ _ _ _ _ _ _ _ _ _
    _ = _ := (hD.algebra_laws (a + b)).zero_smul _

/-- On two unit coefficients with unchanged endpoint shifts, the tensor
coefficient is the identity matrix on fusion rows. -/
theorem coefficient_one (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s t : ZMod 2) (source target : dC.Index a b) :
    coefficient dD dC a b s t t source target
        (dD.algebra a).one (dD.algebra b).one =
      if target = source then (dD.algebra (a + b)).one
      else (dD.algebra (a + b)).zero := by
  unfold coefficient
  rw [routeRowTwist_one_at dD hD, routeRowTwist_one_at dD hD]
  have hsign : s * (t + t) = 0 := by
    rw [ZModModule.add_self, mul_zero]
  rw [hsign, RawDCT.shiftParitySign_zero,
    (hD.algebra_laws (a + b)).one_smul]
  exact leftCoeff_one dD hD dC hC a b target source

/-! ### Coefficient-level super-interchange -/

/-- Matrix coefficients of the stored binary action compose by the
super-interchange convolution.  This is obtained from `CLaws.left_mul` by
acting on a single fusion-row basis and reading one target coordinate. -/
private theorem leftCoeff_mul (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (i j : ZMod 2)
    (source target : dC.Index a b)
    (x x' : (dD.algebra a).carrier)
    (y y' : (dD.algebra b).carrier)
    (hy : (dD.algebra b).MemGrade j y)
    (hx' : (dD.algebra a).MemGrade i x') :
    CData.rawFinSum (dD.algebra (a + b)) (fun middle =>
      (dD.algebra (a + b)).mul
        (dC.leftCoeff a b target middle x y)
        (dC.leftCoeff a b middle source x' y')) =
      (dD.algebra (a + b)).smul (RawDCT.paritySign (j * i))
        (dC.leftCoeff a b target source
          ((dD.algebra a).mul x x') ((dD.algebra b).mul y y')) := by
  let m := kernelRowBasis dD dC a b source
  have h := congrArg (fun q => dC.toCoord a b q target)
    (hC.left_mul a b i j x x' y y' m hy hx')
  rw [hC.toCoord_left, hC.toCoord_smul] at h
  dsimp [m] at h
  simp_rw [leftCoeff_on_rowBasis dD hD dC hC] at h
  exact h

/- The endpoint-shift signs in two successive coefficients reduce to the
single categorical Koszul sign and the sign of the composite coefficient. -/
private theorem coefficient_comp_sign
    (s0 s1 t0 t1 t2 i j : ZMod 2) :
    (RawDCT.paritySign (s1 * (t1 + t2)) *
        RawDCT.paritySign (s0 * (t0 + t1))) *
        (RawDCT.paritySign ((j + t1 + t2) * (i + s0 + s1)) *
          (RawDCT.paritySign ((t1 + t2) * (i + s0 + s1)) *
            RawDCT.paritySign ((s1 + s0) * (j + t1 + t2)))) =
      RawDCT.paritySign (j * i) *
        RawDCT.paritySign (s0 * (t0 + t2)) := by
  rcases zmod2_cases s0 with hs0 | hs0 <;> subst s0 <;>
    rcases zmod2_cases s1 with hs1 | hs1 <;> subst s1 <;>
      rcases zmod2_cases t0 with ht0 | ht0 <;> subst t0 <;>
        rcases zmod2_cases t1 with ht1 | ht1 <;> subst t1 <;>
          rcases zmod2_cases t2 with ht2 | ht2 <;> subst t2 <;>
            rcases zmod2_cases i with hi | hi <;> subst i <;>
              rcases zmod2_cases j with hj | hj <;> subst j <;>
                simp [RawDCT.paritySign, ZModModule.add_self]

/-- The executable endpoint-shifted coefficients satisfy the coefficient
form of super-interchange. -/
theorem coefficient_comp
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8)
    (s0 s1 t0 t1 t2 i j : ZMod 2)
    (source target : dC.Index a b)
    {x1 x2 : (dD.algebra a).carrier}
    {y1 y2 : (dD.algebra b).carrier}
    (hx1 : (dD.algebra a).MemGrade (i + s0 + s1) x1)
    (hy2 : (dD.algebra b).MemGrade (j + t1 + t2) y2) :
    CData.rawFinSum (dD.algebra (a + b)) (fun middle =>
      (dD.algebra (a + b)).mul
        (coefficient dD dC a b s1 t1 t2 middle target x2 y2)
        (coefficient dD dC a b s0 t0 t1 source middle x1 y1)) =
      (dD.algebra (a + b)).smul (RawDCT.paritySign (j * i))
        (coefficient dD dC a b s0 t0 t2 source target
          ((dD.algebra a).mul x2 x1)
          ((dD.algebra b).mul y2 y1)) := by
  let I := i + s0 + s1
  let J := j + t1 + t2
  let signOuter := RawDCT.paritySign (s1 * (t1 + t2))
  let signInner := RawDCT.paritySign (s0 * (t0 + t1))
  let signX := RawDCT.paritySign ((t1 + t2) * I)
  let signY := RawDCT.paritySign ((s1 + s0) * J)
  let signResult := RawDCT.paritySign (s0 * (t0 + t2))
  have hx1T : (dD.algebra a).MemGrade I
      (RawDCT.routeRowTwist dD a t1 x1) :=
    routeRowTwist_memGrade_at dD hD a t1 I x1 hx1
  have hy2T : (dD.algebra b).MemGrade J
      (RawDCT.routeRowTwist dD b s1 y2) :=
    routeRowTwist_memGrade_at dD hD b s1 J y2 hy2
  have hxmul :
      (dD.algebra a).mul (RawDCT.routeRowTwist dD a t2 x2)
          (RawDCT.routeRowTwist dD a t1 x1) =
        (dD.algebra a).smul signX
          (RawDCT.routeRowTwist dD a t2 ((dD.algebra a).mul x2 x1)) := by
    rw [routeRowTwist_change_at dD hD a t1 t2 I x1 hx1,
      (hD.algebra_laws a).mul_smul,
      routeRowTwist_mul_at dD hD a t2]
  have hymul :
      (dD.algebra b).mul (RawDCT.routeRowTwist dD b s1 y2)
          (RawDCT.routeRowTwist dD b s0 y1) =
        (dD.algebra b).smul signY
          (RawDCT.routeRowTwist dD b s0 ((dD.algebra b).mul y2 y1)) := by
    rw [routeRowTwist_change_at dD hD b s1 s0 J y2 hy2,
      (hD.algebra_laws b).smul_mul,
      routeRowTwist_mul_at dD hD b s0]
  unfold coefficient
  calc
    CData.rawFinSum (dD.algebra (a + b)) (fun middle =>
        (dD.algebra (a + b)).mul
          ((dD.algebra (a + b)).smul signOuter
            (dC.leftCoeff a b target middle
              (RawDCT.routeRowTwist dD a t2 x2)
              (RawDCT.routeRowTwist dD b s1 y2)))
          ((dD.algebra (a + b)).smul signInner
            (dC.leftCoeff a b middle source
              (RawDCT.routeRowTwist dD a t1 x1)
              (RawDCT.routeRowTwist dD b s0 y1)))) =
      CData.rawFinSum (dD.algebra (a + b)) (fun middle =>
        (dD.algebra (a + b)).smul (signOuter * signInner)
          ((dD.algebra (a + b)).mul
            (dC.leftCoeff a b target middle
              (RawDCT.routeRowTwist dD a t2 x2)
              (RawDCT.routeRowTwist dD b s1 y2))
            (dC.leftCoeff a b middle source
              (RawDCT.routeRowTwist dD a t1 x1)
              (RawDCT.routeRowTwist dD b s0 y1)))) := by
        congr 1
        funext middle
        rw [(hD.algebra_laws (a + b)).smul_mul,
          (hD.algebra_laws (a + b)).mul_smul,
          ← (hD.algebra_laws (a + b)).smul_assoc]
    _ = (dD.algebra (a + b)).smul (signOuter * signInner)
        (CData.rawFinSum (dD.algebra (a + b)) (fun middle =>
          (dD.algebra (a + b)).mul
            (dC.leftCoeff a b target middle
              (RawDCT.routeRowTwist dD a t2 x2)
              (RawDCT.routeRowTwist dD b s1 y2))
            (dC.leftCoeff a b middle source
              (RawDCT.routeRowTwist dD a t1 x1)
              (RawDCT.routeRowTwist dD b s0 y1)))) :=
      rawFinSum_smul (dD.algebra (a + b))
        (hD.algebra_laws (a + b)) _ _
    _ = (dD.algebra (a + b)).smul (signOuter * signInner)
        ((dD.algebra (a + b)).smul (RawDCT.paritySign (J * I))
          (dC.leftCoeff a b target source
            ((dD.algebra a).mul (RawDCT.routeRowTwist dD a t2 x2)
              (RawDCT.routeRowTwist dD a t1 x1))
            ((dD.algebra b).mul (RawDCT.routeRowTwist dD b s1 y2)
              (RawDCT.routeRowTwist dD b s0 y1)))) := by
      rw [leftCoeff_mul dD hD dC hC a b I J source target
        (RawDCT.routeRowTwist dD a t2 x2)
        (RawDCT.routeRowTwist dD a t1 x1)
        (RawDCT.routeRowTwist dD b s1 y2)
        (RawDCT.routeRowTwist dD b s0 y1) hy2T hx1T]
    _ = (dD.algebra (a + b)).smul (RawDCT.paritySign (j * i))
        ((dD.algebra (a + b)).smul signResult
          (dC.leftCoeff a b target source
            (RawDCT.routeRowTwist dD a t2 ((dD.algebra a).mul x2 x1))
            (RawDCT.routeRowTwist dD b s0 ((dD.algebra b).mul y2 y1)))) := by
      rw [hxmul, hymul,
        leftCoeff_smul_left dD hD dC hC,
        leftCoeff_smul_right dD hD dC hC]
      repeat' rw [← (hD.algebra_laws (a + b)).smul_assoc]
      congr 1
      calc
        (((signOuter * signInner) * RawDCT.paritySign (J * I)) *
            signX) * signY =
            (signOuter * signInner) *
              (RawDCT.paritySign (J * I) * (signX * signY)) := by ring
        _ = RawDCT.paritySign (j * i) * signResult := by
          exact coefficient_comp_sign s0 s1 t0 t1 t2 i j

/-! ## Tensor morphisms -/

/-- One block entry of the tensor of two finite morphism matrices.

If either input atomic morphism changes its label, the corresponding block
is the unique zero morphism.  Otherwise the common-label coefficients are
read through the proof-free atomic quotient and passed to `coefficient`. -/
def entry (dD : DData) (dC : CData dD) {X X' Y Y' : Obj}
    (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    AtomHom dD (slotAtom dD dC X Y q) (slotAtom dD dC X' Y' q') := by
  let A := X.atom q.left
  let A' := X'.atom q'.left
  let B := Y.atom q.right
  let B' := Y'.atom q'.right
  by_cases hA : A.label = A'.label
  · by_cases hB : B.label = B'.label
    · have hIndex :
          dC.Index A'.label B'.label = dC.Index A.label B.label := by
        rw [hA, hB]
      let target : dC.Index A.label B.label := cast hIndex q'.fusion
      have hLabel :
          (slotAtom dD dC X Y q).label =
            (slotAtom dD dC X' Y' q').label := by
        change A.label + B.label = A'.label + B'.label
        rw [hA, hB]
      exact AtomHom.ofLabelEq hLabel
        (coefficient dD dC A.label B.label A.shift B.shift B'.shift
          q.fusion target
          ((f q.left q'.left).coeff hA)
          ((g q.right q'.right).coeff hB))
    · exact AtomHom.zero dD _ _
  · exact AtomHom.zero dD _ _

/-! ### Entrywise tensor laws -/

/-- A tensor block is additive in its first atomic coefficient. -/
theorem entry_add_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f f' : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    entry dD dC (Hom.add f f') g q q' =
      AtomHom.add (entry dD dC f g q q') (entry dD dC f' g q q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · simp [entry, hA, hB, Hom.add]
      exact coefficient_add_left dD hD dC hC _ _ _ _ _ _ _ _ _ _
    · simp [entry, hA, hB]
      exact ((hD.algebra_laws _).zero_add _).symm
  · simp [entry, hA]
    exact ((hD.algebra_laws _).zero_add _).symm

/-- A tensor block is additive in its second atomic coefficient. -/
theorem entry_add_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f : Hom dD X X') (g g' : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    entry dD dC f (Hom.add g g') q q' =
      AtomHom.add (entry dD dC f g q q') (entry dD dC f g' q q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · simp [entry, hA, hB, Hom.add]
      exact coefficient_add_right dD hD dC hC _ _ _ _ _ _ _ _ _ _
    · simp [entry, hA, hB]
      exact ((hD.algebra_laws _).zero_add _).symm
  · simp [entry, hA]
    exact ((hD.algebra_laws _).zero_add _).symm

/-- A tensor block commutes with scalar multiplication in its first atomic
coefficient. -/
theorem entry_smul_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (r : ℝ) (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    entry dD dC (Hom.smul r f) g q q' =
      AtomHom.smul r (entry dD dC f g q q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · simp [entry, hA, hB, Hom.smul]
      exact coefficient_smul_left dD hD dC hC _ _ _ _ _ _ _ _ _ _
    · simp [entry, hA, hB]
      exact ((hD.algebra_laws _).smul_zero r).symm
  · simp [entry, hA]
    exact ((hD.algebra_laws _).smul_zero r).symm

/-- A tensor block commutes with scalar multiplication in its second atomic
coefficient. -/
theorem entry_smul_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (r : ℝ) (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    entry dD dC f (Hom.smul r g) q q' =
      AtomHom.smul r (entry dD dC f g q q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · simp [entry, hA, hB, Hom.smul]
      exact coefficient_smul_right dD hD dC hC _ _ _ _ _ _ _ _ _ _
    · simp [entry, hA, hB]
      exact ((hD.algebra_laws _).smul_zero r).symm
  · simp [entry, hA]
    exact ((hD.algebra_laws _).smul_zero r).symm

private theorem tensorGradeIndex (i j s s' t t' source target : ZMod 2) :
    (i + s + s') + (j + t + t') + source + target =
      (i + j) + (s + t + source) + (s' + t' + target) := by
  ring

private theorem rowParity_cast_eq {dD : DData} (dC : CData dD)
    {a a' b b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : dC.Index a' b') :
    dC.rowParity a b
        (cast (by rw [ha, hb] : dC.Index a' b' = dC.Index a b) r) =
      dC.rowParity a' b' r := by
  subst a'
  subst b'
  rfl

/-- A tensor block has the sum of the categorical degrees of its two input
blocks. -/
theorem entry_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} {i j : ZMod 2}
    (f : Hom dD X X') (g : Hom dD Y Y')
    (hf : Hom.MemGrade i f) (hg : Hom.MemGrade j g)
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    AtomHom.MemGrade (i + j) (entry dD dC f g q q') := by
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · intro hLabel
      have hA' : (X.atom q.left).1 = (X'.atom q'.left).1 := hA
      have hB' : (Y.atom q.right).1 = (Y'.atom q'.right).1 := hB
      let hIndex :
          dC.Index (X'.atom q'.left).label (Y'.atom q'.right).label =
            dC.Index (X.atom q.left).label (Y.atom q.right).label := by
        rw [hA, hB]
      let target :
          dC.Index (X.atom q.left).label (Y.atom q.right).label :=
        cast hIndex q'.fusion
      have hc := coefficient_memGrade dD hD dC hC
        (X.atom q.left).label (Y.atom q.right).label
        (X.atom q.left).shift (Y.atom q.right).shift
        (Y'.atom q'.right).shift q.fusion target
        (i + (X.atom q.left).shift + (X'.atom q'.left).shift)
        (j + (Y.atom q.right).shift + (Y'.atom q'.right).shift)
        ((f q.left q'.left).coeff hA) ((g q.right q'.right).coeff hB)
        (hf q.left q'.left hA) (hg q.right q'.right hB)
      have hrow :
          dC.rowParity (X.atom q.left).label (Y.atom q.right).label target =
            dC.rowParity (X'.atom q'.left).label
              (Y'.atom q'.right).label q'.fusion := by
        simpa [target] using rowParity_cast_eq dC hA hB q'.fusion
      rw [hrow] at hc
      simpa [entry, hA, hB, hA', hB', slotAtom, Atom.label, Atom.shift,
        target, tensorGradeIndex] using hc
    · rw [show entry dD dC f g q q' =
          AtomHom.zero dD _ _ by simp [entry, hA, hB]]
      exact AtomHom.zero_memGrade hD (i + j)
  · rw [show entry dD dC f g q q' =
        AtomHom.zero dD _ _ by simp [entry, hA]]
    exact AtomHom.zero_memGrade hD (i + j)

/-- Tensoring the two identity matrices gives the identity coefficient on
one fixed tensor slot. -/
theorem entry_id_self (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X Y : Obj} (q : Slot dD dC X Y) :
    entry dD dC (Hom.id dD X) (Hom.id dD Y) q q =
      AtomHom.id dD (slotAtom dD dC X Y q) := by
  apply AtomHom.ext
  intro hLabel
  simp [entry, Hom.id, coefficient_one dD hD dC hC,
    slotAtom, Atom.label]

/-- A zero atomic block in the first matrix forces the corresponding tensor
block to vanish. -/
theorem entry_of_left_eq_zero (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y')
    (hf : f q.left q'.left =
      AtomHom.zero dD (X.atom q.left) (X'.atom q'.left)) :
    entry dD dC f g q q' =
      AtomHom.zero dD (slotAtom dD dC X Y q)
        (slotAtom dD dC X' Y' q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · have hA' : (X.atom q.left).1 = (X'.atom q'.left).1 := hA
      have hB' : (Y.atom q.right).1 = (Y'.atom q'.right).1 := hB
      simp [entry, hA, hB, hA', hB', hf,
        coefficient_zero_left dD hD dC hC,
        slotAtom, Atom.label]
    · simp [entry, hA, hB]
  · simp [entry, hA]

/-- A zero atomic block in the second matrix forces the corresponding tensor
block to vanish. -/
theorem entry_of_right_eq_zero (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y')
    (hg : g q.right q'.right =
      AtomHom.zero dD (Y.atom q.right) (Y'.atom q'.right)) :
    entry dD dC f g q q' =
      AtomHom.zero dD (slotAtom dD dC X Y q)
        (slotAtom dD dC X' Y' q') := by
  apply AtomHom.ext
  intro hLabel
  by_cases hA : (X.atom q.left).label = (X'.atom q'.left).label
  · by_cases hB : (Y.atom q.right).label = (Y'.atom q'.right).label
    · have hA' : (X.atom q.left).1 = (X'.atom q'.left).1 := hA
      have hB' : (Y.atom q.right).1 = (Y'.atom q'.right).1 := hB
      simp [entry, hA, hB, hA', hB', hg,
        coefficient_zero_right dD hD dC hC,
        slotAtom, Atom.label]
    · simp [entry, hA, hB]
  · simp [entry, hA]

/-- Distinct tensor slots give a zero block when tensoring identity
matrices. -/
theorem entry_id_of_ne (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X Y : Obj} (q q' : Slot dD dC X Y) (hqq' : q ≠ q') :
    entry dD dC (Hom.id dD X) (Hom.id dD Y) q q' =
      AtomHom.zero dD (slotAtom dD dC X Y q)
        (slotAtom dD dC X Y q') := by
  rcases q with ⟨qi, qj, qr⟩
  rcases q' with ⟨qi', qj', qr'⟩
  by_cases hi : qi = qi'
  · subst qi'
    by_cases hj : qj = qj'
    · subst qj'
      have hrr : qr ≠ qr' := by
        intro h
        subst qr'
        exact hqq' rfl
      have hrr' : qr' ≠ qr := Ne.symm hrr
      apply AtomHom.ext
      intro hLabel
      simp [entry, Hom.id, Slot.left, Slot.right, Slot.fusion,
        coefficient_one dD hD dC hC, slotAtom, Atom.label]
      intro h
      exact (hrr' h).elim
    · apply entry_of_right_eq_zero dD hD dC hC
      simp [Hom.id, Slot.right, hj]
  · apply entry_of_left_eq_zero dD hD dC hC
    simp [Hom.id, Slot.left, hi]


/-- Tensor product of finite morphism matrices. -/
def hom (dD : DData) (dC : CData dD) {X X' Y Y' : Obj}
    (f : Hom dD X X') (g : Hom dD Y Y') :
    Hom dD (obj dD dC X Y) (obj dD dC X' Y') :=
  fun i j =>
    entry dD dC f g
      ((slots dD dC X Y).get i) ((slots dD dC X' Y').get j)

/-! ### Matrix-level tensor laws -/

/-- Tensoring homogeneous matrices adds their categorical degrees. -/
theorem hom_memGrade (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} {i j : ZMod 2}
    (f : Hom dD X X') (g : Hom dD Y Y')
    (hf : Hom.MemGrade i f) (hg : Hom.MemGrade j g) :
    Hom.MemGrade (i + j) (hom dD dC f g) := by
  intro r s
  exact entry_memGrade dD hD dC hC f g hf hg
    ((slots dD dC X Y).get r) ((slots dD dC X' Y').get s)

/-- Tensoring matrices is additive in the first input. -/
theorem hom_add_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f f' : Hom dD X X') (g : Hom dD Y Y') :
    hom dD dC (Hom.add f f') g =
      Hom.add (hom dD dC f g) (hom dD dC f' g) := by
  funext r s
  exact entry_add_left dD hD dC hC f f' g
    ((slots dD dC X Y).get r) ((slots dD dC X' Y').get s)

/-- Tensoring matrices is additive in the second input. -/
theorem hom_add_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (f : Hom dD X X') (g g' : Hom dD Y Y') :
    hom dD dC f (Hom.add g g') =
      Hom.add (hom dD dC f g) (hom dD dC f g') := by
  funext r s
  exact entry_add_right dD hD dC hC f g g'
    ((slots dD dC X Y).get r) ((slots dD dC X' Y').get s)

/-- Tensoring matrices commutes with scalar multiplication in the first
input. -/
theorem hom_smul_left (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (r : ℝ) (f : Hom dD X X') (g : Hom dD Y Y') :
    hom dD dC (Hom.smul r f) g = Hom.smul r (hom dD dC f g) := by
  funext p q
  exact entry_smul_left dD hD dC hC r f g
    ((slots dD dC X Y).get p) ((slots dD dC X' Y').get q)

/-- Tensoring matrices commutes with scalar multiplication in the second
input. -/
theorem hom_smul_right (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Obj} (r : ℝ) (f : Hom dD X X') (g : Hom dD Y Y') :
    hom dD dC f (Hom.smul r g) = Hom.smul r (hom dD dC f g) := by
  funext p q
  exact entry_smul_right dD hD dC hC r f g
    ((slots dD dC X Y).get p) ((slots dD dC X' Y').get q)

/-- Tensoring the two identity matrices gives the identity matrix on the
canonical tensor object. -/
theorem hom_id (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (X Y : Obj) :
    hom dD dC (Hom.id dD X) (Hom.id dD Y) =
      Hom.id dD (obj dD dC X Y) := by
  funext r s
  by_cases hrs : r = s
  · subst s
    simpa [hom, Hom.id, obj, Obj.atom] using
      entry_id_self dD hD dC hC ((slots dD dC X Y).get r)
  · rw [show Hom.id dD (obj dD dC X Y) r s =
        AtomHom.zero dD
          ((obj dD dC X Y).atom r) ((obj dD dC X Y).atom s) by
        simp [Hom.id, hrs]]
    apply entry_id_of_ne dD hD dC hC
    intro hget
    exact hrs ((slots_nodup dD dC X Y).get_inj_iff.mp hget)

/-! ### Fixed-order sums over tensor slots -/

@[implicit_reducible]
private def tensorAtomAddCommGroup {dD : DData} (hD : DLaws dD)
    (X Y : Atom) : AddCommGroup (AtomHom dD X Y) := by
  letI : Zero (AtomHom dD X Y) := ⟨AtomHom.zero dD X Y⟩
  letI : Add (AtomHom dD X Y) := ⟨AtomHom.add⟩
  letI : Neg (AtomHom dD X Y) := ⟨AtomHom.neg⟩
  letI : Sub (AtomHom dD X Y) :=
    ⟨fun f g => AtomHom.add f (AtomHom.neg g)⟩
  exact
    { add_assoc := AtomHom.add_assoc hD
      zero_add := AtomHom.zero_add hD
      add_zero := AtomHom.add_zero hD
      neg_add_cancel := AtomHom.neg_add hD
      add_comm := AtomHom.add_comm hD
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }

@[implicit_reducible]
private def tensorAtomModule {dD : DData} (hD : DLaws dD)
    (X Y : Atom) :
    letI := tensorAtomAddCommGroup hD X Y
    Module ℝ (AtomHom dD X Y) := by
  letI := tensorAtomAddCommGroup hD X Y
  exact
    { smul := AtomHom.smul
      one_smul := AtomHom.one_smul hD
      mul_smul := AtomHom.mul_smul hD
      smul_add := AtomHom.smul_add hD
      smul_zero := AtomHom.smul_zero hD
      add_smul := AtomHom.add_smul hD
      zero_smul := AtomHom.zero_smul hD }

private theorem atomFinSum_eq_sum {dD : DData} (hD : DLaws dD)
    {X Y : Atom} {n : ℕ} (f : Fin n → AtomHom dD X Y) :
    letI := tensorAtomAddCommGroup hD X Y
    AtomHom.finSum n f = ∑ i, f i := by
  letI := tensorAtomAddCommGroup hD X Y
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [AtomHom.finSum]
      rw [ih, Fin.sum_univ_castSucc]
      rfl

private theorem listSum_sigma
    {A : Type*} {B : A → Type*} {M : Type*} [AddCommMonoid M]
    (l : List A) (m : ∀ a, List (B a)) (F : (Σ a, B a) → M) :
    ((l.sigma m).map F).sum =
      (l.map fun a => ((m a).map fun b => F ⟨a, b⟩).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.sigma_cons, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.map_cons, List.sum_cons, ih]

private theorem sum_slots {M : Type*} [AddCommMonoid M]
    (dD : DData) (dC : CData dD) (X Y : Obj)
    (F : Slot dD dC X Y → M) :
    (∑ q : Fin (slots dD dC X Y).length,
        F ((slots dD dC X Y).get q)) =
      ∑ i : Fin X.size, ∑ j : Fin Y.size,
        ∑ r : dC.Index (X.atom i).label (Y.atom j).label,
          F ⟨i, j, r⟩ := by
  rw [← List.sum_ofFn]
  change (List.ofFn (F ∘ (slots dD dC X Y).get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  unfold slots
  rw [listSum_sigma]
  rw [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [listSum_sigma]
  rw [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

private theorem rawFinSum_eq_sum (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) {n : ℕ} (f : Fin n → d.carrier) :
    letI := tensorRawAddCommGroup d h
    CData.rawFinSum d f = ∑ i, f i := by
  letI := tensorRawAddCommGroup d h
  unfold CData.rawFinSum
  change (List.ofFn f).sum = ∑ i, f i
  exact List.sum_ofFn

private theorem atomFinSum_coeff {dD : DData} (hD : DLaws dD)
    {X Y : Atom} {n : ℕ} (f : Fin n → AtomHom dD X Y)
    (hXY : X.label = Y.label) :
    letI := tensorRawAddCommGroup (dD.algebra X.label)
      (hD.algebra_laws X.label)
    (AtomHom.finSum n f).coeff hXY = ∑ i, (f i).coeff hXY := by
  letI := tensorRawAddCommGroup (dD.algebra X.label)
    (hD.algebra_laws X.label)
  induction n with
  | zero =>
      simp only [AtomHom.finSum, AtomHom.coeff_zero]
      rfl
  | succ n ih =>
      simp only [AtomHom.finSum, AtomHom.coeff_add]
      rw [ih, Fin.sum_univ_castSucc]
      rfl

/-! ### Atom-level super-interchange -/

/-- The fused atom attached to a pair of atoms and one fusion row. -/
private abbrev atomSummand (dD : DData) (dC : CData dD)
    (X Y : Atom) (r : dC.Index X.label Y.label) : Atom :=
  (X.label + Y.label,
    X.shift + Y.shift + dC.rowParity X.label Y.label r)

/-- Tensor entry after the two object indices have already been fixed. -/
private def atomEntry (dD : DData) (dC : CData dD)
    {X X' Y Y' : Atom} (f : AtomHom dD X X') (g : AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    AtomHom dD (atomSummand dD dC X Y source)
      (atomSummand dD dC X' Y' target) := by
  by_cases hX : X.label = X'.label
  · by_cases hY : Y.label = Y'.label
    · have hIndex : dC.Index X'.label Y'.label =
          dC.Index X.label Y.label := by rw [hX, hY]
      let target' : dC.Index X.label Y.label := cast hIndex target
      have hLabel :
          (atomSummand dD dC X Y source).label =
            (atomSummand dD dC X' Y' target).label := by
        change X.label + Y.label = X'.label + Y'.label
        rw [hX, hY]
      exact AtomHom.ofLabelEq hLabel
        (coefficient dD dC X.label Y.label X.shift Y.shift Y'.shift
          source target' (f.coeff hX) (g.coeff hY))
    · exact AtomHom.zero dD _ _
  · exact AtomHom.zero dD _ _

private theorem entry_eq_atomEntry
    (dD : DData) (dC : CData dD) {X X' Y Y' : Obj}
    (f : Hom dD X X') (g : Hom dD Y Y')
    (q : Slot dD dC X Y) (q' : Slot dD dC X' Y') :
    entry dD dC f g q q' =
      atomEntry dD dC (f q.left q'.left) (g q.right q'.right)
        q.fusion q'.fusion := by
  unfold entry atomEntry
  dsimp only
  split <;> rename_i hX
  · split <;> rename_i hY
    · rfl
    · rfl
  · rfl

private theorem atomEntry_zero_left
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} (g : AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC (AtomHom.zero dD X X') g source target =
      AtomHom.zero dD (atomSummand dD dC X Y source)
        (atomSummand dD dC X' Y' target) := by
  apply AtomHom.ext
  intro hLabel
  by_cases hX : X.label = X'.label
  · by_cases hY : Y.label = Y'.label
    · have hX' : X.1 = X'.1 := hX
      have hY' : Y.1 = Y'.1 := hY
      simp [atomEntry, hX', hY',
        coefficient_zero_left dD hD dC hC,
        atomSummand, Atom.label]
    · simp [atomEntry, hX, hY]
  · simp [atomEntry, hX]

private theorem atomEntry_zero_right
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} (f : AtomHom dD X X')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC f (AtomHom.zero dD Y Y') source target =
      AtomHom.zero dD (atomSummand dD dC X Y source)
        (atomSummand dD dC X' Y' target) := by
  apply AtomHom.ext
  intro hLabel
  by_cases hX : X.label = X'.label
  · by_cases hY : Y.label = Y'.label
    · have hX' : X.1 = X'.1 := hX
      have hY' : Y.1 = Y'.1 := hY
      simp [atomEntry, hX', hY',
        coefficient_zero_right dD hD dC hC,
        atomSummand, Atom.label]
    · simp [atomEntry, hX, hY]
  · simp [atomEntry, hX]

private theorem atomEntry_add_left
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} (f f' : AtomHom dD X X')
    (g : AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC (AtomHom.add f f') g source target =
      AtomHom.add (atomEntry dD dC f g source target)
        (atomEntry dD dC f' g source target) := by
  apply AtomHom.ext
  intro hLabel
  by_cases hX : X.label = X'.label
  · by_cases hY : Y.label = Y'.label
    · have hX' : X.1 = X'.1 := hX
      have hY' : Y.1 = Y'.1 := hY
      simp [atomEntry, hX', hY', coefficient_add_left dD hD dC hC,
        atomSummand, Atom.label]
    · simp [atomEntry, hX, hY]
      exact ((hD.algebra_laws _).zero_add _).symm
  · simp [atomEntry, hX]
    exact ((hD.algebra_laws _).zero_add _).symm

private theorem atomEntry_add_right
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} (f : AtomHom dD X X')
    (g g' : AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC f (AtomHom.add g g') source target =
      AtomHom.add (atomEntry dD dC f g source target)
        (atomEntry dD dC f g' source target) := by
  apply AtomHom.ext
  intro hLabel
  by_cases hX : X.label = X'.label
  · by_cases hY : Y.label = Y'.label
    · have hX' : X.1 = X'.1 := hX
      have hY' : Y.1 = Y'.1 := hY
      simp [atomEntry, hX', hY', coefficient_add_right dD hD dC hC,
        atomSummand, Atom.label]
    · simp [atomEntry, hX, hY]
      exact ((hD.algebra_laws _).zero_add _).symm
  · simp [atomEntry, hX]
    exact ((hD.algebra_laws _).zero_add _).symm

private theorem atomEntry_finSum_left
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} {n : ℕ}
    (f : Fin n → AtomHom dD X X') (g : AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC (AtomHom.finSum n f) g source target =
      AtomHom.finSum n (fun i => atomEntry dD dC (f i) g source target) := by
  induction n with
  | zero =>
      simp only [AtomHom.finSum]
      exact atomEntry_zero_left dD hD dC hC g source target
  | succ n ih =>
      simp only [AtomHom.finSum]
      rw [atomEntry_add_left dD hD dC hC, ih]

private theorem atomEntry_finSum_right
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X X' Y Y' : Atom} {n : ℕ}
    (f : AtomHom dD X X') (g : Fin n → AtomHom dD Y Y')
    (source : dC.Index X.label Y.label)
    (target : dC.Index X'.label Y'.label) :
    atomEntry dD dC f (AtomHom.finSum n g) source target =
      AtomHom.finSum n (fun i => atomEntry dD dC f (g i) source target) := by
  induction n with
  | zero =>
      simp only [AtomHom.finSum]
      exact atomEntry_zero_right dD hD dC hC f source target
  | succ n ih =>
      simp only [AtomHom.finSum]
      rw [atomEntry_add_right dD hD dC hC, ih]

@[simp] private theorem atomEntry_sameLabels
    (dD : DData) (dC : CData dD) (a b : ZMod 8)
    (s s' t t' : ZMod 2)
    (f : AtomHom dD (a, s) (a, s'))
    (g : AtomHom dD (b, t) (b, t'))
    (source target : dC.Index a b) :
    atomEntry dD dC f g source target =
      AtomHom.ofLabelEq (by rfl)
        (coefficient dD dC a b s t t' source target
          (f.coeff rfl) (g.coeff rfl)) := by
  unfold atomEntry
  dsimp only
  split <;> rename_i hX
  · split <;> rename_i hY
    · rfl
    · exact (hY rfl).elim
  · exact (hX rfl).elim

private def sameLabelEntry (dD : DData) (dC : CData dD)
    (a b : ZMod 8) (s s' t t' : ZMod 2)
    (f : AtomHom dD (a, s) (a, s'))
    (g : AtomHom dD (b, t) (b, t'))
    (source target : dC.Index a b) :
    AtomHom dD
      (a + b, s + t + dC.rowParity a b source)
      (a + b, s' + t' + dC.rowParity a b target) :=
  AtomHom.ofLabelEq rfl
    (coefficient dD dC a b s t t' source target
      (f.coeff rfl) (g.coeff rfl))

private theorem sameLabelEntry_interchange
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s0 s1 s2 t0 t1 t2 i j : ZMod 2)
    (f1 : AtomHom dD (a, s0) (a, s1))
    (f2 : AtomHom dD (a, s1) (a, s2))
    (g1 : AtomHom dD (b, t0) (b, t1))
    (g2 : AtomHom dD (b, t1) (b, t2))
    (hf1 : AtomHom.MemGrade i f1)
    (hg2 : AtomHom.MemGrade j g2)
    (source target : dC.Index a b) :
    AtomHom.finSum (dC.rank a b) (fun middle =>
        AtomHom.comp
          (sameLabelEntry dD dC a b s0 s1 t0 t1 f1 g1 source middle)
          (sameLabelEntry dD dC a b s1 s2 t1 t2 f2 g2 middle target)) =
      AtomHom.smul (RawDCT.paritySign (j * i))
        (sameLabelEntry dD dC a b s0 s2 t0 t2
          (AtomHom.comp f1 f2) (AtomHom.comp g1 g2) source target) := by
  letI := tensorRawAddCommGroup (dD.algebra (a + b))
    (hD.algebra_laws (a + b))
  apply AtomHom.ext_same_label
  rw [atomFinSum_coeff hD]
  simp only [AtomHom.coeff_comp_same_label, sameLabelEntry,
    AtomHom.coeff_ofLabelEq, AtomHom.coeff_smul]
  rw [← rawFinSum_eq_sum
    (dD.algebra (Atom.label
      (a + b, s0 + t0 + dC.rowParity a b source)))
    (hD.algebra_laws (Atom.label
      (a + b, s0 + t0 + dC.rowParity a b source)))]
  simpa only [Atom.label] using
    coefficient_comp dD hD dC hC a b s0 s1 t0 t1 t2 i j source target
      (hf1 rfl) (hg2 rfl)

private theorem atomEntry_sameLabels_interchange
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (a b : ZMod 8) (s0 s1 s2 t0 t1 t2 i j : ZMod 2)
    (f1 : AtomHom dD (a, s0) (a, s1))
    (f2 : AtomHom dD (a, s1) (a, s2))
    (g1 : AtomHom dD (b, t0) (b, t1))
    (g2 : AtomHom dD (b, t1) (b, t2))
    (hf1 : AtomHom.MemGrade i f1)
    (hg2 : AtomHom.MemGrade j g2)
    (source target : dC.Index a b) :
    AtomHom.finSum (dC.rank a b) (fun middle =>
        AtomHom.comp
          (atomEntry dD dC f1 g1 source middle)
          (atomEntry dD dC f2 g2 middle target)) =
      AtomHom.smul (RawDCT.paritySign (j * i))
        (atomEntry dD dC (AtomHom.comp f1 f2)
          (AtomHom.comp g1 g2) source target) := by
  simpa only [atomEntry_sameLabels, sameLabelEntry,
    atomSummand, Atom.label, Atom.shift, Subsingleton.elim] using
    sameLabelEntry_interchange dD hD dC hC a b
      s0 s1 s2 t0 t1 t2 i j f1 f2 g1 g2 hf1 hg2 source target

/-- Zero-extended atom-level super-interchange for arbitrary labels. -/
private theorem atomEntry_interchange
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    (X0 X1 X2 Y0 Y1 Y2 : Atom) (i j : ZMod 2)
    (f1 : AtomHom dD X0 X1) (f2 : AtomHom dD X1 X2)
    (g1 : AtomHom dD Y0 Y1) (g2 : AtomHom dD Y1 Y2)
    (hf1 : AtomHom.MemGrade i f1)
    (hg2 : AtomHom.MemGrade j g2)
    (source : dC.Index X0.label Y0.label)
    (target : dC.Index X2.label Y2.label) :
    AtomHom.finSum (dC.rank X1.label Y1.label) (fun middle =>
        AtomHom.comp
          (atomEntry dD dC f1 g1 source middle)
          (atomEntry dD dC f2 g2 middle target)) =
      AtomHom.smul (RawDCT.paritySign (j * i))
        (atomEntry dD dC (AtomHom.comp f1 f2)
          (AtomHom.comp g1 g2) source target) := by
  rcases X0 with ⟨a0, s0⟩
  rcases X1 with ⟨a1, s1⟩
  rcases X2 with ⟨a2, s2⟩
  rcases Y0 with ⟨b0, t0⟩
  rcases Y1 with ⟨b1, t1⟩
  rcases Y2 with ⟨b2, t2⟩
  by_cases ha01 : a0 = a1
  · subst a1
    by_cases ha12 : a0 = a2
    · subst a2
      by_cases hb01 : b0 = b1
      · subst b1
        by_cases hb12 : b0 = b2
        · subst b2
          exact atomEntry_sameLabels_interchange dD hD dC hC
            a0 b0 s0 s1 s2 t0 t1 t2 i j
            f1 f2 g1 g2 hf1 hg2 source target
        · have hg2zero :
              g2 = AtomHom.zero dD (b0, t1) (b2, t2) :=
            AtomHom.eq_of_label_ne
              (by simpa only [Atom.label] using hb12) _ _
          subst g2
          simp only [atomEntry_zero_right dD hD dC hC,
            AtomHom.comp_zero hD, AtomHom.finSum_zero hD,
            AtomHom.smul_zero hD]
      · have hg1zero :
            g1 = AtomHom.zero dD (b0, t0) (b1, t1) :=
          AtomHom.eq_of_label_ne
            (by simpa only [Atom.label] using hb01) _ _
        subst g1
        simp only [atomEntry_zero_right dD hD dC hC,
          AtomHom.zero_comp hD, AtomHom.finSum_zero hD,
          AtomHom.smul_zero hD]
    · have hf2zero :
          f2 = AtomHom.zero dD (a0, s1) (a2, s2) :=
        AtomHom.eq_of_label_ne
          (by simpa only [Atom.label] using ha12) _ _
      subst f2
      simp only [atomEntry_zero_left dD hD dC hC,
        AtomHom.comp_zero hD, AtomHom.finSum_zero hD,
        AtomHom.smul_zero hD]
  · have hf1zero :
        f1 = AtomHom.zero dD (a0, s0) (a1, s1) :=
      AtomHom.eq_of_label_ne
        (by simpa only [Atom.label] using ha01) _ _
    subst f1
    simp only [atomEntry_zero_left dD hD dC hC,
      AtomHom.zero_comp hD, AtomHom.finSum_zero hD,
      AtomHom.smul_zero hD]

/-! ### Matrix-level super-interchange -/

/-- Super-interchange for the canonical finite tensor matrices. -/
theorem hom_interchange
    (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC)
    {X0 X1 X2 Y0 Y1 Y2 : Obj} (i j : ZMod 2)
    (f1 : Hom dD X0 X1) (f2 : Hom dD X1 X2)
    (g1 : Hom dD Y0 Y1) (g2 : Hom dD Y1 Y2)
    (hf1 : Hom.MemGrade i f1) (hg2 : Hom.MemGrade j g2) :
    Hom.comp (hom dD dC f1 g1) (hom dD dC f2 g2) =
      Hom.smul (RawDCT.paritySign (j * i))
        (hom dD dC (Hom.comp f1 f2) (Hom.comp g1 g2)) := by
  funext q0 q2
  let source : Slot dD dC X0 Y0 := (slots dD dC X0 Y0).get q0
  let target : Slot dD dC X2 Y2 := (slots dD dC X2 Y2).get q2
  letI := tensorAtomAddCommGroup hD
    (slotAtom dD dC X0 Y0 source) (slotAtom dD dC X2 Y2 target)
  letI := tensorAtomModule hD
    (slotAtom dD dC X0 Y0 source) (slotAtom dD dC X2 Y2 target)
  change AtomHom.finSum (slots dD dC X1 Y1).length (fun q1 =>
      AtomHom.comp
        (entry dD dC f1 g1 source ((slots dD dC X1 Y1).get q1))
        (entry dD dC f2 g2 ((slots dD dC X1 Y1).get q1) target)) =
    AtomHom.smul (RawDCT.paritySign (j * i))
      (entry dD dC (Hom.comp f1 f2) (Hom.comp g1 g2) source target)
  rw [atomFinSum_eq_sum hD]
  rw [sum_slots dD dC X1 Y1
    (fun middle : Slot dD dC X1 Y1 =>
      AtomHom.comp
        (entry dD dC f1 g1 source middle)
        (entry dD dC f2 g2 middle target))]
  simp_rw [entry_eq_atomEntry]
  letI := tensorAtomAddCommGroup hD
    (atomSummand dD dC (X0.atom source.left)
      (Y0.atom source.right) source.fusion)
    (atomSummand dD dC (X2.atom target.left)
      (Y2.atom target.right) target.fusion)
  letI := tensorAtomModule hD
    (atomSummand dD dC (X0.atom source.left)
      (Y0.atom source.right) source.fusion)
    (atomSummand dD dC (X2.atom target.left)
      (Y2.atom target.right) target.fusion)
  change (∑ x1 : Fin X1.size, ∑ y1 : Fin Y1.size,
      ∑ middle : dC.Index
          (X1.atom x1).label (Y1.atom y1).label,
        AtomHom.comp
          (atomEntry dD dC (f1 source.left x1)
            (g1 source.right y1) source.fusion middle)
          (atomEntry dD dC (f2 x1 target.left)
            (g2 y1 target.right) middle target.fusion)) =
    AtomHom.smul (RawDCT.paritySign (j * i))
      (atomEntry dD dC
        (Hom.comp f1 f2 source.left target.left)
        (Hom.comp g1 g2 source.right target.right)
        source.fusion target.fusion)
  have hAtom (x1 : Fin X1.size) (y1 : Fin Y1.size) :
      (∑ middle : dC.Index
          (X1.atom x1).label (Y1.atom y1).label,
        AtomHom.comp
          (atomEntry dD dC (f1 source.left x1)
            (g1 source.right y1) source.fusion middle)
          (atomEntry dD dC (f2 x1 target.left)
            (g2 y1 target.right) middle target.fusion)) =
        AtomHom.smul (RawDCT.paritySign (j * i))
          (atomEntry dD dC
            (AtomHom.comp (f1 source.left x1) (f2 x1 target.left))
            (AtomHom.comp (g1 source.right y1) (g2 y1 target.right))
            source.fusion target.fusion) := by
    rw [← atomFinSum_eq_sum hD]
    exact atomEntry_interchange dD hD dC hC
      (X0.atom source.left) (X1.atom x1) (X2.atom target.left)
      (Y0.atom source.right) (Y1.atom y1) (Y2.atom target.right)
      i j (f1 source.left x1) (f2 x1 target.left)
      (g1 source.right y1) (g2 y1 target.right)
      (hf1 source.left x1) (hg2 y1 target.right)
      source.fusion target.fusion
  simp_rw [hAtom]
  change (∑ x1 : Fin X1.size, ∑ y1 : Fin Y1.size,
      (RawDCT.paritySign (j * i) : ℝ) •
        atomEntry dD dC
          (AtomHom.comp (f1 source.left x1) (f2 x1 target.left))
          (AtomHom.comp (g1 source.right y1) (g2 y1 target.right))
          source.fusion target.fusion) =
    (RawDCT.paritySign (j * i) : ℝ) •
      atomEntry dD dC
        (Hom.comp f1 f2 source.left target.left)
        (Hom.comp g1 g2 source.right target.right)
        source.fusion target.fusion
  simp_rw [← Finset.smul_sum]
  congr 1
  simp only [Hom.comp]
  rw [atomEntry_finSum_left dD hD dC hC]
  simp_rw [atomEntry_finSum_right dD hD dC hC]
  simp_rw [atomFinSum_eq_sum hD]

/-! ## Canonical tensor data -/

/-- The tensor operations canonically extracted from a stored binary kernel.

The name distinguishes this constructor from the `Tensor.data` projection
of the completed structure. -/
def canonicalData (dD : DData) (dC : CData dD) : TensorData dD where
  tensorObj := obj dD dC
  tensorHom := hom dD dC

private theorem paritySign_eq_pow (p : ZMod 2) :
    RawDCT.paritySign p = (-1 : ℝ) ^ p.val := by
  rcases zmod2_cases p with hp | hp <;> subst p
  · norm_num [RawDCT.paritySign]
  · rw [ZMod.val_one 2]
    norm_num [RawDCT.paritySign]

/-- All seven tensor laws follow from the completed coefficient algebra and
binary-kernel laws. -/
def canonicalLaws (D : D) (C : C D) :
    TensorLaws D.data D.laws (canonicalData D.data C.data) where
  tensor_grade := by
    intro X₁ Y₁ X₂ Y₂ a b f g hf hg
    exact hom_memGrade D.data D.laws C.data C.laws f g hf hg
  tensor_id := by
    intro X Y
    exact hom_id D.data D.laws C.data C.laws X Y
  tensor_add_left := by
    intro X₁ Y₁ X₂ Y₂ f f' g
    exact hom_add_left D.data D.laws C.data C.laws f f' g
  tensor_add_right := by
    intro X₁ Y₁ X₂ Y₂ f g g'
    exact hom_add_right D.data D.laws C.data C.laws f g g'
  tensor_smul_left := by
    intro X₁ Y₁ X₂ Y₂ r f g
    exact hom_smul_left D.data D.laws C.data C.laws r f g
  tensor_smul_right := by
    intro X₁ Y₁ X₂ Y₂ r f g
    exact hom_smul_right D.data D.laws C.data C.laws r f g
  super_interchange := by
    intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ b c f g h k hg hh
    simpa only [canonicalData, paritySign_eq_pow] using
      hom_interchange D.data D.laws C.data C.laws c b h f k g hh hg

/-- The completed canonical tensor bifunctor extracted from `D` and `C`. -/
def canonical (D : D) (C : C D) : Tensor D where
  data := canonicalData D.data C.data
  laws := canonicalLaws D C

end Tensor

end Superfusion.RMod.FromRawDCT
