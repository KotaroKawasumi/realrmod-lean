import RMod.BrundanEllis.StackingReferenceUniformRows
import RMod.BrundanEllis.StackingReferenceReversedTransport

/-! The concrete reference exchange on arbitrary objects with fixed intrinsic
labels, retaining their original enumeration and all homogeneous morphisms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- The finite-matrix naturality theorem applies to every homogeneous row morphism. -/
theorem tensorExchange_naturality_hom {n m n' m' : ℕ} (a b : ZMod 8)
    (p : Fin n → ZMod 2) (p' : Fin n' → ZMod 2) (q : Fin m → ZMod 2) (q' : Fin m' → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a p'))
    (g : Hom realDData (rowObject b q) (rowObject b q')) (d e : ZMod 2)
    (hf : Hom.MemGrade d f) (hg : Hom.MemGrade e g) :
    Hom.comp (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g)
      (tensorExchange a b p' q') =
    Hom.smul (paritySign (degree a b * (d + e) + d * e))
      (Hom.comp (tensorExchange a b p q)
        (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) g f)) := by
  have h := tensorExchange_naturality a b p p' q q'
    (fun i i' => (f i i').coeff rfl) (fun j j' => (g j j').coeff rfl) d e
    (fun i i' => hf i i' rfl) (fun j j' => hg j j' rfl)
  simpa only [rowHom_reconstruct] using h

/-- The actual tensor on raw morphisms commutes with equality transport. -/
theorem tensorHom_transport {X X' Y Y' U U' V V' : Obj}
    (hx : X = U) (hx' : X' = U') (hy : Y = V) (hy' : Y' = V')
    (f : Hom realDData X X') (g : Hom realDData Y Y') :
    homTransport
      (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hx hy)
      (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hx' hy')
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g) =
    Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (homTransport hx hx' f) (homTransport hy hy' g) := by
  cases hx
  cases hx'
  cases hy
  cases hy'
  rfl

/-- Naturality diagrams commute with simultaneous equality transport of their four objects. -/
theorem tensorExchange_transport_naturality {X X' Y Y' U U' V V' : Obj}
    (hx : X = U) (hx' : X' = U') (hy : Y = V) (hy' : Y' = V')
    (f : Hom realDData X X') (g : Hom realDData Y Y')
    (k : Hom realDData
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y)
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X))
    (k' : Hom realDData
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X' Y')
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y' X'))
    (r : ℝ)
    (h : Hom.comp (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g) k' =
      Hom.smul r (Hom.comp k (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) g f))) :
    Hom.comp (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (homTransport hx hx' f) (homTransport hy hy' g))
      (homTransport (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hx' hy')
        (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hy' hx') k') =
    Hom.smul r (Hom.comp
      (homTransport (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hx hy)
        (congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)) hy hx) k)
      (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data)
        (homTransport hy hy' g) (homTransport hx hx' f))) := by
  cases hx
  cases hx'
  cases hy
  cases hy'
  exact h

theorem homTransport_roundtrip {X Y U V : Obj} (hx : X = U) (hy : Y = V)
    (f : Hom realDData U V) : homTransport hx hy (homTransport hx.symm hy.symm f) = f := by
  cases hx
  cases hy
  rfl

/-- Tensoring the uniform presentations gives the original tensor object. -/
theorem uniformTensor_eq (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    rowTensorObject a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift) =
      Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y :=
  congrArg₂ (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data))
    (rowObject_of_labels a X hX) (rowObject_of_labels b Y hY)

/-- Exchange the actual tensors of arbitrary uniformly labelled objects. -/
def uniformExchange (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    Hom realDData
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y)
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X) :=
  homTransport (uniformTensor_eq a b X Y hX hY) (uniformTensor_eq b a Y X hY hX)
    (tensorExchange a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift))

def uniformExchangeInv (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    Hom realDData
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X)
      (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y) :=
  homTransport (uniformTensor_eq b a Y X hY hX) (uniformTensor_eq a b X Y hX hY)
    (tensorExchangeInv a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift))

theorem uniformExchange_grade (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    Hom.MemGrade (degree a b) (uniformExchange a b X Y hX hY) :=
  homTransport_grade _ _ _ _ (tensorExchange_grade a b _ _)

theorem uniformExchangeInv_grade (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    Hom.MemGrade (degree a b) (uniformExchangeInv a b X Y hX hY) :=
  homTransport_grade _ _ _ _ (tensorExchangeInv_grade a b _ _)

theorem uniformExchange_inverse (a b : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = b) :
    Hom.comp (uniformExchange a b X Y hX hY) (uniformExchangeInv a b X Y hX hY) =
      Hom.id realDData (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) X Y) ∧
    Hom.comp (uniformExchangeInv a b X Y hX hY) (uniformExchange a b X Y hX hY) =
      Hom.id realDData (Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data) Y X) := by
  have h := tensorExchange_inverse a b (fun i => (X.atom i).shift) (fun j => (Y.atom j).shift)
  exact homTransport_inverse _ _ _ _ h.1 h.2

/-- Naturality on the original, uniformly labelled objects in every degree. -/
theorem uniformExchange_naturality (a b : ZMod 8) (X X' Y Y' : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hX' : ∀ i, (X'.atom i).label = a)
    (hY : ∀ j, (Y.atom j).label = b) (hY' : ∀ j, (Y'.atom j).label = b)
    (f : Hom realDData X X') (g : Hom realDData Y Y') (d e : ZMod 2)
    (hf : Hom.MemGrade d f) (hg : Hom.MemGrade e g) :
    Hom.comp (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) f g)
      (uniformExchange a b X' Y' hX' hY') =
    Hom.smul (paritySign (degree a b * (d + e) + d * e))
      (Hom.comp (uniformExchange a b X Y hX hY)
        (Tensor.hom realDData (shiftCData realDData realCData realComputableNuBeta.data) g f)) := by
  let f' := homTransport (rowObject_of_labels a X hX).symm (rowObject_of_labels a X' hX').symm f
  let g' := homTransport (rowObject_of_labels b Y hY).symm (rowObject_of_labels b Y' hY').symm g
  have hf' : Hom.MemGrade d f' := homTransport_grade _ _ _ _ hf
  have hg' : Hom.MemGrade e g' := homTransport_grade _ _ _ _ hg
  have hr := tensorExchange_naturality_hom a b
    (fun i => (X.atom i).shift) (fun i => (X'.atom i).shift)
    (fun j => (Y.atom j).shift) (fun j => (Y'.atom j).shift) f' g' d e hf' hg'
  have h := tensorExchange_transport_naturality
    (rowObject_of_labels a X hX) (rowObject_of_labels a X' hX')
    (rowObject_of_labels b Y hY) (rowObject_of_labels b Y' hY')
    f' g' _ _ _ hr
  have hff : homTransport (rowObject_of_labels a X hX) (rowObject_of_labels a X' hX') f' = f :=
    homTransport_roundtrip _ _ _
  have hgg : homTransport (rowObject_of_labels b Y hY) (rowObject_of_labels b Y' hY') g' = g :=
    homTransport_roundtrip _ _ _
  rw [hff, hgg] at h
  exact h

/-- An odd exchange remains available on a two-row shifted object. -/
example : Hom.MemGrade 1
    (uniformExchange 1 3 (rowObject 1 (fun i : Fin 2 => (i.val : ZMod 2)))
      (rowObject 3 (fun _ : Fin 1 => 1)) (fun _ => rfl) (fun _ => rfl)) :=
  uniformExchange_grade 1 3 _ _ _ _

/-- Type 2 and type 4 have an even exchange, also with nontrivial shifts. -/
example : Hom.MemGrade 0
    (uniformExchange 2 4 (rowObject 2 (fun i : Fin 2 => (i.val : ZMod 2)))
      (rowObject 4 (fun _ : Fin 1 => 1)) (fun _ => rfl) (fun _ => rfl)) :=
  uniformExchange_grade 2 4 _ _ _ _

end RMod.BrundanEllis.Stacking.ReferenceCommutor
