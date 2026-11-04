import Superfusion.RMod.FromRawDCT.Tensor

/-!
# Canonical indices for the raw tensor object

This lightweight abstract file identifies the flattened `Fin` index used by
`Tensor.obj` with the dependent triple consisting of a left object position,
a right object position, and a row of the corresponding raw binary kernel.
It depends only on the executable `DData` and `CData`; no concrete table or
associator law is imported.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace Tensor

/-! ## The dependent row index and its canonical enumeration -/

/-- The sigma-shaped index of one raw tensor summand.

This is definitionally the same dependent triple as `Tensor.Slot`, but the
explicit sigma presentation is convenient when comparing with tensor indices
in another finite presentation. -/
abbrev SlotIndex (dD : DData) (dC : CData dD) (X Y : Obj) :=
  Σ i : Fin X.size, Σ j : Fin Y.size,
    dC.Index (X.atom i).label (Y.atom j).label

/-- Every dependent row index occurs in the canonical lexicographic list. -/
theorem slot_mem_slots (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : SlotIndex dD dC X Y) :
    q ∈ slots dD dC X Y := by
  rcases q with ⟨i, j, r⟩
  simp [slots]

/-- The flattened index of `Tensor.obj` is canonically equivalent to its
left position, right position, and raw fusion-row index.

Both directions are executable: the forward map reads the canonical list,
and the inverse map finds the unique occurrence in that duplicate-free list.
-/
def slotIndexEquiv (dD : DData) (dC : CData dD) (X Y : Obj) :
    Fin (slots dD dC X Y).length ≃ SlotIndex dD dC X Y :=
  (slots_nodup dD dC X Y).getEquivOfForallMemList
    (slots dD dC X Y) (slot_mem_slots dD dC X Y)

@[simp]
theorem slotIndexEquiv_apply (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Fin (slots dD dC X Y).length) :
    slotIndexEquiv dD dC X Y q = (slots dD dC X Y).get q :=
  rfl

@[simp]
theorem slotIndexEquiv_left (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Fin (slots dD dC X Y).length) :
    (slotIndexEquiv dD dC X Y q).1 =
      ((slots dD dC X Y).get q).left :=
  rfl

@[simp]
theorem slotIndexEquiv_right (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Fin (slots dD dC X Y).length) :
    (slotIndexEquiv dD dC X Y q).2.1 =
      ((slots dD dC X Y).get q).right :=
  rfl

@[simp]
theorem slotIndexEquiv_fusion (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Fin (slots dD dC X Y).length) :
    (slotIndexEquiv dD dC X Y q).2.2 =
      ((slots dD dC X Y).get q).fusion :=
  rfl

/-! ## Compatibility with the flattened tensor object -/

/-- Reading the atom at a flattened tensor index is the same as evaluating
the stored atom formula on the corresponding dependent row index. -/
@[simp]
theorem obj_atom_slotIndexEquiv (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Fin (slots dD dC X Y).length) :
    (obj dD dC X Y).atom q =
      slotAtom dD dC X Y (slotIndexEquiv dD dC X Y q) :=
  rfl

end Tensor

end Superfusion.RMod.FromRawDCT
