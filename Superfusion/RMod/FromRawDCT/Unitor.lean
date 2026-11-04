import Superfusion.RMod.FromRawDCT.Associator

/-!
# Unit and unitor data of the finite coordinate envelope

The tensor unit is the unshifted atom at label zero.  A general raw binary
kernel does not by itself say that its left- and right-unit channels are
singletons, so chosen channel rows are executable data and their uniqueness
and parity are separate laws.

For an already shifted raw DCT, the left-unitor coefficients are read from
the actual `(0,0,a)` connector: the forward unitor uses `T.inv`, and its
stored inverse uses `T.hom`.  The right-unitor coefficient is the stored
algebra unit.  No `beta` table is read a second time.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Unit-channel data and laws -/

/-- Chosen executable rows on both unit faces of a binary kernel. -/
structure UnitRowsData (dD : DData) (dC : CData dD) where
  left : ∀ a, dC.Index 0 a
  right : ∀ a, dC.Index a 0

/-- The chosen rows are the unique even rows on their respective faces. -/
structure UnitRowsLaws (dD : DData) (dC : CData dD)
    (d : UnitRowsData dD dC) : Prop where
  left_unique : ∀ a (r : dC.Index 0 a), r = d.left a
  right_unique : ∀ a (r : dC.Index a 0), r = d.right a
  left_even : ∀ a, dC.rowParity 0 a (d.left a) = 0
  right_even : ∀ a, dC.rowParity a 0 (d.right a) = 0

/-- Completed unit-row package over a completed binary kernel. -/
structure UnitRows (D : D) (C : C D) where
  data : UnitRowsData D.data C.data
  laws : UnitRowsLaws D.data C.data data

/-! ## Abstract unitor structure -/

/-- Tensor unit and both executable directions of the two unitors. -/
structure UnitorData (dD : DData) (tensor : TensorData dD) where
  tensorUnit : Obj
  leftUnitorHom : (X : Obj) →
    Hom dD (tensor.tensorObj tensorUnit X) X
  leftUnitorInv : (X : Obj) →
    Hom dD X (tensor.tensorObj tensorUnit X)
  rightUnitorHom : (X : Obj) →
    Hom dD (tensor.tensorObj X tensorUnit) X
  rightUnitorInv : (X : Obj) →
    Hom dD X (tensor.tensorObj X tensorUnit)

/-- Inverse, degree, naturality, and triangle laws for the exact unitors
stored in `d`. -/
structure UnitorLaws (dD : DData) (_hD : DLaws dD)
    (tensor : TensorData dD) (_hTensor : TensorLaws dD _hD tensor)
    (associator : AssociatorData dD tensor)
    (_hAssociator : AssociatorLaws dD _hD tensor _hTensor associator)
    (d : UnitorData dD tensor) : Prop where
  leftUnitor_hom_inv : ∀ X,
    Hom.comp (d.leftUnitorHom X) (d.leftUnitorInv X) =
      Hom.id dD (tensor.tensorObj d.tensorUnit X)
  leftUnitor_inv_hom : ∀ X,
    Hom.comp (d.leftUnitorInv X) (d.leftUnitorHom X) = Hom.id dD X
  leftUnitor_hom_even : ∀ X, Hom.MemGrade 0 (d.leftUnitorHom X)
  leftUnitor_inv_even : ∀ X, Hom.MemGrade 0 (d.leftUnitorInv X)
  leftUnitor_naturality : ∀ {X Y} (f : Hom dD X Y),
    Hom.comp (tensor.tensorHom (Hom.id dD d.tensorUnit) f)
        (d.leftUnitorHom Y) =
      Hom.comp (d.leftUnitorHom X) f
  rightUnitor_hom_inv : ∀ X,
    Hom.comp (d.rightUnitorHom X) (d.rightUnitorInv X) =
      Hom.id dD (tensor.tensorObj X d.tensorUnit)
  rightUnitor_inv_hom : ∀ X,
    Hom.comp (d.rightUnitorInv X) (d.rightUnitorHom X) = Hom.id dD X
  rightUnitor_hom_even : ∀ X, Hom.MemGrade 0 (d.rightUnitorHom X)
  rightUnitor_inv_even : ∀ X, Hom.MemGrade 0 (d.rightUnitorInv X)
  rightUnitor_naturality : ∀ {X Y} (f : Hom dD X Y),
    Hom.comp (tensor.tensorHom f (Hom.id dD d.tensorUnit))
        (d.rightUnitorHom Y) =
      Hom.comp (d.rightUnitorHom X) f
  triangle : ∀ X Y,
    Hom.comp (associator.associatorHom X d.tensorUnit Y)
        (tensor.tensorHom (Hom.id dD X) (d.leftUnitorHom Y)) =
      tensor.tensorHom (d.rightUnitorHom X) (Hom.id dD Y)

/-- Completed unitors over completed tensor and associator structures. -/
structure Unitor (D : D) (tensor : Tensor D)
    (associator : Associator D tensor) where
  data : UnitorData D.data tensor.data
  laws : UnitorLaws D.data D.laws tensor.data tensor.laws
    associator.data associator.laws data

namespace Unitor

/-! ## The coordinate tensor unit -/

/-- The unshifted singleton atom at label zero. -/
def unit : Obj := Obj.singleton (0, 0)

/-! ## Unit-face connector coefficients -/

/-- Cast the common `(0,0,a)` endpoint algebra back to the algebra at `a`. -/
def castUnitTriple (x : RawDCTData) (a : ZMod 8) :
    (x.D.algebra (0 + 0 + a)).carrier → (x.D.algebra a).carrier :=
  cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier) (by simp))

/-- Forward left-unitor coefficient on a stored left-unit row.

It is a coordinate of `T.inv` on the actual `(0,0,a)` connector. -/
def leftHomCoefficient (x : RawDCTData)
    (rows : UnitRowsData x.D x.C) (a : ZMod 8)
    (r : x.C.Index 0 a) : (x.D.algebra a).carrier :=
  castUnitTriple x a <|
    Associator.invCoefficient x 0 0 a
      r
      (Associator.castIndex x rfl (zero_add a).symm r)
      (rows.left 0)
      (Associator.castIndex x (zero_add 0).symm rfl r)

/-- Backward left-unitor coefficient on a stored left-unit row.

It is the opposite coordinate of `T.hom` on the same actual connector. -/
def leftInvCoefficient (x : RawDCTData)
    (rows : UnitRowsData x.D x.C) (a : ZMod 8)
    (r : x.C.Index 0 a) : (x.D.algebra a).carrier :=
  castUnitTriple x a <|
    Associator.homCoefficient x 0 0 a
      (rows.left 0)
      (Associator.castIndex x (zero_add 0).symm rfl r)
      r
      (Associator.castIndex x rfl (zero_add a).symm r)

/-! ## Unitor matrix entries -/

/-- One entry of the forward left unitor. -/
def leftHomEntry (x : RawDCTData) (rows : UnitRowsData x.D x.C)
    (X : Obj) (q : Tensor.Slot x.D x.C unit X) (j : Fin X.size) :
    AtomHom x.D (Tensor.slotAtom x.D x.C unit X q) (X.atom j) := by
  by_cases hj : q.right = j
  · subst j
    have hLabel :
        (Tensor.slotAtom x.D x.C unit X q).label = (X.atom q.right).label := by
      change 0 + (X.atom q.right).label = (X.atom q.right).label
      exact zero_add _
    exact AtomHom.ofLabelEq hLabel
      (cast
        (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
          hLabel).symm
        (leftHomCoefficient x rows (X.atom q.right).label q.fusion))
  · exact AtomHom.zero x.D _ _

/-- One entry of the stored inverse left unitor. -/
def leftInvEntry (x : RawDCTData) (rows : UnitRowsData x.D x.C)
    (X : Obj) (i : Fin X.size) (q : Tensor.Slot x.D x.C unit X) :
    AtomHom x.D (X.atom i) (Tensor.slotAtom x.D x.C unit X q) := by
  by_cases hi : i = q.right
  · subst i
    have hLabel : (X.atom q.right).label =
        (Tensor.slotAtom x.D x.C unit X q).label := by
      change (X.atom q.right).label = 0 + (X.atom q.right).label
      exact (zero_add _).symm
    exact AtomHom.ofLabelEq hLabel
      (leftInvCoefficient x rows (X.atom q.right).label q.fusion)
  · exact AtomHom.zero x.D _ _

/-- One entry of the forward right unitor. -/
def rightHomEntry (x : RawDCTData) (X : Obj)
    (q : Tensor.Slot x.D x.C X unit) (j : Fin X.size) :
    AtomHom x.D (Tensor.slotAtom x.D x.C X unit q) (X.atom j) := by
  by_cases hj : q.left = j
  · subst j
    have hLabel :
        (Tensor.slotAtom x.D x.C X unit q).label = (X.atom q.left).label := by
      change (X.atom q.left).label + 0 = (X.atom q.left).label
      exact add_zero _
    exact AtomHom.ofLabelEq hLabel
      (cast
        (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
          hLabel).symm
        (x.D.algebra (X.atom q.left).label).one)
  · exact AtomHom.zero x.D _ _

/-- One entry of the stored inverse right unitor. -/
def rightInvEntry (x : RawDCTData) (X : Obj) (i : Fin X.size)
    (q : Tensor.Slot x.D x.C X unit) :
    AtomHom x.D (X.atom i) (Tensor.slotAtom x.D x.C X unit q) := by
  by_cases hi : i = q.left
  · subst i
    have hLabel : (X.atom q.left).label =
        (Tensor.slotAtom x.D x.C X unit q).label := by
      change (X.atom q.left).label = (X.atom q.left).label + 0
      exact (add_zero _).symm
    exact AtomHom.ofLabelEq hLabel (x.D.algebra (X.atom q.left).label).one
  · exact AtomHom.zero x.D _ _

/-! ## Unitor matrices -/

def leftHom (x : RawDCTData) (rows : UnitRowsData x.D x.C) (X : Obj) :
    Hom x.D (Tensor.obj x.D x.C unit X) X :=
  fun i j => leftHomEntry x rows X
    ((Tensor.slots x.D x.C unit X).get i) j

def leftInv (x : RawDCTData) (rows : UnitRowsData x.D x.C) (X : Obj) :
    Hom x.D X (Tensor.obj x.D x.C unit X) :=
  fun i j => leftInvEntry x rows X i
    ((Tensor.slots x.D x.C unit X).get j)

def rightHom (x : RawDCTData) (X : Obj) :
    Hom x.D (Tensor.obj x.D x.C X unit) X :=
  fun i j => rightHomEntry x X
    ((Tensor.slots x.D x.C X unit).get i) j

def rightInv (x : RawDCTData) (X : Obj) :
    Hom x.D X (Tensor.obj x.D x.C X unit) :=
  fun i j => rightInvEntry x X i
    ((Tensor.slots x.D x.C X unit).get j)

/-! ## Canonical unitor data -/

/-- Executable unitors extracted from an actual connector and chosen unit
rows. -/
def canonicalData (x : RawDCTData) (rows : UnitRowsData x.D x.C) :
    UnitorData x.D (Tensor.canonicalData x.D x.C) where
  tensorUnit := unit
  leftUnitorHom := leftHom x rows
  leftUnitorInv := leftInv x rows
  rightUnitorHom := rightHom x
  rightUnitorInv := rightInv x

end Unitor

end Superfusion.RMod.FromRawDCT
