import Superfusion.RMod.RawDCT.D

/-!
# Abstract finite graded fusion kernels

`CData`, `CLaws`, and the completed `C` live together in this file.  It
contains no real-gauge table or concrete inhabitant.

The left action is stored in curried form on pure coefficient pairs.  Its
bilinearity and super-multiplication law make it precisely the executable
presentation of the action of the graded tensor product.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-- The real sign represented by a parity bit. -/
def paritySign (i : ZMod 2) : ℝ := if i = 0 then 1 else -1

/-- Computational contents of a finite, coordinate-presented fusion kernel.

`toCoord` and `ofCoord` are computational witnesses, not existential
finiteness proofs.  Their inverse and compatibility laws are stated in
`CLaws`. -/
structure CData (dD : DData) where
  rank : ZMod 8 → ZMod 8 → ℕ
  rowParity : ∀ a b, Fin (rank a b) → ZMod 2
  leftCoeff : ∀ a b,
    Fin (rank a b) → Fin (rank a b) →
      (dD.algebra a).carrier → (dD.algebra b).carrier →
        (dD.algebra (a + b)).carrier
  carrier : ZMod 8 → ZMod 8 → Type
  toCoord : ∀ a b, carrier a b →
    (Fin (rank a b) → (dD.algebra (a + b)).carrier)
  ofCoord : ∀ a b,
    (Fin (rank a b) → (dD.algebra (a + b)).carrier) → carrier a b
  zero : ∀ a b, carrier a b
  add : ∀ a b, carrier a b → carrier a b → carrier a b
  neg : ∀ a b, carrier a b → carrier a b
  smul : ∀ a b, ℝ → carrier a b → carrier a b
  component : ∀ a b, ZMod 2 → carrier a b → carrier a b
  left : ∀ a b,
    (dD.algebra a).carrier → (dD.algebra b).carrier →
      carrier a b → carrier a b
  right : ∀ a b,
    carrier a b → (dD.algebra (a + b)).carrier → carrier a b

namespace CData

/-- Canonical finite row type of the stored presentation. -/
abbrev Index {dD : DData} (dC : CData dD) (a b : ZMod 8) : Type :=
  Fin (dC.rank a b)

/-- The explicit coordinate carrier of the finite free right module. -/
abbrev Coordinates {dD : DData} (dC : CData dD) (a b : ZMod 8) : Type :=
  dC.Index a b → (dD.algebra (a + b)).carrier

/-- A computable finite sum using only operations stored in algebra data. -/
def rawFinSum (A : SuperAlgebraData ℝ) {n : ℕ}
    (f : Fin n → A.carrier) : A.carrier :=
  (List.ofFn f).foldr A.add A.zero

/-- Homogeneity derived from the stored executable kernel projection. -/
def MemGrade {dD : DData} (dC : CData dD) (a b : ZMod 8)
    (i : ZMod 2) (x : dC.carrier a b) : Prop :=
  dC.component a b i x = x

end CData

/-- Actual finite-presentation, additive, scalar, grading, and bimodule laws
of a stored kernel. -/
structure CLaws (dD : DData) (hD : DLaws dD) (dC : CData dD) : Prop where
  /- The computational presentation is genuinely inverse in both directions. -/
  ofCoord_toCoord : ∀ a b (x : dC.carrier a b),
    dC.ofCoord a b (dC.toCoord a b x) = x
  toCoord_ofCoord : ∀ a b (x : dC.Coordinates a b),
    dC.toCoord a b (dC.ofCoord a b x) = x

  /- Every stored operation is tied to that finite coordinate presentation. -/
  toCoord_zero : ∀ a b,
    dC.toCoord a b (dC.zero a b) =
      fun _ => (dD.algebra (a + b)).zero
  toCoord_add : ∀ a b (x y : dC.carrier a b),
    dC.toCoord a b (dC.add a b x y) = fun r =>
      (dD.algebra (a + b)).add (dC.toCoord a b x r) (dC.toCoord a b y r)
  toCoord_neg : ∀ a b (x : dC.carrier a b),
    dC.toCoord a b (dC.neg a b x) = fun r =>
      (dD.algebra (a + b)).neg (dC.toCoord a b x r)
  toCoord_smul : ∀ a b q (x : dC.carrier a b),
    dC.toCoord a b (dC.smul a b q x) = fun r =>
      (dD.algebra (a + b)).smul q (dC.toCoord a b x r)
  toCoord_component : ∀ a b i (x : dC.carrier a b),
    dC.toCoord a b (dC.component a b i x) = fun r =>
      (dD.algebra (a + b)).component (i + dC.rowParity a b r)
        (dC.toCoord a b x r)
  toCoord_left : ∀ a b (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.toCoord a b (dC.left a b x y m) = fun target =>
      CData.rawFinSum (dD.algebra (a + b)) fun source =>
        (dD.algebra (a + b)).mul
          (dC.leftCoeff a b target source x y)
          (dC.toCoord a b m source)
  toCoord_right : ∀ a b (m : dC.carrier a b)
      (x : (dD.algebra (a + b)).carrier),
    dC.toCoord a b (dC.right a b m x) = fun r =>
      (dD.algebra (a + b)).mul (dC.toCoord a b m r) x

  add_assoc : ∀ a b (x y z : dC.carrier a b),
    dC.add a b (dC.add a b x y) z = dC.add a b x (dC.add a b y z)
  add_comm : ∀ a b (x y : dC.carrier a b),
    dC.add a b x y = dC.add a b y x
  zero_add : ∀ a b (x : dC.carrier a b), dC.add a b (dC.zero a b) x = x
  add_zero : ∀ a b (x : dC.carrier a b), dC.add a b x (dC.zero a b) = x
  neg_add : ∀ a b (x : dC.carrier a b),
    dC.add a b (dC.neg a b x) x = dC.zero a b
  add_neg : ∀ a b (x : dC.carrier a b),
    dC.add a b x (dC.neg a b x) = dC.zero a b
  one_smul : ∀ a b (x : dC.carrier a b), dC.smul a b 1 x = x
  smul_assoc : ∀ a b r s (x : dC.carrier a b),
    dC.smul a b (r * s) x = dC.smul a b r (dC.smul a b s x)
  add_smul : ∀ a b r s (x : dC.carrier a b),
    dC.smul a b (r + s) x = dC.add a b (dC.smul a b r x) (dC.smul a b s x)
  smul_add : ∀ a b r (x y : dC.carrier a b),
    dC.smul a b r (dC.add a b x y) =
      dC.add a b (dC.smul a b r x) (dC.smul a b r y)
  zero_smul : ∀ a b (x : dC.carrier a b), dC.smul a b 0 x = dC.zero a b
  smul_zero : ∀ a b r, dC.smul a b r (dC.zero a b) = dC.zero a b

  component_zero : ∀ a b i,
    dC.component a b i (dC.zero a b) = dC.zero a b
  component_add : ∀ a b i (x y : dC.carrier a b),
    dC.component a b i (dC.add a b x y) =
      dC.add a b (dC.component a b i x) (dC.component a b i y)
  component_neg : ∀ a b i (x : dC.carrier a b),
    dC.component a b i (dC.neg a b x) = dC.neg a b (dC.component a b i x)
  component_smul : ∀ a b i r (x : dC.carrier a b),
    dC.component a b i (dC.smul a b r x) =
      dC.smul a b r (dC.component a b i x)
  component_idem : ∀ a b i (x : dC.carrier a b),
    dC.component a b i (dC.component a b i x) = dC.component a b i x
  component_complement : ∀ a b i (x : dC.carrier a b),
    dC.add a b (dC.component a b i x) (dC.component a b (i + 1) x) = x
  grade_disjoint : ∀ a b i (x : dC.carrier a b),
    dC.MemGrade a b i x → dC.MemGrade a b (i + 1) x → x = dC.zero a b

  left_zero_left : ∀ a b (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b (dD.algebra a).zero y m = dC.zero a b
  left_zero_right : ∀ a b (x : (dD.algebra a).carrier) (m : dC.carrier a b),
    dC.left a b x (dD.algebra b).zero m = dC.zero a b
  left_zero_module : ∀ a b (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier),
    dC.left a b x y (dC.zero a b) = dC.zero a b
  left_add_left : ∀ a b (x x' : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b ((dD.algebra a).add x x') y m =
      dC.add a b (dC.left a b x y m) (dC.left a b x' y m)
  left_add_right : ∀ a b (x : (dD.algebra a).carrier)
      (y y' : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b x ((dD.algebra b).add y y') m =
      dC.add a b (dC.left a b x y m) (dC.left a b x y' m)
  left_add_module : ∀ a b (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m m' : dC.carrier a b),
    dC.left a b x y (dC.add a b m m') =
      dC.add a b (dC.left a b x y m) (dC.left a b x y m')
  left_smul_left : ∀ a b r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b ((dD.algebra a).smul r x) y m =
      dC.smul a b r (dC.left a b x y m)
  left_smul_right : ∀ a b r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b x ((dD.algebra b).smul r y) m =
      dC.smul a b r (dC.left a b x y m)
  left_smul_module : ∀ a b r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    dC.left a b x y (dC.smul a b r m) =
      dC.smul a b r (dC.left a b x y m)
  left_one : ∀ a b (m : dC.carrier a b),
    dC.left a b (dD.algebra a).one (dD.algebra b).one m = m
  left_mul : ∀ a b i j (x x' : (dD.algebra a).carrier)
      (y y' : (dD.algebra b).carrier) (m : dC.carrier a b),
    (dD.algebra b).MemGrade j y →
    (dD.algebra a).MemGrade i x' →
    dC.left a b x y (dC.left a b x' y' m) =
      dC.smul a b (paritySign (j * i))
        (dC.left a b ((dD.algebra a).mul x x')
          ((dD.algebra b).mul y y') m)
  left_memGrade : ∀ a b i j k (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b),
    (dD.algebra a).MemGrade i x →
    (dD.algebra b).MemGrade j y →
    dC.MemGrade a b k m →
    dC.MemGrade a b (i + j + k) (dC.left a b x y m)

  right_zero_module : ∀ a b (x : (dD.algebra (a + b)).carrier),
    dC.right a b (dC.zero a b) x = dC.zero a b
  right_zero_algebra : ∀ a b (m : dC.carrier a b),
    dC.right a b m (dD.algebra (a + b)).zero = dC.zero a b
  right_add_module : ∀ a b (m m' : dC.carrier a b)
      (x : (dD.algebra (a + b)).carrier),
    dC.right a b (dC.add a b m m') x =
      dC.add a b (dC.right a b m x) (dC.right a b m' x)
  right_add_algebra : ∀ a b (m : dC.carrier a b)
      (x x' : (dD.algebra (a + b)).carrier),
    dC.right a b m ((dD.algebra (a + b)).add x x') =
      dC.add a b (dC.right a b m x) (dC.right a b m x')
  right_smul_module : ∀ a b r (m : dC.carrier a b)
      (x : (dD.algebra (a + b)).carrier),
    dC.right a b (dC.smul a b r m) x = dC.smul a b r (dC.right a b m x)
  right_smul_algebra : ∀ a b r (m : dC.carrier a b)
      (x : (dD.algebra (a + b)).carrier),
    dC.right a b m ((dD.algebra (a + b)).smul r x) =
      dC.smul a b r (dC.right a b m x)
  right_one : ∀ a b (m : dC.carrier a b),
    dC.right a b m (dD.algebra (a + b)).one = m
  right_assoc : ∀ a b (m : dC.carrier a b)
      (x y : (dD.algebra (a + b)).carrier),
    dC.right a b (dC.right a b m x) y =
      dC.right a b m ((dD.algebra (a + b)).mul x y)
  right_memGrade : ∀ a b i j (m : dC.carrier a b)
      (x : (dD.algebra (a + b)).carrier),
    dC.MemGrade a b i m →
    (dD.algebra (a + b)).MemGrade j x →
    dC.MemGrade a b (i + j) (dC.right a b m x)

  actions_comm : ∀ a b (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dC.carrier a b)
      (z : (dD.algebra (a + b)).carrier),
    dC.right a b (dC.left a b x y m) z =
      dC.left a b x y (dC.right a b m z)

/-- A completed family of actual finite graded fusion kernels over `D`. -/
structure C (D : D) where
  data : CData D.data
  laws : CLaws D.data D.laws data

end Superfusion.RMod.RawDCT
