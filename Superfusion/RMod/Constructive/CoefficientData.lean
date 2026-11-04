import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Superfusion.GaugeChi.CoeffChecker

/-!
# Choice-free coordinate algebras for raw real DCT data

Only executable coefficient data lives here.  Semantic bases and algebra
proofs are deliberately imported by the separate law module.
-/

set_option autoImplicit false

namespace Superfusion
namespace RModCoordinate

/-- Coordinate vectors in the canonical homogeneous basis at `a`. -/
abbrev Coeff (a : ZMod 8) : Type := Fin (realRepDim a.val) → ℝ

namespace Coeff

def zero (a : ZMod 8) : Coeff a := fun _ => 0

def one (a : ZMod 8) : Coeff a := fun i => if i.val = 0 then 1 else 0

def add (a : ZMod 8) (x y : Coeff a) : Coeff a := fun i => x i + y i

def neg (a : ZMod 8) (x : Coeff a) : Coeff a := fun i => -x i

def smul (a : ZMod 8) (r : ℝ) (x : Coeff a) : Coeff a := fun i => r * x i

/-- Signed-xor convolution in the canonical basis. -/
def mul (a : ZMod 8) (x y : Coeff a) : Coeff a := fun k =>
  ∑ i : Fin (realRepDim a.val),
    x i * y (realRepMulIdx a i k) *
      (realRepMulSign a i (realRepMulIdx a i k) : ℝ)

/-- Projection onto one homogeneous coordinate layer. -/
def component (a : ZMod 8) (d : ZMod 2) (x : Coeff a) : Coeff a := fun i =>
  if realRepBasisParity a i = d then x i else 0

/-- Coordinate support in one homogeneous layer. -/
def MemGrade (a : ZMod 8) (d : ZMod 2) (x : Coeff a) : Prop :=
  ∀ i, realRepBasisParity a i ≠ d → x i = 0

end Coeff
end RModCoordinate
end Superfusion
