import RMod.Classification.Abstract.SpanNatural

/-!
# Zero comparisons and scalar natural endomorphisms

Zero components define a comparison in every degree. Real multiples of
identity components define even natural endomorphisms. The associated
laws include signed naturality and are proved for the exact component maps.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNat

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def zeroData (F G : SpanSuperfunctorData C D S T) : SpanHomogeneousNatData F G := ⟨fun _ => 0⟩

theorem zeroLaws (F G : SpanSuperfunctorData C D S T) (a : ZMod 2) :
    SpanHomogeneousNatLaws a (zeroData F G) where
  grade X := D.laws.grade_zero _ _ _
  naturality f hf := by change _ ≫ 0 = _ • (0 ≫ _); simp

def zero (F G : SpanSuperfunctor C D S T) (a : ZMod 2) : SpanHomogeneousNat F G a :=
  ⟨zeroData F.data G.data, zeroLaws F.data G.data a⟩

def scalarData (F : SpanSuperfunctorData C D S T) (r : ℝ) : SpanHomogeneousNatData F F :=
  ⟨fun X => r • 𝟙 (F.obj X)⟩

theorem scalarLaws (F : SpanSuperfunctorData C D S T) (r : ℝ) :
    SpanHomogeneousNatLaws 0 (scalarData F r) where
  grade X := D.laws.grade_smul r _ (D.laws.id_even _)
  naturality {X Y b} f _hf := by
    change F.map f ≫ (r • 𝟙 (F.obj Y)) =
      ((-1 : ℝ) ^ (0 * b : ZMod 2).val) • ((r • 𝟙 (F.obj X)) ≫ F.map f)
    simp only [zero_mul, ZMod.val_zero, pow_zero, one_smul, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]

def scalar (F : SpanSuperfunctor C D S T) (r : ℝ) : SpanHomogeneousNat F F 0 :=
  ⟨scalarData F.data r, scalarLaws F.data r⟩

end RMod.Classification.SpanHomogeneousNat
