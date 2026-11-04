import RMod.Classification.Abstract.SpanNatural

/-!
# Scaling a homogeneous natural comparison

Real scalar multiplication acts componentwise and preserves the degree.
Linearity of composition proves signed naturality for these exact maps.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNat

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def smulData {F G : SpanSuperfunctorData C D S T} (r : ℝ) (η : SpanHomogeneousNatData F G) :
    SpanHomogeneousNatData F G := ⟨fun X => r • η.app X⟩

theorem smulLaws {F G : SpanSuperfunctor C D S T} {a : ZMod 2}
    (r : ℝ) (η : SpanHomogeneousNat F G a) : SpanHomogeneousNatLaws a (smulData r η.data) where
  grade X := D.laws.grade_smul r _ (η.laws.grade X)
  naturality {X Y b} f hf := by
    change F.data.map f ≫ (r • η.data.app Y) =
      ((-1 : ℝ) ^ (a * b).val) • ((r • η.data.app X) ≫ G.data.map f)
    rw [Linear.comp_smul, η.laws.naturality f hf, Linear.smul_comp, smul_smul, smul_smul,
      mul_comm r]

def smul {F G : SpanSuperfunctor C D S T} {a : ZMod 2} (r : ℝ) (η : SpanHomogeneousNat F G a) :
    SpanHomogeneousNat F G a := ⟨smulData r η.data, smulLaws r η⟩

end RMod.Classification.SpanHomogeneousNat
