import RMod.Classification.Abstract.SpanNatural
import RMod.Classification.Proofs.ParityPowers

/-!
# Composition of homogeneous natural transformations

Componentwise composition adds the two degrees. Multiplication of the
two naturality signs is exactly the sign of their sum. This construction
will transport inverse identities from the generator to every object.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNat

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

def compData {F G H : SpanSuperfunctorData C D S T}
    (η : SpanHomogeneousNatData F G) (θ : SpanHomogeneousNatData G H) :
    SpanHomogeneousNatData F H := ⟨fun X => η.app X ≫ θ.app X⟩

theorem compLaws {F G H : SpanSuperfunctor C D S T} {a b : ZMod 2}
    (η : SpanHomogeneousNat F G a) (θ : SpanHomogeneousNat G H b) :
    SpanHomogeneousNatLaws (a + b) (compData η.data θ.data) where
  grade X := D.laws.comp_grade _ _ (η.laws.grade X) (θ.laws.grade X)
  naturality {X Y c} f hf := by
    change F.data.map f ≫ (η.data.app Y ≫ θ.data.app Y) =
      ((-1 : ℝ) ^ ((a + b) * c).val) • ((η.data.app X ≫ θ.data.app X) ≫ H.data.map f)
    rw [← Category.assoc, η.laws.naturality f hf, Linear.smul_comp, Category.assoc,
      θ.laws.naturality f hf, Linear.comp_smul, smul_smul, add_mul, parity_power_add,
      Category.assoc]

def comp {F G H : SpanSuperfunctor C D S T} {a b : ZMod 2}
    (η : SpanHomogeneousNat F G a) (θ : SpanHomogeneousNat G H b) :
    SpanHomogeneousNat F H (a + b) := ⟨compData η.data θ.data, compLaws η θ⟩

/-- Equal homogeneous degrees cancel in the composite. -/
def compSameDegree {F G H : SpanSuperfunctor C D S T} {a : ZMod 2}
    (η : SpanHomogeneousNat F G a) (θ : SpanHomogeneousNat G H a) :
    SpanHomogeneousNat F H 0 :=
  ⟨compData η.data θ.data, by simpa only [CharTwo.add_self_eq_zero] using compLaws η θ⟩

end RMod.Classification.SpanHomogeneousNat
