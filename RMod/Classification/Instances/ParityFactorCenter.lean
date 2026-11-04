import RMod.Classification.Instances.ParityContractionCenter
import RMod.Classification.Proofs.Normalizers

/-!
# Both parity factors and their multiplications in Mathlib's center

The zero factor carries the central unit half-braiding and the odd factor
carries the specified parity half-braiding. Their underlying objects and
multiplication maps are exactly the existing factor and multiplyFactors
data. The four multiplication cases inherit the center-morphism equation
from the unitors or the proved central contraction.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def factorHalfBraiding (a : ZMod 2) :
    HalfBraiding (evenObj ℝ (LinearCategory C) (p.factor a)) := by
  by_cases ha : a = 0
  · subst a
    exact (𝟙_ (Center (EvenSubcategory ℝ (LinearCategory C)))).2
  · simpa only [PiData.factor, if_neg ha] using parityHalfBraiding C p hp

noncomputable def factorCenter (a : ZMod 2) : Center (EvenSubcategory ℝ (LinearCategory C)) :=
  ⟨evenObj ℝ (LinearCategory C) (p.factor a), factorHalfBraiding C p hp a⟩

noncomputable def factorMultiplyCenterHom (a b : ZMod 2) :
    factorCenter C p hp a ⊗ factorCenter C p hp b ⟶ factorCenter C p hp (a + b) where
  f := (IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b)).hom
  comm X := by
    rcases parity_cases a with rfl | rfl <;> rcases parity_cases b with rfl | rfl
    · exact ((λ_ (𝟙_ (Center (EvenSubcategory ℝ (LinearCategory C))))).hom).comm X
    · exact ((λ_ (parityCenter C p hp)).hom).comm X
    · exact ((ρ_ (parityCenter C p hp)).hom).comm X
    · exact (parityContractionCenterHom C p hp).comm X

noncomputable def factorMultiplyCenterIso (a b : ZMod 2) :
    factorCenter C p hp a ⊗ factorCenter C p hp b ≅ factorCenter C p hp (a + b) := by
  let e := IsoData.toEvenIso C (p.multiplyFactors a b) (hp.multiplyFactors_evenIso C.laws a b)
  letI : IsIso (factorMultiplyCenterHom C p hp a b).f := e.isIso_hom
  exact Center.isoMk (factorMultiplyCenterHom C p hp a b)

end RMod.Classification
