import Mathlib.CategoryTheory.Monoidal.Center

/-!
# Duality comparisons for a central factor whose square is the unit

These explicit isomorphisms are the ordinary monoidal expressions behind
the parity dual normalizers. A central square contraction retains both
maps; the positive comparison removes its pair, while the negative one
first crosses the inner factor past the object being evaluated.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.CentralDuality

open CategoryTheory MonoidalCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

noncomputable def positive (X Y : V) (P : Center V) (m : P ⊗ P ≅ 𝟙_ (Center V)) :
    (X ⊗ (Y ⊗ P.1)) ⊗ P.1 ≅ X ⊗ Y :=
  tensorIso (α_ X Y P.1).symm (Iso.refl P.1) ≪≫
    α_ (X ⊗ Y) P.1 P.1 ≪≫
      tensorIso (Iso.refl (X ⊗ Y)) ((Center.forget V).mapIso m) ≪≫ ρ_ (X ⊗ Y)

noncomputable def negative (X Y : V) (P : Center V) (m : P ⊗ P ≅ 𝟙_ (Center V)) :
    ((Y ⊗ P.1) ⊗ X) ⊗ P.1 ≅ Y ⊗ X :=
  tensorIso (α_ Y P.1 X ≪≫ tensorIso (Iso.refl Y) (P.2.β X) ≪≫
    (α_ Y X P.1).symm) (Iso.refl P.1) ≪≫
      α_ (Y ⊗ X) P.1 P.1 ≪≫
        tensorIso (Iso.refl (Y ⊗ X)) ((Center.forget V).mapIso m) ≪≫ ρ_ (Y ⊗ X)

/-- The local associator after deleting its two outer unit factors. -/
noncomputable def middle (X Y Z : V) (P : Center V) :
    ((X ⊗ Y) ⊗ P.1) ⊗ Z ≅ X ⊗ ((Y ⊗ Z) ⊗ P.1) :=
  α_ (X ⊗ Y) P.1 Z ≪≫ tensorIso (Iso.refl (X ⊗ Y)) (P.2.β Z) ≪≫
    (α_ (X ⊗ Y) Z P.1).symm ≪≫ tensorIso (α_ X Y Z) (Iso.refl P.1) ≪≫
      α_ X (Y ⊗ Z) P.1

end RMod.Classification.CentralDuality
