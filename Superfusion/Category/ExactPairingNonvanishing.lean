import Mathlib.CategoryTheory.Preadditive.Biproducts
import Superfusion.Category.Even

/-!
# Nonvanishing consequences of an exact pairing

An exact pairing prevents the tensor product of its two members from being a
zero object unless the left member is already zero.  This follows directly
from the snake identity in the ordinary monoidal even core.

As a finite-biproduct consequence, any decomposition of that tensor product
has a nonempty index whenever the left identity morphism is nonzero.  These
statements require no semisimplicity, dimension calculation, or chosen basis.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Superfusion.Category

variable {K : Type*} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory K C]

namespace SuperExactPairing

variable {X Y : C}

/-- If the tensor product in an exact pairing is zero in the even
subcategory, then its left member is zero there as well. -/
theorem evenTensor_isZero_imp_left_isZero
    (p : SuperExactPairing K X Y)
    (hXY : IsZero (evenObj K C (X ⊗ Y))) :
    IsZero (evenObj K C X) := by
  let pEven : ExactPairing (evenObj K C X) (evenObj K C Y) :=
    p.toEven
  letI : ExactPairing (evenObj K C X) (evenObj K C Y) := pEven
  have hcoevaluation :
      ExactPairing.coevaluation (evenObj K C X) (evenObj K C Y) = 0 :=
    hXY.eq_of_tgt _ _
  have hsnake :=
    ExactPairing.evaluation_coevaluation
      (evenObj K C X) (evenObj K C Y)
  rw [hcoevaluation] at hsnake
  have hunitors :
      (λ_ (evenObj K C X)).hom ≫ (ρ_ (evenObj K C X)).inv = 0 := by
    simpa using hsnake.symm
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (evenObj K C X) =
        (λ_ (evenObj K C X)).inv ≫
          ((λ_ (evenObj K C X)).hom ≫
            (ρ_ (evenObj K C X)).inv) ≫
          (ρ_ (evenObj K C X)).hom := by simp
    _ = 0 := by rw [hunitors]; simp

/-- A nonzero identity on the left member of an exact pairing forces its
tensor product with the right member to be nonzero in the even
subcategory. -/
theorem not_evenTensor_isZero_of_id_ne_zero
    (p : SuperExactPairing K X Y)
    (hX : 𝟙 X ≠ 0) :
    ¬ IsZero (evenObj K C (X ⊗ Y)) := by
  intro hXY
  have hXzero := p.evenTensor_isZero_imp_left_isZero hXY
  apply hX
  have hEvenId :
      𝟙 (evenObj K C X) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hXzero
  exact congrArg (fun f => f.hom) hEvenId

/-- A finite-biproduct decomposition of the tensor product in an exact
pairing has a nonempty index whenever the left member has nonzero
identity. -/
theorem positive_index_of_pairing_decomposition
    [HasFiniteBiproducts (EvenSubcategory K C)]
    (p : SuperExactPairing K X Y)
    (hX : 𝟙 X ≠ 0)
    {r : ℕ} {S : Fin r → C}
    (e : evenObj K C (X ⊗ Y) ≅
      ⨁ fun i : Fin r => evenObj K C (S i)) :
    0 < r := by
  by_contra hr
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
  subst r
  apply p.not_evenTensor_isZero_of_id_ne_zero hX
  have hBiproduct :
      IsZero (⨁ fun i : Fin 0 => evenObj K C (S i)) := by
    rw [IsZero.iff_id_eq_zero]
    have htotal :=
      CategoryTheory.Limits.IsBilimit.total
        (biproduct.isBilimit
          (fun i : Fin 0 => evenObj K C (S i)))
    simpa using htotal.symm
  exact hBiproduct.of_iso e

end SuperExactPairing

end Superfusion.Category
