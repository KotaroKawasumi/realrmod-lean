import RMod.Definitions.WeaklyPointedSuperfusionPredicates

/-!
# Weakly pointed superfusion categories

The laws in this file refer to exactly one
`WeaklyPointedSuperfusionData` value. Existence properties that are not used
by computation remain propositions; all executable operations are already in
the data layer.
-/

set_option autoImplicit false

universe u v

namespace RMod

/-! ## Laws -/

/-- Laws making the raw operations in `D` into a real weakly pointed
superfusion category. -/
structure WeaklyPointedSuperfusionLaws
    (D : WeaklyPointedSuperfusionData.{u, v}) : Prop where
  /- Category laws. -/
  comp_id : ∀ {X Y} (f : D.Hom X Y), D.comp f (D.id Y) = f
  id_comp : ∀ {X Y} (f : D.Hom X Y), D.comp (D.id X) f = f
  comp_assoc : ∀ {W X Y Z} (f : D.Hom W X) (g : D.Hom X Y)
    (h : D.Hom Y Z), D.comp (D.comp f g) h = D.comp f (D.comp g h)

  /- Additive and real-linear laws. -/
  add_assoc : ∀ {X Y} (f g h : D.Hom X Y),
    D.add (D.add f g) h = D.add f (D.add g h)
  zero_add : ∀ {X Y} (f : D.Hom X Y), D.add D.zero f = f
  add_zero : ∀ {X Y} (f : D.Hom X Y), D.add f D.zero = f
  add_comm : ∀ {X Y} (f g : D.Hom X Y), D.add f g = D.add g f
  neg_add : ∀ {X Y} (f : D.Hom X Y), D.add (D.neg f) f = D.zero
  one_smul : ∀ {X Y} (f : D.Hom X Y), D.smul 1 f = f
  mul_smul : ∀ {X Y} (a b : ℝ) (f : D.Hom X Y),
    D.smul (a * b) f = D.smul a (D.smul b f)
  add_smul : ∀ {X Y} (a b : ℝ) (f : D.Hom X Y),
    D.smul (a + b) f = D.add (D.smul a f) (D.smul b f)
  smul_add : ∀ {X Y} (a : ℝ) (f g : D.Hom X Y),
    D.smul a (D.add f g) = D.add (D.smul a f) (D.smul a g)
  zero_smul : ∀ {X Y} (f : D.Hom X Y), D.smul 0 f = D.zero
  smul_zero : ∀ {X Y} (a : ℝ), D.smul a (D.zero : D.Hom X Y) = D.zero
  add_comp : ∀ {X Y Z} (f g : D.Hom X Y) (h : D.Hom Y Z),
    D.comp (D.add f g) h = D.add (D.comp f h) (D.comp g h)
  comp_add : ∀ {X Y Z} (f : D.Hom X Y) (g h : D.Hom Y Z),
    D.comp f (D.add g h) = D.add (D.comp f g) (D.comp f h)
  smul_comp : ∀ {X Y Z} (a : ℝ) (f : D.Hom X Y) (g : D.Hom Y Z),
    D.comp (D.smul a f) g = D.smul a (D.comp f g)
  comp_smul : ∀ {X Y Z} (a : ℝ) (f : D.Hom X Y) (g : D.Hom Y Z),
    D.comp f (D.smul a g) = D.smul a (D.comp f g)

  /- Grading laws. -/
  grade_zero : ∀ X Y a, (D.zero : D.Hom X Y) ∈ D.grade X Y a
  grade_add : ∀ {X Y a} (f g : D.Hom X Y),
    f ∈ D.grade X Y a → g ∈ D.grade X Y a → D.add f g ∈ D.grade X Y a
  grade_neg : ∀ {X Y a} (f : D.Hom X Y),
    f ∈ D.grade X Y a → D.neg f ∈ D.grade X Y a
  grade_smul : ∀ {X Y a} (r : ℝ) (f : D.Hom X Y),
    f ∈ D.grade X Y a → D.smul r f ∈ D.grade X Y a
  grade_decomposition : ∀ {X Y} (f : D.Hom X Y),
    ∃ f₀ f₁ : D.Hom X Y,
      f₀ ∈ D.grade X Y 0 ∧ f₁ ∈ D.grade X Y 1 ∧ D.add f₀ f₁ = f
  grade_disjoint : ∀ {X Y} (f : D.Hom X Y),
    f ∈ D.grade X Y 0 → f ∈ D.grade X Y 1 → f = D.zero
  id_even : ∀ X, D.id X ∈ D.grade X X 0
  comp_grade : ∀ {X Y Z a b} (f : D.Hom X Y) (g : D.Hom Y Z),
    f ∈ D.grade X Y a → g ∈ D.grade Y Z b →
      D.comp f g ∈ D.grade X Z (a + b)

  /- Tensor, super-interchange, and coherence laws. -/
  tensor_grade : ∀ {X₁ Y₁ X₂ Y₂ a b}
    (f : D.Hom X₁ Y₁) (g : D.Hom X₂ Y₂),
    f ∈ D.grade X₁ Y₁ a → g ∈ D.grade X₂ Y₂ b →
      D.tensorHom f g ∈
        D.grade (D.tensorObj X₁ X₂) (D.tensorObj Y₁ Y₂) (a + b)
  tensor_id : ∀ X Y,
    D.tensorHom (D.id X) (D.id Y) = D.id (D.tensorObj X Y)
  tensor_add_left : ∀ {X₁ Y₁ X₂ Y₂}
    (f f' : D.Hom X₁ Y₁) (g : D.Hom X₂ Y₂),
    D.tensorHom (D.add f f') g =
      D.add (D.tensorHom f g) (D.tensorHom f' g)
  tensor_add_right : ∀ {X₁ Y₁ X₂ Y₂}
    (f : D.Hom X₁ Y₁) (g g' : D.Hom X₂ Y₂),
    D.tensorHom f (D.add g g') =
      D.add (D.tensorHom f g) (D.tensorHom f g')
  tensor_smul_left : ∀ {X₁ Y₁ X₂ Y₂} (r : ℝ)
    (f : D.Hom X₁ Y₁) (g : D.Hom X₂ Y₂),
    D.tensorHom (D.smul r f) g = D.smul r (D.tensorHom f g)
  tensor_smul_right : ∀ {X₁ Y₁ X₂ Y₂} (r : ℝ)
    (f : D.Hom X₁ Y₁) (g : D.Hom X₂ Y₂),
    D.tensorHom f (D.smul r g) = D.smul r (D.tensorHom f g)
  super_interchange : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ b c}
    (f : D.Hom Y₁ Z₁) (g : D.Hom Y₂ Z₂)
    (h : D.Hom X₁ Y₁) (k : D.Hom X₂ Y₂),
    g ∈ D.grade Y₂ Z₂ b → h ∈ D.grade X₁ Y₁ c →
      D.comp (D.tensorHom h k) (D.tensorHom f g) =
        D.smul ((-1 : ℝ) ^ (b * c).val)
          (D.tensorHom (D.comp h f) (D.comp k g))
  associator_hom_inv : ∀ X Y Z,
    D.comp (D.associatorHom X Y Z) (D.associatorInv X Y Z) =
      D.id (D.tensorObj (D.tensorObj X Y) Z)
  associator_inv_hom : ∀ X Y Z,
    D.comp (D.associatorInv X Y Z) (D.associatorHom X Y Z) =
      D.id (D.tensorObj X (D.tensorObj Y Z))
  associator_hom_even : ∀ X Y Z,
    D.associatorHom X Y Z ∈
      D.grade (D.tensorObj (D.tensorObj X Y) Z)
        (D.tensorObj X (D.tensorObj Y Z)) 0
  associator_inv_even : ∀ X Y Z,
    D.associatorInv X Y Z ∈
      D.grade (D.tensorObj X (D.tensorObj Y Z))
        (D.tensorObj (D.tensorObj X Y) Z) 0
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃}
    (f₁ : D.Hom X₁ Y₁) (f₂ : D.Hom X₂ Y₂) (f₃ : D.Hom X₃ Y₃),
    D.comp (D.tensorHom (D.tensorHom f₁ f₂) f₃)
        (D.associatorHom Y₁ Y₂ Y₃) =
      D.comp (D.associatorHom X₁ X₂ X₃)
        (D.tensorHom f₁ (D.tensorHom f₂ f₃))
  left_unitor_hom_inv : ∀ X,
    D.comp (D.leftUnitorHom X) (D.leftUnitorInv X) =
      D.id (D.tensorObj D.tensorUnit X)
  left_unitor_inv_hom : ∀ X,
    D.comp (D.leftUnitorInv X) (D.leftUnitorHom X) = D.id X
  left_unitor_hom_even : ∀ X,
    D.leftUnitorHom X ∈ D.grade (D.tensorObj D.tensorUnit X) X 0
  left_unitor_inv_even : ∀ X,
    D.leftUnitorInv X ∈ D.grade X (D.tensorObj D.tensorUnit X) 0
  left_unitor_naturality : ∀ {X Y} (f : D.Hom X Y),
    D.comp (D.tensorHom (D.id D.tensorUnit) f) (D.leftUnitorHom Y) =
      D.comp (D.leftUnitorHom X) f
  right_unitor_hom_inv : ∀ X,
    D.comp (D.rightUnitorHom X) (D.rightUnitorInv X) =
      D.id (D.tensorObj X D.tensorUnit)
  right_unitor_inv_hom : ∀ X,
    D.comp (D.rightUnitorInv X) (D.rightUnitorHom X) = D.id X
  right_unitor_hom_even : ∀ X,
    D.rightUnitorHom X ∈ D.grade (D.tensorObj X D.tensorUnit) X 0
  right_unitor_inv_even : ∀ X,
    D.rightUnitorInv X ∈ D.grade X (D.tensorObj X D.tensorUnit) 0
  right_unitor_naturality : ∀ {X Y} (f : D.Hom X Y),
    D.comp (D.tensorHom f (D.id D.tensorUnit)) (D.rightUnitorHom Y) =
      D.comp (D.rightUnitorHom X) f
  pentagon : ∀ W X Y Z,
    D.comp
      (D.comp
        (D.whiskerRight (D.associatorHom W X Y) Z)
        (D.associatorHom W (D.tensorObj X Y) Z))
      (D.whiskerLeft W (D.associatorHom X Y Z)) =
        D.comp
          (D.associatorHom (D.tensorObj W X) Y Z)
          (D.associatorHom W X (D.tensorObj Y Z))
  triangle : ∀ X Y,
    D.comp
      (D.associatorHom X D.tensorUnit Y)
      (D.whiskerLeft X (D.leftUnitorHom Y)) =
        D.whiskerRight (D.rightUnitorHom X) Y

  /- Superfusion laws. -/
  has_finite_biproducts : ∀ {n : ℕ} (S : Fin n → D.Obj),
    D.HasFiniteBiproduct S
  semisimple : ∀ X : D.Obj,
    ∃ (n : ℕ) (S : Fin n → D.Obj),
      (∀ i, D.IsSimple (S i)) ∧ D.HasDecomposition X S
  graded_schur : ∀ {X Y : D.Obj},
    D.IsSimple X → D.IsSimple Y →
      ∀ {a : ZMod 2} (f : D.Hom X Y),
        D.IsHomogeneous a f → f ≠ D.zero → D.IsIso f
  finite_dimensional_hom : ∀ X Y : D.Obj, D.HasFiniteBasis X Y
  finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → D.Obj),
      (∀ i, D.IsSimple (S i)) ∧
        ∀ X : D.Obj, D.IsSimple X →
          ∃ (i : Fin n) (a : ZMod 2), D.HasHomogeneousIso a X (S i)
  simple_unit : D.IsSimple D.tensorUnit
  unit_end_scalar_injective : ∀ r s : ℝ,
    D.smul r (D.id D.tensorUnit) = D.smul s (D.id D.tensorUnit) → r = s
  unit_end_scalar_surjective : ∀ f : D.Hom D.tensorUnit D.tensorUnit,
    ∃ r : ℝ, D.smul r (D.id D.tensorUnit) = f
  has_right_dual : ∀ X : D.Obj,
    ∃ Y : D.Obj, D.HasExactPairing X Y
  has_left_dual : ∀ X : D.Obj,
    ∃ Y : D.Obj, D.HasExactPairing Y X

  /- Weak pointedness. -/
  weakly_pointed : ∀ X : D.Obj,
    D.IsSimple X → D.IsWeaklyInvertible X

/-! ## Completed structure -/

/-- Computational data bundled with laws for that exact data. -/
structure WeaklyPointedSuperfusion where
  data : WeaklyPointedSuperfusionData.{u, v}
  laws : WeaklyPointedSuperfusionLaws data

end RMod
