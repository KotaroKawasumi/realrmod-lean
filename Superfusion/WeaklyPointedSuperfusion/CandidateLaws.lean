import Superfusion.WeaklyPointedSuperfusion.CandidateData

/-!
# Laws for raw weakly pointed superfusion data

Every notion in this file is stated directly in terms of `CandidateData`.
No project-specific category class is imported or hidden behind the final
predicate.
-/

set_option autoImplicit false

universe u v

namespace Superfusion

namespace CandidateData

variable (D : CandidateData.{u, v})

/-- A morphism belongs to the chosen homogeneous part of degree `a`. -/
def IsHomogeneous {X Y : D.Obj} (a : ZMod 2) (f : D.Hom X Y) : Prop :=
  f ∈ D.grade X Y a

/-- Raw left whiskering, derived from tensoring with an identity. -/
def whiskerLeft (X : D.Obj) {Y Z : D.Obj} (f : D.Hom Y Z) :
    D.Hom (D.tensorObj X Y) (D.tensorObj X Z) :=
  D.tensorHom (D.id X) f

/-- Raw right whiskering, derived from tensoring with an identity. -/
def whiskerRight {X Y : D.Obj} (f : D.Hom X Y) (Z : D.Obj) :
    D.Hom (D.tensorObj X Z) (D.tensorObj Y Z) :=
  D.tensorHom f (D.id Z)

/-- A fixed-order finite sum using only the raw zero and addition. -/
def finSum {X Y : D.Obj} :
    (n : ℕ) → (Fin n → D.Hom X Y) → D.Hom X Y
  | 0, _ => D.zero
  | n + 1, f =>
      D.add (finSum n (fun i => f i.castSucc)) (f (Fin.last n))

/-- A raw morphism has a two-sided inverse. -/
def IsIso {X Y : D.Obj} (f : D.Hom X Y) : Prop :=
  ∃ g : D.Hom Y X,
    D.comp f g = D.id X ∧ D.comp g f = D.id Y

/-- Two objects are isomorphic through raw mutually inverse morphisms. -/
def ObjectsIso (X Y : D.Obj) : Prop :=
  ∃ f : D.Hom X Y, IsIso D f

/-- An object is zero in the raw category. -/
def IsZeroObject (X : D.Obj) : Prop :=
  ∀ Y : D.Obj,
    (∀ f : D.Hom X Y, f = D.zero) ∧
    (∀ f : D.Hom Y X, f = D.zero)

/-- Left cancellation inside the even subcategory. -/
def IsEvenMono {X Y : D.Obj} (f : D.Hom X Y) : Prop :=
  D.IsHomogeneous 0 f ∧
    ∀ (Z : D.Obj) (g h : D.Hom Z X),
      D.IsHomogeneous 0 g → D.IsHomogeneous 0 h →
        D.comp g f = D.comp h f → g = h

/-- Invertibility through even morphisms. -/
def IsEvenIso {X Y : D.Obj} (f : D.Hom X Y) : Prop :=
  D.IsHomogeneous 0 f ∧
    ∃ g : D.Hom Y X,
      D.IsHomogeneous 0 g ∧
        D.comp f g = D.id X ∧ D.comp g f = D.id Y

/-- Simplicity in the even subcategory, stated without a category class. -/
def IsSimple (X : D.Obj) : Prop :=
  ∀ (Y : D.Obj) (f : D.Hom Y X),
    D.IsEvenMono f → (D.IsEvenIso f ↔ f ≠ D.zero)

/-- An isomorphism homogeneous in both directions with parity `a`. -/
structure HomogeneousIso (a : ZMod 2) (X Y : D.Obj) where
  hom : D.Hom X Y
  inv : D.Hom Y X
  hom_inv : D.comp hom inv = D.id X
  inv_hom : D.comp inv hom = D.id Y
  hom_mem : D.IsHomogeneous a hom
  inv_mem : D.IsHomogeneous a inv

/-- Raw finite-biproduct data for a finite family. -/
structure BiproductWitness {n : ℕ} (S : Fin n → D.Obj) where
  object : D.Obj
  inclusion : (i : Fin n) → D.Hom (S i) object
  projection : (i : Fin n) → D.Hom object (S i)
  inclusion_even : ∀ i, D.IsHomogeneous 0 (inclusion i)
  projection_even : ∀ i, D.IsHomogeneous 0 (projection i)
  inclusion_projection_self : ∀ i,
    D.comp (inclusion i) (projection i) = D.id (S i)
  inclusion_projection_ne : ∀ i j, i ≠ j →
    D.comp (inclusion i) (projection j) = D.zero
  projection_inclusion_total :
    D.finSum n (fun i => D.comp (projection i) (inclusion i)) = D.id object

/-- A chosen object is the biproduct of a finite family. -/
structure DecompositionWitness (X : D.Obj) {n : ℕ} (S : Fin n → D.Obj) where
  inclusion : (i : Fin n) → D.Hom (S i) X
  projection : (i : Fin n) → D.Hom X (S i)
  inclusion_even : ∀ i, D.IsHomogeneous 0 (inclusion i)
  projection_even : ∀ i, D.IsHomogeneous 0 (projection i)
  inclusion_projection_self : ∀ i,
    D.comp (inclusion i) (projection i) = D.id (S i)
  inclusion_projection_ne : ∀ i j, i ≠ j →
    D.comp (inclusion i) (projection j) = D.zero
  projection_inclusion_total :
    D.finSum n (fun i => D.comp (projection i) (inclusion i)) = D.id X

/-- Explicit finite basis data for a raw Hom space. -/
structure FiniteBasisWitness (X Y : D.Obj) where
  dimension : ℕ
  basis : Fin dimension → D.Hom X Y
  coordinates : D.Hom X Y → Fin dimension → ℝ
  reconstruct : ∀ f,
    D.finSum dimension (fun i => D.smul (coordinates f i) (basis i)) = f
  coordinates_unique : ∀ f c,
    D.finSum dimension (fun i => D.smul (c i) (basis i)) = f →
      c = coordinates f

/-- Even coevaluation/evaluation data with both zigzag identities. -/
structure ExactPairingWitness (X Y : D.Obj) where
  coeval : D.Hom D.tensorUnit (D.tensorObj X Y)
  eval : D.Hom (D.tensorObj Y X) D.tensorUnit
  coeval_even : D.IsHomogeneous 0 coeval
  eval_even : D.IsHomogeneous 0 eval
  coevaluation_evaluation :
    D.comp
      (D.comp (D.whiskerLeft Y coeval) (D.associatorInv Y X Y))
      (D.whiskerRight eval Y) =
        D.comp (D.rightUnitorHom Y) (D.leftUnitorInv Y)
  evaluation_coevaluation :
    D.comp
      (D.comp (D.whiskerRight coeval X) (D.associatorHom X Y X))
      (D.whiskerLeft X eval) =
        D.comp (D.leftUnitorHom X) (D.rightUnitorInv X)

/-- The parity of an even/odd multiplicity coordinate. -/
def superIndexParity {p q : ℕ} : Fin p ⊕ Fin q → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Fixed-order sum over even and odd multiplicity coordinates. -/
def superFinSum {X Y : D.Obj} {p q : ℕ}
    (f : Fin p ⊕ Fin q → D.Hom X Y) : D.Hom X Y :=
  D.add (D.finSum p (fun i => f (Sum.inl i)))
    (D.finSum q (fun i => f (Sum.inr i)))

/-- A decomposition into `p` even and `q` odd copies of `X`. -/
structure SuperMultiplicityWitness (A X : D.Obj) (p q : ℕ) where
  inclusion : (i : Fin p ⊕ Fin q) → D.Hom X A
  projection : (i : Fin p ⊕ Fin q) → D.Hom A X
  inclusion_mem : ∀ i, D.IsHomogeneous (superIndexParity i) (inclusion i)
  projection_mem : ∀ i, D.IsHomogeneous (superIndexParity i) (projection i)
  inclusion_projection_self : ∀ i,
    D.comp (inclusion i) (projection i) = D.id X
  inclusion_projection_ne : ∀ i j, i ≠ j →
    D.comp (inclusion i) (projection j) = D.zero
  projection_inclusion_total :
    D.superFinSum (fun i => D.comp (projection i) (inclusion i)) = D.id A

/-- Explicit weak-invertibility data for an object. -/
structure WeakInvertibilityWitness (X : D.Obj) where
  dual : D.Obj
  pairing : D.ExactPairingWitness X dual
  evenMultiplicity : ℕ
  oddMultiplicity : ℕ
  multiplicity_pos : 0 < evenMultiplicity + oddMultiplicity
  multiplicity : D.SuperMultiplicityWitness
    (D.tensorObj X dual) D.tensorUnit evenMultiplicity oddMultiplicity

/-- An object is weakly invertible when explicit witness data exists. -/
def IsWeaklyInvertible (X : D.Obj) : Prop :=
  Nonempty (D.WeakInvertibilityWitness X)

end CandidateData

/-- All laws making raw real-linear graded monoidal data into a weakly
pointed superfusion category.  Every field is stated directly using the raw
operations of `D`. -/
structure CandidateLaws (D : CandidateData.{u, v}) : Prop where
  /- Category laws. -/
  comp_id : ∀ {X Y} (f : D.Hom X Y), D.comp f (D.id Y) = f
  id_comp : ∀ {X Y} (f : D.Hom X Y), D.comp (D.id X) f = f
  comp_assoc : ∀ {W X Y Z} (f : D.Hom W X) (g : D.Hom X Y)
    (h : D.Hom Y Z), D.comp (D.comp f g) h = D.comp f (D.comp g h)

  /- Additive and real-linear laws on every Hom space. -/
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
      D.tensorHom f g ∈ D.grade (D.tensorObj X₁ X₂) (D.tensorObj Y₁ Y₂) (a + b)
  tensor_id : ∀ X Y,
    D.tensorHom (D.id X) (D.id Y) = D.id (D.tensorObj X Y)
  tensor_add_left : ∀ {X₁ Y₁ X₂ Y₂}
    (f f' : D.Hom X₁ Y₁) (g : D.Hom X₂ Y₂),
    D.tensorHom (D.add f f') g = D.add (D.tensorHom f g) (D.tensorHom f' g)
  tensor_add_right : ∀ {X₁ Y₁ X₂ Y₂}
    (f : D.Hom X₁ Y₁) (g g' : D.Hom X₂ Y₂),
    D.tensorHom f (D.add g g') = D.add (D.tensorHom f g) (D.tensorHom f g')
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
      D.grade (D.tensorObj (D.tensorObj X Y) Z) (D.tensorObj X (D.tensorObj Y Z)) 0
  associator_inv_even : ∀ X Y Z,
    D.associatorInv X Y Z ∈
      D.grade (D.tensorObj X (D.tensorObj Y Z)) (D.tensorObj (D.tensorObj X Y) Z) 0
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃}
    (f₁ : D.Hom X₁ Y₁) (f₂ : D.Hom X₂ Y₂) (f₃ : D.Hom X₃ Y₃),
    D.comp (D.tensorHom (D.tensorHom f₁ f₂) f₃) (D.associatorHom Y₁ Y₂ Y₃) =
      D.comp (D.associatorHom X₁ X₂ X₃) (D.tensorHom f₁ (D.tensorHom f₂ f₃))
  leftUnitor_hom_inv : ∀ X,
    D.comp (D.leftUnitorHom X) (D.leftUnitorInv X) =
      D.id (D.tensorObj D.tensorUnit X)
  leftUnitor_inv_hom : ∀ X,
    D.comp (D.leftUnitorInv X) (D.leftUnitorHom X) = D.id X
  leftUnitor_hom_even : ∀ X,
    D.leftUnitorHom X ∈ D.grade (D.tensorObj D.tensorUnit X) X 0
  leftUnitor_inv_even : ∀ X,
    D.leftUnitorInv X ∈ D.grade X (D.tensorObj D.tensorUnit X) 0
  leftUnitor_naturality : ∀ {X Y} (f : D.Hom X Y),
    D.comp (D.tensorHom (D.id D.tensorUnit) f) (D.leftUnitorHom Y) =
      D.comp (D.leftUnitorHom X) f
  rightUnitor_hom_inv : ∀ X,
    D.comp (D.rightUnitorHom X) (D.rightUnitorInv X) =
      D.id (D.tensorObj X D.tensorUnit)
  rightUnitor_inv_hom : ∀ X,
    D.comp (D.rightUnitorInv X) (D.rightUnitorHom X) = D.id X
  rightUnitor_hom_even : ∀ X,
    D.rightUnitorHom X ∈ D.grade (D.tensorObj X D.tensorUnit) X 0
  rightUnitor_inv_even : ∀ X,
    D.rightUnitorInv X ∈ D.grade X (D.tensorObj X D.tensorUnit) 0
  rightUnitor_naturality : ∀ {X Y} (f : D.Hom X Y),
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
    Nonempty (D.BiproductWitness S)
  semisimple : ∀ X : D.Obj,
    ∃ (n : ℕ) (S : Fin n → D.Obj),
      (∀ i, D.IsSimple (S i)) ∧ Nonempty (D.DecompositionWitness X S)
  graded_schur : ∀ {X Y : D.Obj},
    D.IsSimple X → D.IsSimple Y →
      ∀ {a : ZMod 2} (f : D.Hom X Y),
        D.IsHomogeneous a f → f ≠ D.zero → D.IsIso f
  finiteDimensional_hom : ∀ X Y : D.Obj,
    Nonempty (D.FiniteBasisWitness X Y)
  finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → D.Obj),
      (∀ i, D.IsSimple (S i)) ∧
        ∀ X : D.Obj, D.IsSimple X →
          ∃ (i : Fin n) (a : ZMod 2), Nonempty (D.HomogeneousIso a X (S i))
  simple_unit : D.IsSimple D.tensorUnit
  unitEnd_scalar_injective : ∀ r s : ℝ,
    D.smul r (D.id D.tensorUnit) = D.smul s (D.id D.tensorUnit) → r = s
  unitEnd_scalar_surjective : ∀ f : D.Hom D.tensorUnit D.tensorUnit,
    ∃ r : ℝ, D.smul r (D.id D.tensorUnit) = f
  has_right_dual : ∀ X : D.Obj,
    ∃ Y : D.Obj, Nonempty (D.ExactPairingWitness X Y)
  has_left_dual : ∀ X : D.Obj,
    ∃ Y : D.Obj, Nonempty (D.ExactPairingWitness Y X)

  /- Weak pointedness. -/
  weaklyPointed : ∀ X : D.Obj,
    D.IsSimple X → D.IsWeaklyInvertible X

end Superfusion
