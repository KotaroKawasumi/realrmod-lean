import RMod.Definitions.WeaklyPointedSuperfusionData

/-!
# Predicates for weakly pointed superfusion data

This module defines proposition-valued notions derived from
`WeaklyPointedSuperfusionData`. They add no executable fields to the data and
assert no laws; the laws of a completed structure are stated separately in
`WeaklyPointedSuperfusion`.
-/

set_option autoImplicit false

universe u v

namespace RMod

namespace WeaklyPointedSuperfusionData

variable (D : WeaklyPointedSuperfusionData.{u, v})

/-! ## Elementary predicates -/

/-- A morphism belongs to the homogeneous component of degree `a`. -/
def IsHomogeneous {X Y : D.Obj} (a : ZMod 2) (f : D.Hom X Y) : Prop :=
  f ∈ D.grade X Y a

/-- A morphism has a two-sided inverse. -/
def IsIso {X Y : D.Obj} (f : D.Hom X Y) : Prop :=
  ∃ g : D.Hom Y X,
    D.comp f g = D.id X ∧ D.comp g f = D.id Y

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

/-- Simplicity in the even subcategory. -/
def IsSimple (X : D.Obj) : Prop :=
  ∀ (Y : D.Obj) (f : D.Hom Y X),
    D.IsEvenMono f → (D.IsEvenIso f ↔ f ≠ D.zero)

/-! ## Existential properties not used as computational data -/

/-- Two objects have an isomorphism homogeneous in both directions. -/
def HasHomogeneousIso (a : ZMod 2) (X Y : D.Obj) : Prop :=
  ∃ (hom : D.Hom X Y) (inv : D.Hom Y X),
    D.comp hom inv = D.id X ∧
    D.comp inv hom = D.id Y ∧
    D.IsHomogeneous a hom ∧
    D.IsHomogeneous a inv

/-- A finite family admits a biproduct object. -/
def HasFiniteBiproduct {n : ℕ} (S : Fin n → D.Obj) : Prop :=
  ∃ (object : D.Obj)
      (inclusion : (i : Fin n) → D.Hom (S i) object)
      (projection : (i : Fin n) → D.Hom object (S i)),
    (∀ i, D.IsHomogeneous 0 (inclusion i)) ∧
    (∀ i, D.IsHomogeneous 0 (projection i)) ∧
    (∀ i, D.comp (inclusion i) (projection i) = D.id (S i)) ∧
    (∀ i j, i ≠ j → D.comp (inclusion i) (projection j) = D.zero) ∧
    D.finSum n (fun i => D.comp (projection i) (inclusion i)) = D.id object

/-- An object admits a chosen decomposition by a finite family. -/
def HasDecomposition (X : D.Obj) {n : ℕ} (S : Fin n → D.Obj) : Prop :=
  ∃ (inclusion : (i : Fin n) → D.Hom (S i) X)
      (projection : (i : Fin n) → D.Hom X (S i)),
    (∀ i, D.IsHomogeneous 0 (inclusion i)) ∧
    (∀ i, D.IsHomogeneous 0 (projection i)) ∧
    (∀ i, D.comp (inclusion i) (projection i) = D.id (S i)) ∧
    (∀ i j, i ≠ j → D.comp (inclusion i) (projection j) = D.zero) ∧
    D.finSum n (fun i => D.comp (projection i) (inclusion i)) = D.id X

/-- A Hom space admits an explicit finite basis and coordinate map. -/
def HasFiniteBasis (X Y : D.Obj) : Prop :=
  ∃ (dimension : ℕ)
      (basis : Fin dimension → D.Hom X Y)
      (coordinates : D.Hom X Y → Fin dimension → ℝ),
    (∀ f,
      D.finSum dimension (fun i => D.smul (coordinates f i) (basis i)) = f) ∧
    (∀ f c,
      D.finSum dimension (fun i => D.smul (c i) (basis i)) = f →
        c = coordinates f)

/-- There are even coevaluation and evaluation maps satisfying both zigzags. -/
def HasExactPairing (X Y : D.Obj) : Prop :=
  ∃ (coeval : D.Hom D.tensorUnit (D.tensorObj X Y))
      (eval : D.Hom (D.tensorObj Y X) D.tensorUnit),
    D.IsHomogeneous 0 coeval ∧
    D.IsHomogeneous 0 eval ∧
    D.comp
        (D.comp (D.whiskerLeft Y coeval) (D.associatorInv Y X Y))
        (D.whiskerRight eval Y) =
      D.comp (D.rightUnitorHom Y) (D.leftUnitorInv Y) ∧
    D.comp
        (D.comp (D.whiskerRight coeval X) (D.associatorHom X Y X))
        (D.whiskerLeft X eval) =
      D.comp (D.leftUnitorHom X) (D.rightUnitorInv X)

/-- An object decomposes into even and odd copies of another object. -/
def HasSuperMultiplicity (A X : D.Obj) (p q : ℕ) : Prop :=
  ∃ (inclusion : (i : Fin p ⊕ Fin q) → D.Hom X A)
      (projection : (i : Fin p ⊕ Fin q) → D.Hom A X),
    (∀ i, D.IsHomogeneous (superIndexParity i) (inclusion i)) ∧
    (∀ i, D.IsHomogeneous (superIndexParity i) (projection i)) ∧
    (∀ i, D.comp (inclusion i) (projection i) = D.id X) ∧
    (∀ i j, i ≠ j → D.comp (inclusion i) (projection j) = D.zero) ∧
    D.superFinSum (fun i => D.comp (projection i) (inclusion i)) = D.id A

/-- An object has a dual whose tensor product is a nonempty super-multiple
of the tensor unit. The witnesses are existential because none is used by
the executable operations in `WeaklyPointedSuperfusionData`. -/
def IsWeaklyInvertible (X : D.Obj) : Prop :=
  ∃ dual : D.Obj,
    D.HasExactPairing X dual ∧
    ∃ evenMultiplicity oddMultiplicity : ℕ,
      0 < evenMultiplicity + oddMultiplicity ∧
      D.HasSuperMultiplicity (D.tensorObj X dual) D.tensorUnit
        evenMultiplicity oddMultiplicity

end WeaklyPointedSuperfusionData

end RMod
