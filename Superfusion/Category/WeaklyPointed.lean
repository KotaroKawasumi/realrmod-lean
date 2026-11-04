import Superfusion.Category.Superfusion

/-!
# Intrinsic weak invertibility and weak pointedness

This file defines weak invertibility by the decomposition of `X ⊗ Xᵈ` into
even and odd copies of the monoidal unit.  Neither weak invertibility nor weak
pointedness contains an external group of labels.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Superfusion.Category

/-- The coordinates of a supermultiplicity `(p|q)`: the left summand indexes
the `p` even copies and the right summand indexes the `q` odd copies. -/
abbrev SuperIndex (p q : ℕ) := Fin p ⊕ Fin q

/-- The parity carried by a coordinate of a supermultiplicity. -/
def superIndexParity {p q : ℕ} : SuperIndex p q → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

@[simp] lemma superIndexParity_inl {p q : ℕ} (i : Fin p) :
    superIndexParity (q := q) (Sum.inl i) = 0 := rfl

@[simp] lemma superIndexParity_inr {p q : ℕ} (i : Fin q) :
    superIndexParity (p := p) (Sum.inr i) = 1 := rfl

@[simp] lemma card_superIndex (p q : ℕ) :
    Fintype.card (SuperIndex p q) = p + q := by
  simp [SuperIndex]

/-- Split an arbitrary parity labelling into its even and odd fibers. -/
private def parityFiberEquiv {r : ℕ} (γ : Fin r → ZMod 2) :
    Fin r ≃ {i // γ i = 0} ⊕ {i // γ i = 1} :=
  (Equiv.sumCompl fun i => γ i = 0).symm.trans
    (Equiv.sumCongr (Equiv.refl _)
      (Equiv.subtypeEquivRight fun i => by
        constructor
        · intro h
          rcases zmod2_cases (γ i) with h0 | h1
          · exact absurd h0 h
          · exact h1
        · intro h h0
          rw [h] at h0
          exact absurd h0 (by decide)))

private theorem parityFiberEquiv_symm_inl {r : ℕ}
    (γ : Fin r → ZMod 2) (i : {j // γ j = 0}) :
    (parityFiberEquiv γ).symm (Sum.inl i) = (i : Fin r) := by
  simp [parityFiberEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.sumCompl_apply_inl]

private theorem parityFiberEquiv_symm_inr {r : ℕ}
    (γ : Fin r → ZMod 2) (i : {j // γ j = 1}) :
    (parityFiberEquiv γ).symm (Sum.inr i) = (i : Fin r) := by
  simp [parityFiberEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.sumCompl_apply_inr]

/-- A finite parity-labelled index decomposed as even and odd coordinates. -/
structure SuperIndexSort {r : ℕ} (γ : Fin r → ZMod 2) where
  evenMultiplicity : ℕ
  oddMultiplicity : ℕ
  equiv : SuperIndex evenMultiplicity oddMultiplicity ≃ Fin r
  parity (i : SuperIndex evenMultiplicity oddMultiplicity) :
    γ (equiv i) = superIndexParity i
  total_eq : evenMultiplicity + oddMultiplicity = r

/-- Choose a parity-sorted enumeration of a finite parity-labelled index. -/
noncomputable def superIndexSort {r : ℕ}
    (γ : Fin r → ZMod 2) : SuperIndexSort γ where
  evenMultiplicity := Fintype.card {i // γ i = 0}
  oddMultiplicity := Fintype.card {i // γ i = 1}
  equiv :=
    ((Fintype.equivFin {i // γ i = 0}).symm.sumCongr
      (Fintype.equivFin {i // γ i = 1}).symm).trans
        (parityFiberEquiv γ).symm
  parity := by
    intro i
    cases i with
    | inl i =>
        show γ ((parityFiberEquiv γ).symm
          (Sum.inl ((Fintype.equivFin {j // γ j = 0}).symm i))) = 0
        rw [parityFiberEquiv_symm_inl]
        exact ((Fintype.equivFin {j // γ j = 0}).symm i).2
    | inr i =>
        show γ ((parityFiberEquiv γ).symm
          (Sum.inr ((Fintype.equivFin {j // γ j = 1}).symm i))) = 1
        rw [parityFiberEquiv_symm_inr]
        exact ((Fintype.equivFin {j // γ j = 1}).symm i).2
  total_eq := by
    simpa using Fintype.card_congr
      (((Fintype.equivFin {i // γ i = 0}).symm.sumCongr
        (Fintype.equivFin {i // γ i = 1}).symm).trans
          (parityFiberEquiv γ).symm)

namespace SuperIndexSort

/-- Reindex a finite biproduct along a chosen parity sort. -/
noncomputable def biproductReindex
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {r : ℕ} {γ : Fin r → ZMod 2} (σ : SuperIndexSort γ)
    (S : Fin r → C) :
    (⨁ S) ≅
      ⨁ fun i : SuperIndex σ.evenMultiplicity σ.oddMultiplicity =>
        S (σ.equiv i) :=
  biproduct.whiskerEquiv σ.equiv.symm
    (fun j => eqToIso (congrArg S (σ.equiv.apply_symm_apply j)))

end SuperIndexSort

variable (K : Type*) [Field K]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C] [HasFiniteBiproducts (EvenSubcategory K C)]

/-- Type-valued data witnessing that `A` is a direct sum of `p` even and `q`
odd copies of `X`.

The direct-sum comparison lies in the even subcategory.  Its summands may be
distinct objects, but the summand at `i` is homogeneously isomorphic to `X`
with parity `superIndexParity i`.  Thus an odd copy is represented by a local
parity-shift summand; an arbitrary inhomogeneous comparison cannot erase the
pair `(p|q)`. -/
structure SuperMultiplicityWitness (A X : C) (p q : ℕ) where
  /-- An object representing each homogeneous copy of `X`. -/
  summand : SuperIndex p q → C
  /-- The `i`-th summand is an even or odd copy of `X`, as prescribed by its
  index. -/
  summandIso (i : SuperIndex p q) :
    HomogeneousIso K (superIndexParity i) (summand i) X
  /-- The object is the finite biproduct of the summand objects, by an even
  isomorphism. -/
  decomposition :
    evenObj K C A ≅ ⨁ fun i : SuperIndex p q => evenObj K C (summand i)

/-- The proposition that `A` has supermultiplicity `(p|q)` with respect to
`X`.  The isomorphism data remain in a Type-valued witness. -/
def IsSuperMultiplicity (A X : C) (p q : ℕ) : Prop :=
  Nonempty (SuperMultiplicityWitness K C A X p q)

namespace SuperMultiplicityWitness

variable {K C}

/-- The summand family of a supermultiplicity witness, regarded in the even
subcategory. -/
abbrev evenSummand {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) :
    SuperIndex p q → EvenSubcategory K C :=
  fun i => evenObj K C (w.summand i)

/-- A homogeneous coordinate projection associated to a supermultiplicity
witness. -/
noncomputable def projection {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) (i : SuperIndex p q) : A ⟶ X :=
  (w.decomposition.hom.hom ≫ (biproduct.π w.evenSummand i).hom) ≫
    (w.summandIso i).iso.hom

/-- A homogeneous coordinate inclusion associated to a supermultiplicity
witness. -/
noncomputable def inclusion {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) (i : SuperIndex p q) : X ⟶ A :=
  ((w.summandIso i).iso.inv ≫ (biproduct.ι w.evenSummand i).hom) ≫
    w.decomposition.inv.hom

lemma projection_mem {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) (i : SuperIndex p q) :
    w.projection i ∈ homGrade K A X (superIndexParity i) := by
  have hd : w.decomposition.hom.hom ∈ homGrade K A
      ((⨁ w.evenSummand).obj) 0 := w.decomposition.hom.property
  have hp : (biproduct.π w.evenSummand i).hom ∈ homGrade K
      ((⨁ w.evenSummand).obj) (w.summand i) 0 :=
    (biproduct.π w.evenSummand i).property
  have hdp := Supercategory.comp_mem _ _ hd hp
  simpa only [projection, homGrade, zero_add] using
    Supercategory.comp_mem _ _ hdp (w.summandIso i).hom_mem

lemma inclusion_mem {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) (i : SuperIndex p q) :
    w.inclusion i ∈ homGrade K X A (superIndexParity i) := by
  have hi : (biproduct.ι w.evenSummand i).hom ∈ homGrade K
      (w.summand i) ((⨁ w.evenSummand).obj) 0 :=
    (biproduct.ι w.evenSummand i).property
  have hd : w.decomposition.inv.hom ∈ homGrade K
      ((⨁ w.evenSummand).obj) A 0 := w.decomposition.inv.property
  have hfirst := Supercategory.comp_mem _ _ (w.summandIso i).inv_mem hi
  simpa only [inclusion, homGrade, add_zero] using
    Supercategory.comp_mem _ _ hfirst hd

@[simp] lemma inclusion_projection_self {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) (i : SuperIndex p q) :
    w.inclusion i ≫ w.projection i = 𝟙 X := by
  have hdecomp := congrArg (fun f => f.hom) w.decomposition.inv_hom_id
  change w.decomposition.inv.hom ≫ w.decomposition.hom.hom =
    𝟙 ((⨁ w.evenSummand).obj) at hdecomp
  have hii := congrArg (fun f => f.hom) (biproduct.ι_π_self w.evenSummand i)
  change (biproduct.ι w.evenSummand i).hom ≫
    (biproduct.π w.evenSummand i).hom = 𝟙 (w.summand i) at hii
  simp only [inclusion, projection, Category.assoc]
  rw [← Category.assoc w.decomposition.inv.hom, hdecomp]
  simp only [Category.id_comp]
  rw [← Category.assoc (biproduct.ι w.evenSummand i).hom, hii]
  simp

lemma inclusion_projection_ne {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) {i j : SuperIndex p q}
    (h : i ≠ j) :
    w.inclusion i ≫ w.projection j = 0 := by
  have hdecomp := congrArg (fun f => f.hom) w.decomposition.inv_hom_id
  change w.decomposition.inv.hom ≫ w.decomposition.hom.hom =
    𝟙 ((⨁ w.evenSummand).obj) at hdecomp
  have hij := congrArg (fun f => f.hom) (biproduct.ι_π_ne w.evenSummand h)
  change (biproduct.ι w.evenSummand i).hom ≫
    (biproduct.π w.evenSummand j).hom = 0 at hij
  simp only [inclusion, projection, Category.assoc]
  rw [← Category.assoc w.decomposition.inv.hom, hdecomp]
  simp only [Category.id_comp]
  rw [← Category.assoc (biproduct.ι w.evenSummand i).hom, hij]
  simp

/-- The homogeneous coordinate projections and inclusions of a
supermultiplicity witness resolve the identity of the decomposed object. -/
theorem projection_inclusion_total {A X : C} {p q : ℕ}
    (w : SuperMultiplicityWitness K C A X p q) :
    ∑ i, w.projection i ≫ w.inclusion i = 𝟙 A := by
  have htotal :
      (∑ i, (biproduct.π w.evenSummand i).hom ≫
        (biproduct.ι w.evenSummand i).hom) =
          𝟙 ((⨁ w.evenSummand).obj) := by
    have h := CategoryTheory.Limits.IsBilimit.total
      (biproduct.isBilimit w.evenSummand)
    let I := wideSubcategoryInclusion (evenMorphismProperty K C)
    have hm := congrArg (fun f => I.map f) h
    rw [I.map_sum
      (fun i : SuperIndex p q =>
        biproduct.π w.evenSummand i ≫
          biproduct.ι w.evenSummand i)
      Finset.univ] at hm
    change
      (∑ i, (biproduct.π w.evenSummand i).hom ≫
        (biproduct.ι w.evenSummand i).hom) =
          𝟙 ((⨁ w.evenSummand).obj) at hm
    exact hm
  simp only [projection, inclusion, Category.assoc]
  simp_rw [← Category.assoc (w.summandIso _).iso.hom]
  simp only [Iso.hom_inv_id, Category.id_comp]
  calc
    _ =
        w.decomposition.hom.hom ≫
          (∑ i, (biproduct.π w.evenSummand i).hom ≫
            (biproduct.ι w.evenSummand i).hom) ≫
              w.decomposition.inv.hom := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp,
          Category.assoc]
    _ = w.decomposition.hom.hom ≫ w.decomposition.inv.hom := by
      rw [htotal]
      simp
    _ = 𝟙 A := by
      exact congrArg (fun f => f.hom) w.decomposition.hom_inv_id

end SuperMultiplicityWitness

section Monoidal

open MonoidalCategory

variable [MonoidalCategoryStruct C] [MonoidalSupercategory K C]

/-- Type-valued weak-invertibility data for `X`: an even right-duality
pairing and a positive supermultiplicity decomposition of `X ⊗ Xᵈ` by the
monoidal unit. -/
structure WeakInvertibilityWitness (X : C) where
  /-- A chosen right dual of `X`. -/
  dual : C
  /-- An even exact pairing between `X` and the chosen right dual. -/
  pairing : SuperExactPairing K X dual
  /-- The number of even copies of the monoidal unit. -/
  evenMultiplicity : ℕ
  /-- The number of odd copies of the monoidal unit. -/
  oddMultiplicity : ℕ
  /-- At least one copy of the monoidal unit occurs. -/
  multiplicity_pos : 0 < evenMultiplicity + oddMultiplicity
  /-- The chosen decomposition of `X ⊗ Xᵈ`. -/
  multiplicity :
    SuperMultiplicityWitness K C (X ⊗ dual) (𝟙_ C)
      evenMultiplicity oddMultiplicity

/-- An object is weakly invertible when weak-invertibility data exists. -/
def IsWeaklyInvertible (X : C) : Prop :=
  Nonempty (WeakInvertibilityWitness K C X)

namespace WeakInvertibilityWitness

variable {K C}

/-- Transport weak-invertibility data in its object argument across an even
isomorphism.

The dual object and its supermultiplicity are unchanged.  The exact pairing
is transported through the ordinary monoidal even core, while tensoring the
displayed even isomorphism with the identity on the dual transports the
source of the biproduct decomposition. -/
noncomputable def congrLeft {X X' : C}
    (e : EvenIso K X X')
    (w : WeakInvertibilityWitness K C X') :
    WeakInvertibilityWitness K C X where
  dual := w.dual
  pairing := SuperExactPairing.congrLeft e w.pairing
  evenMultiplicity := w.evenMultiplicity
  oddMultiplicity := w.oddMultiplicity
  multiplicity_pos := w.multiplicity_pos
  multiplicity :=
    { summand := w.multiplicity.summand
      summandIso := w.multiplicity.summandIso
      decomposition :=
        ((evenSubcategoryIsoOfEvenIso e) ⊗ᵢ
          Iso.refl (evenObj K C w.dual)).trans
            w.multiplicity.decomposition }

end WeakInvertibilityWitness

/-- A weakly pointed superfusion category is one in which every super-simple
object is weakly invertible.  No group of labels is included as structure. -/
class WeaklyPointed [SuperfusionCategory K C] : Prop where
  weaklyInvertible_of_isSuperSimple (X : C) :
    IsSuperSimple K C X → IsWeaklyInvertible K C X

namespace IsWeaklyInvertible

variable {K C}

/-- Weak invertibility pulls back along an even isomorphism. -/
lemma of_evenIso {X X' : C} (e : EvenIso K X X')
    (hX : IsWeaklyInvertible K C X') :
    IsWeaklyInvertible K C X := by
  rcases hX with ⟨w⟩
  exact ⟨w.congrLeft e⟩

/-- A weakly invertible object has an even right dual. -/
lemma hasSuperRightDual {X : C} (hX : IsWeaklyInvertible K C X) :
    HasSuperRightDual K X := by
  rcases hX with ⟨w⟩
  exact ⟨w.dual, ⟨w.pairing⟩⟩

/-- Extract a dual, its even pairing, and the positive supermultiplicity of
`X ⊗ Xᵈ`. -/
lemma exists_pairing_and_multiplicity {X : C}
    (hX : IsWeaklyInvertible K C X) :
    ∃ (Xdual : C) (_ : Nonempty (SuperExactPairing K X Xdual))
      (p q : ℕ), 0 < p + q ∧
        IsSuperMultiplicity K C (X ⊗ Xdual) (𝟙_ C) p q := by
  rcases hX with ⟨w⟩
  exact ⟨w.dual, ⟨w.pairing⟩, w.evenMultiplicity, w.oddMultiplicity,
    w.multiplicity_pos, ⟨w.multiplicity⟩⟩

/-- The multiplicity occurring in weak invertibility has at least one
summand. -/
lemma exists_positive_multiplicity {X : C}
    (hX : IsWeaklyInvertible K C X) :
    ∃ p q : ℕ, 0 < p + q := by
  rcases hX with ⟨w⟩
  exact ⟨w.evenMultiplicity, w.oddMultiplicity, w.multiplicity_pos⟩

end IsWeaklyInvertible

/-- Every super-simple object in a weakly pointed category is weakly
invertible. -/
lemma weaklyInvertible_of_isSuperSimple [SuperfusionCategory K C]
    [WeaklyPointed K C] {X : C} (hX : IsSuperSimple K C X) :
    IsWeaklyInvertible K C X :=
  WeaklyPointed.weaklyInvertible_of_isSuperSimple X hX

end Monoidal

end Superfusion.Category
