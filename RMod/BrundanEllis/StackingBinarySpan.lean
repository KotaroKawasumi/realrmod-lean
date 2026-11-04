import RMod.BrundanEllis.StackingFiniteSpan
import Mathlib.Logic.Equiv.Sum

/-! A finite sum chosen from two objects can be regrouped into a binary
biproduct of their multiplicity sums. This converts an additive-span proof
into the explicit multiplicities required by weak invertibility. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- Separate the two halves of a sum-indexed biproduct. -/
def sumBiproductIso {J K : Type} [Fintype J] [Fintype K] (f : J → C) (g : K → C) :
    (⨁ Sum.elim f g) ≅ (⨁ f) ⊞ (⨁ g) where
  hom := biproduct.desc (fun
    | Sum.inl j => biproduct.ι f j ≫ biprod.inl
    | Sum.inr k => biproduct.ι g k ≫ biprod.inr)
  inv := biprod.desc
    (biproduct.desc (fun j => biproduct.ι (Sum.elim f g) (Sum.inl j)))
    (biproduct.desc (fun k => biproduct.ι (Sum.elim f g) (Sum.inr k)))
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro j
    cases j <;> simp [assoc]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro j
      simp [assoc]
    · apply biproduct.hom_ext'
      intro k
      simp [assoc]

/-- Finite additive spans are closed under binary biproducts. -/
theorem FiniteSpan.binary_biproduct {I : Type} {Z : I → C} {X Y : C}
    (hX : FiniteSpan Z X) (hY : FiniteSpan Z Y) : FiniteSpan Z (X ⊞ Y) := by
  obtain ⟨n, i, ⟨e⟩⟩ := hX
  obtain ⟨m, j, ⟨d⟩⟩ := hY
  let w (k : Fin n ⊕ Fin m) :
      Sum.elim (fun a => Z (i a)) (fun b => Z (j b)) k ≅ Z (Sum.elim i j k) := by
    cases k <;> exact Iso.refl _
  apply FiniteSpan.of_iso (biprod.mapIso e d ≪≫
    (sumBiproductIso (fun a => Z (i a)) (fun b => Z (j b))).symm ≪≫ biproduct.mapIso w)
  exact FiniteSpan.of_finite_family (Sum.elim i j)

/-- Count the two types of summands and reindex them by finite ordinals. -/
theorem binary_multiplicities (U V : C) {X : C}
    (h : FiniteSpan (fun b : Bool => if b then V else U) X) :
    ∃ p q : ℕ, Nonempty (X ≅ (⨁ fun _ : Fin p => U) ⊞ (⨁ fun _ : Fin q => V)) := by
  classical
  obtain ⟨n, b, ⟨e⟩⟩ := h
  let J := {i : Fin n // b i = false}
  let K := {i : Fin n // ¬ b i = false}
  let d : J ⊕ K ≃ Fin n := Equiv.sumCompl (fun i => b i = false)
  let f : J → C := fun _ => U
  let g : K → C := fun _ => V
  let w (j : J ⊕ K) : (if b (d j) then V else U) ≅ Sum.elim f g j := by
    cases j with
    | inl j =>
      change (if b j.val then V else U) ≅ U
      rw [j.property]
      exact Iso.refl _
    | inr k =>
      change (if b k.val then V else U) ≅ V
      have hk : b k.val = true := Bool.eq_true_of_not_eq_false k.property
      rw [hk]
      exact Iso.refl _
  exact ⟨Fintype.card J, Fintype.card K, ⟨e ≪≫
    (biproduct.whiskerEquiv d w).symm ≪≫ sumBiproductIso f g ≪≫
    biprod.mapIso (biproduct.whiskerEquiv (f := f) (g := fun _ : Fin (Fintype.card J) => U) (Fintype.equivFin J) (fun _ => Iso.refl _))
      (biproduct.whiskerEquiv (f := g) (g := fun _ : Fin (Fintype.card K) => V) (Fintype.equivFin K) (fun _ => Iso.refl _))⟩⟩

end RMod.BrundanEllis.Stacking
