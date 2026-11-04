import RMod.BrundanEllis.StackingFiniteSpan

/-! Retract closure of a span of simple objects follows from semisimplicity:
each simple summand of the retract embeds into one original summand and
therefore is isomorphic to that simple generator. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace RMod.BrundanEllis.Stacking.FiniteSpan
variable {C : Type} [Category C] [Abelian C] [hzero : HasZeroMorphisms C]
  [HasFiniteBiproducts C] {I : Type} {Z : I → C}

theorem of_retract
    (hsemi : ∀ X : C, ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S))
    (hZ : ∀ i, Simple (Z i)) {X Y : C} (r : Retract X Y) (hY : FiniteSpan Z Y) :
    FiniteSpan Z X := by
  cases Subsingleton.elim
    (@Preadditive.preadditiveHasZeroMorphisms C _ (Abelian.toPreadditive (C := C))) hzero
  classical
  obtain ⟨m, j, ⟨eY⟩⟩ := hY
  obtain ⟨n, S, hS, ⟨eX⟩⟩ := hsemi X
  have h (k : Fin n) : ∃ i, Nonempty (S k ≅ Z i) := by
    letI : Simple (S k) := hS k
    let q : Retract (S k) X := {
      i := biproduct.ι S k ≫ eX.inv
      r := eX.hom ≫ biproduct.π S k
      retract := by simp [assoc] }
    obtain ⟨l, ⟨s⟩⟩ := simple_retract_summand hsemi (fun l => Z (j l))
      ((q.trans r).trans (Retract.ofIso eY))
    letI : Simple (Z (j l)) := hZ (j l)
    have hi : s.i ≠ 0 := by
      intro he
      apply id_nonzero (S k)
      rw [← s.retract, he, zero_comp]
    letI : IsIso s.i := isIso_of_mono_of_nonzero hi
    exact ⟨j l, ⟨asIso s.i⟩⟩
  choose i hi using h
  exact ⟨n, i, ⟨eX ≪≫ biproduct.mapIso (fun k => (hi k).some)⟩⟩

/-- A simple retract of a finite span is already a retract of one generator. -/
theorem simple_retract_generator
    (hsemi : ∀ X : C, ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S))
    {X Y : C} [Simple X] (r : Retract X Y) (hY : FiniteSpan Z Y) :
    ∃ i, Nonempty (Retract X (Z i)) := by
  cases Subsingleton.elim
    (@Preadditive.preadditiveHasZeroMorphisms C _ (Abelian.toPreadditive (C := C))) hzero
  obtain ⟨n, i, ⟨e⟩⟩ := hY
  obtain ⟨j, hj⟩ := simple_retract_summand hsemi (fun j => Z (i j))
    (r.trans (Retract.ofIso e))
  exact ⟨i j, hj⟩

end RMod.BrundanEllis.Stacking.FiniteSpan
