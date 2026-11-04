import RMod.BrundanEllis.StackingGradedFaithful
import RMod.BrundanEllis.StackingOrbitTransport
import RMod.BrundanEllis.StackingSemisimpleTransfer

/-! A fully faithful enriched functor which is an equivalence on even
categories transports the finite list of simple parity orbits. Reflection
uses all homogeneous components, rather than only ordinary full faithfulness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [Abelian (Even C)] [Abelian (Even D)]

theorem finite_orbits_of_equivalence (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a)) [F.forget.IsEquivalence]
    (h : ∃ (n : ℕ) (S : Fin n → Even D), (∀ i, Simple (S i)) ∧
      ∀ X : Even D, Simple X → ∃ i, SameParityOrbit D X (S i)) :
    ∃ (n : ℕ) (S : Fin n → Even C), (∀ i, Simple (S i)) ∧
      ∀ X : Even C, Simple X → ∃ i, SameParityOrbit C X (S i) := by
  obtain ⟨n, S, hS, hcover⟩ := h
  let E := F.forget.asEquivalence
  let T : Fin n → Even C := fun i => E.inverse.obj (S i)
  refine ⟨n, T, fun i => ?_, fun X hX => ?_⟩
  · letI : Simple (S i) := hS i
    letI : Simple (E.functor.obj (T i)) :=
      Simple.of_iso (Y := S i) (E.counitIso.app (S i))
    exact simple_reflects_equivalence E (T i)
  · letI := hX
    letI : Simple (E.symm.functor.obj (E.functor.obj X)) :=
      Simple.of_iso (Y := X) (E.unitIso.app X).symm
    have hs : Simple (F.forget.obj X) := simple_reflects_equivalence E.symm (E.functor.obj X)
    obtain ⟨i, hi⟩ := hcover (F.forget.obj X) hs
    refine ⟨i, reflect_parity_orbit F hF ?_⟩
    exact parity_orbit_trans D hi (even_iso_orbit D (E.counitIso.app (S i)).symm)

end RMod.BrundanEllis.Stacking
