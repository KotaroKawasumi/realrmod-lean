import RMod.BrundanEllis.StackingPairRetracts
import RMod.BrundanEllis.StackingFaithfulForget
import RMod.BrundanEllis.StackingRetractImage

/-! Graded full faithfulness and generation under finite sums, parity,
and retracts imply essential surjectivity from a fusion source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {C D : WeaklyPointedFusionPiSuperCat}

/-- Absorb the parity choices and the finite sum into a single source object. -/
theorem imageHull_retract (F : SuperFunctor C D) {W : Even D}
    (h : AddPiHull D (fun X : C => evenObj D (F.obj X)) W) :
    ∃ X : Even C, Nonempty (Retract W (F.forget.obj X)) := by
  classical
  obtain ⟨n, Z, p, ⟨r⟩⟩ := h
  let X : Fin n → Even C := fun i =>
    if p i then (piFunctor C).obj (evenObj C (Z i)) else evenObj C (Z i)
  let e (i : Fin n) :
      (if p i then evenObj D (MonoidalPiSuperCategory.pi (C := D)) ⊗
        evenObj D (F.obj (Z i)) else evenObj D (F.obj (Z i))) ≅ F.forget.obj (X i) := by
    dsimp [X]
    cases hp : p i
    · exact Iso.refl _
    · exact (mapParityIso F (evenObj C (Z i))).symm
  exact ⟨⨁ X, ⟨r.trans (Retract.ofIso
    (biproduct.mapIso e ≪≫ (F.forget.mapBiproduct X).symm))⟩⟩

/-- Idempotent completeness turns retract generation into an ordinary equivalence. -/
theorem isEquivalence_of_hull_generation (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (hgen : ∀ W : Even D, AddPiHull D (fun X : C => evenObj D (F.obj X)) W) :
    F.forget.IsEquivalence := by
  let ff := forgetFullyFaithful F hF
  letI : F.forget.Full := ff.full
  letI : F.forget.Faithful := ff.faithful
  letI : F.forget.EssSurj := essSurj_of_retracts F.forget
    (fun W => imageHull_retract F (hgen W))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end RMod.BrundanEllis.Stacking
