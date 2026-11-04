import RMod.Hierarchy.Abstract.Reference
import RMod.Hierarchy.Bridge.Fusion
import RMod.Hierarchy.Bridge.Biproducts
import RMod.Hierarchy.Bridge.CliffordEnd
import RMod.Hierarchy.Bridge.EndConjugation

/-!
# Brauer-Wall types in the two presentations

The old witness allows an arbitrary finite-sum object. An even isomorphism
to Mathlib's chosen biproduct moves its endomorphism algebra by graded
conjugation. This accounts for the choice of biproduct in the new type test.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace RMod.Legacy.Hierarchy

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem oldCliffordEnd_of_evenIso {X Y : C.data.Obj}
    (e : oldEvenObj C X ≅ oldEvenObj C Y) (n : ℕ)
    (h : Classification.HasCliffordEnd C.data X n) : Classification.HasCliffordEnd C.data Y n := by
  obtain ⟨f, hf⟩ := (Classification.hasCliffordEnd_iff C X n).mp h
  apply (Classification.hasCliffordEnd_iff C Y n).mpr
  refine ⟨f.trans (endConjAlgEquiv (oldEvenTotalIso C e)), fun a x => ?_⟩
  exact (hf a x).trans (oldEven_conj_grade_iff C e a (f x)).symm

theorem oldBrauerWallType_iff (P : Classification.PiSuperfusion.{0, 0})
    (X : P.data.Obj) (r : ZMod 8) :
    Classification.HasBWType P.data.toWeaklyPointedSuperfusionData X r ↔
      HasBrauerWallType (ofOldFusionPiSupercategory P)
        (evenObj (ofOldSupercategory P.toWeaklyPointedSuperfusion) X) r := by
  let C := P.toWeaklyPointedSuperfusion
  constructor
  · rintro ⟨n, S, Y, hn, hS, hD, hCl⟩
    let S' : Fin n → Even (ofOldSupercategory C) := fun j => evenObj (ofOldSupercategory C) (S j)
    refine ⟨n, S', hn, fun j => (oldParityOrbit_iff C X (S j)).mp (hS j), ?_⟩
    obtain ⟨e⟩ := (oldDecomposition_iff_evenIso C Y S).mp hD
    let e' : oldEvenObj C Y ≅ oldEvenObj C (biproduct (C := Even (ofOldSupercategory C)) S') := (evenForget C).mapIso e
    exact (oldCliffordEnd_iff C (biproduct (C := Even (ofOldSupercategory C)) S') r.val).mp
      (oldCliffordEnd_of_evenIso C e' r.val hCl)
  · rintro ⟨n, S, hn, hS, e, he⟩
    refine ⟨n, (fun j => (S j : C.data.Obj)), (biproduct (C := Even (ofOldSupercategory C)) S : C.data.Obj), hn,
      fun j => (oldParityOrbit_iff C X (S j)).mpr (hS j), ?_, ?_⟩
    · apply (oldDecomposition_iff_evenIso C (biproduct (C := Even (ofOldSupercategory C)) S) (fun j => (S j : C.data.Obj))).mpr
      exact ⟨Iso.refl _⟩
    · exact (oldCliffordEnd_iff C (biproduct (C := Even (ofOldSupercategory C)) S) r.val).mpr ⟨e, he⟩

end RMod.Legacy.Hierarchy
