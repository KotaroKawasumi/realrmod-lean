import RMod.BrundanEllis.StackingOrbitTransport
import RMod.BrundanEllis.StackingFaithfulForget

/-! The specified all-degree unit and counit give an equivalence of total
categories. Full faithfulness on each homogeneous component follows by
applying this equivalence to a total arrow supported in one degree. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalSuperCategory C] [MonoidalSuperCategory D]
  (e : MonoidalSuperequivalence C D)

def totalEquivalence : TotalCategory C ≌ TotalCategory D :=
  CategoryTheory.Equivalence.mk (totalSuperFunctor e.forward) (totalSuperFunctor e.backward)
    (NatIso.ofComponents (fun X => (superEvenToTotal C).mapIso (e.unit.app (evenObj C X)))
      (fun f => e.unit_natural f))
    (NatIso.ofComponents (fun X => (superEvenToTotal D).mapIso (e.counit.app (evenObj D X)))
      (fun f => e.counit_natural f))

theorem equivalence_bijective (X Y : C) (a : ZMod 2) :
    Function.Bijective (e.forward.map X Y a) := by
  classical
  let E := totalEquivalence e
  constructor
  · intro x y h
    let f : THom C X Y := Pi.single a x
    let g : THom C X Y := Pi.single a y
    have hf : E.functor.map f = E.functor.map g := by
      funext b
      change e.forward.map X Y b (f b) = e.forward.map X Y b (g b)
      by_cases hb : b = a
      · subst b
        simpa only [f, g, Pi.single_eq_same] using h
      · simp only [f, g, Pi.single_eq_of_ne hb]
    have hg : f = g := E.functor.map_injective hf
    simpa only [f, g, Pi.single_eq_same] using congrFun hg a
  · intro y
    let f : THom D (e.forward.obj X) (e.forward.obj Y) := Pi.single a y
    let g := E.functor.preimage (X := totalObj C X) (Y := totalObj C Y) f
    refine ⟨g a, ?_⟩
    have h := congrFun (E.functor.map_preimage f) a
    change e.forward.map X Y a (g a) = f a at h
    simpa only [f, Pi.single_eq_same] using h

end RMod.BrundanEllis.Stacking
