import RMod.Hierarchy.Bridge.EvenCategory
import RMod.Classification.Proofs.EvenSimple
import RMod.Classification.Instances.EvenBiproducts

/-!
# Simplicity and finite biproducts under the enrichment adapter

The ordinary even equivalence transfers Mathlib simplicity and finite
products. In a preadditive category those products are finite biproducts.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace RMod.Legacy.Hierarchy

private theorem simple_reflect {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (F : A ⥤ B)
    [F.IsEquivalence] [F.PreservesZeroMorphisms] (X : A) [Simple (F.obj X)] : Simple X := by
  refine ⟨fun f _ => ?_⟩
  exact (isIso_iff_of_reflects_iso f F).symm.trans
    ((Simple.mono_isIso_iff_nonzero (F.map f)).trans (not_congr (Functor.map_eq_zero_iff F)))

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem oldSimple_iff (X : C.data.Obj) :
    C.data.IsSimple X ↔ Simple (evenObj (ofOldSupercategory C) X) := by
  rw [Classification.isSimple_iff_evenSimple]
  constructor
  · intro h
    haveI : Simple ((evenForget C).obj (evenObj (ofOldSupercategory C) X)) := h
    exact simple_reflect (evenForget C) _
  · intro h
    let e := evenEquivalence C
    haveI : Simple (evenObj (ofOldSupercategory C) X) := h
    let η : evenObj (ofOldSupercategory C) X ≅
        e.inverse.obj (e.functor.obj (evenObj (ofOldSupercategory C) X)) := e.unitIso.app _
    haveI : Simple (e.inverse.obj (e.functor.obj (evenObj (ofOldSupercategory C) X))) :=
      Simple.of_iso η.symm
    exact simple_reflect e.inverse (e.functor.obj (evenObj (ofOldSupercategory C) X))

instance ofOldEvenFiniteBiproducts : HasFiniteBiproducts (Even (ofOldSupercategory C)) := by
  letI : HasFiniteProducts (Even (ofOldSupercategory C)) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (evenForget C)⟩
  exact HasFiniteBiproducts.of_hasFiniteProducts

theorem ofOldSemisimple (X : Even (ofOldSupercategory C)) :
    ∃ (n : ℕ) (S : Fin n → Even (ofOldSupercategory C)),
      (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S) := by
  obtain ⟨n, S, hS, hX⟩ := C.laws.semisimple X
  obtain ⟨d⟩ := (Classification.hasDecomposition_iff C X S).mp hX
  let S' : Fin n → Even (ofOldSupercategory C) := fun i => evenObj (ofOldSupercategory C) (S i)
  let e := biproduct.uniqueUpToIso _ d.evenIsBilimit
  refine ⟨n, S', fun i => (oldSimple_iff C (S i)).mp (hS i), ?_⟩
  exact ⟨(evenForget C).preimageIso (e ≪≫ ((evenForget C).mapBiproduct S').symm)⟩

theorem ofOldHomFinite (X Y : C.data.Obj) (a : ZMod 2) :
    FiniteDimensional ℝ ((ofOldSupercategory C).data.Hom X Y a) := by
  change FiniteDimensional ℝ (Classification.LinearCategory.grade C X Y a)
  infer_instance

end RMod.Legacy.Hierarchy
