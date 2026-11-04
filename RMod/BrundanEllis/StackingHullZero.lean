import RMod.BrundanEllis.StackingBilinear
import RMod.BrundanEllis.StackingExternalObjects
import RMod.Hierarchy.Bridge.OldEquivalenceData

/-! A full additive parity completion preserves vanishing coordinates.
First prove this for an arbitrary enriched functor killing the generators,
then specialize to evaluation of a pullback family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.AddPiHull
variable {C D : WeaklyPointedFusionPiSuperCat} {I : Type} {Z : I → Even C}

/-- A completion of zero generators contains only zero objects. -/
theorem isZero_of_generators (hZ : ∀ i, IsZero (Z i))
    {X : Even C} (hX : AddPiHull C Z X) : IsZero X := by
  classical
  obtain ⟨n, i, p, ⟨r⟩⟩ := hX
  let family := fun j : Fin n =>
    if p j then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j) else Z (i j)
  have hz : ∀ j, IsZero (family j) := by
    intro j
    dsimp only [family]
    split_ifs
    · letI := leftTensorAdditive (evenObj C (MonoidalPiSuperCategory.pi (C := C)))
      exact (tensorLeft _).map_isZero (hZ (i j))
    · exact hZ (i j)
  have hs : IsZero (⨁ family) := (IsZero.iff_id_eq_zero _).2 (by
    apply biproduct.hom_ext
    intro j
    exact (hz j).eq_of_tgt _ _)
  apply (IsZero.iff_id_eq_zero _).2
  rw [← r.retract, hs.eq_of_tgt r.i 0, zero_comp]

/-- An enriched functor killing the original generators kills their full hull. -/
theorem map_isZero (F : SuperFunctor C D) (hZ : ∀ i, IsZero (F.forget.obj (Z i)))
    {X : Even C} (hX : AddPiHull C Z X) : IsZero (F.forget.obj X) :=
  isZero_of_generators hZ (map_super F (fun i => generator i) hX)

end RMod.BrundanEllis.AddPiHull
namespace RMod.BrundanEllis.Stacking
open RMod.Classification RMod.Legacy.Hierarchy

/-- The even zero-object condition is exactly the original identity being zero. -/
theorem fromOld_isZero (P : RMod.Classification.PiSuperfusion.{0, 0}) (X : P.data.Obj) :
    IsZero (evenObj (fromOld P) X) ↔ P.data.id X = P.data.zero := by
  rw [IsZero.iff_id_eq_zero]
  let F := evenForget P.toWeaklyPointedSuperfusion
  constructor
  · intro h
    have hm := congrArg (fun f => (F.map f).hom) h
    rw [F.map_id, F.map_zero] at hm
    exact hm
  · intro h
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact WideSubcategory.hom_ext _ h

/-- A coordinate vanishing on each generator vanishes throughout the completion. -/
theorem pullback_hull_support (s : Twist) {I : Type} (Z : I → Even (pullback s))
    (k : s.group) (hZ : ∀ i, reference.data.id (Z i k).val = reference.data.zero)
    {X : Even (pullback s)} (hX : AddPiHull (pullback s) Z X) :
    reference.data.id (X k).val = reference.data.zero := by
  apply (fromOld_isZero reference (X k).val).1
  exact AddPiHull.map_isZero (evaluate s k)
    (fun i => (fromOld_isZero reference (Z i k).val).2 (hZ i)) hX

end RMod.BrundanEllis.Stacking
