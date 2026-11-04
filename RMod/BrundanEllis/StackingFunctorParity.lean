import RMod.BrundanEllis.StackingGradedIso

/-! Any superfunctor preserves parity up to an even isomorphism: apply it
to the source odd comparison and cancel against the target odd comparison.
The same cancellation identifies the tensor square of pi with the unit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking.GradedIso
variable {C D : Type} [SuperCategory C] [SuperCategory D]

theorem map_grade (F : SuperFunctor C D) {X Y : C} {a : ZMod 2}
    {f : THom C X Y} (h : f ∈ grade C X Y a) :
    tMap F f ∈ grade D (F.obj X) (F.obj Y) a := by
  intro b hb
  change F.map X Y b (f b) = 0
  rw [h b hb, map_zero]

variable [MonoidalCategory (Even C)] [MonoidalSuperCategory C] [MonoidalPiSuperCategory C]
  [MonoidalCategory (Even D)] [MonoidalSuperCategory D] [MonoidalPiSuperCategory D]

def parityComparison (F : SuperFunctor C D) (X : Even C) :
    F.forget.obj ((piFunctor C).forget.obj X) ≅
      (piFunctor D).forget.obj (F.forget.obj X) := by
  let e := (totalSuperFunctor F).mapIso (parity C (ForgetEnrichment.to SuperVec X)) ≪≫
    (parity D (F.obj (ForgetEnrichment.to SuperVec X))).symm
  exact even D e
    (homogeneous_comp_grade D (map_grade F (parity_hom_grade C _)) (parity_inv_grade D _))
    (homogeneous_comp_grade D (parity_hom_grade D _) (map_grade F (parity_inv_grade C _)))

/-- The tensor square of the specified parity object is evenly the unit. -/
def paritySquare (C : Type) [SuperCategory C] [MonoidalCategory (Even C)]
    [MonoidalSuperCategory C] [MonoidalPiSuperCategory C] :
    evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗
      evenObj C (MonoidalPiSuperCategory.pi (C := C)) ≅ 𝟙_ (Even C) :=
  ((piFunctor C).forget.mapIso (ρ_ (evenObj C (MonoidalPiSuperCategory.pi (C := C))))).symm ≪≫
    parityTwice C (𝟙_ (Even C))

end RMod.BrundanEllis.Stacking.GradedIso
