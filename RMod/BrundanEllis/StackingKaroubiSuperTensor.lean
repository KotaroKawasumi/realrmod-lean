import RMod.BrundanEllis.StackingKaroubiProduct
import RMod.BrundanEllis.StackingKaroubiFunctor
import RMod.BrundanEllis.StackingKaroubiEvenMonoidal
import RMod.BrundanEllis.StackingAlignedTensor

/-! The tensor on the enriched idempotent completion is the pairing of
corners followed by the extension of the ambient tensor superfunctor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalSuperCategory C]

def completedTensor :
    SuperFunctor (SuperTensorProduct (Karoubi (Even C)) (Karoubi (Even C))) (Karoubi (Even C)) :=
  (pairFunctor (A := C) (B := C)).comp SuperVec (functor (alignedSuperTensor C))

theorem completedTensor_object (P Q : Karoubi (Even C)) :
    (completedTensor C).obj (P, Q) = KaroubiTensor.objectTensor P Q := by
  refine Karoubi.ext (P := (completedTensor C).obj (P, Q))
    (Q := KaroubiTensor.objectTensor P Q) rfl ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (evenPairFunctor (alignedSuperTensor C)).map
      (X := (P.X, Q.X)) (Y := (P.X, Q.X)) (P.p, Q.p) = P.p ⊗ₘ Q.p
  exact alignedSuperTensor_even C (X := (P.X, Q.X)) (Y := (P.X, Q.X)) (P.p, Q.p)

theorem completedTensor_objects : TensorObjectsAgree (completedTensor C) := by
  intro P Q
  exact completedTensor_object C P Q

/-- Before aligning the tensor objects, the included Hom map is the ambient
specified tensor applied to the included corner vectors. -/
theorem completedTensor_map_inclusion (P P' Q Q' : Karoubi (Even C)) :
    (completedTensor C).map (P, Q) (P', Q') ≫
      inclusion ((completedTensor C).obj (P, Q)) ((completedTensor C).obj (P', Q')) =
    (inclusion P P' ⊗ₘ inclusion Q Q') ≫
      enrichedTensorMap MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        P.X P'.X Q.X Q'.X := by
  change (pairHom P P' Q Q' ≫ mapHom (alignedSuperTensor C) (pairObject P Q) (pairObject P' Q')) ≫
      inclusion (mapObject (alignedSuperTensor C) (pairObject P Q))
        (mapObject (alignedSuperTensor C) (pairObject P' Q')) = _
  rw [assoc, mapHom_inclusion, ← assoc, pairHom_inclusion]
  congr 1

end RMod.BrundanEllis.Stacking.KaroubiSuper
