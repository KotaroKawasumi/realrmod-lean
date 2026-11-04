import RMod.BrundanEllis.MonoidalBridge
import RMod.Enriched.GradedSchur

/-! The specified odd unit comparison makes the parity object simple in a
fusion supercategory. This does not use the weakly pointed condition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)]
  [MonoidalPiSuperCategory C] [MonoidalSuperCategory C]
  [RigidCategory (Even C)] [Abelian (Even C)] [FusionPiSuperCategory C]

theorem fusion_pi_simple : Simple (evenObj C (MonoidalPiSuperCategory.pi (C := C))) := by
  let L := RMod.StatementLegacy.toLegacySupercategory (Bridge.bundled C)
  letI : HasFiniteBiproducts (RMod.Legacy.Even L) := by
    with_unfolding_all exact evenFiniteBiproducts C
  letI : HasKernels (RMod.Legacy.Even L) := by
    with_unfolding_all exact inferInstanceAs (HasKernels (Even C))
  let X : RMod.Legacy.Even L := 𝟙_ (Even C)
  let Y : RMod.Legacy.Even L := MonoidalPiSuperCategory.pi (C := C)
  let e : (RMod.Legacy.evenToTotal L).obj X ≅ (RMod.Legacy.evenToTotal L).obj Y := {
    hom := homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C))
    inv := homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C))
    hom_inv_id := MonoidalPiSuperCategory.inv_hom (C := C)
    inv_hom_id := MonoidalPiSuperCategory.hom_inv (C := C) }
  have he : e.hom ∈ RMod.Legacy.grade L X Y 1 := by
    intro b hb
    change homogeneousPoint 1 (MonoidalPiSuperCategory.inv (C := C)) b = 0
    simp only [homogeneousPoint, dif_neg hb]
  have hi : e.inv ∈ RMod.Legacy.grade L Y X 1 := by
    intro b hb
    change homogeneousPoint 1 (MonoidalPiSuperCategory.hom (C := C)) b = 0
    simp only [homogeneousPoint, dif_neg hb]
  letI : Simple X := FusionPiSuperCategory.simple_unit (C := C)
  with_unfolding_all
    exact RMod.EnrichedSupport.simple_of_odd_iso L
      (FusionPiSuperCategory.semisimple (C := C)) e he hi

end RMod.BrundanEllis.Stacking
