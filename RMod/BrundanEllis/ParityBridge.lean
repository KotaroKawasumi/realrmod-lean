import RMod.BrundanEllis.ParityNaturality
import RMod.BrundanEllis.OddNaturality
import RMod.Hierarchy.Instances.HomogeneousLine

/-! The odd comparison for the Mathlib enriched functor pi tensor -.
All comparison maps are constructed from the specified parity object and the
ordinary unitors; no fusion or Schur assumption enters the construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.ParityConstruction

-- These local unfolding hints affect elaboration only; the kernel still checks every proof.
set_option allowUnsafeReducibility true
attribute [local reducible] RMod.Legacy.MonoidalSupercategory.super
  RMod.Legacy.Hierarchy.toOldData RMod.Classification.PiData.shiftObj
  RMod.Classification.PiData.shiftHom RMod.Classification.PiData.zHom
  RMod.Classification.PiData.zInv RMod.Legacy.TotalCategory
  RMod.Legacy.superTensorProductData

variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)]
  [MonoidalSuperCategory C] [P : MonoidalPiSuperCategory C]

/-- The established proof vocabulary uses the identical enriched category. -/
abbrev monoidal := RMod.StatementLegacy.StatementBridge.toMonoidal (Bridge.toStatementMonoidal C)

/-- The raw odd inverse pair contains only the specified computational data. -/
def parityData : RMod.Classification.PiData (RMod.Legacy.Hierarchy.toOldData (monoidal C)) where
  object := P.pi
  hom := homogeneousPoint 1 P.hom
  inv := homogeneousPoint 1 P.inv

/-- Homogeneity follows from the odd line; inverse equations are the given equations. -/
theorem parityLaws : RMod.Classification.PiLaws
    (RMod.Legacy.Hierarchy.toOldData (monoidal C)) (parityData C) where
  hom_odd := by
    intro b hb
    change homogeneousPoint 1 P.hom b = 0
    simp only [homogeneousPoint, dif_neg hb]
  inv_odd := by
    intro b hb
    change homogeneousPoint 1 P.inv b = 0
    simp only [homogeneousPoint, dif_neg hb]
  hom_inv := P.hom_inv
  inv_hom := P.inv_hom

/-- Data and laws are assembled only after their separate construction. -/
def parity : RMod.Classification.Pi (RMod.Legacy.Hierarchy.toOldData (monoidal C)) :=
  ⟨parityData C, parityLaws C⟩

/-- The odd map pi tensor X to X, evaluated as a map out of the odd line. -/
def zeta (X : C) : oddLine ⟶ SHom C ((piFunctor C).obj X) X :=
  RMod.Legacy.homogeneousMap _ 1 ((parity C).data.zHom X 1)

/-- The inverse uses the inverse odd comparison and the inverse left unitor. -/
def zetaInv (X : C) : oddLine ⟶ SHom C X ((piFunctor C).obj X) :=
  RMod.Legacy.homogeneousMap _ 1 ((parity C).data.zInv X 1)

/-- The map from the odd line recovers the full homogeneous total morphism. -/
theorem point_zeta (X : C) : homogeneousPoint 1 (zeta C X) = (parity C).data.zHom X := by
  funext b
  by_cases hb : b = 1
  · subst b
    exact RMod.Legacy.homogeneousPoint_map_same _ 1 _
  · exact (RMod.Legacy.homogeneousPoint_map_ne _ 1 b _ hb).trans
      ((RMod.Legacy.BrundanEllisParity.z_hom_odd (monoidal C) (parity C) X) b hb).symm

theorem point_zetaInv (X : C) : homogeneousPoint 1 (zetaInv C X) = (parity C).data.zInv X := by
  funext b
  by_cases hb : b = 1
  · subst b
    exact RMod.Legacy.homogeneousPoint_map_same _ 1 _
  · exact (RMod.Legacy.homogeneousPoint_map_ne _ 1 b _ hb).trans
      ((RMod.Legacy.BrundanEllisParity.z_inv_odd (monoidal C) (parity C) X) b hb).symm

/-- Tensoring the specified odd isomorphism and applying the unitor is invertible. -/
theorem zeta_hom_inv (X : C) :
    tComp C (homogeneousPoint 1 (zeta C X)) (homogeneousPoint 1 (zetaInv C X)) =
      evenPoint (eId SuperVec ((piFunctor C).obj X)) := by
  rw [point_zeta, point_zetaInv]
  exact RMod.Legacy.BrundanEllisParity.z_hom_inv (monoidal C) (parity C) X

theorem zeta_inv_hom (X : C) :
    tComp C (homogeneousPoint 1 (zetaInv C X)) (homogeneousPoint 1 (zeta C X)) =
      evenPoint (eId SuperVec X) := by
  rw [point_zetaInv, point_zeta]
  exact RMod.Legacy.BrundanEllisParity.z_inv_hom (monoidal C) (parity C) X

/-- The enriched shift map is the paper-convention left tensor by an even identity. -/
theorem piFunctor_total {X Y : C} (f : THom C X Y) :
    tMap (piFunctor C) f = (parity C).data.shiftHom f := by
  change tMap (piFunctor C) f =
    RMod.Legacy.Hierarchy.legacyTensor (monoidal C)
      (RMod.Legacy.evenPoint ((monoidal C).data.id P.pi)) f
  rw [RMod.Legacy.Hierarchy.legacyTensor_even_left (monoidal C) _ _
    (RMod.Legacy.evenPoint_mem_grade (monoidal C).super ((monoidal C).data.id P.pi))]
  funext a
  change enrichedTensorMap (MonoidalSuperCategory.tensor (C := C))
      MonoidalSuperCategory.tensor_objects P.pi P.pi X Y a
      (((λ_ (SHom C X Y)).inv ≫ (eId SuperVec P.pi ⊗ₘ 𝟙 (SHom C X Y))) a (f a)) = _
  erw [congrFun (RMod.Regression.tensorPoint_even_left (eId SuperVec P.pi) f) a]
  rfl

/-- Definition 1.12 supplies a genuine Definition 1.7 parity shift. -/
def parityShift : RMod.ParityShift C where
  functor := piFunctor C
  hom := {
    app := zetaInv C
    naturality X Y := by
      apply odd_naturality_of_homogeneous (EnrichedFunctor.id SuperVec C) (piFunctor C) (zetaInv C)
      intro X Y a f
      let v : THom C X Y := Pi.single a f
      have hv : v ∈ RMod.Legacy.grade (monoidal C).super X Y a := by
        intro b hb
        change (Pi.single a f : THom C X Y) b = 0
        simp only [Pi.single_eq_of_ne hb]
      change tComp C (homogeneousPoint 1 (zetaInv C X)) (tMap (piFunctor C) v) =
        (-1 : ℝ) ^ a.val • tComp C v (homogeneousPoint 1 (zetaInv C Y))
      rw [point_zetaInv, point_zetaInv, piFunctor_total]
      exact RMod.Legacy.BrundanEllisParity.z_inv_naturality (monoidal C) (parity C) a v hv }
  inv := zeta C
  hom_inv := zeta_inv_hom C
  inv_hom := zeta_hom_inv C

end RMod.BrundanEllis.ParityConstruction
