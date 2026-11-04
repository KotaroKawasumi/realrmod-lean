import RMod.BrundanEllis.StackingModelBridge
import RMod.Hierarchy.Bridge.ReflectTensor
import RMod.BrundanEllis.StackingReferenceUniformRows

/-! Recover the original coefficient morphisms of the concrete reference
from the interfaces used by public pullbacks.  The maps preserve the actual
tensor, including the convention correction in the legacy adapter. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
namespace RMod.BrundanEllis.Stacking
open Superfusion.RMod.FromRawDCT
open RMod.Legacy.Hierarchy

/-- The total Hom equivalence reads the original raw coefficient morphism. -/
def referenceValue {X Y : reference.data.Obj} (f : reference.data.Hom X Y) :
    Hom Superfusion.RMod.RawDCT.realDData X Y := by
  with_unfolding_all exact totalHomEquiv RMod.realRModLegacy X Y f

/-- Conversely every original raw morphism has its unique total-Hom presentation. -/
def referenceLift {X Y : reference.data.Obj} (f : Hom Superfusion.RMod.RawDCT.realDData X Y) :
    reference.data.Hom X Y := by
  with_unfolding_all exact (totalHomEquiv RMod.realRModLegacy X Y).symm f

theorem referenceValue_lift {X Y : reference.data.Obj} (f : Hom Superfusion.RMod.RawDCT.realDData X Y) :
    referenceValue (referenceLift f) = f := by
  with_unfolding_all exact (totalHomEquiv RMod.realRModLegacy X Y).apply_symm_apply f

theorem referenceLift_value {X Y : reference.data.Obj} (f : reference.data.Hom X Y) :
    referenceLift (referenceValue f) = f := by
  with_unfolding_all exact (totalHomEquiv RMod.realRModLegacy X Y).symm_apply_apply f

theorem referenceValue_comp {X Y Z : reference.data.Obj} (f : reference.data.Hom X Y)
    (g : reference.data.Hom Y Z) :
    referenceValue (reference.data.comp f g) = Hom.comp (referenceValue f) (referenceValue g) := by
  with_unfolding_all exact totalHomEquiv_comp RMod.realRModLegacy X Y Z f g

theorem referenceValue_id (X : reference.data.Obj) :
    referenceValue (reference.data.id X) = Hom.id Superfusion.RMod.RawDCT.realDData X := by
  with_unfolding_all exact totalHomEquiv_id RMod.realRModLegacy X

theorem referenceValue_tensor {X X' Y Y' : reference.data.Obj}
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') :
    referenceValue (reference.data.tensorHom f g) =
      Tensor.hom Superfusion.RMod.RawDCT.realDData
        (Superfusion.RMod.RawDCT.shiftCData Superfusion.RMod.RawDCT.realDData
          Superfusion.RMod.RawDCT.realCData Superfusion.RMod.RawDCT.realComputableNuBeta.data)
        (referenceValue f) (referenceValue g) := by
  with_unfolding_all exact totalHomEquiv_legacyTensor RMod.realRModLegacy f g

theorem referenceValue_smul {X Y : reference.data.Obj} (r : ℝ) (f : reference.data.Hom X Y) :
    referenceValue (reference.data.smul r f) = Hom.smul r (referenceValue f) := by
  with_unfolding_all exact (totalHomEquiv RMod.realRModLegacy X Y).map_smul r f

theorem referenceValue_grade {X Y : reference.data.Obj} (d : ZMod 2) (f : reference.data.Hom X Y) :
    reference.data.IsHomogeneous d f ↔ Hom.MemGrade d (referenceValue f) := by
  with_unfolding_all exact totalHomEquiv_grade RMod.realRModLegacy X Y f d

theorem referenceValue_zero (X Y : reference.data.Obj) :
    referenceValue (reference.data.zero (X := X) (Y := Y)) =
      Hom.zero Superfusion.RMod.RawDCT.realDData X Y := by
  with_unfolding_all exact (totalHomEquiv RMod.realRModLegacy X Y).map_zero

/-- Simplicity is unchanged by the interface roundtrip. -/
theorem reference_simple_iff (X : reference.data.Obj) :
    reference.data.IsSimple X ↔ RMod.realRModData.IsSimple X := by
  with_unfolding_all exact (legacySimple_iff (ofOldMonoidalSupercategory RMod.realRModLegacy)
    (RMod.Legacy.evenObj _ X)).trans (oldSimple_iff RMod.realRModLegacy X).symm

/-- The intrinsic type is unchanged by the same roundtrip. -/
theorem reference_type_iff (X : reference.data.Obj) (a : ZMod 8) :
    RMod.Classification.HasBWType reference.data.toWeaklyPointedSuperfusionData X a ↔
      RMod.Classification.HasBWType RMod.realRModData X a := by
  have h : RMod.Classification.HasBWType reference.data.toWeaklyPointedSuperfusionData X a ↔
      HasBrauerWallType realRMod (evenObj realRMod X) a :=
    (legacyBrauerWallType_iff legacyReference X a).trans
      (RMod.StatementLegacy.StatementBridge.hasType_toFusion
        (RMod.EnrichedBridge.toWeak (Bridge.toStage realRMod)).toFusionPiSupercategory _ a)
  exact h.trans (fromOld_type RMod.Classification.realPiSuperfusion X a).symm

/-- A public reference component has its stated label on every stored row. -/
theorem reference_component_label {a : ZMod 8} {X : reference.data.Obj}
    (hX : RMod.Classification.InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (i : Fin X.size) : (X.atom i).label = a := by
  by_contra hne
  have hz := (RMod.Classification.InComponent.iff_orthogonal referenceProperty X a).mp hX
    (Obj.singleton (X.atom i)) (X.atom i).label
    ((reference_simple_iff _).mpr
      (RMod.Classification.realSingleton_simple (X.atom i).label (X.atom i).shift))
    ((reference_type_iff _ _).mpr
      ((RMod.Classification.realSingleton_type_iff (X.atom i).label (X.atom i).shift
        (X.atom i).label).mpr rfl)) hne (referenceLift (Finite.atomInclusion X i))
  have h := congrArg referenceValue hz
  rw [referenceValue_lift, referenceValue_zero] at h
  apply RealSemisimple.atomInclusion_ne_zero X i
  exact h

end RMod.BrundanEllis.Stacking
