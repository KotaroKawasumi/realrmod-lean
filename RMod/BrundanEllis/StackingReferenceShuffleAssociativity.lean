import RMod.BrundanEllis.StackingSuperInterchangeAssociativity
import RMod.BrundanEllis.StackingReferenceComponentHexagon

/-! Associativity of the actual reference shuffle. The explicit coefficient hexagons determine its block crossings and the parity cover recovers their Koszul sign. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "L" => referenceProperty.toWeaklyPointedSuperfusionLaws
local notation "R" => WeaklyPointedSuperfusion.mk reference.data.toWeaklyPointedSuperfusionData
  referenceProperty.toWeaklyPointedSuperfusionLaws

/-- Solve the first hexagon for the actual block exchange. -/
theorem referenceExchange_leftExpansion (a b c : ZMod 8)
    (he : ReferenceCommutor.LeftEquation a b c) (X Y Z : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData c Z) :
    referenceExchange a (b + c) X (reference.data.tensorObj Y Z) hX
      (hY.tensor referenceProperty hZ) =
    superLeftExpansion R X Y Z (referenceExchange a b X Y hX hY)
      (referenceExchange a c X Z hX hZ) := by
  have h := referenceLeftHexagon a b c he X Y Z hX hY hZ
  have h' := congrArg (fun f => reference.data.comp (reference.data.associatorInv X Y Z)
    (reference.data.comp f (reference.data.associatorInv Y Z X))) h
  simp only [referenceLeftHexagonShort, referenceLeftHexagonLong, IsoData.trans,
    IsoData.assoc, IsoData.tensor, IsoData.refl, referenceExchangeData,
    referenceProperty.toWeaklyPointedSuperfusionLaws.comp_assoc] at h'
  rw [referenceProperty.toWeaklyPointedSuperfusionLaws.associator_hom_inv,
    referenceProperty.toWeaklyPointedSuperfusionLaws.comp_id,
    ← referenceProperty.toWeaklyPointedSuperfusionLaws.comp_assoc
      (reference.data.associatorInv X Y Z),
    referenceProperty.toWeaklyPointedSuperfusionLaws.associator_inv_hom,
    referenceProperty.toWeaklyPointedSuperfusionLaws.id_comp] at h'
  exact h'

/-- The second block exchange contains the verified reference defect. -/
theorem referenceExchange_rightExpansion (a b c : ZMod 8)
    (he : ReferenceCommutor.RightEquation a b c) (X Y Z : reference.data.Obj)
    (hX : InComponent reference.data.toWeaklyPointedSuperfusionData a X)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData b Y)
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData c Z) :
    referenceExchange (a + b) c (reference.data.tensorObj X Y) Z
      (hX.tensor referenceProperty hY) hZ =
    reference.data.smul ((-1 : ℝ) ^ (ReferenceCommutor.rightDefect a b c).val)
      (superRightExpansion R X Y Z (referenceExchange b c Y Z hY hZ)
        (referenceExchange a c X Z hX hZ)) := by
  have h := referenceRightHexagon a b c he X Y Z hX hY hZ
  simpa only [referenceRightHexagonShort, referenceRightHexagonLong, IsoData.trans,
    IsoData.assoc, IsoData.tensor, IsoData.refl, IsoData.symm, referenceExchangeData,
    ReferenceCommutor.paritySign_pow, superRightExpansion] using h

/-- The forward reference shuffle is the generic homogeneous shuffle. -/
theorem referenceShuffle_hom (a b : ZMod 8) (A B C D : reference.data.Obj)
    (hB : InComponent reference.data.toWeaklyPointedSuperfusionData a B)
    (hC : InComponent reference.data.toWeaklyPointedSuperfusionData b C) :
    (referenceShuffleData a b A B C D hB hC).hom =
      superInterchangeHom R A B C D (referenceExchange a b B C hB hC) :=
  interchangeIsoData_hom R A B C D (referenceExchangeData a b B C hB hC)

/-- The six-object reference shuffle has exactly the reference hexagon defect
and the Koszul sign of the two disjoint elementary crossings. -/
theorem referenceShuffle_associativity (b c d e : ZMod 8)
    (hl : ReferenceCommutor.LeftEquation b c e)
    (hr : ReferenceCommutor.RightEquation b d e)
    (A B C D E F : reference.data.Obj)
    (hB : InComponent reference.data.toWeaklyPointedSuperfusionData b B)
    (hC : InComponent reference.data.toWeaklyPointedSuperfusionData c C)
    (hD : InComponent reference.data.toWeaklyPointedSuperfusionData d D)
    (hE : InComponent reference.data.toWeaklyPointedSuperfusionData e E) :
    reference.data.comp
      (reference.data.tensorHom (referenceShuffleData b c A B C D hB hC).hom
        (reference.data.id (reference.data.tensorObj E F)))
      (reference.data.comp
        (referenceShuffleData (b + d) e (reference.data.tensorObj A C)
          (reference.data.tensorObj B D) E F (hB.tensor referenceProperty hD) hE).hom
        (reference.data.tensorHom (reference.data.associatorHom A C E) (reference.data.associatorHom B D F))) =
    reference.data.smul
      ((-1 : ℝ) ^ (ReferenceCommutor.rightDefect b d e +
        ReferenceCommutor.degree b c * ReferenceCommutor.degree d e).val)
      (reference.data.comp
        (reference.data.associatorHom (reference.data.tensorObj A B)
          (reference.data.tensorObj C D) (reference.data.tensorObj E F))
        (reference.data.comp
          (reference.data.tensorHom (reference.data.id (reference.data.tensorObj A B))
            (referenceShuffleData d e C D E F hD hE).hom)
          (referenceShuffleData b (c + e) A B (reference.data.tensorObj C E)
            (reference.data.tensorObj D F) hB (hC.tensor referenceProperty hE)).hom)) := by
  have hh := superInterchange_associativity R A B C D E F
    (ReferenceCommutor.degree b c) (ReferenceCommutor.degree b e) (ReferenceCommutor.degree d e)
    (referenceExchange b c B C hB hC) (referenceExchange d e D E hD hE)
    (referenceExchange b e B E hB hE)
    (referenceExchange_grade b c B C hB hC) (referenceExchange_grade d e D E hD hE)
    (referenceExchange_grade b e B E hB hE)
  have hright := referenceExchange_rightExpansion b d e hr B D E hB hD hE
  have hright' := congrArg
    (reference.data.smul ((-1 : ℝ) ^ (ReferenceCommutor.rightDefect b d e).val)) hright
  simp only [← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul,
    parity_power_mul_self, referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul] at hright'
  rw [← hright', ← referenceExchange_leftExpansion b c e hl B C E hB hC hE,
    superInterchangeHom_smul, referenceProperty.toWeaklyPointedSuperfusionLaws.smul_comp,
    referenceProperty.toWeaklyPointedSuperfusionLaws.comp_smul] at hh
  have hh' := congrArg
    (reference.data.smul ((-1 : ℝ) ^ (ReferenceCommutor.rightDefect b d e).val)) hh
  simpa only [referenceShuffle_hom, ← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul,
    parity_power_mul_self, referenceProperty.toWeaklyPointedSuperfusionLaws.one_smul,
    ← parity_power_add] using hh'

end RMod.BrundanEllis.Stacking
