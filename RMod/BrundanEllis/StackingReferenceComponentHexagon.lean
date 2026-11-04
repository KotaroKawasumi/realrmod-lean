import RMod.BrundanEllis.StackingReferenceComponentHexagonNaturality
import RMod.BrundanEllis.StackingReferenceComponentSums
import RMod.BrundanEllis.StackingReferenceCategoricalHexagon
import RMod.BrundanEllis.StackingReferenceCoherenceValue

/-! Extend the actual atom hexagons to all objects in the specified
reference components. Homogeneous inclusions, including odd ones, jointly
detect the desired maps. Finite coefficient equations remain explicit
hypotheses until the separate certificate modules discharge them. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
local notation "C" => reference.data.toWeaklyPointedSuperfusionData
local notation "L" => referenceProperty.toWeaklyPointedSuperfusionLaws

/-- The concrete raw atom identity transfers faithfully to the public reference. -/
theorem referenceLeftHexagon_atom (a b c : ZMod 8) (he : ReferenceCommutor.LeftEquation a b c) :
    (referenceLeftHexagonShort a b c (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))
      (referenceSingleton_component a 0) (referenceSingleton_component b 0) (referenceSingleton_component c 0)).hom =
    (referenceLeftHexagonLong a b c (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))
      (referenceSingleton_component a 0) (referenceSingleton_component b 0) (referenceSingleton_component c 0)).hom := by
  apply referenceValue_injective
  simp only [referenceLeftHexagonShort, referenceLeftHexagonLong, IsoData.trans, IsoData.assoc,
    IsoData.tensor, IsoData.refl, IsoData.symm, referenceExchangeData, referenceExchange,
    referenceValue_comp, referenceValue_tensor, referenceValue_id, referenceValue_smul,
    referenceValue_lift, referenceValue_associator, referenceValue_associatorInv]
  exact ReferenceCommutor.leftHexagon_categorical a b c he

/-- The concrete raw atom identity transfers faithfully to the public reference. -/
theorem referenceRightHexagon_atom (a b c : ZMod 8) (he : ReferenceCommutor.RightEquation a b c) :
    (referenceRightHexagonShort a b c (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))
      (referenceSingleton_component a 0) (referenceSingleton_component b 0) (referenceSingleton_component c 0)).hom =
    reference.data.smul (paritySign (ReferenceCommutor.rightDefect a b c))
      (referenceRightHexagonLong a b c (Obj.singleton (a, 0)) (Obj.singleton (b, 0)) (Obj.singleton (c, 0))
      (referenceSingleton_component a 0) (referenceSingleton_component b 0) (referenceSingleton_component c 0)).hom := by
  apply referenceValue_injective
  simp only [referenceRightHexagonShort, referenceRightHexagonLong, IsoData.trans, IsoData.assoc,
    IsoData.tensor, IsoData.refl, IsoData.symm, referenceExchangeData, referenceExchange,
    referenceValue_comp, referenceValue_tensor, referenceValue_id, referenceValue_smul,
    referenceValue_lift, referenceValue_associator, referenceValue_associatorInv]
  exact ReferenceCommutor.rightHexagon_categorical a b c he

/-- The left reference hexagon on arbitrary objects of the given components. -/
theorem referenceLeftHexagon (a b c : ZMod 8) (he : ReferenceCommutor.LeftEquation a b c)
    (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    (referenceLeftHexagonShort a b c X Y Z hX hY hZ).hom =
    (referenceLeftHexagonLong a b c X Y Z hX hY hZ).hom := by
  obtain ⟨n, ⟨d⟩⟩ := referenceComponent_homogeneousSum a X hX
  obtain ⟨m, ⟨e⟩⟩ := referenceComponent_homogeneousSum b Y hY
  obtain ⟨l, ⟨q⟩⟩ := referenceComponent_homogeneousSum c Z hZ
  apply referenceHom_ext_tensor3 d e q
  intro i j k
  have h₁ := referenceLeftHexagonShort_naturality a b c
    (Obj.singleton (a, 0)) X (Obj.singleton (b, 0)) Y (Obj.singleton (c, 0)) Z
    (referenceSingleton_component a 0) hX (referenceSingleton_component b 0) hY
    (referenceSingleton_component c 0) hZ
    (d.data.inclusion i) (e.data.inclusion j) (q.data.inclusion k)
    (d.data.parity i) (e.data.parity j) (q.data.parity k)
    (d.laws.inclusion_grade i) (e.laws.inclusion_grade j) (q.laws.inclusion_grade k)
  have h₂ := referenceLeftHexagonLong_naturality a b c
    (Obj.singleton (a, 0)) X (Obj.singleton (b, 0)) Y (Obj.singleton (c, 0)) Z
    (referenceSingleton_component a 0) hX (referenceSingleton_component b 0) hY
    (referenceSingleton_component c 0) hZ
    (d.data.inclusion i) (e.data.inclusion j) (q.data.inclusion k)
    (d.data.parity i) (e.data.parity j) (q.data.parity k)
    (d.laws.inclusion_grade i) (e.laws.inclusion_grade j) (q.laws.inclusion_grade k)
  rw [referenceLeftHexagon_atom a b c he] at h₁
  exact h₁.trans h₂.symm

/-- The right reference hexagon on arbitrary objects of the given components. -/
theorem referenceRightHexagon (a b c : ZMod 8) (he : ReferenceCommutor.RightEquation a b c)
    (X Y Z : reference.data.Obj)
    (hX : InComponent C a X) (hY : InComponent C b Y) (hZ : InComponent C c Z) :
    (referenceRightHexagonShort a b c X Y Z hX hY hZ).hom =
    reference.data.smul (paritySign (ReferenceCommutor.rightDefect a b c))
      (referenceRightHexagonLong a b c X Y Z hX hY hZ).hom := by
  obtain ⟨n, ⟨d⟩⟩ := referenceComponent_homogeneousSum a X hX
  obtain ⟨m, ⟨e⟩⟩ := referenceComponent_homogeneousSum b Y hY
  obtain ⟨l, ⟨q⟩⟩ := referenceComponent_homogeneousSum c Z hZ
  apply referenceHom_ext_tensor3 d e q
  intro i j k
  have h₁ := referenceRightHexagonShort_naturality a b c
    (Obj.singleton (a, 0)) X (Obj.singleton (b, 0)) Y (Obj.singleton (c, 0)) Z
    (referenceSingleton_component a 0) hX (referenceSingleton_component b 0) hY
    (referenceSingleton_component c 0) hZ
    (d.data.inclusion i) (e.data.inclusion j) (q.data.inclusion k)
    (d.data.parity i) (e.data.parity j) (q.data.parity k)
    (d.laws.inclusion_grade i) (e.laws.inclusion_grade j) (q.laws.inclusion_grade k)
  have h₂ := referenceRightHexagonLong_naturality a b c
    (Obj.singleton (a, 0)) X (Obj.singleton (b, 0)) Y (Obj.singleton (c, 0)) Z
    (referenceSingleton_component a 0) hX (referenceSingleton_component b 0) hY
    (referenceSingleton_component c 0) hZ
    (d.data.inclusion i) (e.data.inclusion j) (q.data.inclusion k)
    (d.data.parity i) (e.data.parity j) (q.data.parity k)
    (d.laws.inclusion_grade i) (e.laws.inclusion_grade j) (q.laws.inclusion_grade k)
  rw [referenceProperty.toWeaklyPointedSuperfusionLaws.comp_smul, h₁, h₂, referenceRightHexagon_atom a b c he,
    referenceProperty.toWeaklyPointedSuperfusionLaws.smul_comp, ← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul, ← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul, mul_comm]

end RMod.BrundanEllis.Stacking
