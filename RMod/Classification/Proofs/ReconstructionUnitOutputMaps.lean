import RMod.Classification.Proofs.ReconstructionUnitOutputIndex
import RMod.Classification.Proofs.ReconstructionUnitComponentMaps
import RMod.Classification.Instances.ReconstructionTensorComponentBicone
import RMod.Classification.Proofs.SpanEqualityMaps
import Batteries.Tactic.GeneralizeProofs

/-!
# Unit maps on the actual fixed-output tensor presentations

The surviving convolution index gives the canonical unit span after
its group equality transport. The component-inclusion calculation then
identifies the composite with the selected image of the source unitor.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitOutput_map :
    (reconstructionTensorComponentBicone A A.data.tensorUnit X g).ι 1 ≫
      ((reconstructionSourceEquivalence A).inverse.map (A.data.leftUnitorHom X)) g =
      eqToHom (reconstructionLeftUnitOutput_eq A X g) ≫ reconstructionLeftUnitSpanMap A X g := by
  apply ObjectProperty.hom_ext
  change A.data.comp
      (A.data.comp ((reconstructionTensorBicone A A.data.tensorUnit X).ι (1, 1⁻¹ * g))
        ((reconstructionSourceBicone A (A.data.tensorObj A.data.tensorUnit X)).π g))
      (((reconstructionSourceEquivalence A).inverse.map (A.data.leftUnitorHom X)) g).hom =
    A.data.comp (eqToHom (reconstructionLeftUnitOutput_eq A X g)).hom (reconstructionLeftUnitSpanMap A X g).hom
  rw [span_eqToHom_hom]
  let U : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
  let V : SimpleOrbit A.toWeaklyPointedSuperfusion → A.data.Obj :=
    fun j => ((reconstructionSourceEquivalence A).inverse.obj X j).obj
  let i : A.data.Hom U A.data.tensorUnit := (reconstructionSourceBicone A A.data.tensorUnit).ι 1
  let j : ∀ k, A.data.Hom (V k) X := fun k => (reconstructionSourceBicone A X).ι k
  let P : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj A.data.tensorUnit X) g).obj
  let pr : A.data.Hom (A.data.tensorObj A.data.tensorUnit X) P :=
    (reconstructionSourceBicone A (A.data.tensorObj A.data.tensorUnit X)).π g
  let m : A.data.Hom P (V g) := ((reconstructionSourceEquivalence A).inverse.map (A.data.leftUnitorHom X) g).hom
  let c : A.data.Hom (A.data.tensorObj U (V g)) (V g) := (reconstructionLeftUnitSpanMap A X g).hom
  generalize_proofs he
  revert he
  change ∀ he : A.data.tensorObj U (V (1⁻¹ * g)) = A.data.tensorObj U (V g),
    A.data.comp (A.data.comp (A.data.tensorHom i (j (1⁻¹ * g))) pr) m =
      A.data.comp (IsoData.ofEq A.data.toWeaklyPointedSuperfusionData he).hom c
  generalize hg : (1 : SimpleOrbit A.toWeaklyPointedSuperfusion)⁻¹ * g = k
  have hk : k = g := hg.symm.trans (by rw [inv_one, one_mul])
  clear hg
  subst k
  intro he
  exact (reconstructionTensorUnit_component_left A X g).trans (A.laws.id_comp _).symm

theorem reconstructionRightUnitOutput_map :
    (reconstructionTensorComponentBicone A X A.data.tensorUnit g).ι g ≫
      ((reconstructionSourceEquivalence A).inverse.map (A.data.rightUnitorHom X)) g =
      eqToHom (reconstructionRightUnitOutput_eq A X g) ≫ reconstructionRightUnitSpanMap A X g := by
  apply ObjectProperty.hom_ext
  change A.data.comp
      (A.data.comp ((reconstructionTensorBicone A X A.data.tensorUnit).ι (g, g⁻¹ * g))
        ((reconstructionSourceBicone A (A.data.tensorObj X A.data.tensorUnit)).π g))
      (((reconstructionSourceEquivalence A).inverse.map (A.data.rightUnitorHom X)) g).hom =
    A.data.comp (eqToHom (reconstructionRightUnitOutput_eq A X g)).hom (reconstructionRightUnitSpanMap A X g).hom
  rw [span_eqToHom_hom]
  let U : SimpleOrbit A.toWeaklyPointedSuperfusion → A.data.Obj :=
    fun j => ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit j).obj
  let V : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let i : ∀ k, A.data.Hom (U k) A.data.tensorUnit :=
    fun k => (reconstructionSourceBicone A A.data.tensorUnit).ι k
  let j : A.data.Hom V X := (reconstructionSourceBicone A X).ι g
  let P : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X A.data.tensorUnit) g).obj
  let pr : A.data.Hom (A.data.tensorObj X A.data.tensorUnit) P :=
    (reconstructionSourceBicone A (A.data.tensorObj X A.data.tensorUnit)).π g
  let m : A.data.Hom P V := ((reconstructionSourceEquivalence A).inverse.map (A.data.rightUnitorHom X) g).hom
  let c : A.data.Hom (A.data.tensorObj V (U 1)) V := (reconstructionRightUnitSpanMap A X g).hom
  generalize_proofs he
  revert he
  change ∀ he : A.data.tensorObj V (U (g⁻¹ * g)) = A.data.tensorObj V (U 1),
    A.data.comp (A.data.comp (A.data.tensorHom j (i (g⁻¹ * g))) pr) m =
      A.data.comp (IsoData.ofEq A.data.toWeaklyPointedSuperfusionData he).hom c
  generalize hg : g⁻¹ * g = k
  have hk : k = 1 := hg.symm.trans (inv_mul_cancel g)
  clear hg
  subst k
  intro he
  exact (reconstructionTensorUnit_component_right A X g).trans (A.laws.id_comp _).symm

end RMod.Classification
