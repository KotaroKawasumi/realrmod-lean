import RMod.Classification.Proofs.ReconstructionUnitSourceIso
import RMod.Classification.Proofs.UnitGeneratorMaps
import RMod.Classification.Instances.TensorFunctors

/-!
# Unit diagrams after selecting the source unit component

The projection to the selected unit component cancels its inclusion.
Tensor functoriality moves this cancellation through either variable,
leaving exactly the retained generator equality and source unitor.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (Y : A.data.Obj)

theorem reconstructionUnitSource_left_unitor :
    A.data.comp (A.data.tensorHom (reconstructionUnitSourceIsoData A).hom (A.data.id Y))
      (A.data.comp (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) (A.data.id Y))
        (A.data.leftUnitorHom Y)) =
      (leftUnitGeneratorMap A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1)
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y).hom := by
  have ht := (tensorRightLaws A.toWeaklyPointedSuperfusion Y).map_comp
    (reconstructionUnitSourceIsoData A).hom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)
  have hh : A.data.comp (A.data.tensorHom (reconstructionUnitSourceIsoData A).hom (A.data.id Y))
      (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) (A.data.id Y)) =
      A.data.tensorHom
        (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
          (congrArg (fun S => S.data.object)
            (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion))).hom (A.data.id Y) :=
    ht.symm.trans (congrArg (fun f => A.data.tensorHom f (A.data.id Y))
      (reconstructionUnitSourceIso_inclusion A))
  exact (A.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => A.data.comp f (A.data.leftUnitorHom Y)) hh).trans
      (leftUnitGeneratorMap_hom A.toWeaklyPointedSuperfusion _
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y))

theorem reconstructionUnitSource_right_unitor :
    A.data.comp (A.data.tensorHom (A.data.id Y) (reconstructionUnitSourceIsoData A).hom)
      (A.data.comp (A.data.tensorHom (A.data.id Y) ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
        (A.data.rightUnitorHom Y)) =
      (rightUnitGeneratorMap A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1)
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y).hom := by
  have ht := (tensorLeftLaws A.toWeaklyPointedSuperfusion Y).map_comp
    (reconstructionUnitSourceIsoData A).hom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)
  have hh : A.data.comp (A.data.tensorHom (A.data.id Y) (reconstructionUnitSourceIsoData A).hom)
      (A.data.tensorHom (A.data.id Y) ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)) =
      A.data.tensorHom (A.data.id Y)
        (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
          (congrArg (fun S => S.data.object)
            (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion))).hom :=
    ht.symm.trans (congrArg (fun f => A.data.tensorHom (A.data.id Y) f)
      (reconstructionUnitSourceIso_inclusion A))
  exact (A.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => A.data.comp f (A.data.rightUnitorHom Y)) hh).trans
      (rightUnitGeneratorMap_hom A.toWeaklyPointedSuperfusion _
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y))

/-- The retained inverse identifies the selected component unitor with the generator unitor. -/
theorem reconstructionUnitSource_left_unitor_inv :
    A.data.comp (A.data.tensorHom (reconstructionUnitSourceIsoData A).inv (A.data.id Y))
      (leftUnitGeneratorMap A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1)
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y).hom =
      A.data.comp (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) (A.data.id Y))
        (A.data.leftUnitorHom Y) := by
  have he := (reconstructionUnitSourceIso_even A).tensor A.laws.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.refl A.laws.toWeaklyPointedSuperfusionLaws Y)
  have h := congrArg (A.data.comp (A.data.tensorHom (reconstructionUnitSourceIsoData A).inv (A.data.id Y)))
    (reconstructionUnitSource_left_unitor A Y)
  exact h.symm.trans ((A.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => A.data.comp f
      (A.data.comp (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) (A.data.id Y))
        (A.data.leftUnitorHom Y))) he.inv_hom).trans (A.laws.id_comp _)))


/-- The retained inverse identifies the selected component unitor with the generator unitor. -/
theorem reconstructionUnitSource_right_unitor_inv :
    A.data.comp (A.data.tensorHom (A.data.id Y) (reconstructionUnitSourceIsoData A).inv)
      (rightUnitGeneratorMap A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion 1)
        (simpleOrbitRepresentative_one A.toWeaklyPointedSuperfusion) Y).hom =
      A.data.comp (A.data.tensorHom (A.data.id Y) ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
        (A.data.rightUnitorHom Y) := by
  have he := (EvenIsoLaws.refl A.laws.toWeaklyPointedSuperfusionLaws Y).tensor A.laws.toWeaklyPointedSuperfusionLaws (reconstructionUnitSourceIso_even A)
  have h := congrArg (A.data.comp (A.data.tensorHom (A.data.id Y) (reconstructionUnitSourceIsoData A).inv))
    (reconstructionUnitSource_right_unitor A Y)
  exact h.symm.trans ((A.laws.comp_assoc _ _ _).symm.trans
    ((congrArg (fun f => A.data.comp f
      (A.data.comp (A.data.tensorHom (A.data.id Y) ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
        (A.data.rightUnitorHom Y))) he.inv_hom).trans (A.laws.id_comp _)))

end RMod.Classification
