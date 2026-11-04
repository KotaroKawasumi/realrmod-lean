import RMod.Classification.Proofs.ReconstructionTensorBicone
import RMod.Classification.Proofs.ReconstructionUnitSourceUnitor

/-!
# Source unitors on the actual component tensor presentations

On the summand consisting of the selected unit component and a component
of X, the source unitor is the component unitor followed by its inclusion.
This follows from ordinary unitor naturality and even interchange for
the actual selected inclusions.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorUnit_inclusion_left :
    A.data.comp ((reconstructionTensorBicone A A.data.tensorUnit X).ι (1, g)) (A.data.leftUnitorHom X) =
      A.data.comp
        (A.data.comp (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)
          (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj))
          (A.data.leftUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj))
        ((reconstructionSourceBicone A X).ι g) := by
  let U : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
  let Y : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let i : A.data.Hom U A.data.tensorUnit := (reconstructionSourceBicone A A.data.tensorUnit).ι 1
  let j : A.data.Hom Y X := (reconstructionSourceBicone A X).ι g
  have ht : A.data.tensorHom i j = A.data.comp
      (A.data.tensorHom i (A.data.id Y)) (A.data.tensorHom (A.data.id A.data.tensorUnit) j) :=
    ((interchange_first_even A.laws.toWeaklyPointedSuperfusionLaws
      (A.data.id A.data.tensorUnit) j i (A.data.id Y)
      (reconstructionSourceBicone_inclusion_even A A.data.tensorUnit 1)).trans
        (congrArg₂ A.data.tensorHom (A.laws.comp_id i) (A.laws.id_comp j))).symm
  change A.data.comp (A.data.tensorHom i j) (A.data.leftUnitorHom X) =
    A.data.comp (A.data.comp (A.data.tensorHom i (A.data.id Y)) (A.data.leftUnitorHom Y)) j
  exact (congrArg (fun f => A.data.comp f (A.data.leftUnitorHom X)) ht).trans
    ((A.laws.comp_assoc _ _ _).trans
      ((congrArg (A.data.comp (A.data.tensorHom i (A.data.id Y)))
        (A.laws.left_unitor_naturality j)).trans (A.laws.comp_assoc _ _ _).symm))

theorem reconstructionTensorUnit_inclusion_right :
    A.data.comp ((reconstructionTensorBicone A X A.data.tensorUnit).ι (g, 1)) (A.data.rightUnitorHom X) =
      A.data.comp
        (A.data.comp (A.data.tensorHom (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj)
          ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
          (A.data.rightUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj))
        ((reconstructionSourceBicone A X).ι g) := by
  let U : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
  let Y : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let i : A.data.Hom U A.data.tensorUnit := (reconstructionSourceBicone A A.data.tensorUnit).ι 1
  let j : A.data.Hom Y X := (reconstructionSourceBicone A X).ι g
  have ht : A.data.tensorHom j i = A.data.comp
      (A.data.tensorHom (A.data.id Y) i) (A.data.tensorHom j (A.data.id A.data.tensorUnit)) :=
    ((interchange_first_even A.laws.toWeaklyPointedSuperfusionLaws
      j (A.data.id A.data.tensorUnit) (A.data.id Y) i (A.laws.id_even Y)).trans
        (congrArg₂ A.data.tensorHom (A.laws.id_comp j) (A.laws.comp_id i))).symm
  change A.data.comp (A.data.tensorHom j i) (A.data.rightUnitorHom X) =
    A.data.comp (A.data.comp (A.data.tensorHom (A.data.id Y) i) (A.data.rightUnitorHom Y)) j
  exact (congrArg (fun f => A.data.comp f (A.data.rightUnitorHom X)) ht).trans
    ((A.laws.comp_assoc _ _ _).trans
      ((congrArg (A.data.comp (A.data.tensorHom (A.data.id Y) i))
        (A.laws.right_unitor_naturality j)).trans (A.laws.comp_assoc _ _ _).symm))

end RMod.Classification
