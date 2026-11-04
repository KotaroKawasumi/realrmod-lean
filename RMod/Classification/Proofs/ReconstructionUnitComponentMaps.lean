import RMod.Classification.Proofs.ReconstructionUnitPresentation
import RMod.Classification.Proofs.ReconstructionSourceNaturality

/-!
# The source unitors on the selected tensor components

Projection naturality moves the global unitor through the selected
component projector. The tensor-inclusion formula and the diagonal
bicone identity then leave the canonical component unit map.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorUnit_component_left :
    A.data.comp
      (A.data.comp ((reconstructionTensorBicone A A.data.tensorUnit X).ι (1, g))
        ((reconstructionSourceBicone A (A.data.tensorObj A.data.tensorUnit X)).π g))
      (((reconstructionSourceEquivalence A).inverse.map (A.data.leftUnitorHom X)) g).hom =
      A.data.comp (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)
        (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj))
        (A.data.leftUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj) := by
  let U : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
  let Y : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let P : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj A.data.tensorUnit X) g).obj
  let i : A.data.Hom (A.data.tensorObj U Y) (A.data.tensorObj A.data.tensorUnit X) :=
    (reconstructionTensorBicone A A.data.tensorUnit X).ι (1, g)
  let p : A.data.Hom (A.data.tensorObj A.data.tensorUnit X) P :=
    (reconstructionSourceBicone A (A.data.tensorObj A.data.tensorUnit X)).π g
  let m : A.data.Hom P Y := ((reconstructionSourceEquivalence A).inverse.map (A.data.leftUnitorHom X) g).hom
  let j : A.data.Hom Y X := (reconstructionSourceBicone A X).ι g
  let q : A.data.Hom X Y := (reconstructionSourceBicone A X).π g
  let u : A.data.Hom (A.data.tensorObj U Y) Y := A.data.comp
    (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1) (A.data.id Y))
    (A.data.leftUnitorHom Y)
  have hn : A.data.comp (A.data.leftUnitorHom X) q = A.data.comp p m :=
    reconstructionSource_projection_naturality A (A.data.leftUnitorHom X) g
  have hi : A.data.comp i (A.data.leftUnitorHom X) = A.data.comp u j :=
    reconstructionTensorUnit_inclusion_left A X g
  have hj : A.data.comp j q = A.data.id Y :=
    CategoryTheory.Limits.bicone_ι_π_self (reconstructionSourceBicone A X) g
  change A.data.comp (A.data.comp i p) m = u
  calc
    _ = A.data.comp i (A.data.comp p m) := A.laws.comp_assoc _ _ _
    _ = A.data.comp i (A.data.comp (A.data.leftUnitorHom X) q) := congrArg (A.data.comp i) hn.symm
    _ = A.data.comp (A.data.comp i (A.data.leftUnitorHom X)) q := (A.laws.comp_assoc _ _ _).symm
    _ = A.data.comp (A.data.comp u j) q := congrArg (fun f => A.data.comp f q) hi
    _ = A.data.comp u (A.data.comp j q) := A.laws.comp_assoc _ _ _
    _ = u := (congrArg (A.data.comp u) hj).trans (A.laws.comp_id u)

theorem reconstructionTensorUnit_component_right :
    A.data.comp
      (A.data.comp ((reconstructionTensorBicone A X A.data.tensorUnit).ι (g, 1))
        ((reconstructionSourceBicone A (A.data.tensorObj X A.data.tensorUnit)).π g))
      (((reconstructionSourceEquivalence A).inverse.map (A.data.rightUnitorHom X)) g).hom =
      A.data.comp (A.data.tensorHom (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj)
        ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
        (A.data.rightUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj) := by
  let U : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
  let Y : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj X g).obj
  let P : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X A.data.tensorUnit) g).obj
  let i : A.data.Hom (A.data.tensorObj Y U) (A.data.tensorObj X A.data.tensorUnit) :=
    (reconstructionTensorBicone A X A.data.tensorUnit).ι (g, 1)
  let p : A.data.Hom (A.data.tensorObj X A.data.tensorUnit) P :=
    (reconstructionSourceBicone A (A.data.tensorObj X A.data.tensorUnit)).π g
  let m : A.data.Hom P Y := ((reconstructionSourceEquivalence A).inverse.map (A.data.rightUnitorHom X) g).hom
  let j : A.data.Hom Y X := (reconstructionSourceBicone A X).ι g
  let q : A.data.Hom X Y := (reconstructionSourceBicone A X).π g
  let u : A.data.Hom (A.data.tensorObj Y U) Y := A.data.comp
    (A.data.tensorHom (A.data.id Y) ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
    (A.data.rightUnitorHom Y)
  have hn : A.data.comp (A.data.rightUnitorHom X) q = A.data.comp p m :=
    reconstructionSource_projection_naturality A (A.data.rightUnitorHom X) g
  have hi : A.data.comp i (A.data.rightUnitorHom X) = A.data.comp u j :=
    reconstructionTensorUnit_inclusion_right A X g
  have hj : A.data.comp j q = A.data.id Y :=
    CategoryTheory.Limits.bicone_ι_π_self (reconstructionSourceBicone A X) g
  change A.data.comp (A.data.comp i p) m = u
  calc
    _ = A.data.comp i (A.data.comp p m) := A.laws.comp_assoc _ _ _
    _ = A.data.comp i (A.data.comp (A.data.rightUnitorHom X) q) := congrArg (A.data.comp i) hn.symm
    _ = A.data.comp (A.data.comp i (A.data.rightUnitorHom X)) q := (A.laws.comp_assoc _ _ _).symm
    _ = A.data.comp (A.data.comp u j) q := congrArg (fun f => A.data.comp f q) hi
    _ = A.data.comp u (A.data.comp j q) := A.laws.comp_assoc _ _ _
    _ = u := (congrArg (A.data.comp u) hj).trans (A.laws.comp_id u)

end RMod.Classification
