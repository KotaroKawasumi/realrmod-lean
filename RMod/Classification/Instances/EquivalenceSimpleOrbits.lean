import RMod.Classification.Instances.SimpleOrbits
import RMod.Classification.Proofs.TypeTransport

/-!
# The actual permutation of simple parity orbits under an equivalence

Map representatives by the specified forward and backward functors.
Preservation of simplicity and homogeneous isomorphisms makes the maps
well-defined on the quotient. The specified even unit and counit prove
that these two quotient maps are inverse.
-/

set_option autoImplicit false

namespace RMod.Classification.MonoidalSuperequivalence

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (E : MonoidalSuperequivalence C D)

def mapSimpleData (X : SimpleObject C) : SimpleObjectData D.data :=
  ⟨E.data.forward.obj X.data.object⟩

theorem mapSimpleLaws (X : SimpleObject C) : SimpleObjectLaws D.data (E.mapSimpleData X) :=
  ⟨(E.isSimple_map_iff X.data.object).mpr X.laws.simple⟩

def mapSimple (X : SimpleObject C) : SimpleObject D :=
  ⟨E.mapSimpleData X, E.mapSimpleLaws X⟩

def backwardSimpleData (Y : SimpleObject D) : SimpleObjectData C.data :=
  ⟨E.data.backward.obj Y.data.object⟩

theorem backwardSimpleLaws (Y : SimpleObject D) : SimpleObjectLaws C.data (E.backwardSimpleData Y) :=
  ⟨(E.isSimple_backward_map_iff Y.data.object).mpr Y.laws.simple⟩

def backwardSimple (Y : SimpleObject D) : SimpleObject C :=
  ⟨E.backwardSimpleData Y, E.backwardSimpleLaws Y⟩

def simpleOrbitMap : SimpleOrbit C → SimpleOrbit D :=
  Quotient.map E.mapSimple (fun _ _ h => E.sameParityOrbit_map_iff.mpr h)

def simpleOrbitBackward : SimpleOrbit D → SimpleOrbit C :=
  Quotient.map E.backwardSimple (fun _ _ h => E.sameParityOrbit_backward_map_iff.mpr h)

def simpleOrbitEquiv : SimpleOrbit C ≃ SimpleOrbit D where
  toFun := E.simpleOrbitMap
  invFun := E.simpleOrbitBackward
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro X
    apply Quotient.sound
    exact SameParityOrbit.symm
      ⟨0, E.data.unitHom X.data.object, E.data.unitInv X.data.object,
        E.laws.unit_hom_inv X.data.object, E.laws.unit_inv_hom X.data.object,
        E.laws.unit_hom_even X.data.object, E.laws.unit_inv_even X.data.object⟩
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro Y
    apply Quotient.sound
    exact ⟨0, E.data.counitHom Y.data.object, E.data.counitInv Y.data.object,
      E.laws.counit_hom_inv Y.data.object, E.laws.counit_inv_hom Y.data.object,
      E.laws.counit_hom_even Y.data.object, E.laws.counit_inv_even Y.data.object⟩

end RMod.Classification.MonoidalSuperequivalence
