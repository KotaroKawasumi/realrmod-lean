import RMod.Classification.Instances.EquivalenceSimpleOrbits
import RMod.Classification.Instances.SimpleOrbitGroup
import RMod.Classification.Proofs.SimpleTensorRepresentative

/-!
# The orbit permutation of a monoidal superequivalence is multiplicative

Map an actual nonzero simple-constituent inclusion and postcompose with
the inverse tensorator. This is a nonzero even map into the tensor of
the image simples, so tensor isotypy identifies its intrinsic orbit.
-/

set_option autoImplicit false

namespace RMod.Classification.MonoidalSuperequivalence

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (E : MonoidalSuperequivalence C D)

theorem simpleOrbitMap_mul (g h : SimpleOrbit C) :
    E.simpleOrbitMap (g * h) = E.simpleOrbitMap g * E.simpleOrbitMap h := by
  refine Quotient.inductionOn₂ g h ?_
  intro X Y
  apply Quotient.sound
  let d := simpleDecomposition C (C.data.tensorObj X.data.object Y.data.object)
  let j := d.data.decomposition.inclusion (tensorSimpleIndex C X Y)
  have hj : j ≠ C.data.zero := tensor_representative_inclusion_ne_zero C X Y
  have hm : E.data.forward.map j ≠ D.data.zero := by
    intro he
    exact hj ((E.map_bijective _ _).injective
      (he.trans (E.laws.forward.map_zero _ _).symm))
  have hn : D.data.comp (E.data.forward.map j)
      (E.data.forward.tensorInv X.data.object Y.data.object) ≠ D.data.zero := by
    intro he
    have hc := congrArg (fun f => D.data.comp f
      (E.data.forward.tensorHom X.data.object Y.data.object)) he
    rw [D.laws.comp_assoc, E.laws.forward.tensor_inv_hom, D.laws.comp_id,
      raw_zero_comp D.laws] at hc
    exact hm hc
  have hg := D.laws.comp_grade _ _
    (E.laws.forward.map_grade j (d.laws.decomposition.inclusion_even _))
    (E.laws.forward.tensor_inv_even X.data.object Y.data.object)
  rw [zero_add] at hg
  exact simple_orbit_of_map_to_tensor D (E.mapSimple X) (E.mapSimple Y)
    (E.mapSimple (simpleTensorRepresentative C X Y)).laws.simple _ hg hn

end RMod.Classification.MonoidalSuperequivalence
