import RMod.Classification.Instances.ReconstructionSourceEquivalence
import RMod.Classification.Proofs.SpanFamilySumEquivalence

/-! # Superlinear laws of the intrinsic source decomposition -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0})

instance reconstructionSource_forward_additive : (reconstructionSourceEquivalence A).functor.Additive := by
  unfold reconstructionSourceEquivalence
  infer_instance

instance reconstructionSource_forward_linear : (reconstructionSourceEquivalence A).functor.Linear ℝ := by
  unfold reconstructionSourceEquivalence
  infer_instance

instance reconstructionSource_backward_additive : (reconstructionSourceEquivalence A).inverse.Additive :=
  Equivalence.inverse_additive _

instance reconstructionSource_backward_linear : (reconstructionSourceEquivalence A).inverse.Linear ℝ :=
  Equivalence.inverseLinear ℝ _

theorem reconstructionSource_forward_grade
    {X Y : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object)}
    {a : ZMod 2} (f : X ⟶ Y) (hf : ∀ g, A.data.IsHomogeneous a (f g).hom) :
    A.data.IsHomogeneous a ((reconstructionSourceEquivalence A).functor.map f) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySum_map_grade _ _ f hf

theorem reconstructionSource_backward_grade {X Y : LinearCategory A.toWeaklyPointedSuperfusion}
    {a : ZMod 2} (f : X ⟶ Y) (hf : A.data.IsHomogeneous a f)
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous a ((reconstructionSourceEquivalence A).inverse.map f g).hom := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence_inverse_map_grade _ _ _ _ _ f hf g

theorem reconstructionSource_unit_hom_even
    (X : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceEquivalence A).unitIso.hom.app X g).hom := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence_unit_hom_even _ _ _ _ _ X g

theorem reconstructionSource_unit_inv_even
    (X : SpanFamilyCategory A.toWeaklyPointedSuperfusion
      (fun g => (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object))
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceEquivalence A).unitIso.inv.app X g).hom := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence_unit_inv_even _ _ _ _ _ X g

theorem reconstructionSource_counit_hom_even (X : LinearCategory A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceEquivalence A).counitIso.hom.app X) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence_counit_hom_even _ _ _ _ _ X

theorem reconstructionSource_counit_inv_even (X : LinearCategory A.toWeaklyPointedSuperfusion) :
    A.data.IsHomogeneous 0 ((reconstructionSourceEquivalence A).counitIso.inv.app X) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  exact spanFamilySumEquivalence_counit_inv_even _ _ _ _ _ X

end RMod.Classification
