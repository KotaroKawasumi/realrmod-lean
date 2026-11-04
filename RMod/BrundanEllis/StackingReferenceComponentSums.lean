import RMod.BrundanEllis.StackingReferenceComponentExchange
import RMod.Classification.Proofs.HomogeneousSums
import RMod.Classification.Instances.HomogeneousSumTensor

/-! Every object in a reference component has a complete presentation by
homogeneous copies of its unshifted atom. Empty presentations include the
zero object. This is a proof of existence, without a new choice of data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.FromRawDCT
local notation "C" => reference.data.toWeaklyPointedSuperfusionData

/-- Intrinsic type detection supplies homogeneous atom summands. -/
theorem referenceComponent_homogeneousSum (a : ZMod 8) (X : reference.data.Obj)
    (hX : InComponent C a X) :
    ∃ n, Nonempty (HomogeneousSum C (Obj.singleton (a, 0)) X n) := by
  obtain ⟨n, S, hS, hd⟩ := hX
  have hs := (reference_simple_iff _).mpr (realSingleton_simple a 0)
  have ht := (reference_type_iff _ _).mpr ((realSingleton_type_iff a 0 a).mpr rfl)
  have ho (i : Fin n) : RMod.Classification.SameParityOrbit C (Obj.singleton (a, 0)) (S i) :=
    (referenceProperty.type_detects_orbit _ _ a hs (hS i).1 ht).mp (hS i).2
  obtain ⟨d, hdl⟩ := exists_homogeneousSum referenceProperty.toWeaklyPointedSuperfusionLaws ho hd
  exact ⟨n, ⟨⟨d, hdl⟩⟩⟩

/-- Tensor products of homogeneous summand inclusions jointly detect maps.
The signed projections from the existing tensor presentation provide the
completeness equation, including when one of the families is empty. -/
theorem referenceHom_ext_tensor3 {A B D X Y Z W : reference.data.Obj} {n m l : ℕ}
    (d : HomogeneousSum C A X n) (e : HomogeneousSum C B Y m)
    (q : HomogeneousSum C D Z l)
    (f g : reference.data.Hom (reference.data.tensorObj (reference.data.tensorObj X Y) Z) W)
    (h : ∀ i j k, reference.data.comp
      (reference.data.tensorHom (reference.data.tensorHom (d.data.inclusion i) (e.data.inclusion j))
        (q.data.inclusion k)) f = reference.data.comp
      (reference.data.tensorHom (reference.data.tensorHom (d.data.inclusion i) (e.data.inclusion j))
        (q.data.inclusion k)) g) : f = g := by
  let R : WeaklyPointedSuperfusion := ⟨C, referenceProperty.toWeaklyPointedSuperfusionLaws⟩
  let de := @HomogeneousSum.tensor R _ _ _ _ _ _ d e
  let t := @HomogeneousSum.tensor R _ _ _ _ _ _ de q
  apply hom_ext_of_inclusions R.laws t.data.inclusion t.data.projection t.laws.total f g
  intro k
  exact h _ _ _

end RMod.BrundanEllis.Stacking
