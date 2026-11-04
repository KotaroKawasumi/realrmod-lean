import RMod.Classification.Proofs.Isotypy
import RMod.Classification.Proofs.IntrinsicTypes
import RMod.Classification.Proofs.Components
import RMod.Classification.Instances.HomogeneousSumMap

/-!
# Additivity of intrinsic types

The tensor-endomorphism equivalence multiplies Brauer-Wall classes.
Isotypy identifies that class with any simple constituent of the tensor
product. The intrinsic Clifford test and the order-eight calculation then
force the constituent's label to be the sum of the two input labels.
Finally, tensor functors and finite decompositions extend this to all
objects in components of a category satisfying P.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

attribute [local implicit_reducible] PiSuperfusion.toWeaklyPointedSuperfusion
  CategoryTheory.End Category.endSuperAlgebra Category.endGrading

theorem HasBWType.end_isBWEquivalent_realRep (C : WeaklyPointedSuperfusion.{0, 0})
    {X : LinearCategory C} {r : ZMod 8} (h : HasBWType C.data X r) :
    IsBWEquivalent (Category.endSuperAlgebra (K := ℝ) X) (realRep r) := by
  have hr := negativeTower_isBWEquivalent_realRep r.val
  rw [ZMod.natCast_zmod_val] at hr
  exact (HasBWType.isBWEquivalent C h).trans hr

theorem tensorEnd_isBWEquivalent_realRep (C : WeaklyPointedSuperfusion.{0, 0})
    (X Y : LinearCategory C) (hY : C.data.IsSimple Y) {r s : ZMod 8}
    (hr : HasBWType C.data X r) (hs : HasBWType C.data Y s) :
    IsBWEquivalent
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y))
      (realRep (r + s)) := by
  have ht := (HasBWType.end_isBWEquivalent_realRep C hr).gtensor_congr
    (HasBWType.end_isBWEquivalent_realRep C hs)
  exact (IsBWEquivalent.of_superAlgEquiv (tensorEndSuperEquiv C X Y hY).symm).trans
    (ht.trans (IsBWEquivalent.of_matrixSuper (realGauge.size_pos r s) (realFuse r s)))

theorem simple_tensor_inComponent (C : PiSuperfusion.{0, 0})
    (X Y : C.data.Obj) (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y) {r s : ZMod 8}
    (hr : HasBWType C.data.toWeaklyPointedSuperfusionData X r)
    (hs : HasBWType C.data.toWeaklyPointedSuperfusionData Y s) :
    InComponent C.data.toWeaklyPointedSuperfusionData (r + s) (C.data.tensorObj X Y) := by
  let D := C.toWeaklyPointedSuperfusion
  obtain ⟨n, S, hS, hd⟩ := C.laws.semisimple (C.data.tensorObj X Y)
  have hn : 0 < n := by
    by_contra h
    have he : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    obtain ⟨_, _, _, _, _, _, ht⟩ := hd
    exact tensor_id_ne_zero (C := D) (simple_id_ne_zero D.laws hX)
      (simple_id_ne_zero D.laws hY) ht.symm
  let k : Fin n := ⟨0, hn⟩
  obtain ⟨t, ht, _⟩ := simple_has_unique_type C (S k) (hS k)
  have ho (i : Fin n) : SameParityOrbit D.data (S k) (S i) :=
    simple_tensor_isotypic D X Y hX hY hd hS k i
  obtain ⟨d, hdl⟩ := exists_homogeneousSum D.laws ho hd
  let b : HomogeneousSum D.data (S k) (D.data.tensorObj X Y) n := ⟨d, hdl⟩
  have hprod := tensorEnd_isBWEquivalent_realRep D X Y hY hr hs
  have hconst := (b.isBWEquivalent (C := D) hn).trans
    (HasBWType.end_isBWEquivalent_realRep D ht)
  have heq : r + s = t := realRep_label_eq_of_isBWEquivalent (hprod.symm.trans hconst)
  refine ⟨n, S, ?_, hd⟩
  intro i
  refine ⟨hS i, ?_⟩
  rw [heq]
  exact (SameParityOrbit.hasBWType_iff D.laws (ho i) t).mp ht

theorem InComponent.tensor {C : PiSuperfusionData.{0, 0}} (hC : ReferenceProperty C)
    {X Y : C.Obj} {r s : ZMod 8}
    (hX : InComponent C.toWeaklyPointedSuperfusionData r X)
    (hY : InComponent C.toWeaklyPointedSuperfusionData s Y) :
    InComponent C.toWeaklyPointedSuperfusionData (r + s) (C.tensorObj X Y) := by
  let D : PiSuperfusion := ⟨C, hC.toPiSuperfusionLaws⟩
  obtain ⟨n, S, hS, hdS⟩ := hX
  obtain ⟨m, T, hT, hdT⟩ := hY
  apply InComponent.of_decomposition hC (S := fun i => C.tensorObj (S i) Y)
  · intro i
    apply InComponent.of_decomposition hC (S := fun j => C.tensorObj (S i) (T j))
    · intro j
      exact simple_tensor_inComponent D (S i) (T j) (hS i).1 (hT j).1 (hS i).2 (hT j).2
    · exact (tensorLeftSuperfunctor D.toWeaklyPointedSuperfusion (S i)).map_decomposition hdT
  · exact (tensorRightSuperfunctor D.toWeaklyPointedSuperfusion Y).map_decomposition hdS

end RMod.Classification
