import RMod.Classification.Abstract.SpanIntertwinerIso
import RMod.Classification.Proofs.SpanSimpleImages
import RMod.Classification.Proofs.SpanSuperequivalence
import RMod.Classification.Proofs.EndIntertwiners

/-!
# Existence of invertible comparisons at the generator

Two equivalences into the span of a simple target generator send the
source generator to simple objects in one parity orbit. Their actual
endomorphism algebra maps are compared by the signed Skolem--Noether
construction. The resulting maps and inverse identities are retained
as an invertible generator intertwiner.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem exists_spanIntertwinerIso {C D : WeaklyPointedSuperfusion.{0, 0}}
    {S : C.data.Obj} {T : D.data.Obj} (hS : C.data.IsSimple S) (hT : D.data.IsSimple T)
    (E H : SpanSuperequivalence C D S T) :
    ∃ a : ZMod 2, Nonempty (SpanIntertwinerIso E.forwardFunctor H.forwardFunctor a) := by
  let Z := spanGenerator C S
  let F := E.forwardFunctor
  let G := H.forwardFunctor
  have hX := F.map_simple E.fullyFaithful E.map_grade_iff Z hS
  have hY := G.map_simple H.fullyFaithful H.map_grade_iff Z hS
  have hXT := sameParityOrbit_of_simple_in_span D T (F.data.obj Z) hT hX
  have hYT := sameParityOrbit_of_simple_in_span D T (G.data.obj Z) hT hY
  obtain ⟨a, e, he, hn⟩ := exists_homogeneous_end_intertwiner C D S
    (F.data.obj Z).obj (G.data.obj Z).obj hS hY
    (F.endAlgEquiv E.fullyFaithful Z) (G.endAlgEquiv H.fullyFaithful Z)
    (fun hf => F.laws.map_grade (ObjectProperty.homMk _ : Z ⟶ Z) hf)
    (fun hf => G.laws.map_grade (ObjectProperty.homMk _ : Z ⟶ Z) hf)
    (SameParityOrbit.trans D.laws hXT hYT.symm)
  refine ⟨a, ⟨⟨⟨⟨ObjectProperty.homMk e.hom⟩, ObjectProperty.homMk e.inv⟩, ?_⟩⟩⟩
  refine { grade := he, intertwines := ?_, hom_inv := ?_, inv_hom := ?_ }
  · intro b f hf
    exact ObjectProperty.hom_ext _ (hn f.hom hf)
  · exact ObjectProperty.hom_ext _ e.hom_inv_id
  · exact ObjectProperty.hom_ext _ e.inv_hom_id

end RMod.Classification
