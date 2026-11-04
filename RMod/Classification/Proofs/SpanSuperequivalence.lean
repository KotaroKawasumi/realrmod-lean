import RMod.Classification.Instances.SpanSuperequivalence

/-!
# Reflection of parity under component equivalences

The inverse functor preserves parity. Composing with the even unit on
both sides recovers the original map, so the forward functor also
reflects each homogeneous subspace. Full faithfulness uses the specified
inverse and the specified unit and counit of the equivalence.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperequivalence

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  (E : SpanSuperequivalence C D S T)

def fullyFaithful : E.forwardFunctor.toFunctor.FullyFaithful := E.data.fullyFaithfulFunctor

theorem map_grade_iff {X Y : HomogeneousSpanCategory C S} {a : ZMod 2} (f : X ⟶ Y) :
    D.data.IsHomogeneous a (E.forwardFunctor.toFunctor.map f).hom ↔
      C.data.IsHomogeneous a f.hom := by
  refine ⟨fun hf => ?_, E.laws.forward.map_grade f⟩
  have hb := E.laws.backward.map_grade _ hf
  have h := C.laws.comp_grade _ _
    (C.laws.comp_grade _ _ (E.laws.unit_hom_even X) hb) (E.laws.unit_inv_even Y)
  rw [zero_add, add_zero] at h
  have hn := congrArg (fun k : X ⟶ (E.data.functor ⋙ E.data.inverse).obj Y => k.hom)
    (E.data.unitIso.hom.naturality f)
  change C.data.comp f.hom (E.data.unitIso.hom.app Y).hom =
    C.data.comp (E.data.unitIso.hom.app X).hom
      (E.data.inverse.map (E.data.functor.map f)).hom at hn
  have hi : C.data.comp (E.data.unitIso.hom.app Y).hom (E.data.unitIso.inv.app Y).hom =
      C.data.id Y.obj := congrArg (fun k : Y ⟶ Y => k.hom) (E.data.unitIso.hom_inv_id_app Y)
  change C.data.IsHomogeneous a (C.data.comp
    (C.data.comp (E.data.unitIso.hom.app X).hom
      (E.data.inverse.map (E.data.functor.map f)).hom) (E.data.unitIso.inv.app Y).hom) at h
  have he := (congrArg (fun k : C.data.Hom X.obj (E.data.inverse.obj (E.data.functor.obj Y)).obj =>
    C.data.comp k (E.data.unitIso.inv.app Y).hom) hn.symm).trans
      ((C.laws.comp_assoc f.hom (E.data.unitIso.hom.app Y).hom (E.data.unitIso.inv.app Y).hom).trans
        ((congrArg (fun k : C.data.Hom Y.obj Y.obj => C.data.comp f.hom k) hi).trans
          (C.laws.comp_id f.hom)))
  exact (congrArg (fun k : C.data.Hom X.obj Y.obj => C.data.IsHomogeneous a k) he).mp h

end RMod.Classification.SpanSuperequivalence
