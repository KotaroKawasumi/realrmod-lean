import RMod.Classification.Proofs.IsoCalculus

/-!
# Unit coherence of the normalized zero-parity tensorator

The canonical comparison maps the source unitor, inverts the target
unitor, and inserts the chosen unit isomorphism. Its inverse cancels
these exact maps. Naturality of the final right unitor accounts for the
explicit zero parity factor in the model tensor product.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
  {I N Y : C.Obj} (i : IsoData C C.tensorUnit I) (hi : EvenIsoLaws C i)
  (q : IsoData C N Y) (hq : IsoLaws C q)

include hC hi hq

theorem leftUnitTensorComparison_cancel :
    let c := (q.trans C ((IsoData.leftUnit C Y).symm C)).trans C
      (i.tensor C (IsoData.refl C Y))
    C.comp (C.comp (C.tensorHom i.hom (C.id Y)) c.inv) q.hom = C.leftUnitorHom Y := by
  have hv := hi.tensor hC (EvenIsoLaws.refl hC Y)
  have hv' : C.comp (C.tensorHom i.hom (C.id Y)) (C.tensorHom i.inv (C.id Y)) =
      C.id (C.tensorObj C.tensorUnit Y) := hv.hom_inv
  change C.comp (C.comp (C.tensorHom i.hom (C.id Y))
    (C.comp (C.tensorHom i.inv (C.id Y)) (C.comp (C.leftUnitorHom Y) q.inv))) q.hom = _
  rw [← hC.comp_assoc (C.tensorHom i.hom (C.id Y)) (C.tensorHom i.inv (C.id Y)),
    hv', hC.id_comp, hC.comp_assoc, hq.inv_hom, hC.comp_id]

theorem rightUnitTensorComparison_cancel :
    let c := (q.trans C ((IsoData.rightUnit C Y).symm C)).trans C
      ((IsoData.refl C Y).tensor C i)
    C.comp (C.comp (C.tensorHom (C.id Y) i.hom) c.inv) q.hom = C.rightUnitorHom Y := by
  have hv := (EvenIsoLaws.refl hC Y).tensor hC hi
  have hv' : C.comp (C.tensorHom (C.id Y) i.hom) (C.tensorHom (C.id Y) i.inv) =
      C.id (C.tensorObj Y C.tensorUnit) := hv.hom_inv
  change C.comp (C.comp (C.tensorHom (C.id Y) i.hom)
    (C.comp (C.tensorHom (C.id Y) i.inv) (C.comp (C.rightUnitorHom Y) q.inv))) q.hom = _
  rw [← hC.comp_assoc (C.tensorHom (C.id Y) i.hom) (C.tensorHom (C.id Y) i.inv),
    hv', hC.id_comp, hC.comp_assoc, hq.inv_hom, hC.comp_id]

theorem leftUnitTensorator_zero_coherence :
    let c := (q.trans C ((IsoData.leftUnit C Y).symm C)).trans C
      (i.tensor C (IsoData.refl C Y))
    C.comp (C.comp (C.tensorHom (C.tensorHom i.hom (C.id Y)) (C.id C.tensorUnit))
      (C.comp (C.rightUnitorHom (C.tensorObj I Y)) c.inv)) q.hom =
      C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit Y)) (C.leftUnitorHom Y) := by
  dsimp only
  rw [← hC.comp_assoc (C.tensorHom (C.tensorHom i.hom (C.id Y)) (C.id C.tensorUnit)),
    hC.right_unitor_naturality, hC.comp_assoc, hC.comp_assoc,
    ← hC.comp_assoc (C.tensorHom i.hom (C.id Y))]
  exact congrArg (C.comp (C.rightUnitorHom (C.tensorObj C.tensorUnit Y)))
    (leftUnitTensorComparison_cancel hC i hi q hq)

theorem rightUnitTensorator_zero_coherence :
    let c := (q.trans C ((IsoData.rightUnit C Y).symm C)).trans C
      ((IsoData.refl C Y).tensor C i)
    C.comp (C.comp (C.tensorHom (C.tensorHom (C.id Y) i.hom) (C.id C.tensorUnit))
      (C.comp (C.rightUnitorHom (C.tensorObj Y I)) c.inv)) q.hom =
      C.comp (C.rightUnitorHom (C.tensorObj Y C.tensorUnit)) (C.rightUnitorHom Y) := by
  dsimp only
  rw [← hC.comp_assoc (C.tensorHom (C.tensorHom (C.id Y) i.hom) (C.id C.tensorUnit)),
    hC.right_unitor_naturality, hC.comp_assoc, hC.comp_assoc,
    ← hC.comp_assoc (C.tensorHom (C.id Y) i.hom)]
  exact congrArg (C.comp (C.rightUnitorHom (C.tensorObj Y C.tensorUnit)))
    (rightUnitTensorComparison_cancel hC i hi q hq)

end RMod.Classification
