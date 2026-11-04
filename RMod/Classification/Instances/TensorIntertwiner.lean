import RMod.Classification.Abstract.TensorIntertwiner
import RMod.Classification.Abstract.SpanNaturalIso

/-!
# Evaluating a natural comparison at a tensor generator

Compose its specified homogeneous component with an even comparison of
the two tensor actions. Signed naturality supplies precisely the sign
of the total degree of a tensor of two homogeneous endomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (S T : SimpleObject C) (U V : SimpleObject D)

def tensorIntertwinerComparisonData
    {E : SpanSuperfunctorData C D S.data.object U.data.object}
    {H : SpanSuperfunctorData C D T.data.object V.data.object}
    {N M : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object}
    (η : SpanHomogeneousNatIsoData N M) (e : TensorIntertwinerData S T U V E H M) :
    TensorIntertwinerData S T U V E H N :=
  (⟨(η.app (tensorSpanObject C S T)).hom, (η.inv.app (tensorSpanObject C S T)).hom⟩ :
    IsoData D.data _ _).trans D.data e

theorem tensorIntertwinerComparisonLaws
    {E : SpanSuperfunctor C D S.data.object U.data.object}
    {H : SpanSuperfunctor C D T.data.object V.data.object}
    {N M : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}
    (η : SpanHomogeneousNatIso N M a) (e : TensorIntertwinerData S T U V E.data H.data M.data)
    (he : EvenIsoLaws D.data e)
    (hm : ∀ (f : spanGenerator C S.data.object ⟶ spanGenerator C S.data.object)
      (g : spanGenerator C T.data.object ⟶ spanGenerator C T.data.object),
      D.data.comp (M.data.map (ObjectProperty.homMk (C.data.tensorHom f.hom g.hom) :
        tensorSpanObject C S T ⟶ tensorSpanObject C S T)).hom e.hom =
      D.data.comp e.hom (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)) :
    TensorIntertwinerLaws S T U V a (tensorIntertwinerComparisonData S T U V η.data e) where
  hom_inv := by
    let X := tensorSpanObject C S T
    have hη := congrArg (fun f : N.data.obj X ⟶ N.data.obj X => f.hom) (η.laws.hom_inv X)
    change D.data.comp (D.data.comp (η.data.app X).hom e.hom)
      (D.data.comp e.inv (η.data.inv.app X).hom) = _
    rw [D.laws.comp_assoc, ← D.laws.comp_assoc e.hom e.inv, he.hom_inv, D.laws.id_comp]
    exact hη
  inv_hom := by
    let X := tensorSpanObject C S T
    have hη := congrArg (fun f : M.data.obj X ⟶ M.data.obj X => f.hom) (η.laws.inv_hom X)
    change D.data.comp (η.data.inv.app X).hom (η.data.app X).hom =
      D.data.id (M.data.obj X).obj at hη
    change D.data.comp (D.data.comp e.inv (η.data.inv.app X).hom)
      (D.data.comp (η.data.app X).hom e.hom) = _
    rw [D.laws.comp_assoc, ← D.laws.comp_assoc (η.data.inv.app X).hom, hη,
      D.laws.id_comp, he.inv_hom]
  hom_grade := by
    have h := D.laws.comp_grade _ _ (η.laws.grade (tensorSpanObject C S T)) he.hom_even
    rw [add_zero] at h
    exact h
  inv_grade := by
    have h := D.laws.comp_grade _ _ he.inv_even (η.laws.inverse.grade (tensorSpanObject C S T))
    rw [zero_add] at h
    exact h
  intertwines {b c} f g hf hg := by
    let X := tensorSpanObject C S T
    let k : X ⟶ X := ObjectProperty.homMk (C.data.tensorHom f.hom g.hom)
    have hk : C.data.IsHomogeneous (b + c) k.hom := C.laws.tensor_grade _ _ hf hg
    have hη := congrArg (fun q : N.data.obj X ⟶ M.data.obj X => q.hom) (η.laws.naturality k hk)
    change D.data.comp (N.data.map k).hom (η.data.app X).hom =
      D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (D.data.comp (η.data.app X).hom (M.data.map k).hom) at hη
    change D.data.comp (N.data.map k).hom (D.data.comp (η.data.app X).hom e.hom) =
      D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (D.data.comp (D.data.comp (η.data.app X).hom e.hom)
          (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom))
    rw [← D.laws.comp_assoc, hη, D.laws.smul_comp, D.laws.comp_assoc]
    rw [hm f g, D.laws.comp_assoc]

end RMod.Classification
