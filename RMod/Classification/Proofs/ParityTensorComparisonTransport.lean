import RMod.Classification.Instances.ParityTensorComparison

/-!
# Changing the presentation of the same binary comparison degree

Equality of the parity indices transports the source's right factor.
When the specified comparison data agree, the actual even tensorator
agrees after precisely this equality map. This applies to the extracted
degree whose unit values were proved, rather than defined, to be zero.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  (p : Pi C.data) {a b : ZMod 2}
  (η : TensorComparison S T U V E H N a) (θ : TensorComparison S T U V E H N b)

theorem parityTensorComparison_hom_of_data_eq (e : a = b) (he : η.data = θ.data)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object) :
    C.data.comp (IsoData.ofEq C.data
      (congrArg (fun q => C.data.tensorObj
        (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj) (p.data.factor q)) e)).inv
      ((parityTensorComparison p η).data.app X Y).hom =
      ((parityTensorComparison p θ).data.app X Y).hom := by
  cases e
  have hm := congrArg (fun d : TensorComparisonData S T U V E.data H.data N.data => (d.app X Y).inv) he
  change C.data.comp (C.data.id _)
    (C.data.comp (p.data.rightFactorDeletion _ a).hom (η.data.app X Y).inv) =
      C.data.comp (p.data.rightFactorDeletion _ a).hom (θ.data.app X Y).inv
  rw [C.laws.id_comp, hm]

/-- Parity-index transport also commutes with any map inserted before the tensorator. -/
theorem parityTensorComparison_inserted_of_data_eq (e : a = b) (he : η.data = θ.data)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    {W : C.data.Obj} (f : C.data.Hom W (C.data.tensorObj (E.data.obj X).obj (H.data.obj Y).obj)) :
    C.data.comp (IsoData.ofEq C.data
      (congrArg (fun q => C.data.tensorObj W (p.data.factor q)) e)).inv
      (C.data.comp (C.data.tensorHom f (C.data.id (p.data.factor a)))
        ((parityTensorComparison p η).data.app X Y).hom) =
      C.data.comp (C.data.tensorHom f (C.data.id (p.data.factor b)))
        ((parityTensorComparison p θ).data.app X Y).hom := by
  cases e
  have hm := parityTensorComparison_hom_of_data_eq p η θ rfl he X Y
  change C.data.comp (C.data.id _) _ = _ at hm ⊢
  rw [C.laws.id_comp] at hm ⊢
  exact congrArg (C.data.comp (C.data.tensorHom f (C.data.id (p.data.factor a)))) hm

end RMod.Classification
