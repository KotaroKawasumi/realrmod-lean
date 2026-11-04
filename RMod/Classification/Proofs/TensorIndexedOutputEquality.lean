import RMod.Classification.Proofs.TensorEqualityMaps
import RMod.Classification.Instances.TensorFunctors

/-!
# Transporting an output comparison together with its parity factor

The underlying output and the right factor both depend on the index.
Equality elimination keeps these two transports synchronized. This
permits a homogeneous output comparison to be tensored with the correct
factor before and after the output index changes.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem tensor_indexed_output_comparison {I : Type w} (O P : I → C.Obj) {i j : I} (e : i = j)
    {A B : C.Obj} (f : C.Hom A (O i)) (g : C.Hom B (O j)) (b : C.Hom A B)
    (h : C.comp f (IsoData.ofEq C (congrArg O e)).hom = C.comp b g) :
    C.comp (C.tensorHom f (C.id (P i)))
      (IsoData.ofEq C (congrArg (fun k => C.tensorObj (O k) (P k)) e)).hom =
      C.comp (C.comp (C.tensorHom b (C.id (P i)))
        (IsoData.ofEq C (congrArg (fun k => C.tensorObj B (P k)) e)).hom)
        (C.tensorHom g (C.id (P j))) := by
  cases e
  change C.comp f (C.id _) = C.comp b g at h
  rw [hC.comp_id] at h
  change C.comp (C.tensorHom f (C.id (P i))) (C.id _) =
    C.comp (C.comp (C.tensorHom b (C.id (P i))) (C.id _)) (C.tensorHom g (C.id (P i)))
  rw [hC.comp_id, hC.comp_id, h]
  exact (tensorRightLaws ⟨C, hC⟩ (P i)).map_comp b g

end RMod.Classification
