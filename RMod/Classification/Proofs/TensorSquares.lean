import RMod.Classification.Proofs.TensorCalculus

/-!
# Tensoring a commuting square with an arbitrary morphism

For a left inclusion its evenness removes the crossing sign; for a
right inclusion the corresponding target inclusion is even. The other
morphisms may be inhomogeneous. These two forms are the summand squares
used in convolution naturality.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem tensor_square_left {A A' X X' Y Y' : C.Obj}
    (i : C.Hom A X) (j : C.Hom A' X') (m : C.Hom X X') (n : C.Hom A A')
    (f : C.Hom Y Y') (hi : C.IsHomogeneous 0 i) (he : C.comp i m = C.comp n j) :
    C.comp (C.tensorHom i (C.id Y)) (C.tensorHom m f) =
      C.comp (C.tensorHom n f) (C.tensorHom j (C.id Y')) := by
  rw [interchange_first_even hC _ _ _ _ hi,
    interchange_second_even hC _ _ _ _ (hC.id_even Y'), hC.id_comp, hC.comp_id, he]

theorem tensor_square_right {A A' X X' Y Y' : C.Obj}
    (i : C.Hom A Y) (j : C.Hom A' Y') (m : C.Hom Y Y') (n : C.Hom A A')
    (f : C.Hom X X') (hj : C.IsHomogeneous 0 j) (he : C.comp i m = C.comp n j) :
    C.comp (C.tensorHom (C.id X) i) (C.tensorHom f m) =
      C.comp (C.tensorHom f n) (C.tensorHom (C.id X') j) := by
  rw [interchange_first_even hC _ _ _ _ (hC.id_even X),
    interchange_second_even hC _ _ _ _ hj, hC.id_comp, hC.comp_id, he]

end RMod.Classification
