import RMod.Classification.Abstract.HomogeneousIso
import RMod.Classification.Proofs.IsoCalculus

/-!
# Composition and whiskering of homogeneous isomorphisms

Composition adds degrees. Tensoring either side with an identity retains
the degree and the ordinary reverse tensor map as inverse: one crossing
factor is even, so interchange contributes no sign. These laws apply to
odd comparison maps as well as to structural even isomorphisms.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

theorem EvenIsoLaws.homogeneous {C : WeaklyPointedSuperfusionData.{u, v}}
    {X Y : C.Obj} {d : IsoData C X Y} (hd : EvenIsoLaws C d) : HomogeneousIsoLaws C 0 d :=
  ⟨hd.toIsoLaws, hd.hom_even, hd.inv_even⟩

namespace HomogeneousIsoLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

theorem symm {X Y : C.Obj} {a : ZMod 2} {d : IsoData C X Y} (hd : HomogeneousIsoLaws C a d) :
    HomogeneousIsoLaws C a (d.symm C) :=
  ⟨⟨hd.inv_hom, hd.hom_inv⟩, hd.inv_grade, hd.hom_grade⟩

include hC

theorem trans {X Y Z : C.Obj} {a b : ZMod 2} {d : IsoData C X Y} {e : IsoData C Y Z}
    (hd : HomogeneousIsoLaws C a d) (he : HomogeneousIsoLaws C b e) :
    HomogeneousIsoLaws C (a + b) (d.trans C e) where
  hom_inv := by
    change C.comp (C.comp d.hom e.hom) (C.comp e.inv d.inv) = C.id X
    rw [hC.comp_assoc, ← hC.comp_assoc e.hom e.inv d.inv, he.hom_inv, hC.id_comp, hd.hom_inv]
  inv_hom := by
    change C.comp (C.comp e.inv d.inv) (C.comp d.hom e.hom) = C.id Z
    rw [hC.comp_assoc, ← hC.comp_assoc d.inv d.hom e.hom, hd.inv_hom, hC.id_comp, he.inv_hom]
  hom_grade := hC.comp_grade _ _ hd.hom_grade he.hom_grade
  inv_grade := by
    have h := hC.comp_grade _ _ he.inv_grade hd.inv_grade
    rw [add_comm b a] at h
    exact h

theorem whiskerRight {X Y : C.Obj} {a : ZMod 2} {d : IsoData C X Y}
    (hd : HomogeneousIsoLaws C a d) (Z : C.Obj) :
    HomogeneousIsoLaws C a (d.tensor C (IsoData.refl C Z)) where
  hom_inv := by
    change C.comp (C.tensorHom d.hom (C.id Z)) (C.tensorHom d.inv (C.id Z)) = C.id (C.tensorObj X Z)
    rw [interchange_second_even hC _ _ _ _ (hC.id_even Z), hd.hom_inv, hC.id_comp, hC.tensor_id]
  inv_hom := by
    change C.comp (C.tensorHom d.inv (C.id Z)) (C.tensorHom d.hom (C.id Z)) = C.id (C.tensorObj Y Z)
    rw [interchange_second_even hC _ _ _ _ (hC.id_even Z), hd.inv_hom, hC.id_comp, hC.tensor_id]
  hom_grade := by
    have h := hC.tensor_grade _ _ hd.hom_grade (hC.id_even Z)
    rw [add_zero] at h
    exact h
  inv_grade := by
    have h := hC.tensor_grade _ _ hd.inv_grade (hC.id_even Z)
    rw [add_zero] at h
    exact h

theorem whiskerLeft {X Y : C.Obj} {a : ZMod 2} {d : IsoData C X Y}
    (hd : HomogeneousIsoLaws C a d) (Z : C.Obj) :
    HomogeneousIsoLaws C a ((IsoData.refl C Z).tensor C d) where
  hom_inv := by
    change C.comp (C.tensorHom (C.id Z) d.hom) (C.tensorHom (C.id Z) d.inv) = C.id (C.tensorObj Z X)
    rw [interchange_first_even hC _ _ _ _ (hC.id_even Z), hC.id_comp, hd.hom_inv, hC.tensor_id]
  inv_hom := by
    change C.comp (C.tensorHom (C.id Z) d.inv) (C.tensorHom (C.id Z) d.hom) = C.id (C.tensorObj Z Y)
    rw [interchange_first_even hC _ _ _ _ (hC.id_even Z), hC.id_comp, hd.inv_hom, hC.tensor_id]
  hom_grade := by
    have h := hC.tensor_grade _ _ (hC.id_even Z) hd.hom_grade
    rw [zero_add] at h
    exact h
  inv_grade := by
    have h := hC.tensor_grade _ _ (hC.id_even Z) hd.inv_grade
    rw [zero_add] at h
    exact h

end HomogeneousIsoLaws
end RMod.Classification
