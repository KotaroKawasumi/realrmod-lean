import RMod.Hierarchy.Bridge.OldEquivalenceData
import RMod.Hierarchy.Bridge.TensorComponents

/-!
# Total naturality of transported equivalences

The total Hom equivalence turns the unit and counit equations back into
the original equations. Tensor naturality is checked on the four parity
summands, including the corrected sign of the odd-odd summand.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem totalHomEquiv_ofOldEvenIso (C : WeaklyPointedSuperfusion.{0, 0}) {X Y : C.data.Obj}
    (f : C.data.Hom X Y) (g : C.data.Hom Y X)
    (hf : C.data.IsHomogeneous 0 f) (hg : C.data.IsHomogeneous 0 g)
    (hfg : C.data.comp f g = C.data.id X) (hgf : C.data.comp g f = C.data.id Y) :
    totalHomEquiv C X Y (evenPoint (ofOldEvenIso C f g hf hg hfg hgf).hom) = f := by
  rw [totalHomEquiv_even]
  exact ofOldEvenIso_hom C f g hf hg hfg hgf

theorem ofOldSuperfunctor_component {C D : WeaklyPointedSuperfusion.{0, 0}}
    (F : Classification.Superfunctor C D) {X Y : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X Y) (a : ZMod 2) :
    (tMap (ofOldSuperfunctorData F) f a).val = F.data.map (f a).val := rfl

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (E : Classification.MonoidalSuperequivalence C D)

theorem ofOldEquivalence_unit_natural {X Y : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X Y) :
    tComp (ofOldSupercategoryData C) f (evenPoint ((ofOldMonoidalSuperequivalenceData E).unit Y).hom) =
      tComp (ofOldSupercategoryData C) (evenPoint ((ofOldMonoidalSuperequivalenceData E).unit X).hom)
        (tMap (ofOldMonoidalSuperequivalenceData E).backward
          (tMap (ofOldMonoidalSuperequivalenceData E).forward f)) := by
  apply (totalHomEquiv C X (E.data.backward.obj (E.data.forward.obj Y))).injective
  simp only [ofOldMonoidalSuperequivalenceData, totalHomEquiv_comp,
    totalHomEquiv_ofOldEvenIso]
  erw [totalHomEquiv_map (ofOldEquivalenceBackward E) (tMap (ofOldSuperfunctorData (ofOldEquivalenceForward E)) f),
    totalHomEquiv_map (ofOldEquivalenceForward E) f]
  exact E.laws.unit_naturality (totalHomEquiv C X Y f)

theorem ofOldEquivalence_counit_natural {X Y : D.data.Obj}
    (f : THom (ofOldSupercategoryData D) X Y) :
    tComp (ofOldSupercategoryData D)
      (tMap (ofOldMonoidalSuperequivalenceData E).forward
        (tMap (ofOldMonoidalSuperequivalenceData E).backward f))
      (evenPoint ((ofOldMonoidalSuperequivalenceData E).counit Y).hom) =
    tComp (ofOldSupercategoryData D) (evenPoint ((ofOldMonoidalSuperequivalenceData E).counit X).hom) f := by
  apply (totalHomEquiv D (E.data.forward.obj (E.data.backward.obj X)) Y).injective
  simp only [ofOldMonoidalSuperequivalenceData, totalHomEquiv_comp,
    totalHomEquiv_ofOldEvenIso]
  erw [totalHomEquiv_map (ofOldEquivalenceForward E) (tMap (ofOldSuperfunctorData (ofOldEquivalenceBackward E)) f),
    totalHomEquiv_map (ofOldEquivalenceBackward E) f]
  exact E.laws.counit_naturality (totalHomEquiv D X Y f)

theorem ofOldEquivalence_tensor_natural {X X' Y Y' : C.data.Obj}
    (f : THom (ofOldSupercategoryData C) X X') (g : THom (ofOldSupercategoryData C) Y Y') :
    tComp (ofOldSupercategoryData D)
      (tTensor (ofOldMonoidalStructureData D)
        (tMap (ofOldMonoidalSuperequivalenceData E).forward f)
        (tMap (ofOldMonoidalSuperequivalenceData E).forward g))
      (evenPoint ((ofOldMonoidalSuperequivalenceData E).tensorIso X' Y').hom) =
    tComp (ofOldSupercategoryData D)
      (evenPoint ((ofOldMonoidalSuperequivalenceData E).tensorIso X Y).hom)
      (tMap (ofOldMonoidalSuperequivalenceData E).forward
        (tTensor (ofOldMonoidalStructureData C) f g)) := by
  apply (totalHomEquiv D (D.data.tensorObj (E.data.forward.obj X) (E.data.forward.obj Y))
    (E.data.forward.obj (C.data.tensorObj X' Y'))).injective
  simp only [ofOldMonoidalSuperequivalenceData, totalHomEquiv_comp,
    totalHomEquiv_ofOldEvenIso]
  erw [totalHomEquiv_tTensor D (tMap (ofOldSuperfunctorData (ofOldEquivalenceForward E)) f)
      (tMap (ofOldSuperfunctorData (ofOldEquivalenceForward E)) g),
    totalHomEquiv_map (ofOldEquivalenceForward E) (tTensor (ofOldMonoidalStructureData C) f g),
    totalHomEquiv_tTensor C f g]
  simp only [ofOldSuperfunctor_component]
  change D.data.comp
    (D.data.add
      (D.data.add (D.data.tensorHom (E.data.forward.map (f 0).val) (E.data.forward.map (g 0).val))
        (D.data.smul (-1) (D.data.tensorHom (E.data.forward.map (f 1).val) (E.data.forward.map (g 1).val))))
      (D.data.add (D.data.tensorHom (E.data.forward.map (f 0).val) (E.data.forward.map (g 1).val))
        (D.data.tensorHom (E.data.forward.map (f 1).val) (E.data.forward.map (g 0).val))))
    (E.data.forward.tensorHom X' Y') =
    D.data.comp (E.data.forward.tensorHom X Y)
      (E.data.forward.map
        (C.data.add (C.data.add (C.data.tensorHom (f 0).val (g 0).val)
          (C.data.smul (-1) (C.data.tensorHom (f 1).val (g 1).val)))
          (C.data.add (C.data.tensorHom (f 0).val (g 1).val) (C.data.tensorHom (f 1).val (g 0).val))))
  simp only [D.laws.add_comp, D.laws.smul_comp, E.laws.forward.map_add,
    E.laws.forward.map_smul, D.laws.comp_add, D.laws.comp_smul, E.laws.forward.tensor_naturality]

end RMod.Legacy.Hierarchy
