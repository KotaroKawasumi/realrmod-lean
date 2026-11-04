import RMod.Classification.Proofs.IsoEqualityCancellation
import RMod.Classification.Proofs.IsoCalculus

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- A commuting component diagram remains a commuting diagram before the
chosen output-index transports. This isolates equality transport from
all convolution and reference-model calculations. -/
theorem coherence_of_transported_summands (C : WeaklyPointedSuperfusion.{0, 0})
    {L R D E E' U V V' : C.data.Obj}
    (i : C.data.Hom L D) (j : C.data.Hom R E')
    (l : C.data.Hom D U) (n : C.data.Hom U V) (a : C.data.Hom D E)
    (r : C.data.Hom E V) (r' : C.data.Hom E' V') (c : C.data.Hom L R)
    (pL : C.data.Hom L U) (pR : C.data.Hom R V') (eE : E = E') (eV : V = V')
    (hL : C.data.comp i l = pL) (hR : C.data.comp j r' = pR)
    (hc : C.data.comp pL (C.data.comp n (IsoData.ofEq C.data eV).hom) = C.data.comp c pR)
    (hm : C.data.comp (C.data.comp i a) (IsoData.ofEq C.data eE).hom = C.data.comp c j)
    (hi : C.data.comp r (IsoData.ofEq C.data eV).hom = C.data.comp (IsoData.ofEq C.data eE).hom r') :
    C.data.comp i (C.data.comp l n) = C.data.comp i (C.data.comp a r) := by
  apply isoData_ofEq_cancel_right C eV
  have hl : C.data.comp (C.data.comp i (C.data.comp l n)) (IsoData.ofEq C.data eV).hom =
      C.data.comp c pR := by
    calc
      _ = C.data.comp (C.data.comp i l) (C.data.comp n (IsoData.ofEq C.data eV).hom) := by
        simp only [C.laws.comp_assoc]
      _ = C.data.comp pL (C.data.comp n (IsoData.ofEq C.data eV).hom) := by rw [hL]
      _ = _ := hc
  have hr : C.data.comp (C.data.comp i (C.data.comp a r)) (IsoData.ofEq C.data eV).hom =
      C.data.comp c pR := by
    calc
      _ = C.data.comp (C.data.comp i a) (C.data.comp r (IsoData.ofEq C.data eV).hom) := by
        simp only [C.laws.comp_assoc]
      _ = C.data.comp (C.data.comp i a) (C.data.comp (IsoData.ofEq C.data eE).hom r') := by rw [hi]
      _ = C.data.comp (C.data.comp (C.data.comp i a) (IsoData.ofEq C.data eE).hom) r' :=
        (C.laws.comp_assoc _ _ _).symm
      _ = C.data.comp (C.data.comp c j) r' := by rw [hm]
      _ = _ := (C.laws.comp_assoc _ _ _).trans (congrArg (C.data.comp c) hR)
  exact hl.trans hr.symm

/-- Tensoring two even transported squares preserves their composites. -/
theorem tensor_transported_squares (C : WeaklyPointedSuperfusion.{0, 0})
    {L D E E' R L' D' F F' R' : C.data.Obj}
    (i : C.data.Hom L D) (a : C.data.Hom D E) (e : C.data.Hom E E')
    (b : C.data.Hom L R) (j : C.data.Hom R E')
    (i' : C.data.Hom L' D') (a' : C.data.Hom D' F) (e' : C.data.Hom F F')
    (b' : C.data.Hom L' R') (j' : C.data.Hom R' F')
    (ha' : C.data.IsHomogeneous 0 a') (he' : C.data.IsHomogeneous 0 e')
    (hj' : C.data.IsHomogeneous 0 j')
    (h : C.data.comp (C.data.comp i a) e = C.data.comp b j)
    (h' : C.data.comp (C.data.comp i' a') e' = C.data.comp b' j') :
    C.data.comp (C.data.comp (C.data.tensorHom i i') (C.data.tensorHom a a'))
      (C.data.tensorHom e e') = C.data.comp (C.data.tensorHom b b') (C.data.tensorHom j j') := by
  rw [interchange_second_even C.laws _ _ _ _ ha',
    interchange_second_even C.laws _ _ _ _ he', h, h',
    interchange_second_even C.laws _ _ _ _ hj']

end RMod.BrundanEllis.Stacking
