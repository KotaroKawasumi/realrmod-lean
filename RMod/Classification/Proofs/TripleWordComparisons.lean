import RMod.Classification.Proofs.MonoidalWordComparisons

/-!
# Pair replacements have a unique three-factor comparison

Collapse the target triple to its monoid product. Both left and right
pair replacement then become the original collapse followed by the
canonical equality map. As collapse is invertible, the replacement is
the explicit triple comparison, and consecutive comparisons compose.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.MonoidalWord

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable {G : Type u} [Monoid G] {D : Type v} [Category.{w} D] [MonoidalCategory D]
  (F : Discrete G ⥤ D) [F.Monoidal]

theorem collapse_inv_assoc (a b c : G) :
    (α_ (F.obj (Discrete.mk a)) (F.obj (Discrete.mk b)) (F.obj (Discrete.mk c))).inv ≫
        (collapseLeft F a b c).hom =
      (collapseRight F a b c).hom ≫ F.map (Discrete.eqToHom (mul_assoc a b c).symm) := by
  have he := Functor.LaxMonoidal.associativity_inv F (Discrete.mk a) (Discrete.mk b) (Discrete.mk c)
  have hα : (α_ (Discrete.mk a) (Discrete.mk b) (Discrete.mk c)).inv =
      Discrete.eqToHom (mul_assoc a b c).symm := Subsingleton.elim _ _
  rw [hα] at he
  simp only [collapseLeft, collapseRight, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    μIso_hom, tensorHom_id, id_tensorHom, Category.assoc]
  exact he.symm

theorem tripleCompare_collapse (a b c d e f : G) (he : (a * b) * c = (d * e) * f) :
    (tripleCompare F a b c d e f he).hom ≫ (collapseLeft F d e f).hom =
      (collapseLeft F a b c).hom ≫ F.map (Discrete.eqToHom he) := by
  simp only [tripleCompare, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 2

theorem replaceRight_collapse (a b c d e : G) (he : b * c = d * e) :
    (replaceRight F a b c d e he).hom ≫ (collapseLeft F a d e).hom =
      (collapseLeft F a b c).hom ≫ F.map (Discrete.eqToHom
        ((mul_assoc a b c).trans ((congrArg (fun x => a * x) he).trans (mul_assoc a d e).symm))) := by
  simp only [replaceRight, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
    Iso.symm_hom, Category.assoc]
  rw [collapse_inv_assoc, ← Category.assoc (F.obj (Discrete.mk a) ◁ (pairCompare F b c d e he).hom),
    pairCompare_right_collapse, Category.assoc,
    ← Category.assoc _ (collapseRight F a b c).hom, ← collapse_assoc]
  simp only [Category.assoc, ← F.map_comp]
  congr 2
  exact Subsingleton.elim _ _

theorem replaceLeft_eq_tripleCompare (a b c d e : G) (he : a * b = c * d) :
    replaceLeft F a b c d e he =
      tripleCompare F a b e c d e (congrArg (fun x => x * e) he) := by
  apply Iso.ext
  apply (cancel_mono (collapseLeft F c d e).hom).mp
  rw [tripleCompare_collapse]
  simpa only [replaceLeft, tensorIso_hom, Iso.refl_hom, tensorHom_id] using
    pairCompare_left_collapse F a b c d e he

theorem replaceRight_eq_tripleCompare (a b c d e : G) (he : b * c = d * e) :
    replaceRight F a b c d e he =
      tripleCompare F a b c a d e
        ((mul_assoc a b c).trans ((congrArg (fun x => a * x) he).trans (mul_assoc a d e).symm)) := by
  apply Iso.ext
  apply (cancel_mono (collapseLeft F a d e).hom).mp
  rw [tripleCompare_collapse]
  exact replaceRight_collapse F a b c d e he

theorem tripleCompare_trans (a b c d e f g h i : G)
    (he : (a * b) * c = (d * e) * f) (hf : (d * e) * f = (g * h) * i) :
    tripleCompare F a b c d e f he ≪≫ tripleCompare F d e f g h i hf =
      tripleCompare F a b c g h i (he.trans hf) := by
  apply Iso.ext
  apply (cancel_mono (collapseLeft F g h i).hom).mp
  rw [Iso.trans_hom, Category.assoc, tripleCompare_collapse, tripleCompare_collapse,
    ← Category.assoc, tripleCompare_collapse, Category.assoc, ← F.map_comp]
  congr 2
  exact Subsingleton.elim _ _

end RMod.Classification.MonoidalWord
