import RMod.Classification.Instances.MonoidalWordComparisons

/-!
# Coherence of pair replacement inside three-factor words

The inverse tensorator cancels the next multiplication. Naturality then
slides the equality comparison past the outer multiplication. Mathlib's
monoidal associativity identifies the two three-factor collapse maps.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.MonoidalWord

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable {G : Type u} [Monoid G] {D : Type v} [Category.{w} D] [MonoidalCategory D]
  (F : Discrete G ⥤ D) [F.Monoidal]

theorem collapse_assoc (a b c : G) :
    (collapseLeft F a b c).hom ≫ F.map (Discrete.eqToHom (mul_assoc a b c)) =
      (α_ (F.obj (Discrete.mk a)) (F.obj (Discrete.mk b)) (F.obj (Discrete.mk c))).hom ≫
        (collapseRight F a b c).hom := by
  have he := Functor.LaxMonoidal.associativity F (Discrete.mk a) (Discrete.mk b) (Discrete.mk c)
  have hα : (α_ (Discrete.mk a) (Discrete.mk b) (Discrete.mk c)).hom =
      Discrete.eqToHom (mul_assoc a b c) := Subsingleton.elim _ _
  rw [hα] at he
  simp only [collapseLeft, collapseRight, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    μIso_hom, tensorHom_id, id_tensorHom, Category.assoc]
  exact he

theorem pairCompare_collapse (a b c d : G) (he : a * b = c * d) :
    (pairCompare F a b c d he).hom ≫ μ F (Discrete.mk c) (Discrete.mk d) =
      μ F (Discrete.mk a) (Discrete.mk b) ≫ F.map (Discrete.eqToHom he) := by
  simp only [pairCompare, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    μIso_hom, μIso_inv, Category.assoc, δ_μ]
  exact congrArg (fun k => μ F (Discrete.mk a) (Discrete.mk b) ≫ k)
    ((Category.comp_id (F.map (Discrete.eqToIso he).hom)).trans
      (congrArg F.map (Subsingleton.elim _ _)))

theorem pairCompare_left_collapse (a b c d e : G) (he : a * b = c * d) :
    ((pairCompare F a b c d he).hom ▷ F.obj (Discrete.mk e)) ≫ (collapseLeft F c d e).hom =
      (collapseLeft F a b e).hom ≫ F.map (Discrete.eqToHom (congrArg (fun x => x * e) he)) := by
  simp only [collapseLeft, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, μIso_hom,
    tensorHom_id]
  rw [← Category.assoc, ← comp_whiskerRight, pairCompare_collapse F,
    comp_whiskerRight, Category.assoc, μ_natural_left]
  rw [← Category.assoc]
  congr 2

theorem pairCompare_right_collapse (a b c d e : G) (he : b * c = d * e) :
    (F.obj (Discrete.mk a) ◁ (pairCompare F b c d e he).hom) ≫ (collapseRight F a d e).hom =
      (collapseRight F a b c).hom ≫ F.map (Discrete.eqToHom (congrArg (fun x => a * x) he)) := by
  simp only [collapseRight, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, μIso_hom,
    id_tensorHom]
  rw [← Category.assoc, ← whiskerLeft_comp, pairCompare_collapse F,
    whiskerLeft_comp, Category.assoc, μ_natural_right]
  rw [← Category.assoc]
  congr 2

end RMod.Classification.MonoidalWord
