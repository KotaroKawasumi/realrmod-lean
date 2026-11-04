import RMod.Classification.Instances.LinearCategory
import RMod.Classification.Abstract.Normalizers

/-! # Ordinary equality maps and the retained raw isomorphism data -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem linear_eqToHom_eq_ofEq {X Y : LinearCategory C} (e : X = Y) :
    eqToHom e = (IsoData.ofEq C.data e).hom := by
  subst Y
  rfl

theorem isoData_ofEq_hom_comp {X Y Z : C.data.Obj} (e : X = Y) (f : Y = Z) :
    C.data.comp (IsoData.ofEq C.data e).hom (IsoData.ofEq C.data f).hom =
      (IsoData.ofEq C.data (e.trans f)).hom := by
  subst Y
  subst Z
  exact C.laws.id_comp _

theorem isoData_ofEq_hom_comp_assoc {X Y Z W : C.data.Obj} (e : X = Y) (f : Y = Z)
    (q : C.data.Hom Z W) :
    C.data.comp (IsoData.ofEq C.data e).hom (C.data.comp (IsoData.ofEq C.data f).hom q) =
      C.data.comp (IsoData.ofEq C.data (e.trans f)).hom q := by
  rw [← C.laws.comp_assoc, isoData_ofEq_hom_comp]

/-- Compose adjacent equality comparisons inside a diagram with fixed input and output maps. -/
theorem isoData_ofEq_two_comparisons {R S T U V W : C.data.Obj}
    (a : C.data.Hom R S) (b : C.data.Hom S T) (e : T = U) (f : U = V) (q : C.data.Hom V W) :
    C.data.comp a (C.data.comp (C.data.comp b (IsoData.ofEq C.data e).hom)
      (C.data.comp (IsoData.ofEq C.data f).hom q)) =
      C.data.comp (C.data.comp a b) (C.data.comp (IsoData.ofEq C.data (e.trans f)).hom q) := by
  simp only [C.laws.comp_assoc, isoData_ofEq_hom_comp_assoc]

end RMod.Classification
