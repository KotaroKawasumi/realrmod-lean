import RMod.Classification.Instances.SpanNaturalExtension

/-!
# Extension and evaluation are inverse

The generator-map equation applied to its identity recovers the supplied
intertwiner. Conversely, generator evaluation determines every natural
transformation, so extending its value recovers the original comparison.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

theorem spanNaturalExtension_at_generator (t : SpanIntertwiner F G a) :
    (spanNaturalExtension t).data.app (spanGenerator C S) = t.data.hom := by
  let u : F.toFunctor.obj (spanGenerator C S) ⟶ G.toFunctor.obj (spanGenerator C S) := t.data.hom
  let v : F.toFunctor.obj (spanGenerator C S) ⟶ G.toFunctor.obj (spanGenerator C S) :=
    (spanNaturalExtension t).data.app (spanGenerator C S)
  have hh : F.toFunctor.map (𝟙 (spanGenerator C S)) ≫ v =
      ((-1 : ℝ) ^ (a * 0).val) • (u ≫ G.toFunctor.map (𝟙 (spanGenerator C S))) :=
    spanNaturalExtension_on_generator_hom t (𝟙 (spanGenerator C S)) (C.laws.id_even S)
  rw [F.toFunctor.map_id, G.toFunctor.map_id, mul_zero, ZMod.val_zero, pow_zero,
    Category.id_comp, Category.comp_id, one_smul] at hh
  exact hh

theorem SpanIntertwiner.ext_hom (s t : SpanIntertwiner F G a) (hh : s.data.hom = t.data.hom) : s = t := by
  cases s with
  | mk d hd =>
    cases t with
    | mk e he =>
      cases d with
      | mk f =>
        cases e with
        | mk g =>
          change f = g at hh
          subst g
          rfl

theorem spanNaturalExtension_toIntertwiner (t : SpanIntertwiner F G a) :
    (spanNaturalExtension t).toIntertwiner = t :=
  SpanIntertwiner.ext_hom _ _ (spanNaturalExtension_at_generator t)

theorem spanNaturalExtension_of_natural (η : SpanHomogeneousNat F G a) :
    spanNaturalExtension η.toIntertwiner = η :=
  SpanHomogeneousNat.ext_generator _ _ (spanNaturalExtension_at_generator η.toIntertwiner)

end RMod.Classification
