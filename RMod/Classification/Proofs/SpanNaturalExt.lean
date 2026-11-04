import RMod.Classification.Abstract.SpanNatural
import RMod.Classification.Proofs.SpanGeneratorExt

/-!
# Homogeneous natural comparisons are determined at the generator

Signed naturality identifies the composites with every mapped generator
inclusion. Their total matrix identity then determines each component.
This argument uses odd inclusions as well as even ones.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNat

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

theorem app_eq_of_generator (η θ : SpanHomogeneousNat F G a)
    (h : η.data.app (spanGenerator C S) = θ.data.app (spanGenerator C S))
    (X : HomogeneousSpanCategory C S) : η.data.app X = θ.data.app X := by
  apply F.hom_ext_generator
  intro i
  let k : spanGenerator C S ⟶ X := ObjectProperty.homMk ((spanPresentation X).data.inclusion i)
  have hη := η.laws.naturality k ((spanPresentation X).laws.inclusion_grade i)
  have hθ := θ.laws.naturality k ((spanPresentation X).laws.inclusion_grade i)
  exact hη.trans ((congrArg (fun z => ((-1 : ℝ) ^ (a * (spanPresentation X).data.parity i).val) •
    (z ≫ G.data.map k)) h).trans hθ.symm)

theorem ext_generator (η θ : SpanHomogeneousNat F G a)
    (h : η.data.app (spanGenerator C S) = θ.data.app (spanGenerator C S)) : η = θ := by
  have hh := funext (app_eq_of_generator η θ h)
  cases η with
  | mk d hd =>
    cases θ with
    | mk e he =>
      cases d with
      | mk d =>
        cases e with
        | mk e =>
          change d = e at hh
          subst e
          rfl

end RMod.Classification.SpanHomogeneousNat
