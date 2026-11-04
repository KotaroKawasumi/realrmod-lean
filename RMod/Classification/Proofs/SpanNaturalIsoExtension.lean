import RMod.Classification.Instances.SpanNaturalIsoExtensionData
import RMod.Classification.Instances.SpanIntertwinerIso
import RMod.Classification.Instances.SpanNaturalComposition
import RMod.Classification.Instances.SpanNaturalScalars
import RMod.Classification.Proofs.SpanNaturalEvaluation

/-!
# Generator inverses extend to pointwise inverses

The two extended transformations compose to even natural endomorphisms.
Their generator values are identities, so generator evaluation forces
the composites to be identity transformations on the entire span.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

theorem spanNatural_comp_eq_id_of_generator (η : SpanHomogeneousNat F G a)
    (θ : SpanHomogeneousNat G F a)
    (h : η.data.app (spanGenerator C S) ≫ θ.data.app (spanGenerator C S) = 𝟙 _) :
    ∀ X, η.data.app X ≫ θ.data.app X = 𝟙 _ := by
  have he : η.compSameDegree θ = SpanHomogeneousNat.scalar F 1 := by
    apply SpanHomogeneousNat.ext_generator
    change η.data.app (spanGenerator C S) ≫ θ.data.app (spanGenerator C S) = 1 • 𝟙 _
    exact h.trans (one_smul ℝ _).symm
  intro X
  have hh := congrArg (fun z : SpanHomogeneousNat F F 0 => z.data.app X) he
  exact hh.trans (one_smul ℝ _)

theorem spanNaturalIsoExtensionLaws (t : SpanIntertwinerIso F G a) :
    SpanHomogeneousNatIsoLaws a (spanNaturalIsoExtensionData F.data G.data a t.data) where
  toSpanHomogeneousNatLaws := spanNaturalExtensionLaws t.toIntertwiner
  inverse := spanNaturalExtensionLaws t.inverse
  hom_inv := spanNatural_comp_eq_id_of_generator (spanNaturalExtension t.toIntertwiner)
    (spanNaturalExtension t.inverse) (by
      rw [spanNaturalExtension_at_generator, spanNaturalExtension_at_generator]
      exact t.laws.hom_inv)
  inv_hom := spanNatural_comp_eq_id_of_generator (spanNaturalExtension t.inverse)
    (spanNaturalExtension t.toIntertwiner) (by
      rw [spanNaturalExtension_at_generator, spanNaturalExtension_at_generator]
      exact t.laws.inv_hom)

end RMod.Classification
