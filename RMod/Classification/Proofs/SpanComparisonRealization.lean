import RMod.Classification.Proofs.SpanComparisonObject
import RMod.Classification.Proofs.RetractSumTransportAction
import RMod.Classification.Proofs.SimpleRetractTransport
import RMod.Classification.Proofs.SimpleCornerEquivalence
import RMod.Classification.Instances.SpanComparisonEquivalence
import RMod.Classification.Instances.SpanSuperequivalence

/-!
# Realizing a prescribed ambient algebra equivalence by a component functor

Transport a simple retract, compare its corner algebra, and use the
canonical matrix functor on its homogeneous span. The transported sum
presentation gives an even isomorphism from the functor's value at the
ambient source object to the prescribed target object. Its intertwining
equation reproduces the originally supplied endomorphism algebra map.
This includes nonsimple ambient generators, such as tensor products.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem exists_spanComparison_realizing_algebra (C D : PiSuperfusion.{0, 0})
    (X : LinearCategory C.toWeaklyPointedSuperfusion) (Y : LinearCategory D.toWeaklyPointedSuperfusion)
    (d : SimpleRetract C.toWeaklyPointedSuperfusion X)
    (hX : InHomogeneousSpan C.toWeaklyPointedSuperfusion d.data.object X)
    (φ : End X ≃ₐ[ℝ] End Y)
    (hφ : ∀ {a : ZMod 2} (f : End X), D.data.IsHomogeneous a (φ f) ↔ C.data.IsHomogeneous a f) :
    ∃ (T : SimpleObject D.toWeaklyPointedSuperfusion)
      (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
        d.data.object T.data.object)
      (e : IsoData D.data.toWeaklyPointedSuperfusionData
        (E.forwardFunctor.data.obj ⟨X, hX⟩).obj Y),
      EvenIsoLaws D.data.toWeaklyPointedSuperfusionData e ∧
      ∀ f : End X,
        D.data.comp (E.forwardFunctor.data.map
          (ObjectProperty.homMk f : (⟨X, hX⟩ : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion d.data.object) ⟶
            ⟨X, hX⟩)).hom e.hom = D.data.comp e.hom (φ f) := by
  obtain ⟨t, hproj⟩ := exists_simpleRetract_transport C.toWeaklyPointedSuperfusion
    D.toWeaklyPointedSuperfusion X Y d φ hφ
  let a := simpleCornerEquivalence d t φ hproj
  have ha : ∀ b f, D.data.IsHomogeneous b (a f) ↔ C.data.IsHomogeneous b f :=
    fun _ f => simpleCornerEquivalence_grade_iff d t φ hproj hφ f
  let X' : HomogeneousSpanCategory C.toWeaklyPointedSuperfusion d.data.object := ⟨X, hX⟩
  let A := spanPresentation X'
  let B := retractSumTransport d t φ A hproj (fun hf => (hφ _).mpr hf)
  let E := spanComparisonSuperequivalence C D d.data.object t.data.object a ha
  let e := spanComparisonObjectIsoData D t.data.object a X' B
  refine ⟨⟨t.data.toSimpleObjectData, t.laws.toSimpleObjectLaws⟩, E, e, ?_, ?_⟩
  · exact spanComparisonObjectIsoLaws D t.data.object a X' B (fun b f hf => (ha b f).mpr hf) rfl
  · intro f
    have h := spanComparisonObject_intertwines D t.data.object a X' B
      (fun b f hf => (ha b f).mpr hf) f
    exact h.trans (congrArg (fun k => D.data.comp e.hom k)
      (retractSumTransport_action d t φ A hproj (fun hf => (hφ _).mpr hf) f))

end RMod.Classification
