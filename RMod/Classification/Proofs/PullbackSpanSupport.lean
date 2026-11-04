import RMod.Classification.Instances.PullbackSimpleLabels
import RMod.Classification.Instances.RestrictedSpanFunctor

/-!
# Every object in a simple pullback component has the same support

At a coordinate outside the generator's support every homogeneous
inclusion is zero. The total matrix-unit identity then makes the
identity of the whole object zero there. This applies to arbitrary
finite sums in the component, including the zero object.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

theorem pullback_span_supported
    (S : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (X : HomogeneousSpanCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion S.data.object)
    (k : t.data.group) (hk : k ≠ pullbackSimpleDegree C hC t S) : C.id (X.obj k).val = C.zero := by
  obtain ⟨n, ⟨d⟩⟩ := X.property
  have hz := pullbackSimpleDegree_supported C hC t S k hk
  have hi (i : Fin n) : d.data.inclusion i k = C.zero :=
    hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws hz _
  have he := (PullbackCategory.finSum_apply C hC t.data t.laws
    (X := X.obj) (Y := X.obj) n
    (fun i => (twistedPullback C hC t).data.comp (d.data.projection i) (d.data.inclusion i)) k).symm.trans
      (congrFun d.laws.total k)
  change C.finSum n (fun i => C.comp (d.data.projection i k) (d.data.inclusion i k)) =
    C.id (X.obj k).val at he
  simp only [hi, raw_comp_zero hC.toWeaklyPointedSuperfusionLaws,
    raw_finSum_zero hC.toWeaklyPointedSuperfusionLaws] at he
  exact he.symm

end RMod.Classification
