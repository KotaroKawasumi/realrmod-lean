import RMod.Classification.Instances.PullbackObjects

/-!
# Objects and maps supported at an arbitrary group degree

A C-object of type rho(g) is placed at g and extended by the chosen
zero object elsewhere. The same operation on Hom maps uses the specified
map at g and zero at the other coordinates. These are actual objects and
maps in the fixed pullback carrier, with no extra reconstruction data.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (g : t.group)

noncomputable def placedObj (X : C.Obj)
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X) :
    PullbackObj C t := by
  classical
  exact fun k => ⟨if k = g then X else (pullbackZeroObj C hC t k).val, by
    split_ifs with hk
    · simpa only [hk] using hX
    · exact (pullbackZeroObj C hC t k).property⟩

noncomputable def placedHom {X Y : C.Obj}
    (hX : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) X)
    (hY : InComponent C.toWeaklyPointedSuperfusionData (Multiplicative.toAdd (t.rho g)) Y)
    (f : C.Hom X Y) : PullbackHom C t (placedObj C hC t g X hX) (placedObj C hC t g Y hY) := by
  classical
  intro k
  by_cases hk : k = g
  · simpa only [placedObj, if_pos hk] using f
  · exact C.zero

noncomputable def componentInclusion (X : PullbackObj C t) :
    PullbackHom C t (placedObj C hC t g (X g).val (X g).property) X := by
  classical
  intro k
  by_cases hk : k = g
  · subst k
    simpa [placedObj] using C.id (X g).val
  · exact C.zero

noncomputable def componentProjection (X : PullbackObj C t) :
    PullbackHom C t X (placedObj C hC t g (X g).val (X g).property) := by
  classical
  intro k
  by_cases hk : k = g
  · subst k
    simpa [placedObj] using C.id (X g).val
  · exact C.zero

end RMod.Classification
