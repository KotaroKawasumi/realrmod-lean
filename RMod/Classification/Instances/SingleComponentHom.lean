import RMod.Classification.Abstract.Pullback

/-!
# A morphism supported at one group coordinate

This operation extends one specified coordinate map by zero between two
arbitrary pullback families. In particular it extends a section or a
retraction found in the original category to the relevant supported
pullback object. All other coordinate maps are explicitly zero.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def singleComponentHom (C : PiSuperfusionData.{0, 0}) (t : TwistData)
    {X Y : PullbackObj C t} (g : t.group) (f : C.Hom (X g).val (Y g).val) : PullbackHom C t X Y := by
  classical
  intro k
  by_cases hk : k = g
  · subst k
    exact f
  · exact C.zero

end RMod.Classification
