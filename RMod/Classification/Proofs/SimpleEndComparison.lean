import RMod.Classification.Proofs.IntrinsicTypes

/-!
# Comparing actual simple endomorphism algebras of the same type

The real graded division classification identifies each endomorphism
algebra with its unique division representative. Intrinsic type uniqueness
forces both labels to be the prescribed common label. Composing these
maps gives an actual graded algebra isomorphism, which will act entrywise
on Hom matrices in the component comparison functor.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

theorem exists_simpleEndComparison (C D : PiSuperfusion.{0, 0})
    (X : C.data.Obj) (Y : D.data.Obj) (hX : C.data.IsSimple X) (hY : D.data.IsSimple Y)
    {r : ZMod 8} (hr : HasBWType C.data.toWeaklyPointedSuperfusionData X r)
    (hs : HasBWType D.data.toWeaklyPointedSuperfusionData Y r) :
    Nonempty (SuperAlgEquiv
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory C.toWeaklyPointedSuperfusion) X)
      (Category.endSuperAlgebra (K := ℝ) (C := LinearCategory D.toWeaklyPointedSuperfusion) Y)) := by
  obtain ⟨a, ⟨eX⟩⟩ := simple_end_realRep C.toWeaklyPointedSuperfusion X hX
  obtain ⟨b, ⟨eY⟩⟩ := simple_end_realRep D.toWeaklyPointedSuperfusion Y hY
  have ha := HasBWType.unique C.toWeaklyPointedSuperfusion (hasBWType_of_end_realRep C X a eX) hr
  have hb := HasBWType.unique D.toWeaklyPointedSuperfusion (hasBWType_of_end_realRep D Y b eY) hs
  subst a
  subst b
  exact ⟨eX.trans eY.symm⟩

end RMod.Classification
