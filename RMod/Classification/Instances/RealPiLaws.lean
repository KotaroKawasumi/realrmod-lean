import RMod.Classification.Instances.RealPi
import RMod.Theorems.RealRMod

/-! # Verified specified parity on the existing real regular-module category -/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion.RMod.FromRawDCT

/-- Both coefficient-one directions are odd, and their composites are the
actual identities. This reuses the checked coordinate composition lemmas. -/
theorem realPiLaws : PiLaws RMod.realRModData realPi where
  hom_odd := by
    change Hom.MemGrade 1 (RealPairing.singletonShiftHom 0 1 0)
    simpa only [add_zero] using RealPairing.singletonShiftHom_mem 0 1 0
  inv_odd := by
    change Hom.MemGrade 1 (RealPairing.singletonShiftHom 0 0 1)
    simpa only [zero_add] using RealPairing.singletonShiftHom_mem 0 0 1
  hom_inv := RealPairing.singletonShiftHom_comp 0 1 0
  inv_hom := RealPairing.singletonShiftHom_comp 0 0 1

/-- The structured real category, before the stronger BW-reference theorem. -/
theorem realPiSuperfusionLaws : PiSuperfusionLaws realPiData where
  toWeaklyPointedSuperfusionLaws := RMod.realRModLaws
  pi := realPiLaws

def realPiSuperfusion : PiSuperfusion.{0, 0} where
  data := realPiData
  laws := realPiSuperfusionLaws

/-! Two nontrivial checks of the chosen concrete example. -/

/-- The chosen parity singleton differs from the unit singleton. -/
example : realPi.object ≠ RMod.realRModData.tensorUnit := by
  intro h
  have hs := congrArg (fun X : Obj => List.ofFn (fun i => (X.atom i).shift)) h
  change ([1] : List (ZMod 2)) = [0] at hs
  exact one_ne_zero (List.cons.inj hs).1

/-- Its odd comparison is nonzero; this is not a degenerate odd isomorphism
on a zero object. -/
example : realPi.hom ≠ RMod.realRModData.zero := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
  have hc := congrArg (fun f => AtomHom.coeff f rfl) he
  have hv := congrFun hc (0 : Fin 1)
  change (1 : ℝ) = 0 at hv
  exact one_ne_zero hv

end RMod.Classification
