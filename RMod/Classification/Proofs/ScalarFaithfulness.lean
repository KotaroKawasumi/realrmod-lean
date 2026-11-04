import RMod.Classification.Instances.LinearCategory
import RMod.Classification.Proofs.IsoCalculus

/-!
# Scalar faithfulness on nonzero maps

The raw Hom spaces carry the real vector-space structure of the linear
category. Mathlib's scalar cancellation therefore detects coefficients
on any nonzero map. An isomorphism out of a nonzero object supplies such
a map without a simplicity assumption.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v})

theorem raw_smul_injective {X Y : C.data.Obj} (f : C.data.Hom X Y) (hf : f ≠ C.data.zero)
    {r s : ℝ} (h : C.data.smul r f = C.data.smul s f) : r = s := by
  exact smul_left_injective ℝ (M := @Quiver.Hom (LinearCategory C) _ X Y) (m := f) hf h

theorem iso_hom_ne_zero {X Y : C.data.Obj} {d : IsoData C.data X Y}
    (hd : IsoLaws C.data d) (hX : C.data.id X ≠ C.data.zero) : d.hom ≠ C.data.zero := by
  intro hz
  apply hX
  rw [← hd.hom_inv, hz, raw_zero_comp C.laws]

end RMod.Classification
