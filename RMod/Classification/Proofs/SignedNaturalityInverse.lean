import RMod.Classification.Proofs.IsoCalculus

/-!
# Inversion of a rectangular signed naturality square

An involutive real scalar gives the same sign in the square for the
inverse maps. The source and target objects may differ; this is needed
for natural comparisons on all morphisms, not just endomorphisms.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem signed_naturality_symm {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    (hd : IsoLaws C d) (hd' : IsoLaws C d') {r : ℝ} (hr : r * r = 1)
    {f : C.Hom X X'} {g : C.Hom Y Y'}
    (he : C.comp f d'.hom = C.smul r (C.comp d.hom g)) :
    C.comp g d'.inv = C.smul r (C.comp d.inv f) := by
  have hh := congrArg (fun q => C.comp d.inv (C.comp q d'.inv)) he
  have heq : C.comp d.inv f = C.smul r (C.comp g d'.inv) := by
    simpa only [hC.comp_smul, hC.smul_comp, hC.comp_assoc, hd'.hom_inv, hC.comp_id,
      ← hC.comp_assoc d.inv d.hom, hd.inv_hom, hC.id_comp] using hh
  calc
    _ = C.smul r (C.smul r (C.comp g d'.inv)) := by rw [← hC.mul_smul, hr, hC.one_smul]
    _ = _ := congrArg (C.smul r) heq.symm

end RMod.Classification
