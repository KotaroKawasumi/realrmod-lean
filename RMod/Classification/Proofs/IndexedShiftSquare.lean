import RMod.Classification.Instances.IndexedShiftSquare
import RMod.Classification.Proofs.GaugeShiftSquare

/-! # Coordinate cancellation is even and natural for every family of maps -/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)
  {I : Type w} (X : I → C.Obj) (lam : I → ZMod 2) {i j : I} (e : j = i)

include hC hp

theorem indexedShiftSquare_evenIso : EvenIsoLaws C (p.indexedShiftSquare X lam e) :=
  (hp.rightShiftSquare_evenIso hC (X j) (lam j)).trans hC
    (EvenIsoLaws.ofEq hC (congrArg X e))

theorem indexedMixedShiftSquare_evenIso : EvenIsoLaws C (p.indexedMixedShiftSquare X lam e) :=
  (EvenIsoLaws.ofEq hC (congrArg (fun k => C.tensorObj (C.tensorObj (X k) (p.factor (lam k)))
    (p.factor (lam i))) e)).trans hC (hp.rightShiftSquare_evenIso hC (X i) (lam i))

theorem indexedShiftSquare_naturality {Y : I → C.Obj} (f : ∀ k, C.Hom (X k) (Y k)) :
    C.comp (C.tensorHom (C.tensorHom (f j) (C.id (p.factor (lam j)))) (C.id (p.factor (lam j))))
      (p.indexedShiftSquare Y lam e).hom =
      C.comp (p.indexedShiftSquare X lam e).hom (f i) := by
  cases e
  dsimp only [PiData.indexedShiftSquare, IsoData.trans, IsoData.ofEq, IsoData.refl]
  rw [hC.comp_id, hC.comp_id]
  exact hp.rightShiftSquare_naturality hC (f i) (lam i)

theorem indexedMixedShiftSquare_naturality {Y : I → C.Obj} (f : ∀ k, C.Hom (X k) (Y k)) :
    C.comp (C.tensorHom (C.tensorHom (f j) (C.id (p.factor (lam j)))) (C.id (p.factor (lam i))))
      (p.indexedMixedShiftSquare Y lam e).hom =
      C.comp (p.indexedMixedShiftSquare X lam e).hom (f i) := by
  cases e
  dsimp only [PiData.indexedMixedShiftSquare, IsoData.trans, IsoData.ofEq, IsoData.refl]
  rw [hC.id_comp, hC.id_comp]
  exact hp.rightShiftSquare_naturality hC (f i) (lam i)

end RMod.Classification.PiLaws
