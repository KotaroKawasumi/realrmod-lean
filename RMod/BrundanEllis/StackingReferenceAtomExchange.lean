import RMod.BrundanEllis.StackingReferenceKernelHom
import Superfusion.RMod.FromRawDCT.Tensor

/-! Identify the reference fusion row objects with the actual tensor products
of singleton atoms, then transport the exchange and its inverse to them. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- The actual tensor of singleton atoms enumerates precisely the stored fusion rows. -/
theorem tensorAtom_rowObject (a b : ZMod 8) (p q : ZMod 2) :
    Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, p)) (Obj.singleton (b, q)) =
      rowObject (a + b) (fun i => p + q + kernelRowParity a b i) := by
  have hs : Tensor.slots realDData (shiftCData realDData realCData realComputableNuBeta.data)
      (Obj.singleton (a, p)) (Obj.singleton (b, q)) =
        List.ofFn (fun r : (shiftCData realDData realCData realComputableNuBeta.data).Index a b => ⟨(0 : Fin 1), (0 : Fin 1), r⟩) := by
    change ((List.ofFn fun i : Fin 1 => i).sigma fun _ =>
      (List.ofFn fun j : Fin 1 => j).sigma fun _ =>
        List.ofFn fun r : (shiftCData realDData realCData realComputableNuBeta.data).Index a b => r) = _
    rw [show (List.ofFn fun i : Fin 1 => i) = [0] from rfl]
    simp only [List.sigma_cons, List.nil_sigma, List.append_nil, List.map_ofFn]
    rfl
  unfold Tensor.obj
  rw [hs]
  dsimp only [Tensor.slotAtom, Tensor.Slot, Tensor.Slot.left, Tensor.Slot.right,
    Tensor.Slot.fusion, Obj.singleton, Obj.size, Obj.atom, Atom.label, Atom.shift, CData.Index]
  simp only [rowObject]
  apply Fin.sigma_eq_of_eq_comp_cast List.length_ofFn
  funext i
  simp only [List.get_ofFn, Function.comp_apply]
  rfl

/-- Transport a raw morphism only along the displayed endpoint equalities. -/
def homTransport {X Y X' Y' : Obj} (hx : X = X') (hy : Y = Y')
    (f : Hom realDData X Y) : Hom realDData X' Y' := hx ▸ hy ▸ f

/-- Transport preserves homogeneous degree. -/
theorem homTransport_grade {X Y X' Y' : Obj} (hx : X = X') (hy : Y = Y')
    (f : Hom realDData X Y) (d : ZMod 2) (hf : Hom.MemGrade d f) :
    Hom.MemGrade d (homTransport hx hy f) := by
  cases hx
  cases hy
  exact hf

/-- Transport preserves both inverse identities. -/
theorem homTransport_inverse {X Y X' Y' : Obj} (hx : X = X') (hy : Y = Y')
    (f : Hom realDData X Y) (g : Hom realDData Y X)
    (hf : Hom.comp f g = Hom.id realDData X) (hg : Hom.comp g f = Hom.id realDData Y) :
    Hom.comp (homTransport hx hy f) (homTransport hy hx g) = Hom.id realDData X' ∧
      Hom.comp (homTransport hy hx g) (homTransport hx hy f) = Hom.id realDData Y' := by
  cases hx
  cases hy
  exact ⟨hf, hg⟩

/-- Tensor object for two unshifted atoms in the actual reference category. -/
def atomTensor (a b : ZMod 8) : Obj :=
  Tensor.obj realDData (shiftCData realDData realCData realComputableNuBeta.data)
    (Obj.singleton (a, 0)) (Obj.singleton (b, 0))

theorem atomTensor_source (a b : ZMod 8) :
    rowObject (a + b) (kernelRowParity a b) = atomTensor a b := by
  simpa only [zero_add, atomTensor] using (tensorAtom_rowObject a b 0 0).symm

theorem atomTensor_target (a b : ZMod 8) :
    rowObject (a + b) (kernelRowParity b a) = atomTensor b a := by
  rw [← atomTensor_source]
  rw [add_comm a b]

/-- The exchange is a morphism of the actual tensor products, of degree bit(a)bit(b). -/
def atomExchange (a b : ZMod 8) : Hom realDData (atomTensor a b) (atomTensor b a) :=
  homTransport (atomTensor_source a b) (atomTensor_target a b) (kernelHom a b)

/-- Its inverse uses the inverse module map, not an assumed symmetry identity. -/
def atomExchangeInv (a b : ZMod 8) : Hom realDData (atomTensor b a) (atomTensor a b) :=
  homTransport (atomTensor_target a b) (atomTensor_source a b) (kernelInv a b)

theorem atomExchange_grade (a b : ZMod 8) : Hom.MemGrade (degree a b) (atomExchange a b) :=
  homTransport_grade _ _ _ _ (kernelHom_grade a b)

theorem atomExchangeInv_grade (a b : ZMod 8) : Hom.MemGrade (degree a b) (atomExchangeInv a b) :=
  homTransport_grade _ _ _ _ (kernelInv_grade a b)

theorem atomExchange_inverse (a b : ZMod 8) :
    Hom.comp (atomExchange a b) (atomExchangeInv a b) = Hom.id realDData (atomTensor a b) ∧
      Hom.comp (atomExchangeInv a b) (atomExchange a b) = Hom.id realDData (atomTensor b a) :=
  homTransport_inverse _ _ _ _ (kernelHom_inverse a b).1 (kernelHom_inverse a b).2

example : Hom.MemGrade 1 (atomExchange 1 1) := atomExchange_grade 1 1

example : Hom.comp (atomExchange 1 4) (atomExchangeInv 1 4) = Hom.id realDData (atomTensor 1 4) :=
  (atomExchange_inverse 1 4).1

end RMod.BrundanEllis.Stacking.ReferenceCommutor
