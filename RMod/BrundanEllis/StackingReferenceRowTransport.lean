import RMod.BrundanEllis.StackingReferenceExchangeNaturality

/-! Equality transport for row presentations.  These lemmas only change the
name of the endpoint algebra, retaining the actual objects and morphisms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Apply an equality of algebra labels to every coefficient. -/
def rowCoefficientCast {n : ℕ} {a b : ZMod 8} (h : a = b) :
    (Fin n → Coeff a) ≃ₗ[ℝ] (Fin n → Coeff b) :=
  LinearEquiv.piCongrRight (fun _ => coefficientCast h)

theorem rowCoefficientCast_apply {n : ℕ} {a b : ZMod 8} (h : a = b)
    (v : Fin n → Coeff a) (i : Fin n) :
    rowCoefficientCast h v i = coefficientCast h (v i) := rfl

theorem rowCoefficientCast_symm {n : ℕ} {a b : ZMod 8} (h : a = b) :
    (@rowCoefficientCast n a b h).symm = rowCoefficientCast h.symm := by
  cases h
  rfl

/-- Unit-column extraction commutes with conjugation by equality transport. -/
theorem rowMatrixOf_conjugate {n m : ℕ} {a b : ZMod 8} (h : a = b)
    (F : (Fin n → Coeff a) →ₗ[ℝ] (Fin m → Coeff a)) :
    rowMatrixOf b ((rowCoefficientCast h).toLinearMap.comp
      (F.comp (rowCoefficientCast h).symm.toLinearMap)) =
      fun j i => coefficientCast h (rowMatrixOf a F j i) := by
  cases h
  rfl

/-- A coefficientwise label cast is exactly transport of the raw morphism. -/
theorem rowHom_transport_label {n m : ℕ} {a b : ZMod 8} (h : a = b)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    homTransport (congrArg (fun c => rowObject c p) h) (congrArg (fun c => rowObject c q) h)
      (rowHom a p q M) = rowHom b p q (fun j i => coefficientCast h (M j i)) := by
  cases h
  rfl

/-- Transport preserves composition, with the common middle object retained. -/
theorem homTransport_comp {X Y Z X' Y' Z' : Obj} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (f : Hom realDData X Y) (g : Hom realDData Y Z) :
    homTransport hx hz (Hom.comp f g) =
      Hom.comp (homTransport hx hy f) (homTransport hy hz g) := by
  cases hx
  cases hy
  cases hz
  rfl

theorem homTransport_smul {X Y X' Y' : Obj} (hx : X = X') (hy : Y = Y')
    (r : ℝ) (f : Hom realDData X Y) :
    homTransport hx hy (Hom.smul r f) = Hom.smul r (homTransport hx hy f) := by
  cases hx
  cases hy
  rfl

theorem homTransport_trans {X Y X' Y' X'' Y'' : Obj}
    (hx : X = X') (hy : Y = Y') (hx' : X' = X'') (hy' : Y' = Y'')
    (f : Hom realDData X Y) :
    homTransport hx' hy' (homTransport hx hy f) = homTransport (hx.trans hx') (hy.trans hy') f := by
  cases hx
  cases hy
  cases hx'
  cases hy'
  rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
