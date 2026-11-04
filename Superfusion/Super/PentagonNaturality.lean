/-
Superfusion / Super / PentagonNaturality

Milestone M7d-5b-4-iii(b), part 4: **the naturality kit** — the
composite-interchange laws needed to factor the pentagon vertex
routes through a common cluster-fusion prefix (for the cluster
edges e24/e13/e35):

- `gtensorCongr_trans_apply`: functoriality of the bundled
  congruence, `(e ≫ e') ⊗c (f ≫ f') = (e ⊗c f) ≫ (e' ⊗c f')`;
- `gassoc_natural_apply`: naturality of the associator;
- `matrixSuper_trans_apply`: functoriality of matrix
  stabilization.

All stated in applied form.  The ((P ᵍ⊗ Q) ᵍ⊗ R)-source equality of
`gassoc_natural_apply` reduces to pure tensors by `LinearMap.ext` +
`TensorProduct.induction_on`, fixing the right factor `c` and letting
the left factor range over `P.grading ᵍ⊗[K] Q.grading`.  A local
cast marker `toCarrier` re-anchors the `.carrier` field projection of
`SuperAlgebra.gtensor` (reducible but not syntactic), which
`rw`/`simp` cannot see through on their own; the extension step
avoids `rw` at the raw-tensor case boundary entirely by working with
genuine `LinearMap`s and term-mode `map_zero`/`map_add`.
-/
import Superfusion.Super.PentagonAlign

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Naturality

universe u

variable {K : Type u} [CommRing K]

/-- A cast marker: `SuperAlgebra.gtensor`'s `carrier` field is
*definitionally* `P.grading ᵍ⊗[K] Q.grading`, but that unfold is not
syntactic, so bare `ᵍ⊗ₜ` terms at the `.carrier` type defeat `rw`'s
pattern matching.  Wrapping with `toCarrier` gives `rw` an actual
function application to match against. -/
private def toCarrier {P Q : SuperAlgebra K} (x : P.grading ᵍ⊗[K] Q.grading) :
    (P.gtensor Q).carrier := x

/-- Unfolding `SuperAlgEquiv.gtensorCongr` on a pure tensor: a
`gcongr_tmul` restatement through the bundled layer. -/
private theorem gtensorCongr_tmul' {P P' Q Q' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (a : P.carrier) (b : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv (toCarrier (a ᵍ⊗ₜ[K] b))
      = toCarrier (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading e.toAlgEquiv
    f.toAlgEquiv e.map_grading f.map_grading a b

/-- Unfolding `gtensorAssoc` on a pure tensor: a `gassoc_tmul`
restatement through the bundled layer. -/
private theorem gtensorAssoc_tmul' {P Q R : SuperAlgebra K}
    (a : P.carrier) (b : Q.carrier) (c : R.carrier) :
    (gtensorAssoc P Q R).toAlgEquiv (toCarrier (toCarrier (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c))
      = toCarrier (a ᵍ⊗ₜ[K] toCarrier (b ᵍ⊗ₜ[K] c)) :=
  gassoc_tmul P.grading Q.grading R.grading a b c

/-- Functoriality of the bundled congruence, applied form. -/
theorem gtensorCongr_trans_apply {P P' P'' Q Q' Q'' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (e' : SuperAlgEquiv P' P'')
    (f : SuperAlgEquiv Q Q') (f' : SuperAlgEquiv Q' Q'')
    (w : (P.gtensor Q).carrier) :
    ((e.trans e').gtensorCongr (f.trans f')).toAlgEquiv w
      = (e'.gtensorCongr f').toAlgEquiv
        ((e.gtensorCongr f).toAlgEquiv w) := by
  have hhom : ((e.trans e').gtensorCongr (f.trans f')).toAlgEquiv.toAlgHom
      = ((e'.gtensorCongr f').toAlgEquiv.toAlgHom).comp
        ((e.gtensorCongr f).toAlgEquiv.toAlgHom) := by
    refine galgHom_ext P.grading Q.grading ?_
    intro a b
    change ((e.trans e').gtensorCongr (f.trans f')).toAlgEquiv
        (toCarrier (a ᵍ⊗ₜ[K] b))
      = (e'.gtensorCongr f').toAlgEquiv
        ((e.gtensorCongr f).toAlgEquiv (toCarrier (a ᵍ⊗ₜ[K] b)))
    rw [gtensorCongr_tmul', gtensorCongr_tmul', gtensorCongr_tmul']
    rfl
  exact AlgHom.congr_fun hhom w

/-! ### Naturality of the associator: the pure-tensor computation -/

private theorem congrCongr_eq {P P' Q Q' R R' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') (g : SuperAlgEquiv R R')
    (a : P.carrier) (b : Q.carrier) (c : R.carrier) :
    ((e.gtensorCongr f).gtensorCongr g).toAlgEquiv
        (toCarrier (toCarrier (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c))
      = toCarrier (toCarrier (e.toAlgEquiv a ᵍ⊗ₜ[K] f.toAlgEquiv b)
          ᵍ⊗ₜ[K] g.toAlgEquiv c) := by
  rw [gtensorCongr_tmul', gtensorCongr_tmul']

private theorem congr_gtensorAssoc_eq {P P' Q Q' R R' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') (g : SuperAlgEquiv R R')
    (a : P.carrier) (b : Q.carrier) (c : R.carrier) :
    (e.gtensorCongr (f.gtensorCongr g)).toAlgEquiv
        (toCarrier (a ᵍ⊗ₜ[K] toCarrier (b ᵍ⊗ₜ[K] c)))
      = toCarrier (e.toAlgEquiv a ᵍ⊗ₜ[K]
          toCarrier (f.toAlgEquiv b ᵍ⊗ₜ[K] g.toAlgEquiv c)) := by
  rw [gtensorCongr_tmul', gtensorCongr_tmul']

/-- Naturality of the bundled associator, on a pure tensor
`(a ᵍ⊗ b) ᵍ⊗ c`. -/
private theorem gassoc_natural_tmul {P P' Q Q' R R' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') (g : SuperAlgEquiv R R')
    (a : P.carrier) (b : Q.carrier) (c : R.carrier) :
    (gtensorAssoc P' Q' R').toAlgEquiv
        (((e.gtensorCongr f).gtensorCongr g).toAlgEquiv
          (toCarrier (toCarrier (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c)))
      = (e.gtensorCongr (f.gtensorCongr g)).toAlgEquiv
        ((gtensorAssoc P Q R).toAlgEquiv
          (toCarrier (toCarrier (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] c))) := by
  rw [congrCongr_eq, gtensorAssoc_tmul', gtensorAssoc_tmul', congr_gtensorAssoc_eq]

/-- `v ↦ toCarrier v ᵍ⊗ c` as a `LinearMap`, for fixed `c`; used to
extend the pure-tensor computation `gassoc_natural_tmul` from
`u = toCarrier (a ᵍ⊗ b)` to all `u : (P.gtensor Q).carrier` by
`LinearMap.ext` + `TensorProduct.induction_on`. -/
private noncomputable def tmulRightFix {P Q R : SuperAlgebra K} (c : R.carrier) :
    (P.grading ᵍ⊗[K] Q.grading) →ₗ[K] ((P.gtensor Q).grading ᵍ⊗[K] R.grading) :=
  (GradedTensorProduct.of K (P.gtensor Q).grading R.grading).toLinearMap ∘ₗ
    (TensorProduct.mk K (P.gtensor Q).carrier R.carrier).flip c

private theorem tmulRightFix_apply {P Q R : SuperAlgebra K} (c : R.carrier)
    (v : P.grading ᵍ⊗[K] Q.grading) :
    tmulRightFix c v = toCarrier v ᵍ⊗ₜ[K] c := rfl

/-- Naturality of the bundled associator, applied form. -/
theorem gassoc_natural_apply {P P' Q Q' R R' : SuperAlgebra K}
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (g : SuperAlgEquiv R R')
    (w : ((P.gtensor Q).gtensor R).carrier) :
    (gtensorAssoc P' Q' R').toAlgEquiv
        (((e.gtensorCongr f).gtensorCongr g).toAlgEquiv w)
      = (e.gtensorCongr (f.gtensorCongr g)).toAlgEquiv
        ((gtensorAssoc P Q R).toAlgEquiv w) := by
  set F : (P.gtensor Q).grading ᵍ⊗[K] R.grading →ₐ[K] (P'.gtensor (Q'.gtensor R')).carrier :=
    ((gtensorAssoc P' Q' R').toAlgEquiv.toAlgHom).comp
      (((e.gtensorCongr f).gtensorCongr g).toAlgEquiv.toAlgHom) with hF
  set G : (P.gtensor Q).grading ᵍ⊗[K] R.grading →ₐ[K] (P'.gtensor (Q'.gtensor R')).carrier :=
    ((e.gtensorCongr (f.gtensorCongr g)).toAlgEquiv.toAlgHom).comp
      ((gtensorAssoc P Q R).toAlgEquiv.toAlgHom) with hG
  have hhom : F = G := by
    refine galgHom_ext (P.gtensor Q).grading R.grading ?_
    intro u c
    -- The equation, for fixed `c`, is additive/zero-preserving in `u`
    -- (`tmulRightFix c` is a genuine `LinearMap`) and holds on pure
    -- tensors `u = toCarrier (a ᵍ⊗ b)` by `gassoc_natural_tmul`.
    have key : F.toLinearMap ∘ₗ tmulRightFix c = G.toLinearMap ∘ₗ tmulRightFix c := by
      apply LinearMap.ext
      intro v
      refine TensorProduct.induction_on
        (motive := fun v : P.grading ᵍ⊗[K] Q.grading =>
          (F.toLinearMap ∘ₗ tmulRightFix c) v = (G.toLinearMap ∘ₗ tmulRightFix c) v)
        v ?_ ?_ ?_
      · exact (map_zero (F.toLinearMap ∘ₗ tmulRightFix c)).trans
          (map_zero (G.toLinearMap ∘ₗ tmulRightFix c)).symm
      · intro a b
        show F (tmulRightFix c (a ᵍ⊗ₜ[K] b)) = G (tmulRightFix c (a ᵍ⊗ₜ[K] b))
        rw [tmulRightFix_apply, hF, hG]
        exact gassoc_natural_tmul e f g a b c
      · intro x y hx hy
        exact (map_add (F.toLinearMap ∘ₗ tmulRightFix c) x y).trans <|
          hx ▸ hy ▸ (map_add (G.toLinearMap ∘ₗ tmulRightFix c) x y).symm
    exact LinearMap.congr_fun key u
  exact AlgHom.congr_fun hhom w

/-- Functoriality of matrix stabilization, applied form. -/
theorem matrixSuper_trans_apply {P Q R : SuperAlgebra K}
    (e : SuperAlgEquiv P Q) (f : SuperAlgEquiv Q R) (p q : ℕ)
    (M : (P.matrixSuper p q).carrier) :
    ((e.trans f).matrixSuper p q).toAlgEquiv M
      = (f.matrixSuper p q).toAlgEquiv
        ((e.matrixSuper p q).toAlgEquiv M) := by
  rfl

end Naturality

end Superfusion
