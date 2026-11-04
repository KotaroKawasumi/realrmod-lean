import RMod.Classification.Proofs.EndDivisionType
import RMod.Classification.Proofs.EndConjugation
import RMod.Classification.Proofs.ParityAutomorphism
import RMod.Classification.Proofs.ParityPowers
import Superfusion.Super.SkolemNoetherIso
import Superfusion.Wedderburn.MatrixRealization

/-!
# Invertible signed comparisons between generator algebra actions

Choose any homogeneous isomorphism between the target objects. Its
conjugation is corrected by the source parity automorphism before
applying super Skolem--Noether. The resulting homogeneous unit corrects
the chosen isomorphism to an intertwiner whose sign uses its actual
total degree. No extra algebraic existence hypothesis is introduced.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endGrading Superfusion.Category.endSuperAlgebra

theorem exists_homogeneous_end_intertwiner (C D : WeaklyPointedSuperfusion.{0, 0})
    (S : LinearCategory C) (X Y : LinearCategory D)
    (hS : C.data.IsSimple S) (hY : D.data.IsSimple Y)
    (φ : End S ≃ₐ[ℝ] End X) (ψ : End S ≃ₐ[ℝ] End Y)
    (hφ : ∀ {b : ZMod 2} {f : End S}, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (φ f))
    (hψ : ∀ {b : ZMod 2} {f : End S}, C.data.IsHomogeneous b f → D.data.IsHomogeneous b (ψ f))
    (hXY : SameParityOrbit D.data X Y) :
    ∃ (a : ZMod 2) (e : X ≅ Y), D.data.IsHomogeneous a e.hom ∧
      ∀ {b : ZMod 2} (f : End S), C.data.IsHomogeneous b f →
        φ f ≫ e.hom = ((-1 : ℝ) ^ (a * b).val) • (e.hom ≫ ψ f) := by
  obtain ⟨q, u, v, huv, hvu, hu, _⟩ := hXY
  let e₀ : X ≅ Y := ⟨u, v, huv, hvu⟩
  let 𝒜 := Superfusion.Category.endGrading (K := ℝ) S
  let ℬ := Superfusion.Category.endGrading (K := ℝ) Y
  letI : IsSuperCentral 𝒜 := end_isSuperCentral C S hS
  letI : IsSuperCentral ℬ := end_isSuperCentral D Y hY
  letI : IsGradedSimple 𝒜 := IsSuperDivision.isGradedSimple (end_isSuperDivision C S hS)
  letI : IsGradedSimple ℬ := IsSuperDivision.isGradedSimple (end_isSuperDivision D Y hY)
  letI : Nontrivial (End S) := ⟨⟨1, 0, simple_id_ne_zero C.laws hS⟩⟩
  letI : Nontrivial (End Y) := ⟨⟨1, 0, simple_id_ne_zero D.laws hY⟩⟩
  letI : FiniteDimensional ℝ (End S) := LinearCategory.finiteDimensionalHom C S S
  letI : FiniteDimensional ℝ (End Y) := LinearCategory.finiteDimensionalHom D Y Y
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let φ₀ := (parityAutomorphism 𝒜 q).trans (φ.trans (endConjugation e₀))
  have hφ₀ : IsHomogeneousHom 𝒜 ℬ φ₀.toAlgHom := by
    intro b f hf
    exact endConjugation_grade D e₀ hu _
      (hφ (parityAutomorphism_homogeneous 𝒜 q b f hf))
  obtain ⟨p, t, ht, htu, hti⟩ := superSkolemNoether_exists_of_surjective 𝒜 ℬ
    φ₀.toAlgHom ψ.toAlgHom hφ₀ (fun _ _ hf => hψ hf) φ₀.surjective ψ.surjective
  obtain ⟨w, hw⟩ := htu
  let et : Y ≅ Y := Aut.unitsEndEquivAut Y w
  have het : et.hom = t := hw
  let e := e₀ ≪≫ et
  refine ⟨q + p, e, ?_, ?_⟩
  · exact D.laws.comp_grade _ _ hu (het.symm ▸ ht)
  · intro b f hf
    have hi := hti hf
    rw [← Superfusion.Category.koszulSign_smul_eq_sgn_zsmul ℝ b p] at hi
    have hf₀ : φ₀ f = ((-1 : ℝ) ^ (q * b).val) • (e₀.inv ≫ φ f ≫ e₀.hom) := by
      change endConjugation e₀ (φ (parityAutomorphism 𝒜 q f)) = _
      rw [parityAutomorphism_of_mem 𝒜 q hf, map_smul, map_smul]
      rfl
    change t ≫ ψ f = ((-1 : ℝ) ^ (b * p).val) • (φ₀ f ≫ t) at hi
    have hs : ((-1 : ℝ) ^ (b * p).val) * ((-1 : ℝ) ^ (q * b).val) =
        (-1 : ℝ) ^ ((q + p) * b).val := by
      rw [add_mul, parity_power_add, mul_comm b p, mul_comm]
    have he : e.hom ≫ ψ f = ((-1 : ℝ) ^ ((q + p) * b).val) • (φ f ≫ e.hom) := by
      change (e₀.hom ≫ et.hom) ≫ ψ f =
        ((-1 : ℝ) ^ ((q + p) * b).val) • (φ f ≫ (e₀.hom ≫ et.hom))
      rw [het, Category.assoc, hi, hf₀]
      simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, hs, Category.assoc,
        Iso.hom_inv_id_assoc]
    calc
      φ f ≫ e.hom = ((-1 : ℝ) ^ ((q + p) * b).val) •
          (((-1 : ℝ) ^ ((q + p) * b).val) • (φ f ≫ e.hom)) := by
        rw [smul_smul, parity_power_mul_self, one_smul]
      _ = _ := congrArg (fun k => ((-1 : ℝ) ^ ((q + p) * b).val) • k) he.symm

end RMod.Classification
