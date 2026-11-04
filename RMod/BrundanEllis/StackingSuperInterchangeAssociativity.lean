import RMod.BrundanEllis.StackingParityCoverMonoidal
import RMod.BrundanEllis.StackingInterchangeAssociativity
import RMod.BrundanEllis.StackingInterchangeIso

/-! Six-factor coherence with three specified homogeneous crossings.
The auxiliary parity cover turns super-interchange into ordinary interchange;
forgetting its labels recovers the single Koszul correction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.MonoidalCategory
variable (S : WeaklyPointedSuperfusion.{u, v})

/-- The middle-arrow shuffle, using the actual associators of the supercategory. -/
def superInterchangeHom (A B C D : S.data.Obj)
    (e : S.data.Hom (S.data.tensorObj B C) (S.data.tensorObj C B)) :=
  S.data.comp (S.data.associatorHom A B (S.data.tensorObj C D))
    (S.data.comp (S.data.tensorHom (S.data.id A) (S.data.associatorInv B C D))
      (S.data.comp (S.data.tensorHom (S.data.id A) (S.data.tensorHom e (S.data.id D)))
        (S.data.comp (S.data.tensorHom (S.data.id A) (S.data.associatorHom C B D))
          (S.data.associatorInv A C (S.data.tensorObj B D)))))

/-- Expanding a crossing of two objects against a third from the right. -/
def superRightExpansion (B D E : S.data.Obj)
    (de : S.data.Hom (S.data.tensorObj D E) (S.data.tensorObj E D))
    (be : S.data.Hom (S.data.tensorObj B E) (S.data.tensorObj E B)) :=
  S.data.comp (S.data.associatorHom B D E)
    (S.data.comp (S.data.tensorHom (S.data.id B) de)
      (S.data.comp (S.data.associatorInv B E D)
        (S.data.comp (S.data.tensorHom be (S.data.id D)) (S.data.associatorHom E B D))))

/-- Expanding a crossing of one object against the next two from the left. -/
def superLeftExpansion (B C E : S.data.Obj)
    (bc : S.data.Hom (S.data.tensorObj B C) (S.data.tensorObj C B))
    (be : S.data.Hom (S.data.tensorObj B E) (S.data.tensorObj E B)) :=
  S.data.comp (S.data.associatorInv B C E)
    (S.data.comp (S.data.tensorHom bc (S.data.id E))
      (S.data.comp (S.data.associatorHom C B E)
        (S.data.comp (S.data.tensorHom (S.data.id C) be) (S.data.associatorInv C E B))))

/-- Scalar multiplication of the middle arrow scales the whole shuffle. -/
theorem superInterchangeHom_smul (A B C D : S.data.Obj) (z : ℝ)
    (e : S.data.Hom (S.data.tensorObj B C) (S.data.tensorObj C B)) :
    superInterchangeHom S A B C D (S.data.smul z e) =
      S.data.smul z (superInterchangeHom S A B C D e) := by
  simp only [superInterchangeHom, S.laws.tensor_smul_left, S.laws.tensor_smul_right,
    S.laws.comp_smul, S.laws.smul_comp]

/-- The existing isomorphism data have exactly this forward map. -/
theorem interchangeIsoData_hom (A B C D : S.data.Obj)
    (e : IsoData S.data (S.data.tensorObj B C) (S.data.tensorObj C B)) :
    (interchangeIsoData S.data A B C D e).hom = superInterchangeHom S A B C D e.hom := by
  simp only [interchangeIsoData, IsoData.trans, IsoData.assoc, IsoData.tensor,
    IsoData.refl, IsoData.symm, superInterchangeHom, S.laws.comp_assoc]

/-- The two orders of the three elementary crossings differ only by the
Koszul sign of the first and the disjoint second crossing. -/
theorem superInterchange_associativity (A B C D E F : S.data.Obj) (p q r : ZMod 2)
    (bc : S.data.Hom (S.data.tensorObj B C) (S.data.tensorObj C B))
    (de : S.data.Hom (S.data.tensorObj D E) (S.data.tensorObj E D))
    (be : S.data.Hom (S.data.tensorObj B E) (S.data.tensorObj E B))
    (hbc : S.data.IsHomogeneous p bc) (hde : S.data.IsHomogeneous r de)
    (hbe : S.data.IsHomogeneous q be) :
    S.data.comp
      (S.data.tensorHom (superInterchangeHom S A B C D bc) (S.data.id (S.data.tensorObj E F)))
      (S.data.comp
        (superInterchangeHom S (S.data.tensorObj A C) (S.data.tensorObj B D) E F
          (superRightExpansion S B D E de be))
        (S.data.tensorHom (S.data.associatorHom A C E) (S.data.associatorHom B D F))) =
    S.data.smul ((-1 : ℝ) ^ (p * r).val)
      (S.data.comp (S.data.associatorHom (S.data.tensorObj A B) (S.data.tensorObj C D) (S.data.tensorObj E F))
        (S.data.comp
          (S.data.tensorHom (S.data.id (S.data.tensorObj A B)) (superInterchangeHom S C D E F de))
          (superInterchangeHom S A B (S.data.tensorObj C E) (S.data.tensorObj D F)
            (superLeftExpansion S B C E bc be)))) := by
  let A₀ : ParityCover S := (A, 0)
  let B₀ : ParityCover S := (B, 0)
  let B₁ : ParityCover S := (B, p)
  let B₂ : ParityCover S := (B, p + q)
  let C₀ : ParityCover S := (C, 0)
  let D₀ : ParityCover S := (D, 0)
  let D₁ : ParityCover S := (D, r)
  let E₀ : ParityCover S := (E, 0)
  let F₀ : ParityCover S := (F, 0)
  let bc' : B₀ ⊗ C₀ ⟶ C₀ ⊗ B₁ := ⟨bc, by simpa [B₀, C₀, B₁] using hbc⟩
  let de' : D₀ ⊗ E₀ ⟶ E₀ ⊗ D₁ := ⟨de, by simpa [D₀, E₀, D₁] using hde⟩
  let be' : B₁ ⊗ E₀ ⟶ E₀ ⊗ B₂ := ⟨be, by
    simpa only [ParityCover.tensorObj_snd, B₁, E₀, B₂, add_zero, zero_add,
      ← add_assoc, CharTwo.add_self_eq_zero] using hbe⟩
  have hh := congrArg (fun f => f.val)
    (interchangeMap_associativity A₀ B₀ B₁ B₂ C₀ D₀ D₁ E₀ F₀ bc' de' be')
  simp only [interchangeMap, ← id_tensorHom, ← tensorHom_id, ParityCover.comp_val, ParityCover.tensor_val,
    ParityCover.id_val, ParityCover.assoc_hom_val, ParityCover.assoc_inv_val,
    ParityCover.tensorObj_snd, ParityCover.tensorObj_fst,
    A₀, B₀, B₁, B₂, C₀, D₀, D₁, E₀, F₀, bc', de', be',
    add_zero, zero_add, add_assoc, CharTwo.add_self_eq_zero, zero_mul, mul_zero,
    ZMod.val_zero, pow_zero, S.laws.one_smul,
    S.laws.tensor_smul_left, S.laws.tensor_smul_right,
    S.laws.comp_smul, S.laws.smul_comp] at hh
  have hh' := congrArg (S.data.smul ((-1 : ℝ) ^ (p * r).val)) hh
  simpa only [superInterchangeHom, superRightExpansion, superLeftExpansion,
    ← S.laws.mul_smul, parity_power_mul_self, S.laws.one_smul] using hh'

end RMod.BrundanEllis.Stacking
