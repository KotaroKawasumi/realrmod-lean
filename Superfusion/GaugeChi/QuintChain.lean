/-
Superfusion / GaugeChi / QuintChain

Assembly of the nine faces of the associahedral `K₅` boundary.  The six
pentagon faces contribute the five `gChiCanon` terms, while the three
square faces contribute the three terms of `p ∪₁ p`.
-/
import Superfusion.Cochain.Cup
import Superfusion.GaugeChi.QuintFaces
import Superfusion.GaugeChi.QuintFaces3
import Superfusion.GaugeChi.QuintFacesPDE
import Superfusion.GaugeChi.QuintNontrivial
import Superfusion.GaugeChi.QuintSquares
import Superfusion.GaugeChi.QuintSquares2
import Superfusion.GaugeChi.QuintFacesPCD

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d e : G)

attribute [local instance 500] leftModule rightModule

/-! ### The square signs as `K`-scalars -/

omit [Invertible (2 : K)] in
private theorem intCast_sgn_eq (q : ZMod 2) :
    (((sgn q : ℤˣ) : ℤ) : K) = ((sgn q : Kˣ) : K) := by
  rcases zmod2_cases q with hq | hq <;> subst hq <;> simp [sgn]

private theorem square_S1_K :
    E16M K Γ a b c d e ∘ₗ E1M K Γ a b c d e
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : Kˣ) : K) •
          (E20M K Γ a b c d e ∘ₗ E13M K Γ a b c d e) := by
  calc
    _ = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : ℤˣ) : ℤ) •
          (E20M K Γ a b c d e ∘ₗ E13M K Γ a b c d e) :=
      square_S1 K Γ a b c d e
    _ = _ := by
      rw [← Int.cast_smul_eq_zsmul K, intCast_sgn_eq]

private theorem square_S2_K :
    E18M K Γ a b c d e ∘ₗ E3M K Γ a b c d e
      = ((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
          (E6M K Γ a b c d e ∘ₗ E15M K Γ a b c d e) := by
  calc
    _ = ((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : ℤˣ) : ℤ) •
          (E6M K Γ a b c d e ∘ₗ E15M K Γ a b c d e) :=
      square_S2 K Γ a b c d e
    _ = _ := by
      rw [← Int.cast_smul_eq_zsmul K, intCast_sgn_eq]

private theorem square_S3_K :
    E21M K Γ a b c d e ∘ₗ E12M K Γ a b c d e
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (E8M K Γ a b c d e ∘ₗ E19M K Γ a b c d e) := by
  calc
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : ℤˣ) : ℤ) •
          (E8M K Γ a b c d e ∘ₗ E19M K Γ a b c d e) :=
      square_S3 K Γ a b c d e
    _ = _ := by
      rw [← Int.cast_smul_eq_zsmul K, intCast_sgn_eq]

/-! ### The nine routes used by the boundary walk -/

private noncomputable def chainW :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E21M K Γ a b c d e ∘ₗ E14M K Γ a b c d e ∘ₗ E13M K Γ a b c d e

private noncomputable def chainR1 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E21M K Γ a b c d e ∘ₗ E12M K Γ a b c d e ∘ₗ
    E11M K Γ a b c d e ∘ₗ E4M K Γ a b c d e

private noncomputable def chainR2 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E8M K Γ a b c d e ∘ₗ E19M K Γ a b c d e ∘ₗ
    E11M K Γ a b c d e ∘ₗ E4M K Γ a b c d e

private noncomputable def chainR3 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E8M K Γ a b c d e ∘ₗ E7M K Γ a b c d e ∘ₗ
    E18M K Γ a b c d e ∘ₗ E5M K Γ a b c d e ∘ₗ E4M K Γ a b c d e

private noncomputable def chainR4 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E8M K Γ a b c d e ∘ₗ E7M K Γ a b c d e ∘ₗ E18M K Γ a b c d e ∘ₗ
    E3M K Γ a b c d e ∘ₗ E2M K Γ a b c d e ∘ₗ E1M K Γ a b c d e

private noncomputable def chainR5 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E8M K Γ a b c d e ∘ₗ E7M K Γ a b c d e ∘ₗ E6M K Γ a b c d e ∘ₗ
    E15M K Γ a b c d e ∘ₗ E2M K Γ a b c d e ∘ₗ E1M K Γ a b c d e

private noncomputable def chainR6 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E10M K Γ a b c d e ∘ₗ E9M K Γ a b c d e ∘ₗ E15M K Γ a b c d e ∘ₗ
    E2M K Γ a b c d e ∘ₗ E1M K Γ a b c d e

private noncomputable def chainR7 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E10M K Γ a b c d e ∘ₗ E17M K Γ a b c d e ∘ₗ
    E16M K Γ a b c d e ∘ₗ E1M K Γ a b c d e

private noncomputable def chainR8 :
    V1 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  E10M K Γ a b c d e ∘ₗ E17M K Γ a b c d e ∘ₗ
    E20M K Γ a b c d e ∘ₗ E13M K Γ a b c d e

/-! ### The nine whiskered face equations -/

private theorem chain_pab :
    chainR1 K Γ a b c d e
      = gChiCanon K Γ (a + b) c d e • chainW K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_PAB K Γ a b c d e) x
  simp only [chainR1, chainW, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul]

private theorem chain_s3 :
    chainR1 K Γ a b c d e
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          chainR2 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (square_S3_K K Γ a b c d e)
    (E11M K Γ a b c d e (E4M K Γ a b c d e x))
  simpa only [chainR1, chainR2, LinearMap.comp_apply, LinearMap.smul_apply] using h

private theorem chain_pcd :
    chainR3 K Γ a b c d e
      = gChiCanon K Γ a b (c + d) e • chainR2 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_PCD K Γ a b c d e)
    (E4M K Γ a b c d e x)
  simp only [chainR3, chainR2, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul]

private theorem chain_p6 :
    chainR4 K Γ a b c d e
      = gChiCanon K Γ a b c d • chainR3 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_P6 K Γ a b c d e) x
  simp only [chainR4, chainR3, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul, map_smul, map_smul]

private theorem chain_s2 :
    chainR4 K Γ a b c d e
      = ((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
          chainR5 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (square_S2_K K Γ a b c d e)
    (E2M K Γ a b c d e (E1M K Γ a b c d e x))
  simp only [chainR4, chainR5, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul, map_smul]

private theorem chain_p1 :
    chainR5 K Γ a b c d e
      = gChiCanon K Γ b c d e • chainR6 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_P1 K Γ a b c d e)
    (E15M K Γ a b c d e (E2M K Γ a b c d e (E1M K Γ a b c d e x)))
  simpa only [chainR5, chainR6, LinearMap.comp_apply, LinearMap.smul_apply] using h

private theorem chain_pbc :
    chainR6 K Γ a b c d e
      = gChiCanon K Γ a (b + c) d e • chainR7 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_PBC K Γ a b c d e)
    (E1M K Γ a b c d e x)
  simp only [chainR6, chainR7, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul]

private theorem chain_s1 :
    chainR7 K Γ a b c d e
      = ((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : Kˣ) : K) •
          chainR8 K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (square_S1_K K Γ a b c d e) x
  simp only [chainR7, chainR8, LinearMap.comp_apply, LinearMap.smul_apply] at h ⊢
  rw [h, map_smul, map_smul]

private theorem chain_pde :
    chainR8 K Γ a b c d e
      = gChiCanon K Γ a b c (d + e) • chainW K Γ a b c d e := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (face_PDE K Γ a b c d e)
    (E13M K Γ a b c d e x)
  simpa only [chainR8, chainW, LinearMap.comp_apply, LinearMap.smul_apply] using h

/-! ### The boundary walk and scalar cancellation -/

omit [Invertible (2 : K)] in
private theorem smul_smul_commute {M : Type*} [AddCommMonoid M] [Module K M]
    (r s : K) (x : M) : r • (s • x) = s • (r • x) := by
  rw [smul_smul, smul_smul, mul_comm]

private theorem chain_boundary :
    gChiCanon K Γ a b c d •
        (gChiCanon K Γ a b (c + d) e •
          (gChiCanon K Γ (a + b) c d e • chainW K Γ a b c d e))
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
            (gChiCanon K Γ b c d e •
              (gChiCanon K Γ a (b + c) d e •
                (((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : Kˣ) : K) •
                  (gChiCanon K Γ a b c (d + e) • chainW K Γ a b c d e))))) := by
  calc
    _ = gChiCanon K Γ a b c d •
          (gChiCanon K Γ a b (c + d) e • chainR1 K Γ a b c d e) := by
        rw [chain_pab]
    _ = gChiCanon K Γ a b c d •
          (gChiCanon K Γ a b (c + d) e •
            (((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
              chainR2 K Γ a b c d e)) := by
        rw [chain_s3]
    _ = gChiCanon K Γ a b c d •
          (((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
            (gChiCanon K Γ a b (c + d) e • chainR2 K Γ a b c d e)) := by
        exact congrArg (fun z => gChiCanon K Γ a b c d • z)
          (smul_smul_commute K (gChiCanon K Γ a b (c + d) e)
            ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K)
            (chainR2 K Γ a b c d e))
    _ = gChiCanon K Γ a b c d •
          (((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
            chainR3 K Γ a b c d e) := by
        rw [chain_pcd]
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (gChiCanon K Γ a b c d • chainR3 K Γ a b c d e) := by
        exact smul_smul_commute K (gChiCanon K Γ a b c d)
          ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K)
          (chainR3 K Γ a b c d e)
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          chainR4 K Γ a b c d e := by
        rw [chain_p6]
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
            chainR5 K Γ a b c d e) := by
        rw [chain_s2]
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
            (gChiCanon K Γ b c d e • chainR6 K Γ a b c d e)) := by
        rw [chain_p1]
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
            (gChiCanon K Γ b c d e •
              (gChiCanon K Γ a (b + c) d e • chainR7 K Γ a b c d e))) := by
        rw [chain_pbc]
    _ = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) •
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) •
            (gChiCanon K Γ b c d e •
              (gChiCanon K Γ a (b + c) d e •
                (((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : Kˣ) : K) •
                  chainR8 K Γ a b c d e)))) := by
        rw [chain_s1]
    _ = _ := by
        rw [chain_pde]

private theorem chainW_bijective :
    Function.Bijective (chainW K Γ a b c d e) := by
  unfold chainW
  exact (E21M_bijective K Γ a b c d e).comp
    ((E14M_bijective K Γ a b c d e).comp (E13M_bijective K Γ a b c d e))

private theorem chainW_ne_zero : chainW K Γ a b c d e ≠ 0 := by
  obtain ⟨x, hx⟩ := V1_exists_ne_zero K Γ a b c d e
  intro hW
  apply hx
  apply (chainW_bijective K Γ a b c d e).injective
  have : chainW K Γ a b c d e x = 0 := by
    rw [hW]
    rfl
  simpa only [map_zero] using this

private theorem chain_scalar_identity :
    gChiCanon K Γ a b c d *
        (gChiCanon K Γ a b (c + d) e * gChiCanon K Γ (a + b) c d e)
      = ((sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e)) : Kˣ) : K) *
          (((sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e) : Kˣ) : K) *
            (gChiCanon K Γ b c d e *
              (gChiCanon K Γ a (b + c) d e *
                (((sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e) : Kˣ) : K) *
                  gChiCanon K Γ a b c (d + e))))) := by
  apply smul_left_injective K (chainW_ne_zero K Γ a b c d e)
  simpa only [smul_smul] using chain_boundary K Γ a b c d e

/-! ### The public supercocycle -/

/-- The two coherence equations for a degree-four Gu--Wen supercocycle.
Normalization is deliberately not included: it is an independent choice of
cochain representative. -/
def IsDegreeFourSuperCocycle {H M : Type*} [Group H] [CommGroup M] [GroupSign M]
    (p : H → H → H → ZMod 2) (χ : H → H → H → H → M) : Prop :=
  (∀ a b c d, d₃ p a b c d = 0) ∧
    ∀ a b c d e, dm₄ χ a b c d e = sgn (cupOne₃₃ p p a b c d e)

/-- The canonical pentagon scalar, regarded as a unit using its proved
nonvanishing. -/
noncomputable def gChiCanonUnit (a b c d : G) : Kˣ :=
  Units.mk0 (gChiCanon K Γ a b c d) (gChiCanon_ne_zero K Γ a b c d)

@[simp] theorem gChiCanonUnit_val (a b c d : G) :
    ((gChiCanonUnit K Γ a b c d : Kˣ) : K) = gChiCanon K Γ a b c d := rfl

/-- The canonical pentagon scalar as a multiplicative four-cochain on the
group associated to the additive index group. -/
noncomputable def gChiCanonCochain :
    Multiplicative G → Multiplicative G → Multiplicative G → Multiplicative G → Kˣ :=
  fun a b c d => gChiCanonUnit K Γ a.toAdd b.toAdd c.toAdd d.toAdd

/-- The parity of the canonical intertwiner super-line as an additive
three-cochain on the same group. -/
noncomputable def gParityCochain :
    Multiplicative G → Multiplicative G → Multiplicative G → ZMod 2 :=
  fun a b c => gParity K Γ a.toAdd b.toAdd c.toAdd

/-- The cochain form of `gParity_cocycle`: the canonical parity is a
three-cocycle. -/
theorem gParityCochain_cocycle (a b c d : Multiplicative G) :
    d₃ (gParityCochain K Γ) a b c d = 0 := by
  have h := gParity_cocycle K Γ a.toAdd b.toAdd c.toAdd d.toAdd
  have sub_eq_add : ∀ x y : ZMod 2, x - y = x + y := by decide
  have two_eq_zero : (2 : ZMod 2) = 0 := by decide
  simp only [d₃, gParityCochain, toAdd_mul, sub_eq_add]
  linear_combination h +
    (gParity K Γ (a.toAdd + b.toAdd) c.toAdd d.toAdd +
      gParity K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd)) * two_eq_zero

/-- The five-term identity extracted from the nine faces of `K₅`.  The
three square faces are precisely the three summands of `p ∪₁ p`. -/
theorem gChiCanon_five_term :
    gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
        gChiCanonUnit K Γ a b c (d + e)
      = sgn
          (gParity K Γ a b c * gParity K Γ (a + b + c) d e +
            gParity K Γ b c d * gParity K Γ a (b + c + d) e +
            gParity K Γ c d e * gParity K Γ a b (c + d + e)) *
          (gChiCanonUnit K Γ (a + b) c d e *
            gChiCanonUnit K Γ a b (c + d) e * gChiCanonUnit K Γ a b c d) := by
  let s1 : Kˣ := sgn (gParity K Γ a b c * gParity K Γ (a + b + c) d e)
  let s2 : Kˣ := sgn (gParity K Γ b c d * gParity K Γ a (b + c + d) e)
  let s3 : Kˣ := sgn (gParity K Γ c d e * gParity K Γ a b (c + d + e))
  have hBoundary :
      gChiCanonUnit K Γ a b c d *
          (gChiCanonUnit K Γ a b (c + d) e * gChiCanonUnit K Γ (a + b) c d e)
        = s3 * (s2 *
            (gChiCanonUnit K Γ b c d e *
              (gChiCanonUnit K Γ a (b + c) d e *
                (s1 * gChiCanonUnit K Γ a b c (d + e))))) := by
    apply Units.ext
    exact chain_scalar_identity K Γ a b c d e
  have hBoundary' :
      gChiCanonUnit K Γ (a + b) c d e * gChiCanonUnit K Γ a b (c + d) e *
          gChiCanonUnit K Γ a b c d
        = (s1 * s2 * s3) *
            (gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
              gChiCanonUnit K Γ a b c (d + e)) := by
    calc
      _ = gChiCanonUnit K Γ a b c d *
          (gChiCanonUnit K Γ a b (c + d) e * gChiCanonUnit K Γ (a + b) c d e) := by
            ac_rfl
      _ = _ := hBoundary
      _ = _ := by ac_rfl
  have hSignSquare : (s1 * s2 * s3) * (s1 * s2 * s3) = 1 := by
    calc
      _ = (s1 * s1) * (s2 * s2) * (s3 * s3) := by ac_rfl
      _ = 1 := by simp [s1, s2, s3]
  have hReverse :
      gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
          gChiCanonUnit K Γ a b c (d + e)
        = (s1 * s2 * s3) *
            (gChiCanonUnit K Γ (a + b) c d e * gChiCanonUnit K Γ a b (c + d) e *
              gChiCanonUnit K Γ a b c d) := by
    calc
      _ = 1 * (gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
          gChiCanonUnit K Γ a b c (d + e)) := by rw [one_mul]
      _ = ((s1 * s2 * s3) * (s1 * s2 * s3)) *
          (gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
            gChiCanonUnit K Γ a b c (d + e)) := by rw [hSignSquare]
      _ = (s1 * s2 * s3) *
          ((s1 * s2 * s3) *
            (gChiCanonUnit K Γ b c d e * gChiCanonUnit K Γ a (b + c) d e *
              gChiCanonUnit K Γ a b c (d + e))) := by ac_rfl
      _ = _ := by rw [← hBoundary']
  have hSign :
      s1 * s2 * s3 =
        sgn
          (gParity K Γ a b c * gParity K Γ (a + b + c) d e +
            gParity K Γ b c d * gParity K Γ a (b + c + d) e +
            gParity K Γ c d e * gParity K Γ a b (c + d + e)) := by
    simp only [s1, s2, s3, sgn_add]
  rw [← hSign]
  exact hReverse

/-- **The canonical supercocycle equation**
`δχ = (-1)^(p ∪₁ p)` for every division fusion gauge. -/
theorem gChiCanon_supercocycle
    (a b c d e : Multiplicative G) :
    dm₄ (gChiCanonCochain K Γ) a b c d e =
      sgn (cupOne₃₃ (gParityCochain K Γ) (gParityCochain K Γ) a b c d e) := by
  have hFive := gChiCanon_five_term K Γ a.toAdd b.toAdd c.toAdd d.toAdd e.toAdd
  have hCup :
      gParity K Γ a.toAdd b.toAdd c.toAdd *
            gParity K Γ (a.toAdd + b.toAdd + c.toAdd) d.toAdd e.toAdd +
          gParity K Γ b.toAdd c.toAdd d.toAdd *
            gParity K Γ a.toAdd (b.toAdd + c.toAdd + d.toAdd) e.toAdd +
          gParity K Γ c.toAdd d.toAdd e.toAdd *
            gParity K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd + e.toAdd)
        = cupOne₃₃ (gParityCochain K Γ) (gParityCochain K Γ) a b c d e := by
    simp only [cupOne₃₃, gParityCochain, toAdd_mul]
    ring
  simp only [dm₄, gChiCanonCochain, toAdd_mul]
  calc
    _ = (gChiCanonUnit K Γ b.toAdd c.toAdd d.toAdd e.toAdd *
          gChiCanonUnit K Γ a.toAdd (b.toAdd + c.toAdd) d.toAdd e.toAdd *
          gChiCanonUnit K Γ a.toAdd b.toAdd c.toAdd (d.toAdd + e.toAdd)) *
        (gChiCanonUnit K Γ (a.toAdd + b.toAdd) c.toAdd d.toAdd e.toAdd *
          gChiCanonUnit K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd) e.toAdd *
          gChiCanonUnit K Γ a.toAdd b.toAdd c.toAdd d.toAdd)⁻¹ := by
            group
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (sgn
          (gParity K Γ a.toAdd b.toAdd c.toAdd *
              gParity K Γ (a.toAdd + b.toAdd + c.toAdd) d.toAdd e.toAdd +
            gParity K Γ b.toAdd c.toAdd d.toAdd *
              gParity K Γ a.toAdd (b.toAdd + c.toAdd + d.toAdd) e.toAdd +
            gParity K Γ c.toAdd d.toAdd e.toAdd *
              gParity K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd + e.toAdd)) *
          (gChiCanonUnit K Γ (a.toAdd + b.toAdd) c.toAdd d.toAdd e.toAdd *
            gChiCanonUnit K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd) e.toAdd *
            gChiCanonUnit K Γ a.toAdd b.toAdd c.toAdd d.toAdd)) *
        (gChiCanonUnit K Γ (a.toAdd + b.toAdd) c.toAdd d.toAdd e.toAdd *
          gChiCanonUnit K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd) e.toAdd *
          gChiCanonUnit K Γ a.toAdd b.toAdd c.toAdd d.toAdd)⁻¹ := by rw [hFive]
    _ = sgn
        (gParity K Γ a.toAdd b.toAdd c.toAdd *
            gParity K Γ (a.toAdd + b.toAdd + c.toAdd) d.toAdd e.toAdd +
          gParity K Γ b.toAdd c.toAdd d.toAdd *
            gParity K Γ a.toAdd (b.toAdd + c.toAdd + d.toAdd) e.toAdd +
          gParity K Γ c.toAdd d.toAdd e.toAdd *
            gParity K Γ a.toAdd b.toAdd (c.toAdd + d.toAdd + e.toAdd)) := by group
    _ = _ := congrArg sgn hCup

/-- The canonical pair `(p, χ)` attached to a division fusion gauge satisfies
both degree-four supercocycle equations. -/
theorem gCanon_isDegreeFourSuperCocycle :
    IsDegreeFourSuperCocycle (gParityCochain K Γ) (gChiCanonCochain K Γ) := by
  exact ⟨gParityCochain_cocycle K Γ, gChiCanon_supercocycle K Γ⟩

end GaugeChi

end Superfusion
