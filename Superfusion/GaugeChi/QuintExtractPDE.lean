/-
Superfusion / GaugeChi / QuintExtractPDE

Completion of the five spectator recognitions for the `(d+e)`-cluster
pentagon face.  The preceding files recognize edges 20, 17, 14, and 21.
Here edge 10 is recognized through the standard `omegaV14` presentation,
whose first stage cancels the opaque `gq4Close` output of `E10M`.
-/
import Superfusion.GaugeChi.QuintExtract4

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

/-! ### Recognition of edge 10 -/

section RecogE10M

private theorem fusionColumnCast_symm_eq_pde {x y : G} (h : x = y) :
    fusionColumnCast K Γ a h.symm = (fusionColumnCast K Γ a h).symm := by
  subst y
  rfl

private noncomputable def pdeE10ShiftedColumn
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    FusionColumn (Γ.fuse a (b + c + (d + e))) :=
  fusionColumnCast K Γ a (add_assoc (b + c) d e) x

private noncomputable def pdeE10GQ3Gen (u : FusionColumn (Γ.fuse b c))
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    GQ3 K Γ a b c (d + e) :=
  GQ3.mk K Γ a b c (d + e) u
    (GBR.mk Γ a (b + c) (d + e) q (pdeE10ShiftedColumn K Γ a b c d e x))

private noncomputable def pdeE10GQ4Gen (u : FusionColumn (Γ.fuse b c))
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    GQ4 K Γ a b c (d + e) :=
  GQ4.mk K Γ a b c (d + e)
    (gTCanon K Γ b c (d + e) (GBL.mk Γ b c (d + e) u q))
    (pdeE10ShiftedColumn K Γ a b c d e x)

private theorem GE3_e10_mk (u : FusionColumn (Γ.fuse b c))
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
        (gCanonRight K Γ b c (d + e)) (pdeE10GQ3Gen K Γ a b c d e u q x)
      = pdeE10GQ4Gen K Γ a b c d e u q x :=
  GE3_mk K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
    (gCanonRight K Γ b c (d + e)) u q (pdeE10ShiftedColumn K Γ a b c d e x)

/-- The inverse-close spelling of a split `GQ4(a,b+c,d,e)` generator. -/
private theorem pdeE10Close_raw (w : FusionColumn (Γ.fuse d e))
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    gq4Close K Γ a (b + c) d e
        (GQ4r.mk K Γ a (b + c) d e w
          (GBR.mk Γ a (b + c) (d + e) q
            (pdeE10ShiftedColumn K Γ a b c d e x)))
      = GQ4.mk K Γ a (b + c) d e (GBR.mk Γ (b + c) d e w q) x := by
  have hClose : gq4Close K Γ a (b + c) d e
        (GQ4r.mk K Γ a (b + c) d e w
          (GBR.mk Γ a (b + c) (d + e) q
            (pdeE10ShiftedColumn K Γ a b c d e x)))
      = GQ4.mk K Γ a (b + c) d e (GBR.mk Γ (b + c) d e w q)
          (fusionColumnCast K Γ a (add_assoc (b + c) d e).symm
            (pdeE10ShiftedColumn K Γ a b c d e x)) :=
    gq4Close_mk K Γ a (b + c) d e w q
      (pdeE10ShiftedColumn K Γ a b c d e x)
  rw [hClose]
  unfold pdeE10ShiftedColumn
  rw [fusionColumnCast_symm_eq_pde K Γ a (add_assoc (b + c) d e),
    LinearEquiv.symm_apply_apply]

/-- The ordinary split `V12` generator in the inverse-close spelling
consumed by `omegaV12`. -/
private theorem pdeE10V12_assoc (u : FusionColumn (Γ.fuse b c))
    (w : FusionColumn (Γ.fuse d e))
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    (gV12Assoc K Γ a b c d e).symm
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
          (GQ4 K Γ a (b + c) d e) u
          (gq4Close K Γ a (b + c) d e
            (GQ4r.mk K Γ a (b + c) d e w
              (GBR.mk Γ a (b + c) (d + e) q
                (pdeE10ShiftedColumn K Γ a b c d e x)))))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x := by
  rw [pdeE10Close_raw K Γ a b c d e]
  exact RelTensor.assoc_symm_mk K (Γ.D (b + c)).carrier
    (Γ.D (b + c + d + e)).carrier (FusionColumn (Γ.fuse b c))
    (GBR Γ (b + c) d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
    u (GBR.mk Γ (b + c) d e w q) x

private theorem omegaV12_e10_mk_of_mem {ju jw : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV12 K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
          (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x)
      = ((sgn (jw * ju) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ3 K Γ a b c (d + e)) w
            (pdeE10GQ3Gen K Γ a b c d e u q x) := by
  have h := omegaV12_mk_of_mem K Γ a b c d e hu hw
    (GBR.mk Γ a (b + c) (d + e) q
      (pdeE10ShiftedColumn K Γ a b c d e x))
  rw [pdeE10V12_assoc K Γ a b c d e] at h
  exact h

private noncomputable def pdeE10V14Gen (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ b c (d + e)) : GQ4 K Γ b c d e :=
  gq4Close K Γ b c d e (GQ4r.mk K Γ b c d e w p)

private noncomputable def pdeE10V14Input (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ b c (d + e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) : V14 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ4 K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e)))
    (pdeE10V14Gen K Γ b c d e w p) x

private theorem omegaV14_e10_mk (w : FusionColumn (Γ.fuse d e))
    (p : GBR Γ b c (d + e))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14 K Γ a b c d e
        (pdeE10V14Input K Γ a b c d e w p x)
      = RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
          (GQ4 K Γ a b c (d + e)) w
          (GQ4.mk K Γ a b c (d + e) p
            (pdeE10ShiftedColumn K Γ a b c d e x)) :=
  omegaV14_mk_of_mem K Γ a b c d e w p x

/-- Edge 10 recognition on a fully split homogeneous generator. -/
private theorem recog_E10M_generator {ju jw : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {w : FusionColumn (Γ.fuse d e)} (hw : w ∈ FusionColumn.grading (Γ.fuse d e) jw)
    (q : FusionColumn (Γ.fuse (b + c) (d + e)))
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    omegaV14 K Γ a b c d e
        (E10M K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x))
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
            (gCanonRight K Γ b c (d + e)))
          (gParity K Γ b c (d + e)) (hg3 K Γ a b c d e)
          (omegaV12 K Γ a b c d e
            (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
              (FusionColumn (Γ.fuse a (b + c + d + e)))
              (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x)) := by
  have sign_id : ∀ p ju jw : ZMod 2,
      jw * (p + ju) = jw * ju + p * jw := by decide
  have hGE : GE5 K Γ b c d e (gParity K Γ b c (d + e))
        (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)
        (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q))
      = ((sgn (jw * (gParity K Γ b c (d + e) + ju)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ b c d e w
            (gTCanon K Γ b c (d + e) (GBL.mk Γ b c (d + e) u q)) :=
    GE5_mk_of_mem K Γ b c d e (gParity K Γ b c (d + e))
      (gTCanon K Γ b c (d + e)).toLinearMap (gCanonHphi5 K Γ b c d e)
      hw hu q
  have hLHS : omegaV14 K Γ a b c d e
        (E10M K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x))
      = ((sgn (jw * (gParity K Γ b c (d + e) + ju)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ4 K Γ a b c (d + e)) w
            (pdeE10GQ4Gen K Γ a b c d e u q x) := by
    have hE10 : E10M K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x)
        = ((sgn (jw * (gParity K Γ b c (d + e) + ju)) : ℤˣ) : ℤ) •
            pdeE10V14Input K Γ a b c d e w
              (gTCanon K Γ b c (d + e) (GBL.mk Γ b c (d + e) u q)) x := by
      rw [E10M_mk, hGE]
      simp only [map_zsmul, LinearMap.smul_apply]
      rfl
    rw [hE10]
    refine (map_zsmul (omegaV14 K Γ a b c d e) _ _).trans ?_
    rw [omegaV14_e10_mk]
    rfl
  have hRHS : smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
        (GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
          (gCanonRight K Γ b c (d + e)))
        (gParity K Γ b c (d + e)) (hg3 K Γ a b c d e)
        (omegaV12 K Γ a b c d e
          (RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
            (FusionColumn (Γ.fuse a (b + c + d + e)))
            (GQ5.mk K Γ b c d e u (GBR.mk Γ (b + c) d e w q)) x))
      = ((sgn (jw * ju) * sgn (gParity K Γ b c (d + e) * jw) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (d + e)).carrier (FusionColumn (Γ.fuse d e))
            (GQ4 K Γ a b c (d + e)) w
            (pdeE10GQ4Gen K Γ a b c d e u q x) := by
    rw [omegaV12_e10_mk_of_mem K Γ a b c d e hu hw]
    refine (map_zsmul _ _ _).trans ?_
    rw [smap_mk_of_mem (Γ.D (d + e)).grading
        (FusionColumn.grading (Γ.fuse d e))
        (GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
          (gCanonRight K Γ b c (d + e)))
        (gParity K Γ b c (d + e)) (hg3 K Γ a b c d e) hw,
      GE3_e10_mk, smul_smul, ← Units.val_mul]
  rw [hLHS, hRHS]
  congr 2
  rw [← sgn_add, sign_id]

private noncomputable def pdeE10GQ5DomainGen (u : FusionColumn (Γ.fuse b c))
    (n : GBR Γ (b + c) d e) : GQ5 K Γ b c d e :=
  GQ5.mk K Γ b c d e u n

@[simp] private theorem pdeE10GQ5DomainGen_zero_right
    (u : FusionColumn (Γ.fuse b c)) :
    pdeE10GQ5DomainGen K Γ b c d e u 0 = 0 := by
  unfold pdeE10GQ5DomainGen GQ5.mk
  rw [map_zero]

@[simp] private theorem pdeE10GQ5DomainGen_add_right
    (u : FusionColumn (Γ.fuse b c)) (n n' : GBR Γ (b + c) d e) :
    pdeE10GQ5DomainGen K Γ b c d e u (n + n')
      = pdeE10GQ5DomainGen K Γ b c d e u n
        + pdeE10GQ5DomainGen K Γ b c d e u n' := by
  unfold pdeE10GQ5DomainGen GQ5.mk
  rw [map_add]

@[simp] private theorem pdeE10GQ5DomainGen_zero_left (n : GBR Γ (b + c) d e) :
    pdeE10GQ5DomainGen K Γ b c d e 0 n = 0 := by
  unfold pdeE10GQ5DomainGen GQ5.mk
  rw [map_zero, LinearMap.zero_apply]

@[simp] private theorem pdeE10GQ5DomainGen_add_left
    (u u' : FusionColumn (Γ.fuse b c)) (n : GBR Γ (b + c) d e) :
    pdeE10GQ5DomainGen K Γ b c d e (u + u') n
      = pdeE10GQ5DomainGen K Γ b c d e u n
        + pdeE10GQ5DomainGen K Γ b c d e u' n := by
  unfold pdeE10GQ5DomainGen GQ5.mk
  rw [map_add, LinearMap.add_apply]

private noncomputable def pdeE10V12DomainGen (m : GQ5 K Γ b c d e)
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) : V12 K Γ a b c d e :=
  RelTensor.mk K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) m x

@[simp] private theorem pdeE10V12DomainGen_zero
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pdeE10V12DomainGen K Γ a b c d e 0 x = 0 := by
  unfold pdeE10V12DomainGen
  rw [map_zero, LinearMap.zero_apply]
  rfl

@[simp] private theorem pdeE10V12DomainGen_add (m m' : GQ5 K Γ b c d e)
    (x : FusionColumn (Γ.fuse a (b + c + d + e))) :
    pdeE10V12DomainGen K Γ a b c d e (m + m') x
      = pdeE10V12DomainGen K Γ a b c d e m x
        + pdeE10V12DomainGen K Γ a b c d e m' x := by
  unfold pdeE10V12DomainGen
  rw [map_add, LinearMap.add_apply]
  rfl

@[elab_as_elim]
private theorem pdeE10GQ5_induction_on
    {motive : GQ5 K Γ b c d e → Prop} (m : GQ5 K Γ b c d e)
    (zero : motive 0)
    (mk : ∀ (u : FusionColumn (Γ.fuse b c)) (n : GBR Γ (b + c) d e),
      motive (pdeE10GQ5DomainGen K Γ b c d e u n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m :=
  RelTensor.induction_on K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c))
    (GBR Γ (b + c) d e) m zero mk add

@[elab_as_elim]
private theorem pdeE10V12_induction_on
    {motive : V12 K Γ a b c d e → Prop} (m : V12 K Γ a b c d e)
    (zero : motive 0)
    (mk : ∀ (n : GQ5 K Γ b c d e)
      (x : FusionColumn (Γ.fuse a (b + c + d + e))),
      motive (pdeE10V12DomainGen K Γ a b c d e n x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m :=
  RelTensor.induction_on K (Γ.D (b + c + d + e)).carrier (GQ5 K Γ b c d e)
    (FusionColumn (Γ.fuse a (b + c + d + e))) m zero mk add

/-- **`recog_E10M`**: edge 10 is the shifted third pentagon edge after
extracting the `F_{d,e}` spectator. -/
theorem recog_E10M :
    (omegaV14 K Γ a b c d e).toLinearMap ∘ₗ E10M K Γ a b c d e
      = smap (Γ.D (d + e)).grading (FusionColumn.grading (Γ.fuse d e))
          (GE3 K Γ a b c (d + e) (gTCanon K Γ b c (d + e)).toLinearMap
            (gCanonRight K Γ b c (d + e)))
          (gParity K Γ b c (d + e)) (hg3 K Γ a b c d e)
          ∘ₗ (omegaV12 K Γ a b c d e).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using pdeE10V12_induction_on K Γ a b c d e with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk m x =>
      induction m using pdeE10GQ5_induction_on K Γ b c d e with
      | zero => simp only [pdeE10V12DomainGen_zero, map_zero]
      | add m m' hm hm' =>
          simp only [pdeE10V12DomainGen_add, map_add, hm, hm']
      | mk u n =>
          induction n using GBR.induction_on_left_homog K Γ (b + c) d e with
          | zero =>
              simp only [pdeE10GQ5DomainGen_zero_right,
                pdeE10V12DomainGen_zero, map_zero]
          | add n n' hn hn' =>
              simp only [pdeE10GQ5DomainGen_add_right, pdeE10V12DomainGen_add,
                map_add, hn, hn']
          | homog jw w q hw =>
              induction u using DirectSum.Decomposition.inductionOn
                  (FusionColumn.grading (Γ.fuse b c)) with
              | zero =>
                  simp only [pdeE10GQ5DomainGen_zero_left,
                    pdeE10V12DomainGen_zero, map_zero]
              | add u u' hu hu' =>
                  simp only [pdeE10GQ5DomainGen_add_left, pdeE10V12DomainGen_add,
                    map_add, hu, hu']
              | homogeneous xu =>
                  exact recog_E10M_generator K Γ a b c d e xu.2 hw q x

end RecogE10M

end GaugeChi

end Superfusion
