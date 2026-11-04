/-
Superfusion / GaugeChi / QuintExtractPBC

Support for the `F_{b,c}` spectator extraction.  This file supplies the
one deferred PBC edge computation (edge 15), elementary transports across
`a+b+c = a+(b+c)`, and the five signed-equivariance witnesses needed by
the PBC recognition equations.
-/
import Superfusion.GaugeChi.QuintExtract6

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

/-! ### Elementary transports -/

/-- Successive first-index column casts compose. -/
theorem gColumnCastFst_trans (r : G) {x y z : G} (hxy : x = y)
    (hyz : y = z) (w : FusionColumn (Γ.fuse x r)) :
    gColumnCastFst K Γ r hyz (gColumnCastFst K Γ r hxy w)
      = gColumnCastFst K Γ r (hxy.trans hyz) w := by
  subst hxy
  subst hyz
  rfl

/-- `gGbrCastFst` on a split `GBR` generator. -/
theorem gGbrCastFst_mk (q r : G) {p p' : G} (h : p = p')
    (u : FusionColumn (Γ.fuse q r))
    (w : FusionColumn (Γ.fuse p (q + r))) :
    gGbrCastFst K Γ q r h (GBR.mk Γ p q r u w)
      = GBR.mk Γ p' q r u (gColumnCastFst K Γ (q + r) h w) := by
  subst h
  rfl

/-- Naturality of the canonical triple map under a propositional change
of its first index.  This is transport, not a new coherence axiom: after
substitution both sides are literally identical. -/
theorem gTCanon_cast_fst_mk (q r : G) {p p' : G} (h : p = p')
    (u : FusionColumn (Γ.fuse p q))
    (w : FusionColumn (Γ.fuse (p + q) r)) :
    gGbrCastFst K Γ q r h
        (gTCanon K Γ p q r (GBL.mk Γ p q r u w))
      = gTCanon K Γ p' q r
          (GBL.mk Γ p' q r (gColumnCastFst K Γ q h u)
            (gColumnCastFst K Γ r (congrArg (· + q) h) w)) := by
  subst h
  rfl

/-! ### Edge 15 on an extracted generator -/

private theorem gq3Assoc_symm_mk_pbc
    (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse a (b + c + d))) :
    (gq3Assoc K Γ a b c d).symm
        (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x))
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d)))
          (GBL.mk Γ b c d u v) x := by
  apply (gq3Assoc K Γ a b c d).injective
  rw [LinearEquiv.apply_symm_apply, gq3Assoc_mk]
  rfl

/-- Generator formula for `gV4Assoc`, with the second `GQ3Inner` factor
split but no use of `gTCanon`. -/
theorem gV4Assoc_mk_pbc
    (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse (b + c) d))
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    gV4Assoc K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t)
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (GBL Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) t)) := by
  have hA : gV4AssocA K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t)
      = RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
            (FusionColumn (Γ.fuse a (b + c + d))))
          (FusionColumn (Γ.fuse (a + b + c + d) e))
          (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
            (FusionColumn (Γ.fuse a (b + c + d)))
            (GBL.mk Γ b c d u v) x) t := by
    show RelTensor.map (gq3Assoc K Γ a b c d).symm.toLinearMap
        (LinearMap.id : FusionColumn (Γ.fuse (a + b + c + d) e) →ₗ[K] _)
        (gq3Assoc_symm_rightTotal K Γ a b c d) (fun _ _ => rfl)
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t) = _
    rw [RelTensor.map_mk, LinearMap.id_apply]
    exact congrArg
      (fun z => RelTensor.mk K (Γ.D (a + b + c + d)).carrier
        (RelTensor K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))))
        (FusionColumn (Γ.fuse (a + b + c + d) e)) z t)
      (gq3Assoc_symm_mk_pbc K Γ a b c d u v x)
  have hB := RelTensor.assoc_mk K (Γ.D (b + c + d)).carrier
    (Γ.D (a + b + c + d)).carrier (GBL Γ b c d)
    (FusionColumn (Γ.fuse a (b + c + d)))
    (FusionColumn (Γ.fuse (a + b + c + d) e))
    (GBL.mk Γ b c d u v) x t
  show gV4AssocC K Γ a b c d e
      (gV4AssocB K Γ a b c d e
        (gV4AssocA K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t))) = _
  rw [hA]
  refine (congrArg (fun z => gV4AssocC K Γ a b c d e z) hB).trans ?_
  show RelTensor.map (LinearMap.id : GBL Γ b c d →ₗ[K] GBL Γ b c d)
      (gFourCast K Γ a b c d e).toLinearMap (fun _ _ => rfl)
      (gFourCast_midSlot K Γ a b c d e)
      (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
        (RelTensor K (Γ.D (a + b + c + d)).carrier
          (FusionColumn (Γ.fuse a (b + c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)))
        (GBL.mk Γ b c d u v)
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (FusionColumn (Γ.fuse a (b + c + d)))
          (FusionColumn (Γ.fuse (a + b + c + d) e)) x t)) = _
  rw [RelTensor.map_mk, LinearMap.id_apply]
  exact congrArg
    (fun z => RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
      (GBL Γ a (b + c + d) e) (GBL.mk Γ b c d u v) z)
    (gFourCast_mk K Γ a b c d e x t)

/-- The shifted `GQ3` generator, relocated to a top-level definition so
the named `GBR`/`GQ3Inner` definitional equality is elaborated once. -/
private noncomputable def pbcV10GQ3GenMap
    (v : FusionColumn (Γ.fuse (b + c) d)) :
    GBR Γ a (b + c + d) e →ₗ[K] GQ3 K Γ a (b + c) d e :=
  GQ3.mk K Γ a (b + c) d e v

noncomputable def pbcV10GQ3Gen
    (v : FusionColumn (Γ.fuse (b + c) d))
    (y : GBR Γ a (b + c + d) e) : GQ3 K Γ a (b + c) d e :=
  pbcV10GQ3GenMap K Γ a b c d e v y

theorem pbcV10GQ3Gen_eq
    (v : FusionColumn (Γ.fuse (b + c) d))
    (y : GBR Γ a (b + c + d) e) :
    pbcV10GQ3Gen K Γ a b c d e v y
      = GQ3.mk K Γ a (b + c) d e v y :=
  rfl

@[simp] private theorem pbcV10GQ3Gen_zero
    (v : FusionColumn (Γ.fuse (b + c) d)) :
    pbcV10GQ3Gen K Γ a b c d e v 0 = 0 := by
  exact map_zero (pbcV10GQ3GenMap K Γ a b c d e v)

@[simp] private theorem pbcV10GQ3Gen_add
    (v : FusionColumn (Γ.fuse (b + c) d))
    (y y' : GBR Γ a (b + c + d) e) :
    pbcV10GQ3Gen K Γ a b c d e v (y + y')
      = pbcV10GQ3Gen K Γ a b c d e v y
        + pbcV10GQ3Gen K Γ a b c d e v y' := by
  exact map_add (pbcV10GQ3GenMap K Γ a b c d e v) y y'

private theorem gV10Assoc_symm_generator_pbc
    (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse (b + c + d) e))
    (t : FusionColumn (Γ.fuse a (b + c + d + e))) :
    (gV10Assoc K Γ a b c d e).symm
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (GBR Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
          (GBR.mk Γ a (b + c + d) e w t))
      = RelTensor.mk K (Γ.D (b + c + d + e)).carrier
          (GQ1 K Γ b c d e) (FusionColumn (Γ.fuse a (b + c + d + e)))
          (GQ1.mk K Γ b c d e (GBL.mk Γ b c d u v) w) t :=
  RelTensor.assoc_symm_mk K (Γ.D (b + c + d)).carrier
    (Γ.D (b + c + d + e)).carrier (GBL Γ b c d)
    (FusionColumn (Γ.fuse (b + c + d) e))
    (FusionColumn (Γ.fuse a (b + c + d + e)))
    (GBL.mk Γ b c d u v) w t

/-- Extracting `F_{b,c}` after undoing `gV10Assoc` only reassociates the
remaining opaque `GBR(a,b+c+d,e)` factor. -/
theorem omegaPbcV10_gV10Assoc_symm_mk
    (u : FusionColumn (Γ.fuse b c))
    (v : FusionColumn (Γ.fuse (b + c) d))
    (y : GBR Γ a (b + c + d) e) :
    omegaPbcV10 K Γ a b c d e
        ((gV10Assoc K Γ a b c d e).symm
          (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
            (GBR Γ a (b + c + d) e) (GBL.mk Γ b c d u v) y))
      = RelTensor.mk K (Γ.D (b + c)).carrier
          (FusionColumn (Γ.fuse b c)) (GQ3 K Γ a (b + c) d e) u
          (pbcV10GQ3Gen K Γ a b c d e v y) := by
  induction y using GBR.induction_on K Γ a (b + c + d) e with
  | zero => simp only [map_zero, pbcV10GQ3Gen_zero]
  | add y y' hy hy' => simp only [map_add, pbcV10GQ3Gen_add, hy, hy']
  | mk w t =>
      rw [gV10Assoc_symm_generator_pbc, omegaPbcV10_mk]
      rfl

/-- The deferred edge-15 generator formula.  The output of `gTCanon` is
kept opaque; `omegaPbcV10_gV10Assoc_symm_mk` is precisely what later
extracts the spectator without decomposing it. -/
theorem E15M_leaf_pbc {ju jv : ZMod 2}
    {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) ju)
    {v : FusionColumn (Γ.fuse (b + c) d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    (x : FusionColumn (Γ.fuse a (b + c + d)))
    (t : FusionColumn (Γ.fuse (a + b + c + d) e)) :
    E15M K Γ a b c d e
        (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
          (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t)
      = ((sgn (gParity K Γ a (b + c + d) e * (ju + jv)) : ℤˣ) : ℤ) •
          (gV10Assoc K Γ a b c d e).symm
            (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
              (GBR Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
              (gTCanon K Γ a (b + c + d) e
                (GBL.mk Γ a (b + c + d) e x
                  (gColumnCastFst K Γ e (add_assoc_four a b c d) t)))) := by
  have hV4 := gV4Assoc_mk_pbc K Γ a b c d e u v x t
  have hstep : gE15Step K Γ a b c d e
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (GBL Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) t)))
      = ((sgn (gParity K Γ a (b + c + d) e * (ju + jv)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
            (GBR Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
            (gTCanon K Γ a (b + c + d) e
              (GBL.mk Γ a (b + c + d) e x
                (gColumnCastFst K Γ e (add_assoc_four a b c d) t))) := by
    change smap (Γ.D (b + c + d)).grading (GBL.grading Γ b c d)
        (gTCanon K Γ a (b + c + d) e).toLinearMap
        (gParity K Γ a (b + c + d) e)
        (gCanonMidSlot K Γ a (b + c + d) e)
        (RelTensor.mk K (Γ.D (b + c + d)).carrier (GBL Γ b c d)
          (GBL Γ a (b + c + d) e) (GBL.mk Γ b c d u v)
          (GBL.mk Γ a (b + c + d) e x
            (gColumnCastFst K Γ e (add_assoc_four a b c d) t))) = _
    exact smap_mk_of_mem (Γ.D (b + c + d)).grading
      (GBL.grading Γ b c d) (gTCanon K Γ a (b + c + d) e).toLinearMap
      (gParity K Γ a (b + c + d) e)
      (gCanonMidSlot K Γ a (b + c + d) e)
      (GBL.mk_mem_grading Γ b c d hu hv)
      (GBL.mk Γ a (b + c + d) e x
        (gColumnCastFst K Γ e (add_assoc_four a b c d) t))
  show (gV10Assoc K Γ a b c d e).symm
      (gE15Step K Γ a b c d e
        (gV4Assoc K Γ a b c d e
          (RelTensor.mk K (Γ.D (a + b + c + d)).carrier
            (GQ3 K Γ a b c d) (FusionColumn (Γ.fuse (a + b + c + d) e))
            (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v x)) t))) = _
  rw [hV4, hstep, map_zsmul]

/-! ### The five PBC spectator-slot equivariance witnesses -/

theorem pbcHg1 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ1 K Γ a (b + c) d e,
        GE1 K Γ a (b + c) d e
            (gTCanon K Γ a (b + c) d).toLinearMap
            (gCanonRight K Γ a (b + c) d) (τ • n)
          = ((sgn (gParity K Γ a (b + c) d * i) : ℤˣ) : ℤ) •
              (τ • GE1 K Γ a (b + c) d e
                (gTCanon K Γ a (b + c) d).toLinearMap
                (gCanonRight K Γ a (b + c) d) n) :=
  fun _i _τ hτ n => GE1.comp_bslot K Γ a (b + c) d e
    (gTCanon K Γ a (b + c) d).toLinearMap
    (gCanonRight K Γ a (b + c) d)
    (gCanonMidSlot K Γ a (b + c) d hτ) n

theorem pbcHg2 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ2 K Γ a (b + c) d e,
        GE2 K Γ a (b + c) d e
            (gParity K Γ a (b + c + d) e)
            (gt2Canon K Γ a (b + c) d e
              (gTCanon K Γ a (b + c + d) e)).toLinearMap
            (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
              (gParity K Γ a (b + c + d) e)
              (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)) (τ • n)
          = ((sgn (gParity K Γ a (b + c + d) e * i) : ℤˣ) : ℤ) •
              (τ • GE2 K Γ a (b + c) d e
                (gParity K Γ a (b + c + d) e)
                (gt2Canon K Γ a (b + c) d e
                  (gTCanon K Γ a (b + c + d) e)).toLinearMap
                (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
                  (gParity K Γ a (b + c + d) e)
                  (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)) n) :=
  fun _i _τ hτ n => GE2.comp_bslot_univ K Γ a (b + c) d e
    (gParity K Γ a (b + c + d) e)
    (gt2Canon K Γ a (b + c) d e
      (gTCanon K Γ a (b + c + d) e)).toLinearMap
    (gt2Canon_bcSlot K Γ (gTCanon K Γ a (b + c + d) e)
      (gParity K Γ a (b + c + d) e)
      (gTCanon_mem_gInterSpace K Γ a (b + c + d) e)) hτ n

theorem pbcHg3 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ3 K Γ a (b + c) d e,
        GE3 K Γ a (b + c) d e
            (gTCanon K Γ (b + c) d e).toLinearMap
            (gCanonRight K Γ (b + c) d e) (τ • n)
          = ((sgn (gParity K Γ (b + c) d e * i) : ℤˣ) : ℤ) •
              (τ • GE3 K Γ a (b + c) d e
                (gTCanon K Γ (b + c) d e).toLinearMap
                (gCanonRight K Γ (b + c) d e) n) :=
  fun _i _τ hτ n => GE3.comp_bslot_univ K Γ a (b + c) d e
    (gTCanon K Γ (b + c) d e).toLinearMap
    (gCanonRight K Γ (b + c) d e)
    (gCanonHphi4 K Γ b c d e hτ) n

theorem pbcHg4 :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ1 K Γ a (b + c) d e,
        GE4 K Γ a (b + c) d e
            (gParity K Γ (a + (b + c)) d e)
            (gTCanon K Γ (a + (b + c)) d e).toLinearMap
            (gCanonHphi4 K Γ a (b + c) d e) (τ • n)
          = ((sgn (gParity K Γ (a + (b + c)) d e * i) : ℤˣ) : ℤ) •
              (τ • GE4 K Γ a (b + c) d e
                (gParity K Γ (a + (b + c)) d e)
                (gTCanon K Γ (a + (b + c)) d e).toLinearMap
                (gCanonHphi4 K Γ a (b + c) d e) n) :=
  fun _i _τ hτ n => GE4.comp_bslot_univ K Γ a (b + c) d e
    (gParity K Γ (a + (b + c)) d e)
    (gTCanon K Γ (a + (b + c)) d e).toLinearMap
    (gCanonHphi4 K Γ a (b + c) d e) hτ n

/-- The fifth shifted pentagon edge including its closing map. -/
noncomputable def pbcE17Map : GQ5 K Γ a (b + c) d e →ₗ[K]
    GQ4 K Γ a (b + c) d e :=
  (gq4Close K Γ a (b + c) d e).toLinearMap.comp
    (GE5 K Γ a (b + c) d e
      (gParity K Γ a (b + c) (d + e))
      (gTCanon K Γ a (b + c) (d + e)).toLinearMap
      (gCanonHphi5 K Γ a (b + c) d e))

theorem pbcE17Map_hg :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (b + c)).carrier⦄,
      τ ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ5 K Γ a (b + c) d e,
        pbcE17Map K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ a (b + c) (d + e) * i) : ℤˣ) : ℤ) •
              (τ • pbcE17Map K Γ a b c d e n) := by
  intro i τ hτ n
  show gq4Close K Γ a (b + c) d e
      (GE5 K Γ a (b + c) d e
        (gParity K Γ a (b + c) (d + e))
        (gTCanon K Γ a (b + c) (d + e)).toLinearMap
        (gCanonHphi5 K Γ a (b + c) d e) (τ • n)) = _
  rw [GE5.comp_bslot_univ K Γ a (b + c) d e
      (gParity K Γ a (b + c) (d + e))
      (gTCanon K Γ a (b + c) (d + e)).toLinearMap
      (gCanonHphi5 K Γ a (b + c) d e) hτ
      (gCanonMidSlot K Γ a (b + c) (d + e) hτ) n,
    map_zsmul, GQ4Close.comp_bslot_univ K Γ a (b + c) d e hτ]
  rfl

end GaugeChi

end Superfusion
