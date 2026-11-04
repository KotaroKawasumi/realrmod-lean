/-
Superfusion / Super / WallFactor

Milestone M7f-2b (part ii): **the Wall-map factorization and the
super-Azumaya `ᵍ⊗`-closure** —

  `Wall_{A ᵍ⊗ B} = endTensorHom ∘ (Wall_A ᵍ⊗ Wall_B) ∘ gmiddleFour
                     ∘ (id ᵍ⊗ sopDistrib.symm)`
  (`wall_factorization`),

whence, for finite free `A`, `B`:

  `IsSuperAzumaya 𝒜 → IsSuperAzumaya ℬ →
   IsSuperAzumaya (tensorGrading 𝒜 ℬ)`
  (`isSuperAzumaya_tensorGrading`)

— the graded tensor product of super-Azumaya algebras is
super-Azumaya: the Wall map of the product is a composition of
bijections.  Classically this is the closure of central simplicity
under `ᵍ⊗`, proven by a minimal-length ideal argument; here it falls
out of the factorization, with every sign already absorbed in the
M7f-1 reshuffling kit and the four innermost identities (M7f-2b-i).

The factorization is proven by extensionality on pure tensors: both
sides are algebra maps, so it suffices to compare them after
composing with the two inclusions, and there the innermost identities
(La)–(Rb) apply, decomposing the remaining slots into homogeneous
parts.
-/
import Superfusion.Super.WallFactorParts

namespace Superfusion

open TensorProduct
open GradedTensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-! ### The chain -/

/-- Step 1: distribute the super-opposite over the second factor. -/
private noncomputable def wallStep1 :
    ((tensorGrading 𝒜 ℬ) ᵍ⊗[K]
        (SuperOp.grading (tensorGrading 𝒜 ℬ))) ≃ₐ[K]
      ((tensorGrading 𝒜 ℬ) ᵍ⊗[K]
        (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ))) :=
  gcongr (tensorGrading 𝒜 ℬ) (SuperOp.grading (tensorGrading 𝒜 ℬ))
    (tensorGrading 𝒜 ℬ)
    (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ))
    (AlgEquiv.refl) (sopDistrib 𝒜 ℬ).symm
    (fun _ => Submodule.map_id _)
    (map_grading_symm _ _ (sopDistrib 𝒜 ℬ) (sopDistrib_map_grading 𝒜 ℬ))

/-- Step 3: the two Wall maps, tensored. -/
private noncomputable def wallGmap :
    ((tensorGrading 𝒜 (SuperOp.grading 𝒜)) ᵍ⊗[K]
        (tensorGrading ℬ (SuperOp.grading ℬ))) →ₐ[K]
      ((endGrading 𝒜) ᵍ⊗[K] (endGrading ℬ)) :=
  gmap (tensorGrading 𝒜 (SuperOp.grading 𝒜))
    (tensorGrading ℬ (SuperOp.grading ℬ))
    (endGrading 𝒜) (endGrading ℬ)
    (superMulLeftRight 𝒜) (superMulLeftRight ℬ)
    (superMulLeftRight_isHomogeneous 𝒜)
    (superMulLeftRight_isHomogeneous ℬ)

/-- The right-hand side of the Wall-map factorization. -/
noncomputable def wallTensorChain :
    SuperEnvelope (tensorGrading 𝒜 ℬ) →ₐ[K]
      Module.End K (𝒜 ᵍ⊗[K] ℬ) :=
  (endTensorHom 𝒜 ℬ).comp
    ((wallGmap 𝒜 ℬ).comp
      (((gmiddleFour 𝒜 ℬ (SuperOp.grading 𝒜)
          (SuperOp.grading ℬ)).toAlgHom).comp
        (wallStep1 𝒜 ℬ).toAlgHom))

private theorem wallTensorChain_apply
    (v : SuperEnvelope (tensorGrading 𝒜 ℬ)) :
    wallTensorChain 𝒜 ℬ v
      = endTensorHom 𝒜 ℬ (wallGmap 𝒜 ℬ
          (gmiddleFour 𝒜 ℬ (SuperOp.grading 𝒜) (SuperOp.grading ℬ)
            (wallStep1 𝒜 ℬ v))) := rfl

/-- The unit of a graded tensor product as a pure tensor of units:
proved via the underlying-module identification `of` rather than by
`rfl`, since the two layers of `deriving`-generated `One` instances
(`SuperOp` on top of `GradedTensorProduct`) make direct defeq
checking blow up. -/
private theorem gtmul_one_one {C : Type*} [Ring C] [Algebra K C]
    {D : Type*} [Ring D] [Algebra K D] (𝒞 : ZMod 2 → Submodule K C)
    (𝒟 : ZMod 2 → Submodule K D) [GradedAlgebra 𝒞] [GradedAlgebra 𝒟] :
    ((1 : C) ᵍ⊗ₜ[K] (1 : D) : 𝒞 ᵍ⊗[K] 𝒟) = 1 := by
  show of K 𝒞 𝒟 ((1 : C) ⊗ₜ[K] (1 : D)) = 1
  rw [← Algebra.TensorProduct.one_def, of_one]

/-! ### The left branch -/

private theorem chainL_homog {jb : ZMod 2} (a : A) {b : B}
    (hb : b ∈ ℬ jb) :
    wallTensorChain 𝒜 ℬ
        (includeLeft (tensorGrading 𝒜 ℬ)
          (SuperOp.grading (tensorGrading 𝒜 ℬ)) (a ᵍ⊗ₜ[K] b))
      = superMulLeftRight (tensorGrading 𝒜 ℬ)
          (includeLeft (tensorGrading 𝒜 ℬ)
            (SuperOp.grading (tensorGrading 𝒜 ℬ)) (a ᵍ⊗ₜ[K] b)) := by
  have hincl : includeLeft (tensorGrading 𝒜 ℬ)
      (SuperOp.grading (tensorGrading 𝒜 ℬ)) (a ᵍ⊗ₜ[K] b)
      = (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K]
        (1 : SuperOp (tensorGrading 𝒜 ℬ)) := rfl
  rw [hincl,
    wallTensorChain_apply,
    show wallStep1 𝒜 ℬ ((a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K]
        (1 : SuperOp (tensorGrading 𝒜 ℬ)))
      = (a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K]
        ((1 : SuperOp 𝒜) ᵍ⊗ₜ[K] (1 : SuperOp ℬ)) from by
      rw [wallStep1, gcongr_tmul, AlgEquiv.coe_refl, id_eq, map_one,
        gtmul_one_one],
    gmiddleFour_tmul 𝒜 ℬ (SuperOp.grading 𝒜) (SuperOp.grading ℬ)
      a (1 : SuperOp ℬ) hb (SetLike.one_mem_graded (SuperOp.grading 𝒜)),
    zero_mul, uzpow_zero, one_smul,
    show wallGmap 𝒜 ℬ ((a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜)) ᵍ⊗ₜ[K]
        (b ᵍ⊗ₜ[K] (1 : SuperOp ℬ)))
      = (superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜)))
        ᵍ⊗ₜ[K] (superMulLeftRight ℬ (b ᵍ⊗ₜ[K] (1 : SuperOp ℬ))) from
      gmap_tmul _ _ _ _ _ _ _ _ _ _,
    show superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜))
      = Algebra.lmul K A a from
      AlgHom.congr_fun (superMulLeftRight_comp_includeLeft 𝒜) a,
    show superMulLeftRight ℬ (b ᵍ⊗ₜ[K] (1 : SuperOp ℬ))
      = Algebra.lmul K B b from
      AlgHom.congr_fun (superMulLeftRight_comp_includeLeft ℬ) b,
    endTensorHom_tmul, ← lmul_tmul_one 𝒜 ℬ a, ← lmul_one_tmul 𝒜 ℬ hb,
    ← map_mul,
    show ((a ᵍ⊗ₜ[K] (1 : B)) * ((1 : A) ᵍ⊗ₜ[K] b) : 𝒜 ᵍ⊗[K] ℬ)
      = a ᵍ⊗ₜ[K] b from tmul_one_mul_one_tmul 𝒜 ℬ a b,
    show superMulLeftRight (tensorGrading 𝒜 ℬ)
        ((a ᵍ⊗ₜ[K] b) ᵍ⊗ₜ[K] (1 : SuperOp (tensorGrading 𝒜 ℬ)))
      = Algebra.lmul K (𝒜 ᵍ⊗[K] ℬ) (a ᵍ⊗ₜ[K] b) from
      AlgHom.congr_fun
        (superMulLeftRight_comp_includeLeft (tensorGrading 𝒜 ℬ))
        (a ᵍ⊗ₜ[K] b)]

private theorem chainL :
    (wallTensorChain 𝒜 ℬ).comp
        (includeLeft (tensorGrading 𝒜 ℬ)
          (SuperOp.grading (tensorGrading 𝒜 ℬ)))
      = (superMulLeftRight (tensorGrading 𝒜 ℬ)).comp
          (includeLeft (tensorGrading 𝒜 ℬ)
            (SuperOp.grading (tensorGrading 𝒜 ℬ))) := by
  refine galgHom_ext 𝒜 ℬ fun a b => ?_
  simp only [AlgHom.comp_apply]
  have hb := evenPart_add_oddPart ℬ b
  calc wallTensorChain 𝒜 ℬ (includeLeft _ _ (a ᵍ⊗ₜ[K] b))
      = wallTensorChain 𝒜 ℬ (includeLeft _ _
          (a ᵍ⊗ₜ[K] evenPart ℬ b))
        + wallTensorChain 𝒜 ℬ (includeLeft _ _
          (a ᵍ⊗ₜ[K] oddPart ℬ b)) := by
        rw [← map_add, ← map_add, ← gtmul_add 𝒜 ℬ, hb]
    _ = superMulLeftRight (tensorGrading 𝒜 ℬ) (includeLeft _ _
          (a ᵍ⊗ₜ[K] evenPart ℬ b))
        + superMulLeftRight (tensorGrading 𝒜 ℬ) (includeLeft _ _
          (a ᵍ⊗ₜ[K] oddPart ℬ b)) := by
        rw [chainL_homog 𝒜 ℬ a (evenPart_mem ℬ b),
          chainL_homog 𝒜 ℬ a (oddPart_mem ℬ b)]
    _ = superMulLeftRight (tensorGrading 𝒜 ℬ)
          (includeLeft _ _ (a ᵍ⊗ₜ[K] b)) := by
        rw [← map_add, ← map_add, ← gtmul_add 𝒜 ℬ, hb]

/-! ### The right branch -/

private theorem chainR_homog {ja jb : ZMod 2} {a : A} {b : B}
    (ha : a ∈ 𝒜 ja) (hb : b ∈ ℬ jb) :
    wallTensorChain 𝒜 ℬ
        (includeRight (tensorGrading 𝒜 ℬ)
          (SuperOp.grading (tensorGrading 𝒜 ℬ))
          (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)))
      = superMulLeftRight (tensorGrading 𝒜 ℬ)
          (includeRight (tensorGrading 𝒜 ℬ)
            (SuperOp.grading (tensorGrading 𝒜 ℬ))
            (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b))) := by
  have hsymm : (sopDistrib 𝒜 ℬ).symm
      (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b))
      = SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b := by
    rw [AlgEquiv.symm_apply_eq, sopDistrib_tmul]
  have hop : SuperOp.op 𝒜 a ∈ SuperOp.grading 𝒜 ja := ha
  rw [show includeRight (tensorGrading 𝒜 ℬ)
      (SuperOp.grading (tensorGrading 𝒜 ℬ))
      (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b))
      = (1 : 𝒜 ᵍ⊗[K] ℬ) ᵍ⊗ₜ[K]
        (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)) from rfl,
    wallTensorChain_apply,
    show wallStep1 𝒜 ℬ ((1 : 𝒜 ᵍ⊗[K] ℬ) ᵍ⊗ₜ[K]
        (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)))
      = (1 : 𝒜 ᵍ⊗[K] ℬ) ᵍ⊗ₜ[K]
        (SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b) from by
      rw [wallStep1, gcongr_tmul, AlgEquiv.coe_refl, id_eq, hsymm],
    show ((1 : 𝒜 ᵍ⊗[K] ℬ) ᵍ⊗ₜ[K]
        (SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b) :
        (tensorGrading 𝒜 ℬ) ᵍ⊗[K]
          (tensorGrading (SuperOp.grading 𝒜) (SuperOp.grading ℬ)))
      = ((1 : A) ᵍ⊗ₜ[K] (1 : B)) ᵍ⊗ₜ[K]
        (SuperOp.op 𝒜 a ᵍ⊗ₜ[K] SuperOp.op ℬ b) from rfl,
    gmiddleFour_tmul 𝒜 ℬ (SuperOp.grading 𝒜) (SuperOp.grading ℬ)
      (1 : A) (SuperOp.op ℬ b) (SetLike.one_mem_graded ℬ) hop,
    mul_zero, uzpow_zero, one_smul,
    show wallGmap 𝒜 ℬ (((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 a) ᵍ⊗ₜ[K]
        ((1 : B) ᵍ⊗ₜ[K] SuperOp.op ℬ b))
      = (superMulLeftRight 𝒜 ((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 a))
        ᵍ⊗ₜ[K]
        (superMulLeftRight ℬ ((1 : B) ᵍ⊗ₜ[K] SuperOp.op ℬ b)) from
      gmap_tmul _ _ _ _ _ _ _ _ _ _,
    show superMulLeftRight 𝒜 ((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 a)
      = signedRightMul 𝒜 (SuperOp.op 𝒜 a) from
      AlgHom.congr_fun (superMulLeftRight_comp_includeRight 𝒜)
        (SuperOp.op 𝒜 a),
    show superMulLeftRight ℬ ((1 : B) ᵍ⊗ₜ[K] SuperOp.op ℬ b)
      = signedRightMul ℬ (SuperOp.op ℬ b) from
      AlgHom.congr_fun (superMulLeftRight_comp_includeRight ℬ)
        (SuperOp.op ℬ b),
    endTensorHom_tmul, ← sRM_op_tmul_one 𝒜 ℬ ha,
    ← sRM_op_one_tmul 𝒜 ℬ hb,
    show (a ᵍ⊗ₜ[K] (1 : B) : 𝒜 ᵍ⊗[K] ℬ) = includeLeft 𝒜 ℬ a from
      (GradedTensorProduct.includeLeft_apply 𝒜 ℬ a).symm,
    show ((1 : A) ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ) = includeRight 𝒜 ℬ b from
      (GradedTensorProduct.includeRight_apply 𝒜 ℬ b).symm,
    ← map_mul,
    op_incl_mul_op_incl_of_mem 𝒜 ℬ ha hb,
    show superMulLeftRight (tensorGrading 𝒜 ℬ)
        ((1 : 𝒜 ᵍ⊗[K] ℬ) ᵍ⊗ₜ[K]
          (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)))
      = signedRightMul (tensorGrading 𝒜 ℬ)
          (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)) from
      AlgHom.congr_fun
        (superMulLeftRight_comp_includeRight (tensorGrading 𝒜 ℬ))
        (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b))]

private theorem chainR :
    (wallTensorChain 𝒜 ℬ).comp
        (includeRight (tensorGrading 𝒜 ℬ)
          (SuperOp.grading (tensorGrading 𝒜 ℬ)))
      = (superMulLeftRight (tensorGrading 𝒜 ℬ)).comp
          (includeRight (tensorGrading 𝒜 ℬ)
            (SuperOp.grading (tensorGrading 𝒜 ℬ))) := by
  refine AlgHom.ext fun w => ?_
  simp only [AlgHom.comp_apply]
  -- write w = op z, decompose z into pure tensors is not needed:
  -- both sides are linear in w; reduce to w = op (z) with z a sum of
  -- pure tensors via the linear identification.
  have key : ∀ t : A ⊗[K] B,
      wallTensorChain 𝒜 ℬ (includeRight _ _
          (SuperOp.op (tensorGrading 𝒜 ℬ) (of K 𝒜 ℬ t)))
        = superMulLeftRight (tensorGrading 𝒜 ℬ) (includeRight _ _
            (SuperOp.op (tensorGrading 𝒜 ℬ) (of K 𝒜 ℬ t))) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
        rw [show of K 𝒜 ℬ (a ⊗ₜ[K] b) = a ᵍ⊗ₜ[K] b from rfl]
        have ha := evenPart_add_oddPart 𝒜 a
        have hb := evenPart_add_oddPart ℬ b
        have hsplit : (a ᵍ⊗ₜ[K] b : 𝒜 ᵍ⊗[K] ℬ)
            = ((evenPart 𝒜 a ᵍ⊗ₜ[K] evenPart ℬ b
                + evenPart 𝒜 a ᵍ⊗ₜ[K] oddPart ℬ b)
              + oddPart 𝒜 a ᵍ⊗ₜ[K] evenPart ℬ b)
              + oddPart 𝒜 a ᵍ⊗ₜ[K] oddPart ℬ b := by
          conv_lhs => rw [← ha, ← hb]
          rw [add_gtmul 𝒜 ℬ, gtmul_add 𝒜 ℬ, gtmul_add 𝒜 ℬ]
          abel
        have expand : ∀ (F : SuperEnvelope (tensorGrading 𝒜 ℬ) →ₐ[K]
            Module.End K (𝒜 ᵍ⊗[K] ℬ)),
            F (includeRight _ _
              (SuperOp.op (tensorGrading 𝒜 ℬ) (a ᵍ⊗ₜ[K] b)))
            = F (includeRight _ _ (SuperOp.op (tensorGrading 𝒜 ℬ)
                (evenPart 𝒜 a ᵍ⊗ₜ[K] evenPart ℬ b)))
              + F (includeRight _ _ (SuperOp.op (tensorGrading 𝒜 ℬ)
                (evenPart 𝒜 a ᵍ⊗ₜ[K] oddPart ℬ b)))
              + F (includeRight _ _ (SuperOp.op (tensorGrading 𝒜 ℬ)
                (oddPart 𝒜 a ᵍ⊗ₜ[K] evenPart ℬ b)))
              + F (includeRight _ _ (SuperOp.op (tensorGrading 𝒜 ℬ)
                (oddPart 𝒜 a ᵍ⊗ₜ[K] oddPart ℬ b))) := by
          intro F
          rw [hsplit, map_add, map_add, map_add, map_add, map_add,
            map_add, map_add, map_add, map_add]
        rw [expand, expand,
          chainR_homog 𝒜 ℬ (evenPart_mem 𝒜 a) (evenPart_mem ℬ b),
          chainR_homog 𝒜 ℬ (evenPart_mem 𝒜 a) (oddPart_mem ℬ b),
          chainR_homog 𝒜 ℬ (oddPart_mem 𝒜 a) (evenPart_mem ℬ b),
          chainR_homog 𝒜 ℬ (oddPart_mem 𝒜 a) (oddPart_mem ℬ b)]
    | add u v hu hv =>
        simp only [map_add, hu, hv]
  have h := key ((of K 𝒜 ℬ).symm (SuperOp.unop (tensorGrading 𝒜 ℬ) w))
  rwa [symm_of_of, SuperOp.op_unop] at h

/-! ### The factorization -/

/-- **The Wall-map factorization** (M7f-2b): the Wall map of a graded
tensor product is the End-tensor map of the two Wall maps, up to the
canonical reshuffling. -/
theorem wall_factorization :
    superMulLeftRight (tensorGrading 𝒜 ℬ) = wallTensorChain 𝒜 ℬ := by
  refine galgHom_ext (tensorGrading 𝒜 ℬ)
    (SuperOp.grading (tensorGrading 𝒜 ℬ)) fun z w => ?_
  have hz := AlgHom.congr_fun (chainL 𝒜 ℬ) z
  have hw := AlgHom.congr_fun (chainR 𝒜 ℬ) w
  simp only [AlgHom.comp_apply] at hz hw
  rw [← includeLeft_mul_includeRight (tensorGrading 𝒜 ℬ)
      (SuperOp.grading (tensorGrading 𝒜 ℬ)) z w,
    map_mul, map_mul, ← hz, ← hw]

/-! ### Closure -/

private theorem wallGmap_bijective [IsSuperAzumaya 𝒜]
    [IsSuperAzumaya ℬ] :
    Function.Bijective (wallGmap 𝒜 ℬ) := by
  have h : ⇑(wallGmap 𝒜 ℬ)
      = ⇑(gcongr (tensorGrading 𝒜 (SuperOp.grading 𝒜))
          (tensorGrading ℬ (SuperOp.grading ℬ))
          (endGrading 𝒜) (endGrading ℬ)
          (AlgEquiv.ofBijective (superMulLeftRight 𝒜)
            IsSuperAzumaya.bij)
          (AlgEquiv.ofBijective (superMulLeftRight ℬ)
            IsSuperAzumaya.bij)
          (superMulLeftRight_map_grading 𝒜)
          (superMulLeftRight_map_grading ℬ)) := rfl
  rw [h]
  exact (gcongr _ _ _ _ _ _ _ _).bijective

/-- **The graded tensor product of super-Azumaya algebras is
super-Azumaya** (M7f-2): the Wall map of the product factors as a
composition of bijections.  Classically: central simplicity is closed
under `ᵍ⊗`. -/
theorem isSuperAzumaya_tensorGrading
    [Module.Free K A] [Module.Finite K A]
    [Module.Free K B] [Module.Finite K B]
    [IsSuperAzumaya 𝒜] [IsSuperAzumaya ℬ] :
    IsSuperAzumaya (tensorGrading 𝒜 ℬ) := by
  constructor
  rw [wall_factorization 𝒜 ℬ]
  have hcomp : ⇑(wallTensorChain 𝒜 ℬ)
      = ⇑(endTensorHom 𝒜 ℬ) ∘ ⇑(wallGmap 𝒜 ℬ)
        ∘ ⇑(gmiddleFour 𝒜 ℬ (SuperOp.grading 𝒜) (SuperOp.grading ℬ))
        ∘ ⇑(wallStep1 𝒜 ℬ) := rfl
  rw [hcomp]
  exact (endTensorHom_bijective 𝒜 ℬ).comp
    ((wallGmap_bijective 𝒜 ℬ).comp
      ((gmiddleFour 𝒜 ℬ (SuperOp.grading 𝒜)
        (SuperOp.grading ℬ)).bijective.comp
        (wallStep1 𝒜 ℬ).bijective))

end Superfusion
