import RMod.BrundanEllis.StackingReindexConvolution
import RMod.Classification.Proofs.ConvolutionInsertions
import RMod.Classification.Proofs.IsoCalculus

/-! The coordinate restriction comparison is natural on every raw Hom map,
so in particular on both even and odd morphisms. Equality transports are
isolated before the actual convolution inclusion calculation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

/-- Equality transport in the reference even category retains its raw identity map. -/
theorem referenceEven_eqToHom_value {X Y : C.Obj} (h : X = Y)
    (e : referenceEvenObj C hC X = referenceEvenObj C hC Y) :
    (eqToHom e).hom = (IsoData.ofEq C.toWeaklyPointedSuperfusionData h).hom := by
  cases h
  rfl

include hC in
/-- Reindexing a coordinate and a parity bit commutes with the tensor on all maps. -/
theorem tensorFactor_transport_natural {I : Type} (U U' : C.Obj) (u : C.Hom U U')
    (V V' : I → C.Obj) (v : ∀ i, C.Hom (V i) (V' i))
    (i j : I) (hi : i = j) (p q : ZMod 2) (hp : p = q) :
    C.comp (C.tensorHom (C.tensorHom u (v i)) (C.id (C.pi.factor p)))
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg₂ (fun k r => C.tensorObj (C.tensorObj U' (V' k)) (C.pi.factor r)) hi hp)).hom =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg₂ (fun k r => C.tensorObj (C.tensorObj U (V k)) (C.pi.factor r)) hi hp)).hom
      (C.tensorHom (C.tensorHom u (v j)) (C.id (C.pi.factor q))) := by
  subst j
  subst q
  exact (hC.comp_id _).trans (hC.id_comp _).symm

variable (s t : Twist) (f : t.data.group →* s.data.group)
  (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))

/-- The local square between the actual restricted convolution summands. -/
theorem coordinateRestriction_summand_natural
    {X X' Y Y' : PullbackObj C s.data}
    (u : PullbackHom C s.data X X') (v : PullbackHom C s.data Y Y')
    (k g : t.data.group) :
    C.comp (twistSummandHom C t.data
      ((coordinateRestrictionData C hC s t f hρ).map u)
      ((coordinateRestrictionData C hC s t f hρ).map v) g (g⁻¹ * k))
      (eqToHom (coordinateRestriction_summand C hC s t f hρ hν X' Y' k g)).hom =
    C.comp (eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g)).hom
      (twistSummandHom C s.data u v (f g) ((f g)⁻¹ * f k)) := by
  rw [referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν X' Y' k g),
    referenceEven_eqToHom_value C hC
      (coordinateRestriction_summandObj C hC s t f hρ hν X Y k g)]
  have hi : f (g⁻¹ * k) = (f g)⁻¹ * f k := by rw [map_mul, map_inv]
  exact tensorFactor_transport_natural C hC (X (f g)).val (X' (f g)).val (u (f g))
    (fun j => (Y j).val) (fun j => (Y' j).val) v _ _ hi _ _
    ((hν g (g⁻¹ * k)).trans (congrArg (s.data.nu (f g)) hi))

/-- The even inclusion equation also fixes the raw, all-degree comparison map. -/
theorem coordinateRestrictionTensorIso_raw_inclusion
    (X Y : PullbackObj C s.data) (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero) (k g : t.data.group) :
    C.comp (convolutionInclusion C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y) k g)
      (coordinateRestrictionTensorIso C hC s t f hρ hν X Y hf hX k).hom.hom =
    C.comp (eqToHom (coordinateRestriction_summand C hC s t f hρ hν X Y k g)).hom
      (convolutionInclusion C hC s.data X Y (f k) (f g)) :=
  congrArg (fun u => u.hom)
    (coordinateRestrictionTensorIso_inclusion C hC s t f hρ hν X Y hf hX k g)

/-- Equality on each convolution inclusion proves naturality on the entire raw Hom. -/
theorem coordinateRestrictionTensorIso_naturality
    {X X' Y Y' : PullbackObj C s.data}
    (u : PullbackHom C s.data X X') (v : PullbackHom C s.data Y Y')
    (hf : Function.Injective f)
    (hX : ∀ k, (¬ ∃ g, f g = k) → C.id (X k).val = C.zero)
    (hX' : ∀ k, (¬ ∃ g, f g = k) → C.id (X' k).val = C.zero) (k : t.data.group) :
    C.comp (convolutionHom C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).map u)
      ((coordinateRestrictionData C hC s t f hρ).map v) k)
      (coordinateRestrictionTensorIso C hC s t f hρ hν X' Y' hf hX' k).hom.hom =
    C.comp (coordinateRestrictionTensorIso C hC s t f hρ hν X Y hf hX k).hom.hom
      (convolutionHom C hC s.data u v (f k)) := by
  apply hom_ext_of_convolutionInclusions C hC t.data
    ((coordinateRestrictionData C hC s t f hρ).obj X)
    ((coordinateRestrictionData C hC s t f hρ).obj Y) k
  intro g
  rw [← hC.comp_assoc, convolutionInclusion_map, hC.comp_assoc,
    coordinateRestrictionTensorIso_raw_inclusion, ← hC.comp_assoc,
    coordinateRestriction_summand_natural C hC s t f hρ hν, hC.comp_assoc,
    ← convolutionInclusion_map, ← hC.comp_assoc,
    ← coordinateRestrictionTensorIso_raw_inclusion, hC.comp_assoc]

end RMod.Classification
