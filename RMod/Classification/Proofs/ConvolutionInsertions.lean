import RMod.Classification.Instances.ConvolutionInsertions
import RMod.Classification.Proofs.ConvolutionBiproduct

/-!
# Summand equations for the actual convolution maps

At an enumerated group element the new notation is exactly the supplied
raw inclusion or projection. Thus the already proved finite-sum map laws
apply to arbitrary graded morphisms, not just morphisms of the even
subcategory used to define the comparison isomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionInclusion_enumeration (X Y : PullbackObj C t) (k : t.group)
    (i : Fin (Nat.card t.group)) :
    convolutionInclusion C hC t X Y k (groupEnumeration t i) =
      (convolutionSum C hC t X Y k).data.inclusion i := by
  exact congrArg (fun f => f.hom) (convolutionEvenIso_inclusion_inv C hC t X Y k i)

theorem convolutionProjection_enumeration (X Y : PullbackObj C t) (k : t.group)
    (i : Fin (Nat.card t.group)) :
    convolutionProjection C hC t X Y k (groupEnumeration t i) =
      (convolutionSum C hC t X Y k).data.projection i := by
  have he := convolutionEvenIso_inv_projection C hC t X Y k i
  have hh := congrArg (fun f => (convolutionEvenIso C hC t X Y k).hom ≫ f) he
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  exact congrArg (fun f => f.hom) hh.symm

theorem convolutionInclusion_grade (X Y : PullbackObj C t) (k g : t.group) :
    C.IsHomogeneous 0 (convolutionInclusion C hC t X Y k g) :=
  (convolutionInclusionEven C hC t X Y k g).property

theorem convolutionProjection_grade (X Y : PullbackObj C t) (k g : t.group) :
    C.IsHomogeneous 0 (convolutionProjection C hC t X Y k g) :=
  (convolutionProjectionEven C hC t X Y k g).property

theorem convolutionInclusion_map {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (f' : PullbackHom C t Y Y') (k g : t.group) :
    C.comp (convolutionInclusion C hC t X Y k g) (convolutionHom C hC t f f' k) =
      C.comp (twistSummandHom C t f f' g (g⁻¹ * k))
        (convolutionInclusion C hC t X' Y' k g) := by
  obtain ⟨i, rfl⟩ := (groupEnumeration t).surjective g
  rw [convolutionInclusion_enumeration, convolutionInclusion_enumeration]
  exact Biproduct.inclusion_mapHom hC.toWeaklyPointedSuperfusionLaws _ _ _ i

theorem convolutionMap_projection {X X' Y Y' : PullbackObj C t}
    (f : PullbackHom C t X X') (f' : PullbackHom C t Y Y') (k g : t.group) :
    C.comp (convolutionHom C hC t f f' k) (convolutionProjection C hC t X' Y' k g) =
      C.comp (convolutionProjection C hC t X Y k g) (twistSummandHom C t f f' g (g⁻¹ * k)) := by
  obtain ⟨i, rfl⟩ := (groupEnumeration t).surjective g
  rw [convolutionProjection_enumeration, convolutionProjection_enumeration]
  exact Biproduct.mapHom_projection hC.toWeaklyPointedSuperfusionLaws _ _ _ i

/-- The group-indexed maps give a complete even direct-sum decomposition. -/
theorem convolutionInclusion_projection (X Y : PullbackObj C t) (k g : t.group) :
    C.comp (convolutionInclusion C hC t X Y k g) (convolutionProjection C hC t X Y k g) =
      C.id (twistSummand C t X Y g (g⁻¹ * k)) := by
  obtain ⟨i, rfl⟩ := (groupEnumeration t).surjective g
  rw [convolutionInclusion_enumeration, convolutionProjection_enumeration]
  exact (convolutionSum C hC t X Y k).laws.diagonal i

theorem convolutionInclusion_projection_ne (X Y : PullbackObj C t) (k g g' : t.group)
    (h : g ≠ g') :
    C.comp (convolutionInclusion C hC t X Y k g) (convolutionProjection C hC t X Y k g') =
      C.zero := by
  obtain ⟨i, rfl⟩ := (groupEnumeration t).surjective g
  obtain ⟨j, rfl⟩ := (groupEnumeration t).surjective g'
  rw [convolutionInclusion_enumeration, convolutionProjection_enumeration]
  exact (convolutionSum C hC t X Y k).laws.off_diagonal i j
    (fun he => h (congrArg (groupEnumeration t) he))

theorem convolutionInsertions_total (X Y : PullbackObj C t) (k : t.group) :
    C.finSum (Nat.card t.group) (fun i => C.comp
      (convolutionProjection C hC t X Y k (groupEnumeration t i))
      (convolutionInclusion C hC t X Y k (groupEnumeration t i))) =
        C.id (convolutionObj C hC t X Y k).val := by
  simp only [convolutionProjection_enumeration, convolutionInclusion_enumeration]
  exact (convolutionSum C hC t X Y k).laws.total

/-- Summand inclusions detect equality on the full graded Hom space. -/
theorem hom_ext_of_convolutionInclusions (X Y : PullbackObj C t) (k : t.group)
    {M : C.Obj} {f g : C.Hom (convolutionObj C hC t X Y k).val M}
    (he : ∀ a, C.comp (convolutionInclusion C hC t X Y k a) f =
      C.comp (convolutionInclusion C hC t X Y k a) g) : f = g := by
  apply hom_ext_of_inclusions hC.toWeaklyPointedSuperfusionLaws
    (convolutionSum C hC t X Y k).data.inclusion
    (convolutionSum C hC t X Y k).data.projection (convolutionSum C hC t X Y k).laws.total
  intro i
  have hi := he (groupEnumeration t i)
  simp only [convolutionInclusion_enumeration] at hi
  exact hi

theorem hom_ext_of_convolutionProjections (X Y : PullbackObj C t) (k : t.group)
    {M : C.Obj} {f g : C.Hom M (convolutionObj C hC t X Y k).val}
    (he : ∀ a, C.comp f (convolutionProjection C hC t X Y k a) =
      C.comp g (convolutionProjection C hC t X Y k a)) : f = g := by
  apply hom_ext_of_projections hC.toWeaklyPointedSuperfusionLaws
    (convolutionSum C hC t X Y k).data.inclusion
    (convolutionSum C hC t X Y k).data.projection (convolutionSum C hC t X Y k).laws.total
  intro i
  have hi := he (groupEnumeration t i)
  simp only [convolutionProjection_enumeration] at hi
  exact hi

end RMod.Classification
