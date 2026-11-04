import RMod.Classification.Proofs.ReconstructionComponentProjection

/-!
# Naturality of the selected component inclusions and projections

The inverse source functor uses the actual diagonal matrix entries of
the conjugated map. Its g entry is therefore inclusion, the original
map, and projection. Orthogonality removes the complementary component
projector and gives naturality on every morphism, including odd maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) {X Y : LinearCategory A.toWeaklyPointedSuperfusion}

theorem reconstructionSource_inverse_map_eq (f : X ⟶ Y) (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    ((reconstructionSourceEquivalence A).inverse.map f g).hom =
      A.data.comp (A.data.comp ((reconstructionSourceBicone A X).ι g) f)
        ((reconstructionSourceBicone A Y).π g) := by
  letI := Fintype.ofFinite (SimpleOrbit A.toWeaklyPointedSuperfusion)
  let bX := evenBiproductFullBicone A.toWeaklyPointedSuperfusion
    (spanFamilyEvenObjects A.toWeaklyPointedSuperfusion _ ((reconstructionSourceEquivalence A).inverse.obj X))
  let bY := evenBiproductFullBicone A.toWeaklyPointedSuperfusion
    (spanFamilyEvenObjects A.toWeaklyPointedSuperfusion _ ((reconstructionSourceEquivalence A).inverse.obj Y))
  let eX : A.data.Hom bX.pt X := (reconstructionSourceEquivalence A).counitIso.hom.app X
  let iY : A.data.Hom Y bY.pt := (reconstructionSourceEquivalence A).counitIso.inv.app Y
  change A.data.comp (A.data.comp (bX.ι g) (A.data.comp eX (A.data.comp f iY))) (bY.π g) =
    A.data.comp (A.data.comp (A.data.comp (bX.ι g) eX) f) (A.data.comp iY (bY.π g))
  simp only [A.laws.comp_assoc]

theorem reconstructionSource_inclusion_naturality (f : X ⟶ Y)
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.comp ((reconstructionSourceBicone A X).ι g) f =
      A.data.comp ((reconstructionSourceEquivalence A).inverse.map f g).hom
        ((reconstructionSourceBicone A Y).ι g) := by
  let ix : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj X g).obj X :=
    (reconstructionSourceBicone A X).ι g
  let iy : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj Y g).obj Y :=
    (reconstructionSourceBicone A Y).ι g
  let py : A.data.Hom Y ((reconstructionSourceEquivalence A).inverse.obj Y g).obj :=
    (reconstructionSourceBicone A Y).π g
  have h : A.data.comp (A.data.comp ix f) (A.data.comp py iy) = A.data.comp ix f :=
    reconstructionComponentProjection_incoming A g
      ((reconstructionSourceEquivalence A).inverse.obj X g).property (A.data.comp ix f)
  rw [← A.laws.comp_assoc] at h
  change A.data.comp ix f = A.data.comp ((reconstructionSourceEquivalence A).inverse.map f g).hom iy
  rw [reconstructionSource_inverse_map_eq]
  exact h.symm

theorem reconstructionSource_projection_naturality (f : X ⟶ Y)
    (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.comp f ((reconstructionSourceBicone A Y).π g) =
      A.data.comp ((reconstructionSourceBicone A X).π g)
        ((reconstructionSourceEquivalence A).inverse.map f g).hom := by
  let ix : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj X g).obj X :=
    (reconstructionSourceBicone A X).ι g
  let px : A.data.Hom X ((reconstructionSourceEquivalence A).inverse.obj X g).obj :=
    (reconstructionSourceBicone A X).π g
  let py : A.data.Hom Y ((reconstructionSourceEquivalence A).inverse.obj Y g).obj :=
    (reconstructionSourceBicone A Y).π g
  have h : A.data.comp px (A.data.comp ix (A.data.comp f py)) = A.data.comp f py :=
    reconstructionComponentProjection_outgoing A g
      ((reconstructionSourceEquivalence A).inverse.obj Y g).property (A.data.comp f py)
  change A.data.comp f py = A.data.comp px ((reconstructionSourceEquivalence A).inverse.map f g).hom
  rw [reconstructionSource_inverse_map_eq, A.laws.comp_assoc]
  exact h.symm

end RMod.Classification
