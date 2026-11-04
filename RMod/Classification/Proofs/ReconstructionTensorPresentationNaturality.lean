import RMod.Classification.Proofs.ReconstructionSourceNaturality
import RMod.Classification.Proofs.ReconstructionMappedTensorBicone
import RMod.Classification.Instances.ReconstructionTensorComponentMaps
import RMod.Classification.Instances.ReconstructionUnderlyingEquivalence

/-!
# Naturality of the actual tensor-component presentations

Even component inclusions let super-interchange commute an arbitrary
pair of maps with the tensor presentation. Naturality of the component
projection gives the restricted presentation square. Applying the
selected component functor gives the square in the reference category.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) {X X' Y Y' : LinearCategory A.toWeaklyPointedSuperfusion}

theorem reconstructionTensorBicone_inclusion_naturality (f : X ⟶ X') (h : Y ⟶ Y')
    (g k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.comp ((reconstructionTensorBicone A X Y).ι (g, k)) (A.data.tensorHom f h) =
      A.data.comp (reconstructionTensorSpanMap A f h g k).hom
        ((reconstructionTensorBicone A X' Y').ι (g, k)) := by
  let ix : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj X g).obj X :=
    (reconstructionSourceBicone A X).ι g
  let iy : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj Y k).obj Y :=
    (reconstructionSourceBicone A Y).ι k
  let ix' : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj X' g).obj X' :=
    (reconstructionSourceBicone A X').ι g
  let iy' : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj Y' k).obj Y' :=
    (reconstructionSourceBicone A Y').ι k
  let fg : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj X' g).obj :=
    ((reconstructionSourceEquivalence A).inverse.map f g).hom
  let hk : A.data.Hom ((reconstructionSourceEquivalence A).inverse.obj Y k).obj
    ((reconstructionSourceEquivalence A).inverse.obj Y' k).obj :=
    ((reconstructionSourceEquivalence A).inverse.map h k).hom
  have hx : A.data.comp ix f = A.data.comp fg ix' := reconstructionSource_inclusion_naturality A f g
  have hy : A.data.comp iy h = A.data.comp hk iy' := reconstructionSource_inclusion_naturality A h k
  change A.data.comp (A.data.tensorHom ix iy) (A.data.tensorHom f h) =
    A.data.comp (A.data.tensorHom fg hk) (A.data.tensorHom ix' iy')
  have h₁ := interchange_first_even A.laws.toWeaklyPointedSuperfusionLaws f h ix iy
    (reconstructionSourceBicone_inclusion_even A X g)
  have h₂ := interchange_second_even A.laws.toWeaklyPointedSuperfusionLaws ix' iy' fg hk
    (reconstructionSourceBicone_inclusion_even A Y' k)
  exact h₁.trans ((congrArg₂ A.data.tensorHom hx hy).trans h₂.symm)

theorem reconstructionTensorComponentBicone_inclusion_naturality (f : X ⟶ X') (h : Y ⟶ Y')
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    A.data.comp ((reconstructionTensorComponentBicone A X Y k).ι g).hom
      ((reconstructionSourceEquivalence A).inverse.map (A.data.tensorHom f h) k).hom =
    A.data.comp (reconstructionTensorOutputSpanMap A f h k g).hom
      ((reconstructionTensorComponentBicone A X' Y' k).ι g).hom := by
  let i : A.data.Hom (reconstructionTensorOutputSpan A X Y k g).obj (A.data.tensorObj X Y) :=
    (reconstructionTensorBicone A X Y).ι (g, g⁻¹ * k)
  let i' : A.data.Hom (reconstructionTensorOutputSpan A X' Y' k g).obj (A.data.tensorObj X' Y') :=
    (reconstructionTensorBicone A X' Y').ι (g, g⁻¹ * k)
  let p : A.data.Hom (A.data.tensorObj X Y)
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) k).obj :=
    (reconstructionSourceBicone A (A.data.tensorObj X Y)).π k
  let p' : A.data.Hom (A.data.tensorObj X' Y')
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X' Y') k).obj :=
    (reconstructionSourceBicone A (A.data.tensorObj X' Y')).π k
  let m := (reconstructionTensorOutputSpanMap A f h k g).hom
  let n := ((reconstructionSourceEquivalence A).inverse.map (A.data.tensorHom f h) k).hom
  have hi : A.data.comp i (A.data.tensorHom f h) = A.data.comp m i' :=
    reconstructionTensorBicone_inclusion_naturality A f h g (g⁻¹ * k)
  have hp : A.data.comp (A.data.tensorHom f h) p' = A.data.comp p n :=
    reconstructionSource_projection_naturality A (A.data.tensorHom f h) k
  change A.data.comp (A.data.comp i p) n = A.data.comp m (A.data.comp i' p')
  rw [A.laws.comp_assoc, ← hp, ← A.laws.comp_assoc, hi, A.laws.comp_assoc]

theorem reconstructionMappedTensorBicone_inclusion_naturality
    (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data) (f : X ⟶ X') (h : Y ⟶ Y')
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp ((reconstructionMappedTensorBicone A C hC X Y k).ι g)
      ((reconstructionUnderlyingEquivalence A C hC).functor.map (A.data.tensorHom f h) k) =
    C.data.comp ((reconstructionComponentRealization A C hC k).map (reconstructionTensorOutputSpanMap A f h k g))
      ((reconstructionMappedTensorBicone A C hC X' Y' k).ι g) := by
  let F := reconstructionComponentRealization A C hC k
  have hs : (reconstructionTensorComponentBicone A X Y k).ι g ≫
      (reconstructionSourceEquivalence A).inverse.map (A.data.tensorHom f h) k =
    reconstructionTensorOutputSpanMap A f h k g ≫ (reconstructionTensorComponentBicone A X' Y' k).ι g := by
    apply ObjectProperty.hom_ext
    exact reconstructionTensorComponentBicone_inclusion_naturality A f h k g
  exact (F.map_comp _ _).symm.trans ((congrArg F.map hs).trans (F.map_comp _ _))

end RMod.Classification
