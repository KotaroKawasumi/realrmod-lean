import RMod.Classification.Proofs.ReconstructionTriplePresentation
import RMod.Classification.Proofs.ReconstructionSourceNaturality
import RMod.Classification.Proofs.IndexedEqualityMaps

/-!
# The source associator on the selected triple tensor presentations

Associator naturality identifies the two threefold tensor inclusions.
Naturality of the selected output projection restricts that square to
one component. The group associativity equality is retained in the
comparison between the two output indices.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A : PiSuperfusion.{0, 0}) (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleInclusion_associator :
    A.data.comp (reconstructionTripleLeftInclusion A X Y Z g h k).hom
      ((reconstructionSourceEquivalence A).inverse.map (A.data.associatorHom X Y Z) ((g * h) * k)).hom =
    A.data.comp
      (A.data.comp
        (A.data.associatorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj
          ((reconstructionSourceEquivalence A).inverse.obj Y h).obj
          ((reconstructionSourceEquivalence A).inverse.obj Z k).obj)
        (reconstructionTripleRightInclusion A X Y Z g h k).hom)
      (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
        (congrArg (fun j => ((reconstructionSourceEquivalence A).inverse.obj
          (A.data.tensorObj X (A.data.tensorObj Y Z)) j).obj) (mul_assoc g h k))).inv := by
  let L : A.data.Obj := (reconstructionTripleLeftSpan A X Y Z g h k).obj
  let R : A.data.Obj := (reconstructionTripleRightSpan A X Y Z g h k).obj
  let T : A.data.Obj := A.data.tensorObj (A.data.tensorObj X Y) Z
  let T' : A.data.Obj := A.data.tensorObj X (A.data.tensorObj Y Z)
  let P : SimpleOrbit A.toWeaklyPointedSuperfusion → A.data.Obj :=
    fun j => ((reconstructionSourceEquivalence A).inverse.obj T' j).obj
  let Q : A.data.Obj := ((reconstructionSourceEquivalence A).inverse.obj T ((g * h) * k)).obj
  let i : A.data.Hom L T := A.data.tensorHom
    ((reconstructionTensorBicone A X Y).ι (g, h)) ((reconstructionSourceBicone A Z).ι k)
  let j : A.data.Hom R T' := A.data.tensorHom
    ((reconstructionSourceBicone A X).ι g) ((reconstructionTensorBicone A Y Z).ι (h, k))
  let p : A.data.Hom T Q := (reconstructionSourceBicone A T).π ((g * h) * k)
  let p' : ∀ d, A.data.Hom T' (P d) := (reconstructionSourceBicone A T').π
  let a : A.data.Hom T T' := A.data.associatorHom X Y Z
  let b : A.data.Hom L R := A.data.associatorHom
    ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj Y h).obj
    ((reconstructionSourceEquivalence A).inverse.obj Z k).obj
  let n : A.data.Hom Q (P ((g * h) * k)) :=
    ((reconstructionSourceEquivalence A).inverse.map a ((g * h) * k)).hom
  let v : A.data.Hom (P (g * (h * k))) (P ((g * h) * k)) :=
    (IsoData.ofEq A.toWeaklyPointedSuperfusion.data (congrArg P (mul_assoc g h k))).inv
  have hi : A.data.comp i a = A.data.comp b j := A.laws.associator_naturality
    ((reconstructionSourceBicone A X).ι g) ((reconstructionSourceBicone A Y).ι h)
    ((reconstructionSourceBicone A Z).ι k)
  have hn : A.data.comp a (p' ((g * h) * k)) = A.data.comp p n :=
    reconstructionSource_projection_naturality A a ((g * h) * k)
  have hp : A.data.comp (p' (g * (h * k))) v = p' ((g * h) * k) :=
    indexed_map_to_eq A.toWeaklyPointedSuperfusion P p' (mul_assoc g h k)
  change A.data.comp (A.data.comp i p) n =
    A.data.comp (A.data.comp b (A.data.comp j (p' (g * (h * k))))) v
  calc
    _ = A.data.comp i (A.data.comp p n) := A.laws.comp_assoc _ _ _
    _ = A.data.comp i (A.data.comp a (p' ((g * h) * k))) := congrArg (A.data.comp i) hn.symm
    _ = A.data.comp (A.data.comp i a) (p' ((g * h) * k)) := (A.laws.comp_assoc _ _ _).symm
    _ = A.data.comp (A.data.comp b j) (p' ((g * h) * k)) := congrArg (fun f => A.data.comp f _) hi
    _ = A.data.comp (A.data.comp b j) (A.data.comp (p' (g * (h * k))) v) :=
      congrArg (A.data.comp (A.data.comp b j)) hp.symm
    _ = _ := by simp only [A.laws.comp_assoc]

end RMod.Classification
