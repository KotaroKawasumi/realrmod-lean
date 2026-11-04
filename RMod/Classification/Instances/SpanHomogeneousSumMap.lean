import RMod.Classification.Instances.SpanSuperfunctor
import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Proofs.SpanHomSums

/-!
# Mapping a homogeneous presentation through a component functor

Both vertices are objects of the specified source span. The inclusions
and projections are sent by the given functor and keep their parities.
Functoriality and linearity prove the matrix-unit equations for these
same maps; no extension of the functor outside its component is used.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {X Y : HomogeneousSpanCategory C S} {n : ℕ}

def spanHomogeneousSumMapData (F : SpanSuperfunctorData C D S T)
    (d : HomogeneousSumData C.data X.obj Y.obj n) :
    HomogeneousSumData D.data (F.obj X).obj (F.obj Y).obj n where
  parity := d.parity
  inclusion i := (F.map (ObjectProperty.homMk (d.inclusion i) : X ⟶ Y)).hom
  projection i := (F.map (ObjectProperty.homMk (d.projection i) : Y ⟶ X)).hom

theorem spanHomogeneousSumMapLaws (F : SpanSuperfunctor C D S T)
    (d : HomogeneousSum C.data X.obj Y.obj n) :
    HomogeneousSumLaws (spanHomogeneousSumMapData (X := X) (Y := Y) F.data d.data) where
  inclusion_grade i := F.laws.map_grade _ (d.laws.inclusion_grade i)
  projection_grade i := F.laws.map_grade _ (d.laws.projection_grade i)
  diagonal i := by
    have h : (ObjectProperty.homMk (d.data.inclusion i) : X ⟶ Y) ≫
        ObjectProperty.homMk (d.data.projection i) = 𝟙 X := by
      apply ObjectProperty.hom_ext
      exact d.laws.diagonal i
    exact congrArg (fun f : F.data.obj X ⟶ F.data.obj X => f.hom)
      ((F.laws.map_comp _ _).symm.trans ((congrArg F.data.map h).trans (F.laws.map_id X)))
  off_diagonal i j hij := by
    have h : (ObjectProperty.homMk (d.data.inclusion i) : X ⟶ Y) ≫
        ObjectProperty.homMk (d.data.projection j) = 0 := by
      apply ObjectProperty.hom_ext
      exact d.laws.off_diagonal i j hij
    exact congrArg (fun f : F.data.obj X ⟶ F.data.obj X => f.hom)
      ((F.laws.map_comp _ _).symm.trans ((congrArg F.data.map h).trans (F.laws.map_zero X X)))
  total := by
    let p : Fin n → (Y ⟶ X) := fun i => ObjectProperty.homMk (d.data.projection i)
    let q : Fin n → (X ⟶ Y) := fun i => ObjectProperty.homMk (d.data.inclusion i)
    have ht : ∑ i, p i ≫ q i = 𝟙 Y := by
      apply ObjectProperty.hom_ext
      rw [span_sum_hom]
      exact (LinearCategory.finSum_eq_sum C n _).symm.trans d.laws.total
    have hm : ∑ i, F.toFunctor.map (p i) ≫ F.toFunctor.map (q i) = 𝟙 (F.toFunctor.obj Y) := by
      simp only [← Functor.map_comp, ← Functor.map_sum, ht]
      exact F.toFunctor.map_id Y
    have hraw := congrArg (fun f : F.toFunctor.obj Y ⟶ F.toFunctor.obj Y => f.hom) hm
    rw [span_sum_hom] at hraw
    change D.data.finSum n (fun i => D.data.comp
      (F.data.map (p i)).hom (F.data.map (q i)).hom) = D.data.id (F.data.obj Y).obj
    rw [LinearCategory.finSum_eq_sum D]
    exact hraw

def spanHomogeneousSumMap (F : SpanSuperfunctor C D S T)
    (d : HomogeneousSum C.data X.obj Y.obj n) :
    HomogeneousSum D.data (F.data.obj X).obj (F.data.obj Y).obj n :=
  ⟨spanHomogeneousSumMapData (X := X) (Y := Y) F.data d.data, spanHomogeneousSumMapLaws F d⟩

end RMod.Classification
