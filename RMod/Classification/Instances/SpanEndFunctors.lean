import RMod.Classification.Instances.SpanSuperfunctor
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Endomorphism algebra maps of component functors

Forgetting the full-subcategory wrapper identifies its endomorphisms
with the ambient endomorphism algebra. The given superfunctor acts on
this actual algebra; full faithfulness makes this map an equivalence.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  (F : SpanSuperfunctor C D S T)

def endAlgHom (X : HomogeneousSpanCategory C S) :
    @End (LinearCategory C) _ X.obj →ₐ[ℝ]
      @End (LinearCategory D) _ (F.data.obj X).obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => (F.data.map (ObjectProperty.homMk f : X ⟶ X)).hom
      map_add' := fun f g => congrArg (fun k => k.hom)
        (F.laws.map_add (ObjectProperty.homMk f : X ⟶ X) (ObjectProperty.homMk g : X ⟶ X))
      map_smul' := fun r f => congrArg (fun k => k.hom)
        (F.laws.map_smul r (ObjectProperty.homMk f : X ⟶ X)) }
    (congrArg (fun k => k.hom) (F.laws.map_id X))
    (fun f g => congrArg (fun k => k.hom)
      (F.laws.map_comp (ObjectProperty.homMk g : X ⟶ X) (ObjectProperty.homMk f : X ⟶ X)))

theorem endAlgHom_bijective (hF : F.toFunctor.FullyFaithful) (X : HomogeneousSpanCategory C S) :
    Function.Bijective (F.endAlgHom X) := by
  constructor
  · intro f g h
    have hm : F.toFunctor.map (ObjectProperty.homMk f : X ⟶ X) =
        F.toFunctor.map (ObjectProperty.homMk g : X ⟶ X) := ObjectProperty.hom_ext _ h
    exact congrArg (fun k : X ⟶ X => k.hom) (hF.map_injective hm)
  · intro f
    refine ⟨(hF.preimage (ObjectProperty.homMk f)).hom, ?_⟩
    exact congrArg (fun k => k.hom) (hF.map_preimage (ObjectProperty.homMk f))

noncomputable def endAlgEquiv (hF : F.toFunctor.FullyFaithful) (X : HomogeneousSpanCategory C S) :
    @End (LinearCategory C) _ X.obj ≃ₐ[ℝ]
      @End (LinearCategory D) _ (F.data.obj X).obj :=
  AlgEquiv.ofBijective (F.endAlgHom X) (F.endAlgHom_bijective hF X)

end RMod.Classification.SpanSuperfunctor
