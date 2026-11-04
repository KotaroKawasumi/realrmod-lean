import RMod.Classification.Instances.SpanEndFunctors
import RMod.Classification.Proofs.SimpleOfSchur
import RMod.Classification.Proofs.HomogeneousSumDetection

/-!
# Simple generators remain simple under component equivalences

Full faithfulness and reflection of parity transport the even division
property of endomorphisms. Semisimplicity then recovers simplicity in
the ambient category. Any simple object in a homogeneous span is in the
same parity orbit as its simple generator, by a nonzero projection.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

namespace SpanSuperfunctor

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  (F : SpanSuperfunctor C D S T) (hF : F.toFunctor.FullyFaithful)
  (hgrade : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
    D.data.IsHomogeneous b (F.toFunctor.map f).hom ↔ C.data.IsHomogeneous b f.hom)

include hF hgrade

theorem map_simple (X : HomogeneousSpanCategory C S) (hX : C.data.IsSimple X.obj) :
    D.data.IsSimple (F.data.obj X).obj := by
  let e := F.endAlgEquiv hF X
  have hne : D.data.id (F.data.obj X).obj ≠ D.data.zero := by
    intro hz
    have hh : (1 : @End (LinearCategory C) _ X.obj) = 0 :=
      e.injective ((map_one e).trans (hz.trans (map_zero e).symm))
    exact simple_id_ne_zero C.laws hX hh
  apply simple_of_even_schur D hne
  intro k hk hkne
  obtain ⟨f, rfl⟩ := e.surjective k
  have hf : C.data.IsHomogeneous 0 f := (hgrade (ObjectProperty.homMk f : X ⟶ X)).mp hk
  have hfne : f ≠ 0 := fun hz => hkne (hz ▸ map_zero e)
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur hX hX f hf hfne
  have hg := homogeneous_inverse C.laws f g hfg hgf hf
  have hg' := F.laws.map_grade (ObjectProperty.homMk g : X ⟶ X) hg
  refine ⟨hk, e g, hg', ?_, ?_⟩
  · exact (e.map_mul (g : @End (LinearCategory C) _ X.obj) (f : @End (LinearCategory C) _ X.obj)).symm.trans ((congrArg e hfg).trans (map_one e))
  · exact (e.map_mul (f : @End (LinearCategory C) _ X.obj) (g : @End (LinearCategory C) _ X.obj)).symm.trans ((congrArg e hgf).trans (map_one e))

end SpanSuperfunctor

theorem sameParityOrbit_of_simple_in_span (C : WeaklyPointedSuperfusion.{0, 0})
    (S : C.data.Obj) (X : HomogeneousSpanCategory C S)
    (hS : C.data.IsSimple S) (hX : C.data.IsSimple X.obj) :
    SameParityOrbit C.data X.obj S := by
  obtain ⟨n, ⟨d⟩⟩ := X.property
  obtain ⟨i, hi⟩ := d.exists_nonzero_projection C (C.data.id X.obj) (simple_id_ne_zero C.laws hX)
  have hpi : d.data.projection i ≠ C.data.zero := by
    intro hz
    exact hi ((C.laws.id_comp _).trans hz)
  exact ⟨d.data.parity i, homogeneous_schur C.laws hX hS (d.data.projection i)
    (d.laws.projection_grade i) hpi⟩

end RMod.Classification
