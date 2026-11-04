import RMod.Hierarchy.Abstract.Equivalence
import RMod.Hierarchy.Instances.TotalFunctor
import RMod.Hierarchy.Instances.TensorPoints
import RMod.Hierarchy.Instances.HomogeneousPoints
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Mathlib functors associated with a monoidal superequivalence

The specified enriched functors give ordinary even functors. Their strong
monoidal structure reuses Mathlib's coherence and composition machinery.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

def Superfunctor.comp {A B C : Supercategory} (F : Superfunctor A B) (G : Superfunctor B C) :
    Superfunctor A C where
  data := { obj := fun X => G.data.obj (F.data.obj X)
            map := fun X Y => F.data.map X Y ≫ G.data.map _ _ }
  laws := {
    map_id := (F.enriched.comp SuperVec G.enriched).map_id
    map_comp := (F.enriched.comp SuperVec G.enriched).map_comp }

@[simp] theorem tMap_comp_functor {A B C : Supercategory}
    (F : Superfunctor A B) (G : Superfunctor B C) {X Y : A.data.Obj} (f : THom A.data X Y) :
    tMap (F.comp G).data f = tMap G.data (tMap F.data f) := rfl

namespace MonoidalSuperequivalence
variable {C D : MonoidalSupercategory} (E : MonoidalSuperequivalence C D)

def forward : Superfunctor C.super D.super := ⟨E.data.forward, E.laws.forward⟩
def backward : Superfunctor D.super C.super := ⟨E.data.backward, E.laws.backward⟩
def evenForward : Even C.super ⥤ Even D.super := E.forward.enriched.forget
def evenBackward : Even D.super ⥤ Even C.super := E.backward.enriched.forget

theorem even_tensor_natural {X X' Y Y' : Even C.super} (f : X ⟶ X') (g : Y ⟶ Y') :
    (E.evenForward.map f ⊗ₘ E.evenForward.map g) ≫ (E.data.tensorIso X' Y').hom =
      (E.data.tensorIso X Y).hom ≫ E.evenForward.map (f ⊗ₘ g) := by
  apply evenPoint_injective
  change evenPoint (eComp D.super.data
      (eTensor D.data.monoidal (f ≫ E.data.forward.map _ _) (g ≫ E.data.forward.map _ _))
      (E.data.tensorIso X' Y').hom) =
    evenPoint (eComp D.super.data (E.data.tensorIso X Y).hom
      (eTensor C.data.monoidal f g ≫ E.data.forward.map _ _))
  rw [evenPoint_comp, evenPoint_comp, evenPoint_tensor]
  have hf := tMap_evenPoint E.forward f
  have hg := tMap_evenPoint E.forward g
  have ht := tMap_evenPoint E.forward (eTensor C.data.monoidal f g)
  erw [← hf, ← hg, ← ht, evenPoint_tensor]
  exact E.laws.tensor_natural (evenPoint f) (evenPoint g)

def evenCoreMonoidal : E.evenForward.CoreMonoidal where
  εIso := E.data.unitIso
  μIso := E.data.tensorIso
  μIso_hom_natural_left f Z := by
    have h := E.even_tensor_natural f (𝟙 Z)
    rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
    exact h
  μIso_hom_natural_right Z f := by
    have h := E.even_tensor_natural (𝟙 Z) f
    rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h
    exact h
  associativity := E.laws.associativity
  left_unitality X := (E.laws.left_unit X).symm
  right_unitality X := (E.laws.right_unit X).symm

instance evenForward_monoidal : E.evenForward.Monoidal := E.evenCoreMonoidal.toMonoidal

end MonoidalSuperequivalence
end RMod.Legacy
