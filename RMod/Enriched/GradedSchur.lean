import RMod.Enriched.SimpleCriterion
import RMod.Hierarchy.Instances.EvenTotal
import RMod.Hierarchy.Abstract.ParityShift
import Mathlib.CategoryTheory.Preadditive.Schur

/-! Ordinary Schur, semisimplicity, and the specified odd parity isomorphisms
imply graded Schur. No graded division property is assumed here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace RMod.EnrichedSupport

variable (C : Legacy.Supercategory)

/-- Recover an even morphism from a total morphism supported in degree zero. -/
def liftEven {X Y : Legacy.Even C} (f : Legacy.THom C.data X Y)
    (hf : f ∈ Legacy.grade C X Y 0) : X ⟶ Y :=
  (Legacy.evenHomGradeEquiv C X Y).symm ⟨f, hf⟩

theorem liftEven_map {X Y : Legacy.Even C} (f : Legacy.THom C.data X Y)
    (hf : f ∈ Legacy.grade C X Y 0) : (Legacy.evenToTotal C).map (liftEven C f hf) = f :=
  congrArg Subtype.val ((Legacy.evenHomGradeEquiv C X Y).apply_symm_apply ⟨f, hf⟩)

section
variable [HasFiniteBiproducts (Legacy.Even C)] [HasKernels (Legacy.Even C)]
  (hsemi : ∀ Y : Legacy.Even C, ∃ (n : ℕ) (S : Fin n → Legacy.Even C),
    (∀ i, Simple (S i)) ∧ Nonempty (Y ≅ ⨁ S))

include hsemi

/-- Odd conjugation transports simplicity through the even endomorphism criterion. -/
theorem simple_of_odd_iso {X Y : Legacy.Even C} [Simple X]
    (e : (Legacy.evenToTotal C).obj X ≅ (Legacy.evenToTotal C).obj Y)
    (he : e.hom ∈ Legacy.grade C X Y 1) (hi : e.inv ∈ Legacy.grade C Y X 1) : Simple Y := by
  let F := Legacy.evenToTotal C
  apply simple_of_mono_end hsemi Y
  · intro hy
    have hx : 𝟙 X = 0 := by
      apply F.map_injective
      rw [CategoryTheory.Functor.map_id, Functor.map_zero]
      have hy' := congrArg F.map hy
      rw [CategoryTheory.Functor.map_id, Functor.map_zero] at hy'
      calc
        𝟙 (F.obj X) = e.hom ≫ 𝟙 (F.obj Y) ≫ e.inv := by
          rw [Category.id_comp]
          exact e.hom_inv_id.symm
        _ = 0 := by rw [hy']; simp
    exact id_nonzero X hx
  · intro f hf
    let q := e.hom ≫ F.map f ≫ e.inv
    have hq : q ∈ Legacy.grade C X X 0 := by
      have hh := Legacy.tComp_mem_grade C e.hom
        (Legacy.tComp C.data (F.map f) e.inv) he
        (Legacy.tComp_mem_grade C (F.map f) e.inv (Legacy.evenPoint_mem_grade C f) hi)
      exact hh
    let g : X ⟶ X := liftEven C q hq
    have hgmap : F.map g = q := liftEven_map C q hq
    have hg : g ≠ 0 := by
      intro hz
      have hqz : q = 0 := by rw [← hgmap, hz, Functor.map_zero]
      have hfz : F.map f = 0 := by
        calc
          F.map f = e.inv ≫ q ≫ e.hom := by simp [q]
          _ = 0 := by rw [hqz]; simp
      exact hf ((Functor.map_eq_zero_iff F).mp hfz)
    haveI : IsIso g := isIso_of_hom_simple hg
    haveI : IsIso q := hgmap ▸ (inferInstance : IsIso (F.map g))
    haveI : IsIso (F.map f) := by
      have h : F.map f = e.inv ≫ q ≫ e.hom := by simp [q]
      rw [h]
      infer_instance
    exact F.mono_of_mono_map inferInstance

/-- A nonzero homogeneous map between simples is invertible in the total category. -/
theorem graded_schur (p : Legacy.ParityShift C)
    (X Y : Legacy.Even C) (hX : Simple X) (hY : Simple Y)
    (a : ZMod 2) (f : Legacy.THom C.data X Y)
    (hf : f ∈ Legacy.grade C X Y a) (hne : f ≠ 0) :
    @IsIso (Legacy.TotalCategory C) _ X Y f := by
  let F := Legacy.evenToTotal C
  haveI := hX
  haveI := hY
  rcases Classification.parity_cases a with rfl | rfl
  · let g : X ⟶ Y := liftEven C f hf
    have hg : F.map g = f := liftEven_map C f hf
    haveI : IsIso g := isIso_of_hom_simple (fun hz => hne (by rw [← hg, hz, Functor.map_zero]))
    exact hg ▸ (inferInstance : IsIso (F.map g))
  · let P : Legacy.Even C := Legacy.evenObj C (p.data.functor.obj X)
    let e : F.obj X ≅ F.obj P :=
      ⟨Legacy.homogeneousPoint 1 (p.data.hom X), Legacy.homogeneousPoint 1 (p.data.inv X),
        p.laws.hom_inv X, p.laws.inv_hom X⟩
    have he : e.hom ∈ Legacy.grade C X P 1 := by
      intro b hb
      simp [e, Legacy.homogeneousPoint, hb]
    have hi : e.inv ∈ Legacy.grade C P X 1 := by
      intro b hb
      simp [e, Legacy.homogeneousPoint, hb]
    haveI : Simple P := simple_of_odd_iso C hsemi e he hi
    let q := e.inv ≫ f
    have hq : q ∈ Legacy.grade C P Y 0 := Legacy.tComp_mem_grade C e.inv f hi hf
    let g : P ⟶ Y := liftEven C q hq
    have hgmap : F.map g = q := liftEven_map C q hq
    have hg : g ≠ 0 := by
      intro hz
      have hqz : q = 0 := by rw [← hgmap, hz, Functor.map_zero]
      apply hne
      calc
        f = e.hom ≫ q := by simp [q]
        _ = 0 := by rw [hqz]; simp
    haveI : IsIso g := isIso_of_hom_simple hg
    have heq : (e ≪≫ F.mapIso (asIso g)).hom = f := by
      change e.hom ≫ F.map g = f
      rw [hgmap]
      simp [q]
    exact heq ▸ (e ≪≫ F.mapIso (asIso g)).isIso_hom

end
end RMod.EnrichedSupport
