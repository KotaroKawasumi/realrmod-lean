import RMod.BrundanEllis.StackingKaroubiFaithful
import RMod.BrundanEllis.StackingRetractImage

/-! A fully faithful exterior model whose objects are retracts of paired
objects realizes the ordinary idempotent completion. This equivalence
transports categorical properties without choosing extra mathematical data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D]

/-- Apply the underlying even functor to a corner and its arrows. -/
def ordinaryFunctor (F : SuperFunctor C D) : Karoubi (Even C) ⥤ Karoubi (Even D) where
  obj := mapObject F
  map f := {
    f := F.forget.map f.f
    comm := by
      change F.forget.map _ ≫ F.forget.map _ ≫ F.forget.map _ = _
      rw [← F.forget.map_comp, ← F.forget.map_comp, f.comm] }
  map_id P := Karoubi.hom_ext _ _ rfl
  map_comp f g := Karoubi.hom_ext _ _ (F.forget.map_comp f.f g.f)

/-- The image of a trivial corner is the trivial corner of the image. -/
def ordinaryEmbeddingIso (F : SuperFunctor C D) (X : Even C) :
    (toKaroubi (Even D)).obj (F.forget.obj X) ≅
      (ordinaryFunctor F).obj ((toKaroubi (Even C)).obj X) where
  hom := {
    f := 𝟙 _
    comm := by
      change 𝟙 _ ≫ 𝟙 _ ≫ F.forget.map (𝟙 X) = 𝟙 _
      simp only [CategoryTheory.Functor.map_id, Category.id_comp] }
  inv := {
    f := 𝟙 _
    comm := by
      change F.forget.map (𝟙 X) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp only [CategoryTheory.Functor.map_id, Category.id_comp] }
  hom_inv_id := by
    apply Karoubi.hom_ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  inv_hom_id := by
    apply Karoubi.hom_ext
    change 𝟙 _ ≫ 𝟙 _ = F.forget.map (𝟙 X)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]

variable (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))

/-- Full faithfulness restricts to idempotent corners on even arrows. -/
def ordinaryFullyFaithful : (ordinaryFunctor F).FullyFaithful := by
  let h := forgetFullyFaithful F hF
  letI := h.full
  letI := h.faithful
  refine {
    preimage := fun {P Q} f => {
      f := F.forget.preimage f.f
      comm := ?_ }
    map_preimage := fun f => Karoubi.hom_ext _ _ (F.forget.map_preimage f.f)
    preimage_map := fun f => Karoubi.hom_ext _ _ (F.forget.preimage_map f.f) }
  apply F.forget.map_injective
  simp only [CategoryTheory.Functor.map_comp, F.forget.map_preimage]
  exact f.comm

/-- A retract-dense enriched functor realizes the ordinary completion. -/
def realization [IsIdempotentComplete (Even D)]
    (h : ∀ W : Even D, ∃ X : Even C, Nonempty (Retract W (F.forget.obj X))) :
    Even (Karoubi (Even C)) ≌ Even D := by
  let J := ordinaryFunctor F
  let ff := ordinaryFullyFaithful F hF
  letI : J.Full := ff.full
  letI : J.Faithful := ff.faithful
  letI : J.EssSurj := essSurj_of_retracts J (fun P => by
    obtain ⟨X, ⟨r⟩⟩ := h P.X
    exact ⟨(toKaroubi (Even C)).obj X, ⟨(Karoubi.retract P).trans
      ((r.map (toKaroubi (Even D))).trans (Retract.ofIso (ordinaryEmbeddingIso F X)))⟩⟩)
  letI : J.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact (evenEquivalence (C := C)).trans
    (J.asEquivalence.trans (toKaroubiEquivalence (Even D)).symm)

end RMod.BrundanEllis.Stacking.KaroubiSuper
