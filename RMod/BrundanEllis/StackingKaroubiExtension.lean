import RMod.BrundanEllis.StackingKaroubiRetraction
import RMod.BrundanEllis.StackingKaroubiRealization

/-! Extend an enriched functor to its source completion by splitting the
image corner in the target. Full graded faithfulness and retract density
then give an equivalence of the underlying even categories. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C D : Type} [SuperCategory C] [SuperCategory D] [IsIdempotentComplete (Even D)]

/-- Complete on the source and split the resulting corner on the target. -/
def extension (F : SuperFunctor C D) : SuperFunctor (Karoubi (Even C)) D :=
  (functor F).comp SuperVec (retraction D)

theorem extension_bijective (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (P Q : Karoubi (Even C)) (a : ZMod 2) :
    Function.Bijective ((extension F).map P Q a) :=
  (retraction_bijective D (mapObject F P) (mapObject F Q) a).comp
    (functor_bijective F hF P Q a)

/-- The extension agrees with the original functor on trivial corners. -/
def extensionEmbeddingIso (F : SuperFunctor C D) (X : Even C) :
    (extension F).forget.obj ((embedding C).forget.obj X) ≅ F.forget.obj X := by
  apply (embedding D).forget.preimageIso
  exact retractComparison D (mapObject F (original C (ForgetEnrichment.to SuperVec X))) ≪≫
    ((evenEquivalence (C := D)).inverse.mapIso (ordinaryEmbeddingIso F X)).symm

instance evenIdempotentComplete : IsIdempotentComplete (Even (Karoubi (Even C))) :=
  (isIdempotentComplete_iff_of_equivalence (evenEquivalence (C := C))).mpr inferInstance

/-- Full faithfulness and the concrete retract presentation give essential surjectivity. -/
def extensionEquivalence (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (h : ∀ W : Even D, ∃ X : Even C, Nonempty (Retract W (F.forget.obj X))) :
    Even (Karoubi (Even C)) ≌ Even D := by
  let J := (extension F).forget
  let ff := forgetFullyFaithful (extension F) (extension_bijective F hF)
  letI : J.Full := ff.full
  letI : J.Faithful := ff.faithful
  letI : J.EssSurj := essSurj_of_retracts J (fun W => by
    obtain ⟨X, ⟨r⟩⟩ := h W
    exact ⟨(embedding C).forget.obj X, ⟨r.trans (Retract.ofIso (extensionEmbeddingIso F X).symm)⟩⟩)
  letI : J.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact J.asEquivalence

end RMod.BrundanEllis.Stacking.KaroubiSuper
