import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_8_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/- Semantic recall for this item:
`Scheme.bigPhSite` is the Chapter 34 owner for the big ph slice site `(\mathit{Sch}/S)_{ph}`.
Lemma 34.8.15 supplies the source-facing sheaf criterion for that concrete presentation on
`Over S` by Zariski coverings together with proper-surjective singleton coverings. -/

section

variable {S : Scheme.{u}}

/-- The equalizer target attached to a singleton covering `{V ⟶ U}` in `(Sch/S)`. -/
def ProperSurjectiveEqualizer
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) : Type v :=
  { s : F.obj (op V) //
      F.map (Limits.pullback.fst f f).op s = F.map (Limits.pullback.snd f f).op s }

/-- Restricting a section on `U` along a singleton cover `{V ⟶ U}` lands in the corresponding
equalizer. -/
theorem properSurjectiveEqualizerMap_property
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) (s : F.obj (op U)) :
    F.map (Limits.pullback.fst f f).op (F.map f.op s) =
      F.map (Limits.pullback.snd f f).op (F.map f.op s) := by
  simpa [FunctorToTypes.map_comp_apply] using
    congrArg (fun k : pullback f f ⟶ U ↦ F.map k.op s)
      (Limits.pullback.condition : Limits.pullback.fst f f ≫ f = Limits.pullback.snd f f ≫ f)

/-- The canonical map from sections on `U` to the equalizer attached to `{V ⟶ U}`. -/
def properSurjectiveEqualizerMap
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) :
    F.obj (op U) → ProperSurjectiveEqualizer F f :=
  fun s ↦ ⟨F.map f.op s, properSurjectiveEqualizerMap_property F f s⟩

/-- The singleton-cover formulation of the proper-surjective sheaf condition from Lemma 34.8.15. -/
abbrev satisfiesProperSurjectiveSingletonSheafCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsProper f.left] [Surjective f.left],
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- The affine-target singleton-cover formulation from Lemma 34.8.15. -/
abbrev satisfiesAffineProperSurjectiveSingletonSheafCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsAffine U.left] [IsProper f.left] [Surjective f.left],
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- For a singleton cover `{V ⟶ U}` in `(Sch/S)`, the source equalizer condition is exactly the
canonical singleton presieve sheaf condition. -/
theorem isSheafFor_singleton_iff_bijective_properSurjectiveEqualizerMap
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) :
    Presieve.IsSheafFor F (Presieve.singleton f) ↔
      Function.Bijective (properSurjectiveEqualizerMap F f) := by
  have hfork :
      F.map f.op ≫ F.map (Limits.pullback.fst f f).op =
        F.map f.op ≫ F.map (Limits.pullback.snd f f).op := by
    ext s
    exact properSurjectiveEqualizerMap_property F f s
  have hsingleton :
      Presieve.IsSheafFor F (Presieve.singleton f) ↔
        Nonempty (IsLimit (Fork.ofι (F.map f.op) hfork)) := by
    simpa [hfork] using
      (Equalizer.Presieve.isSheafFor_singleton_iff_of_hasPullback :
        Presieve.IsSheafFor F (Presieve.singleton f) ↔ _)
  rw [hsingleton]
  rw [Limits.Types.type_equalizer_iff_unique]
  constructor
  · intro h
    constructor
    · intro s₁ s₂ hs
      have hsval : F.map f.op s₁ = F.map f.op s₂ := by
        simpa using congrArg Subtype.val hs
      let y : F.obj (op V) := F.map f.op s₁
      have hy :
          F.map (Limits.pullback.fst f f).op y =
            F.map (Limits.pullback.snd f f).op y := by
        simpa [y] using properSurjectiveEqualizerMap_property F f s₁
      rcases h y hy with ⟨t, ht, huniq⟩
      have hs₁' : s₁ = t := huniq s₁ (by simpa [y] using rfl)
      have hs₂' : s₂ = t := huniq s₂ (by simpa [y] using hsval.symm)
      exact hs₁'.trans hs₂'.symm
    · intro s
      rcases h s.1 s.2 with ⟨t, ht, _⟩
      exact ⟨t, Subtype.ext ht⟩
  · intro h s hs
    rcases h.2 ⟨s, hs⟩ with ⟨t, ht⟩
    refine ⟨t, ?_, ?_⟩
    · simpa using congrArg Subtype.val ht
    intro t' ht'
    apply h.1
    exact Subtype.ext (ht'.trans (congrArg Subtype.val ht).symm)

/-- The proper-surjective equalizer condition from Lemma 34.8.15. -/
def satisfiesProperSurjectiveEqualizerCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsProper f.left] [Surjective f.left],
    Function.Bijective (properSurjectiveEqualizerMap F f)

/-- The affine-target version of the proper-surjective equalizer condition from Lemma 34.8.15. -/
def satisfiesAffineProperSurjectiveEqualizerCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsAffine U.left] [IsProper f.left] [Surjective f.left],
    Function.Bijective (properSurjectiveEqualizerMap F f)

/-- The source equalizer condition from Lemma 34.8.15 is equivalent to the canonical singleton
presieve sheaf condition on each proper-surjective singleton cover. -/
theorem satisfiesProperSurjectiveEqualizerCondition_iff_singletonSheafCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    satisfiesProperSurjectiveEqualizerCondition F ↔
      satisfiesProperSurjectiveSingletonSheafCondition F := by
  constructor
  · intro h U V f _ _
    exact (isSheafFor_singleton_iff_bijective_properSurjectiveEqualizerMap F f).2 (h f)
  · intro h U V f _ _
    exact (isSheafFor_singleton_iff_bijective_properSurjectiveEqualizerMap F f).1 (h f)

/-- The affine-target equalizer condition from Lemma 34.8.15 is equivalent to the canonical
singleton presieve sheaf condition on affine proper-surjective singleton covers. -/
theorem satisfiesAffineProperSurjectiveEqualizerCondition_iff_singletonSheafCondition
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    satisfiesAffineProperSurjectiveEqualizerCondition F ↔
      satisfiesAffineProperSurjectiveSingletonSheafCondition F := by
  constructor
  · intro h U V f _ _ _
    exact (isSheafFor_singleton_iff_bijective_properSurjectiveEqualizerMap F f).2 (h f)
  · intro h U V f _ _ _
    exact (isSheafFor_singleton_iff_bijective_properSurjectiveEqualizerMap F f).1 (h f)

/-- Lemma 34.8.15 (1): a presheaf on `(Sch/S)_{ph}` is a sheaf if and only if it satisfies the
sheaf condition for Zariski coverings and the equalizer condition for every proper surjective
singleton covering `{V ⟶ U}`. -/
@[stacks 04B9]
theorem isSheaf_bigPhSite_iff
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (Scheme.bigPhSite S) F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        satisfiesProperSurjectiveEqualizerCondition F := sorry

/-- Lemma 34.8.15 (2): assuming the Zariski sheaf condition, the proper-surjective equalizer
condition can be checked on affine targets. -/
@[stacks 04B9]
theorem properSurjectiveEqualizerCondition_iff_affine
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hzar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) :
    satisfiesProperSurjectiveEqualizerCondition F ↔
      satisfiesAffineProperSurjectiveEqualizerCondition F := sorry

end

end AlgebraicGeometry
