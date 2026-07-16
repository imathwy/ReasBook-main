import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_20_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_40_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Helper for Lemma 18.40.12: after rewriting the localized structure sheaf as a pullback along
`Over.forget U`, the `18.40.2.1` equalizer map is just the image of the base equalizer map. -/
private theorem isIso_oneNeverZeroEqualizerMap_over
    (U : C) [IsIso (oneNeverZeroEqualizerMap 𝒪)] :
    IsIso (oneNeverZeroEqualizerMap (𝒪.over U)) := by
  -- Proof comment: compare the localized source via the Chapter 7 sheafification/restriction
  -- isomorphism, compare the localized target via equalizer preservation, and then use
  -- initiality of the source to identify the transported morphism with the canonical slice map.
  let F : Sheaf J (Type (max u v)) ⥤ Sheaf (J.over U) (Type (max u v)) :=
    J.overPullback (Type (max u v)) U
  letI :
      IsIso
        ((Over.forget U).pushforwardContinuousSheafificationComparison
          (J.over U) J) :=
    Functor.pushforwardContinuousSheafificationComparison_isIso
      (G := Over.forget U) (J := J.over U) (K := J)
  let emptyRestrictionIso :
      ((Over.forget U).op ⋙ (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) ≅
        (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v))) :=
    Limits.PreservesInitial.iso
      ((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type (max u v))).obj (Over.forget U).op)
  let α :
      (presheafToSheaf (J.over U) (Type (max u v))).obj
          (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v))) ≅
        F.obj ((presheafToSheaf J (Type (max u v))).obj
          (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) := by
    exact
      (Functor.mapIso (presheafToSheaf (J.over U) (Type (max u v))) emptyRestrictionIso).symm ≪≫
        (asIso
          ((Over.forget U).pushforwardContinuousSheafificationComparison
            (J.over U) J)).app (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
  let β :
      F.obj (Limits.equalizer (zeroSection 𝒪) (oneSection 𝒪)) ≅
        Limits.equalizer (zeroSection (𝒪.over U)) (oneSection (𝒪.over U)) := by
    -- The slice restriction functor preserves equalizers, and the localized zero/one sections are
    -- the images of the ambient zero/one sections.
    simpa [F, Sheaf.over, GrothendieckTopology.overPullback] using
      (Limits.PreservesEqualizer.iso F (zeroSection 𝒪) (oneSection 𝒪))
  let m :
      (presheafToSheaf (J.over U) (Type (max u v))).obj
          (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v))) ⟶
        Limits.equalizer (zeroSection (𝒪.over U)) (oneSection (𝒪.over U)) :=
    α.hom ≫ F.map (oneNeverZeroEqualizerMap 𝒪) ≫ β.hom
  have hMap : IsIso (F.map (oneNeverZeroEqualizerMap 𝒪)) := by
    exact Functor.map_isIso F (oneNeverZeroEqualizerMap 𝒪)
  have hmIso : IsIso m := by
    dsimp [m]
    infer_instance
  let S :
      Sheaf (J.over U) (Type (max u v)) :=
    (presheafToSheaf (J.over U) (Type (max u v))).obj
      (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v)))
  letI : ∀ Y : Sheaf (J.over U) (Type (max u v)), Unique (S ⟶ Y) :=
    fun Y ↦
      { default :=
          ((sheafificationAdjunction (J.over U) (Type (max u v))).homEquiv
            (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v))) Y).symm
            (Limits.initial.to ((sheafToPresheaf (J.over U) (Type (max u v))).obj Y))
        uniq := fun f ↦ by
          apply
            ((sheafificationAdjunction (J.over U) (Type (max u v))).homEquiv
              (⊥_ ((Over U)ᵒᵖ ⥤ Type (max u v))) Y).injective
          exact Limits.IsInitial.hom_ext Limits.initialIsInitial _ _ }
  have hInitial :
      Limits.IsInitial S :=
    Limits.IsInitial.ofUnique S
  have hm :
      m = oneNeverZeroEqualizerMap (𝒪.over U) :=
    hInitial.hom_ext _ _
  simpa [hm] using hmIso

-- Proof sketch: apply Lemma `18.40.5 (1)` to the localization functor
-- `Over.forget U : C/U ⥤ C`; its inverse image on commutative ring sheaves is exactly the
-- restricted structure sheaf `\mathcal O_U`.
/-- Lemma 18.40.12 (1): if `(\mathcal C, \mathcal O)` is a locally ringed site and `U` is an
object of `\mathcal C`, then the localization `(\mathcal C/U, \mathcal O_U)` is a locally
ringed site. -/
theorem localization_isLocallyRingedSite
    (U : C) [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite ((J.overPullback CommRingCat.{max u v} U).obj 𝒪) := by
  -- Route correction: the owner theorem is blocked by a universe restriction on `Over U`, so we
  -- rebuild the two defining fields locally and keep the equalizer clause in a one-line helper.
  -- The `0 = 1` equalizer clause descends by functoriality of the slice pullback.
  letI : IsIso (oneNeverZeroEqualizerMap (𝒪.over U)) :=
    isIso_oneNeverZeroEqualizerMap_over (𝒪 := 𝒪) U
  -- The direct localization functor also carries the local-unit dichotomy to the slice site.
  letI : HasLocalUnitDichotomy (J.over U) (𝒪.over U) := by
    refine
      { local_unit_dichotomy := fun X f ↦ ?_ }
    -- Pull the covering family back from the underlying object `X.left`.
    obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) X.left f
    let SOver : (J.over U).Cover X :=
      ⟨(Sieve.overEquiv X).symm (S : Sieve X.left), by
        -- Covers on the slice site are exactly the base covers under `Sieve.overEquiv`.
        rw [GrothendieckTopology.mem_over_iff]
        simpa using S.property⟩
    refine ⟨SOver, ?_⟩
    intro I
    -- Convert the localized cover arrow to the corresponding base-cover arrow.
    let iOver : I.Y ⟶ X := I.f
    have hI : ((S : Sieve X.left).arrows iOver.left) := by
      have hIOver : ((Sieve.overEquiv X) SOver.1).arrows iOver.left := by
        rw [Sieve.overEquiv_iff]
        exact I.hf
      simpa [SOver] using hIOver
    let IBase : S.Arrow := ⟨I.Y.left, iOver.left, hI⟩
    -- Restriction in the localized structure sheaf is the ambient restriction map.
    simpa [Sheaf.over, GrothendieckTopology.overPullback] using hS IBase
  -- The localized structure sheaf is definitionally `𝒪.over U`.
  simpa [Sheaf.over, GrothendieckTopology.overPullback] using
    (instIsLocallyRingedSiteOfConditions (J := J.over U) (𝒪 := 𝒪.over U))

end

end CategoryTheory
