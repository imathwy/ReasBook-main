import StacksProject_2024.stacks_project.Chap22.Lemma_22_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uE vE uO vO

section

variable {DE : Type uE} {DO : Type uO}
variable [Category.{vE} DE] [Category.{vO} DO]
variable [Preadditive DO] [HasCoproducts.{max uO vO} DO]
variable [HasShift DE ℤ] [HasShift DO ℤ]
variable (derivedTensorWithK : DE ⥤ DO) [derivedTensorWithK.CommShift ℤ]
variable (Eunit : DE) (Kbullet : DO)

-- Semantic recall: Lemma `22.35.4` identifies the canonical Ext map with `ShiftedHom.map`, while
-- Lemma `22.33.7` already owns the fully-faithful criterion with the explicit shifted target.
-- This file is the source-facing specialization from `N` to `K^bullet`.

omit [derivedTensorWithK.CommShift ℤ] in
/-- Lemma 22.35.6: let `(C, O)` be a ringed site, let `K^bullet` be a complex of
`O`-modules, and let
`derivedTensorWithK : D(E, d) ⥤ D(O)`, given source-faithfully by derived tensoring with
`K^bullet` over `E`, be the functor of
Lemma `22.35.3`. If the canonical left-adjoint structure from Lemma `22.35.5` is fixed,
`Eunit` maps to `K^bullet`, the shifted free objects `Eunit[n]` map to the shifted complex
`K^bullet[n]`, `K^bullet` is compact in `D(O)`, and the induced self-Ext maps
`Hom(Eunit, Eunit[n]) → Hom(K^bullet, K^bullet[n])`
are bijective for every `n : ℤ`, then the induced map on every Hom-set is bijective, i.e.
the derived tensor functor is fully faithful. -/
@[stacks 09LZ]
theorem derivedTensorWithK_fullyFaithful_of_compact_of_selfExtComputes
    (hLeftAdjoint : Functor.IsLeftAdjoint derivedTensorWithK)
    (hTensorUnit : derivedTensorWithK.obj Eunit ≅ Kbullet)
    (hTensorShift :
      ∀ n : ℤ,
        derivedTensorWithK.obj ((shiftFunctor DE n).obj Eunit) ≅
          (shiftFunctor DO n).obj Kbullet)
    (hKCompact : IsCompactObject Kbullet)
    (hSelfExtComputes :
      ∀ n : ℤ,
        Function.Bijective
          (tensorSelfExtMap derivedTensorWithK Eunit Kbullet hTensorUnit hTensorShift n))
    (X Y : DE) :
    Function.Bijective
      (derivedTensorWithK.map : (X ⟶ Y) → (derivedTensorWithK.obj X ⟶ derivedTensorWithK.obj Y)) :=
  by
  letI := hLeftAdjoint
  simpa using
    derivedTensorWithN_fullyFaithful_of_compact_of_selfExt
      derivedTensorWithK Eunit Kbullet hLeftAdjoint
      hTensorUnit hTensorShift hKCompact hSelfExtComputes X Y

omit [derivedTensorWithK.CommShift ℤ] in
/-- Bundled fully-faithful witness extracted from Lemma `22.35.6`. -/
theorem derivedTensorWithK_fullyFaithful_nonempty_of_compact_of_selfExtComputes
    (hLeftAdjoint : Functor.IsLeftAdjoint derivedTensorWithK)
    (hTensorUnit : derivedTensorWithK.obj Eunit ≅ Kbullet)
    (hTensorShift :
      ∀ n : ℤ,
        derivedTensorWithK.obj ((shiftFunctor DE n).obj Eunit) ≅
          (shiftFunctor DO n).obj Kbullet)
    (hKCompact : IsCompactObject Kbullet)
    (hSelfExtComputes :
      ∀ n : ℤ,
        Function.Bijective
          (tensorSelfExtMap derivedTensorWithK Eunit Kbullet hTensorUnit hTensorShift n)) :
    Nonempty derivedTensorWithK.FullyFaithful := by
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  intro X Y
  simpa using
    derivedTensorWithK_fullyFaithful_of_compact_of_selfExtComputes
      derivedTensorWithK Eunit Kbullet hLeftAdjoint hTensorUnit hTensorShift
      hKCompact hSelfExtComputes X Y

end
