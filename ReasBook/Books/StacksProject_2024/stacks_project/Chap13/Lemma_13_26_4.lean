import Mathlib
import StacksProject_2024.Chap12.Lemma_12_5_13
import StacksProject_2024.Chap12.Lemma_12_19_10
import StacksProject_2024.Chap13.Lemma_13_26_3

noncomputable section

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open FilteredObject.Hom
open scoped CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma `13.26.4`.
- primary domain: strict monomorphisms of finite filtered objects and extension into filtered
  injectives;
- sampled owner declarations:
  `FilteredObject.Hom.Strict`,
  `IsFilteredInjective`,
  `Injective.factors`,
  `Injective.factorThru`,
  `Injective.comp_factorThru`;
- best owner abstraction: the chapter owner `IsFilteredInjective`, with the source-facing
  extension theorem modeled on the theorem-level owner `Injective.factors`; unlike ordinary
  injective objects, no canonical filtered factorization morphism is available here, so the public
  API should stay existential rather than introducing a chosen witness;
- primitive data: a strict monomorphism `u : A ⟶ B` in `Fil^f(𝒜)`, a map `f : A ⟶ I`, and a
  filtered-injective target `I`;
- derived API: only the theorem-level factorization statement below;
- source/core/bridge triage:
  `source-facing`: extension of a morphism across a strict monomorphism in `Fil^f(𝒜)`;
  `core/canonical`: `Strict` and `IsFilteredInjective`;
  `bridge/view`: the theorem below, which is the filtered analogue of `Injective.factors`.
-/

namespace IsFilteredInjective

/-- Helper for Lemma 13.26.4: in an abelian category, the right leg of a pushout square is mono
whenever the left leg is mono. -/
private lemma pushout_right_mono_of_left_mono
    {A B I P : FilteredObject 𝒜} {u : A ⟶ B} {f : A ⟶ I} {b : B ⟶ P} {i : I ⟶ P}
    [Mono u] (sq : IsPushout u f b i) :
    Mono i := by
  -- Proof comment: this is exactly the pushout-stability of monomorphisms from Lemma 12.5.13.
  exact mono_bottom_of_isPushout_of_mono_top sq

/-- Helper for Lemma 13.26.4: the source proof needs only the pushout package consisting of a
commuting square together with a strict monic right leg. -/
private theorem strict_mono_pushout_data
    {A B I : Fil^f(𝒜)} (f : A ⟶ I) (u : A ⟶ B) [Mono u] (hu : Strict u.hom) :
    ∃ (P : FilteredObject 𝒜) (b : B.obj ⟶ P) (i : I.obj ⟶ P),
      u.hom ≫ b = f.hom ≫ i ∧ Mono i ∧ Strict i := by
  -- Route correction: the source-faithful proof is to apply the Chapter 12 pushout theorem
  -- `exists_filtered_pushout_preserving_strictness` to `u.hom` and `f.hom`, then read off the
  -- commuting square, derive `Mono i` from pushout-stability of monomorphisms, and conclude
  -- `Strict i` from the theorem's strictness implication applied to `hu`.
  obtain ⟨P, b, i, sq, hi_strict_of_strict⟩ :=
    exists_filtered_pushout_preserving_strictness (f := u.hom) (g := f.hom)
  have hi_mono : Mono i := pushout_right_mono_of_left_mono (u := u.hom) (f := f.hom) sq
  have hi_strict : Strict i := hi_strict_of_strict hu
  -- Proof comment: the canonical pushout square provides the commuting relation, and the two
  -- structural properties of the right leg are now recorded separately.
  exact ⟨P, b, i, sq.w, hi_mono, hi_strict⟩

/-- Helper for Lemma 13.26.4: once the source square commutes and the right leg is split mono,
postcomposing by its retraction gives the desired extension across `u`. -/
private lemma factorisation_of_commuting_split_mono
    {A B I : Fil^f(𝒜)} {P : FilteredObject 𝒜} (f : A ⟶ I) (u : A ⟶ B)
    (b : B.obj ⟶ P) (i : I.obj ⟶ P) [IsSplitMono i]
    (hcomm : u.hom ≫ b = f.hom ≫ i) :
    u ≫ (b ≫ @retraction (FilteredObject 𝒜) _ _ _ i ‹IsSplitMono i›) = f := by
  let r : P ⟶ I.obj := @retraction (FilteredObject 𝒜) _ _ _ i ‹IsSplitMono i›
  -- Proof comment: use the commuting square, then collapse the ambient split retraction
  -- `i ≫ r = 𝟙` inside `FilteredObject 𝒜`.
  calc
    u ≫ (b ≫ r) = f ≫ i ≫ r := by
      simpa [r, Category.assoc] using congrArg (fun k ↦ k ≫ r) hcomm
    _ = f := by
      simp [r, Category.assoc]

/-- Helper for Lemma 13.26.4: a commuting square with split mono right leg yields an actual
factorization of `f` across `u`. -/
private lemma exists_factor_of_commuting_split_mono
    {A B I : Fil^f(𝒜)} {P : FilteredObject 𝒜} (f : A ⟶ I) (u : A ⟶ B)
    (b : B.obj ⟶ P) (i : I.obj ⟶ P) [IsSplitMono i]
    (hcomm : u.hom ≫ b = f.hom ≫ i) :
    ∃ g : B ⟶ I, u ≫ g = f := by
  -- Proof comment: choose the extension to be the composite with the split retraction of `i`.
  refine ⟨b ≫ @retraction (FilteredObject 𝒜) _ _ _ i ‹IsSplitMono i›, ?_⟩
  exact factorisation_of_commuting_split_mono (f := f) (u := u) b i hcomm

/-- Lemma 13.26.4: a morphism from the source of a strict monomorphism in `Fil^f(𝒜)` to a
filtered injective object factors through that strict monomorphism. -/
theorem factors
    {A B I : Fil^f(𝒜)} [IsFilteredInjective I] (f : A ⟶ I) (u : A ⟶ B) [Mono u]
    (hu : Strict u.hom) :
    ∃ g : B ⟶ I, u ≫ g = f := by
  obtain ⟨P, b, i, hcomm, hi_mono, hi_strict⟩ := strict_mono_pushout_data (f := f) (u := u) hu
  letI : Mono i := hi_mono
  -- Proof comment: Lemma 13.26.3 splits the strict right leg out of the filtered-injective source.
  have hi_split : IsSplitMono i := IsFilteredInjective.isSplitMono_of_strict i hi_strict
  letI : IsSplitMono i := hi_split
  -- Proof comment: the split-mono retraction packages the final extension as an existential.
  exact exists_factor_of_commuting_split_mono (f := f) (u := u) b i hcomm

end IsFilteredInjective

end CategoryTheory
