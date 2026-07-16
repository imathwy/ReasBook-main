import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open LocalizedModule
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R) (I : Ideal R)

local notation "IM" => I • (⊤ : Submodule R M)
local notation "Rs" => Localization S
local notation "Ms" => LocalizedModule S M
local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "IS" => Ideal.map (algebraMap R Rs) I
local notation "mkQIM" => Submodule.mkQ (I • (⊤ : Submodule R M))
local notation "ISM" => IS • (⊤ : Submodule Rs Ms)
local notation "mkQISM" => Submodule.mkQ ISM

/-
Layering for this item:
* source-facing statement: generators of the localization of `M / IM` at `S` already generate some
  away-localization `M_f` for `f ∈ S + I`.
* core/canonical owners: `localizedQuotientEquiv`, `Localization.algEquiv`, and
  `exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top`.
* bridge/view: transport the generation hypothesis across the canonical quotient-localization
  equivalences, apply the owner theorem over `Localization S`, and clear denominators in the
  resulting element of `1 + IS`.
-/

/-- Lemma 10.20.2: if the images of finitely many elements of a finite `R`-module generate the
localization of `M / IM` at `S`, then those elements already generate some away-localization `M_f`
for an element `f ∈ S + I`. -/
-- Proof sketch: use the canonical quotient-localization identifications
-- `localizedQuotientEquiv` and `Localization.algEquiv` to rewrite the hypothesis as a generation
-- statement for `(M_S) / I_S M_S`, where `M_S` is the localization of `M` at `S` and
-- `I_S = I · Localization S`. Apply the owner theorem
-- `exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top` from
-- Lemma `10.20.1` over the localized ring `Localization S`. Finally clear the denominator of the
-- resulting element `g ∈ 1 + I_S` to rewrite the away-localization `(M_S)_g` as `M_f` for some
-- `f ∈ S + I`.
theorem exists_mem_submonoid_add_ideal_and_span_localizedAway_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] {n : ℕ} (x : Fin n → M)
    (hgen :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized Sbar = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      (Submodule.span R (Set.range x)).localized (Submonoid.powers f) = ⊤ := by
  classical
  have hIMs : (I • (⊤ : Submodule R M)).localized S = ISM := by
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top]
  let quotLocalizedEquiv : LocalizedModule S (M ⧸ IM) ≃ₗ[Rs] Ms ⧸ ISM :=
    (localizedQuotientEquiv S IM).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hIMs
  let localizedGenerators : Fin n → Ms := LocalizedModule.mkLinearMap S M ∘ x
  have hgenS :
      Submodule.span Rs (Set.range (mkQISM ∘ localizedGenerators)) = ⊤ := by
    have hgenQ :
        Submodule.span (Localization Sbar)
          (Set.range (LocalizedModule.mkLinearMap Sbar (M ⧸ IM) ∘ mkQIM ∘ x)) = ⊤ := by
      simpa [Submodule.localized, Set.range_comp] using hgen
    -- Transport the localized quotient-generation statement through the canonical owner
    -- equivalences from Proposition `10.9.14` and Lemma `10.9.13`, implemented by
    -- `Localization.algEquiv` and `localizedQuotientEquiv`.
    sorry
  let localizedGeneratorSet : Finset Ms := Finset.univ.image localizedGenerators
  have hgenS' :
      Submodule.span Rs (mkQISM '' (localizedGeneratorSet : Set Ms)) = ⊤ := by
    have hset : (localizedGeneratorSet : Set Ms) = Set.range localizedGenerators := by
      ext y
      simp [localizedGeneratorSet]
    rw [hset]
    simpa [Set.range_comp] using hgenS
  obtain ⟨g, hg, hgspan⟩ :=
    exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top
      IS localizedGeneratorSet hgenS'
  -- Clear a denominator in `g ∈ 1 + IS`; the resulting element has the form `s + i` with
  -- `s ∈ S` and `i ∈ I`, and `(M_S)_g` identifies with the away-localization `M_f`.
  sorry

end
