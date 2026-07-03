import Mathlib
import StacksProject_2024.Chap12.Lemma_12_13_9
import StacksProject_2024.Chap15.Lemma_15_88_1_Base

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

/- Domain-style sampling for Lemma 15.88.7:
- primary domain: cochain-complex representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`, together with their stagewise restriction maps;
- sampled declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `DerivedCategory.Q.objObjPreimageIso`,
  `sequentialRingedModuleCochainEvaluationStep`,
  `cochainComplex_epi_iff_degreewise_epi`;
- best owner abstraction: a representative complex `M` together with its canonical identification
  `DerivedCategory.Q.obj M ≅ K`; the chosen preimage `DerivedCategory.Q.objPreimage K` is only an
  internal bridge to that owner surface;
- target layer here: the `source-facing` existence of a representative whose stagewise transition
  maps are termwise epimorphic, together with the bridge/view expressing the same condition as a
  complex-level `Epi`;
- primitive data: the representative complex `M` and its isomorphism `DerivedCategory.Q.obj M ≅
  K`;
- derived API: the stagewise evaluation complexes and their restriction maps; the complex-level
  `Epi` formulation is derived from the source-facing degreewise condition via
  `cochainComplex_epi_iff_degreewise_epi`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise transition maps are
  termwise surjective;
- `core/canonical`: the derived-category realization owner `DerivedCategory.Q.obj`;
- `bridge/view`: the internal preimage comparison `DerivedCategory.Q.objObjPreimageIso K` and the
  cochain-level evaluation-step morphisms `sequentialRingedModuleCochainEvaluationStep A ρ n`. -/

-- Proof sketch: start from the canonical preimage complex `DerivedCategory.Q.objPreimage K`.
-- Evaluating it at each stage `n` gives the system of complexes `M_n^•`, and the structural
-- restriction maps in `\mathrm{Mod}(\mathbf N, (A_n))` induce the transition morphisms
-- `M_{n + 1}^• → M_n^•` after restriction of scalars. Apply Lemma `13.9.8` inductively to replace
-- this canonical preimage by a quasi-isomorphic complex with termwise surjective transition maps.
private theorem exists_complex_representation_with_surjective_transition_maps_to_preimage
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (α : M ⟶ DerivedCategory.Q.objPreimage K),
      QuasiIso α ∧
      ∀ n i,
        Epi (((sequentialRingedModuleCochainEvaluationStep A ρ n).app M).f i) := sorry

/-- Lemma 15.88.7: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object
`K ∈ D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a cochain-complex representative `M^•` in
`\mathrm{Mod}(\mathbf N, (A_n))` whose evaluated transition maps
`M_{n + 1}^• → M_n^•` are termwise epimorphic, equivalently termwise surjective after
restriction of scalars along `A_{n + 1} → A_n`. -/
theorem exists_complex_representation_with_surjective_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n i,
        Epi (((sequentialRingedModuleCochainEvaluationStep A ρ n).app M).f i) := by
  obtain ⟨M, α, hα, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps_to_preimage K
  letI : QuasiIso α := hα
  refine ⟨M, asIso (DerivedCategory.Q.map α) ≪≫ DerivedCategory.Q.objObjPreimageIso K, hM⟩

/-- Companion bridge for Lemma 15.88.7: the same representative may be chosen so that every
evaluated transition map `M_{n + 1}^• → M_n^•` is an epimorphism of cochain complexes. -/
theorem exists_complex_representation_with_epi_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n,
        Epi ((sequentialRingedModuleCochainEvaluationStep A ρ n).app M) := by
  obtain ⟨M, e, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps K
  refine ⟨M, e, ?_⟩
  intro n
  exact (cochainComplex_epi_iff_degreewise_epi
    ((sequentialRingedModuleCochainEvaluationStep A ρ n).app M)).2 (hM n)

end
