import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import stacks_project.Chap15.Lemma_15_59_10
import stacks_project.Chap15.Lemma_15_88_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [∀ n : ℕ, MonoidalCategory (ModuleCat (A n))]
variable [∀ n : ℕ, (curriedTensor (ModuleCat (A n))).Additive]
variable [∀ n : ℕ,
  ∀ X : ModuleCat (A n), ((curriedTensor (ModuleCat (A n))).obj X).Additive]

attribute [local instance] seqRingMod_abelian

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/- Domain-style sampling for Lemma 15.88.8:
- primary domain: K-flat stagewise representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`;
- sampled owner declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `sequentialRingedModuleCochainEval`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.exists_epi_kFlatResolution`;
- best owner abstraction: a representative complex `M` together with an isomorphism
  `DerivedCategory.Q.obj M ≅ K`, with each stagewise evaluation complex carrying the canonical
  owner predicate `IsKFlat`;
- target layer here: a source-facing existence statement asserting that the stagewise evaluations
  of one representing complex satisfy the canonical K-flatness owner;
- primitive data: the representative complex `M` and its realization isomorphism
  `DerivedCategory.Q.obj M ≅ K`;
- derived API: the stagewise K-flatness assertions obtained by applying
  `sequentialRingedModuleCochainEval` and then the owner predicate `IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise evaluations are
  K-flat;
- `core/canonical`: `DerivedCategory.Q.obj` for the realization surface and
  `CochainComplex.IsKFlat` for the stagewise property;
- `bridge/view`: `sequentialRingedModuleCochainEvaluation`; the canonical owner-level resolution
  theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10` belongs to the proof
  route, not to the public owner surface. -/

-- Proof sketch: first use the owner-level companion
-- `exists_complex_representation_with_epi_transition_maps` from Lemma `15.88.7` to choose a
-- representative complex `M^•` of `K` whose evaluated transition maps are epimorphisms of
-- cochain complexes; internally this is obtained by replacing the canonical preimage complex
-- `DerivedCategory.Q.objPreimage K` by a quasi-isomorphic one. Then apply the owner-level
-- stagewise resolution theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10`
-- to the evaluated complexes, replacing each stage by a quasi-isomorphic K-flat complex while
-- preserving compatibility with the transition maps, and reassemble the resulting stagewise data
-- into a representing complex of module systems.
/-- Lemma 15.88.8: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a representative by a system of cochain complexes
`(K_n^•)` in which every stage `K_n^•` is K-flat. -/
theorem exists_kFlat_complex_representation
    (K : DModSeq) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        (sequentialRingedModuleCochainEval A ρ n M).IsKFlat := by
  sorry

end
