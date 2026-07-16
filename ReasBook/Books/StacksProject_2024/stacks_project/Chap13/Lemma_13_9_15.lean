import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

section

variable [HasBinaryBiproducts 𝒜]

/- Domain-style sampling for Lemma 13.9.15:
- primary domain: finite composable rows of cochain complexes and commutative ladders whose
  horizontal maps are termwise split monomorphisms and whose vertical maps are homotopy
  equivalences;
- sampled owner declarations:
  `CategoryTheory.ComposableArrows`,
  `CategoryTheory.ComposableArrows.arrow`,
  `CochainComplex.splitMono_factorization_through_biproduct_mappingCone_id`,
  `HomologicalComplex.homotopyEquivalences`;
- best owner abstraction: the ladder data already lives canonically as a morphism
  `φ : T ⟶ S` in `ComposableArrows`, and the horizontal edges are canonically indexed by `Fin n`;
  the split-mono and homotopy-equivalence conditions are theorem-side properties expressed
  componentwise by the canonical owners `IsSplitMono` and `homotopyEquivalences`; the boundedness
  clauses likewise belong directly to the existing owners `CochainComplex.plus`,
  `CochainComplex.minus`, and `CochainComplex.bounded`;
- source/core/bridge triage:
  `source-facing`: existence of a replacement row with split-monomorphic horizontal maps and
    homotopy-equivalent vertical comparison maps;
  `core/canonical`: `ComposableArrows`, `IsSplitMono`, `homotopyEquivalences`, and the
    cochain-complex boundedness owners;
  `bridge/view`: the componentwise predicates imposed on the existing ladder morphism `φ`.
- primitive data: only the replacement row `T` and comparison morphism `φ : T ⟶ S`;
- derived API: the componentwise split-mono, homotopy-equivalence, and boundedness-preservation
  clauses.

This theorem should therefore quantify directly over the canonical owner `φ : T ⟶ S` instead of
introducing a separate wrapper class for these theorem-side properties.
-/

-- Proof sketch: argue by induction on the length of the composable sequence. The case of a single
-- object is trivial. For the induction step, first construct the replacement up to the penultimate
-- complex, then apply Lemma 13.9.6 to the composite from the last replacement complex to the final
-- complex to extend the diagram by one more term. The boundedness assertions are propagated at
-- each step using the corresponding boundedness clauses in Lemma 13.9.6.
/-- Lemma 13.9.15: every finite composable sequence of cochain complexes in an additive category
admits a commutative diagram from another sequence whose successive maps are termwise split
injections and whose vertical maps to the original sequence are homotopy equivalences; moreover,
if the original sequence is termwise bounded below, bounded above, or bounded, then the replacing
sequence has the same property termwise. -/
@[stacks 014M]
theorem exists_splitMono_homotopyReplacement
    {n : ℕ} (S : ComposableArrows (Comp(𝒜)) n) :
    ∃ (T : ComposableArrows (Comp(𝒜)) n) (φ : T ⟶ S),
      (∀ i : Fin n, ∀ k : ℤ, IsSplitMono ((T.map' i.1 (i.1 + 1)).f k)) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences 𝒜 (up ℤ) (φ.app i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (T.obj i)) := by
  sorry

end

end ComposableArrows

end CategoryTheory
