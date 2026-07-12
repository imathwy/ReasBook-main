import Mathlib
import StacksProject_2024.Chap14.Lemma_14_23_1
import StacksProject_2024.Chap14.Lemma_14_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.2:
- primary domain: chain-complex exactness and Dold-Kan comparison for simplicial objects in an
  abelian category;
- sampled owner declarations:
  `HomologicalComplex.Acyclic`,
  `eilenbergMacLaneExtensionComplex_acyclic`,
  `HomologicalComplex.ExactAt.of_iso`,
  `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
- best owner abstraction: the public theorem should stay at the owner predicate
  `HomologicalComplex.Acyclic` on `s[eilenbergMacLaneExtension A k]`;
- primitive data: the upstream owners `eilenbergMacLaneExtensionComplex A k` and
  `eilenbergMacLaneExtension A k`;
- derived API: transfer of the owner-level model acyclicity across the Dold-Kan counit isomorphism
  and then across the normalized-Moore/alternating-face-map homotopy equivalence.

Source/core/bridge triage:
- `source-facing`: the acyclicity statement for the chain complex `s(E)` attached to the extension
  object `E`;
- `core/canonical`: `HomologicalComplex.Acyclic`,
  `eilenbergMacLaneExtensionComplex_acyclic`, and the Dold-Kan homotopy equivalence;
- `bridge/view`: the proof passes through the owner complex
  `eilenbergMacLaneExtensionComplex A k` and the Dold-Kan counit isomorphism, but introduces no
  parallel local model API. -/

/-- Helper for Lemma 14.23.2: the normalized Moore complex of the simplicial extension object is
exact in every degree. -/
private lemma normalizedMooreComplex_eilenbergMacLaneExtension_exactAt
    (A : 𝒜) (k i : ℕ) :
    ((normalizedMooreComplex 𝒜).obj (eilenbergMacLaneExtension A k)).ExactAt i := by
  -- Rewrite the simplicial extension through the Dold–Kan counit so exactness can be imported
  -- from the acyclic two-term chain model.
  change
    ((normalizedMooreComplex 𝒜).obj (Γ.obj (eilenbergMacLaneExtensionComplex A k))).ExactAt i
  let η := equivalence.counitIso.app (eilenbergMacLaneExtensionComplex A k)
  -- Transport degreewise exactness across the counit isomorphism.
  exact HomologicalComplex.ExactAt.of_iso
    (eilenbergMacLaneExtensionComplex_acyclic A k i) η.symm

/-- Lemma 14.23.2: if `E` is the simplicial object of Lemma 14.22.4 attached to an object `A` and
an integer `k ≥ 0`, then the associated chain complex `s(E)` is acyclic. -/
@[stacks 0196]
theorem alternatingFaceMapComplex_eilenbergMacLaneExtension_acyclic (A : 𝒜) (k : ℕ) :
    s[eilenbergMacLaneExtension A k].Acyclic := by
  intro i
  -- Compare the alternating face map complex with the normalized Moore complex by the standard
  -- Dold–Kan homotopy equivalence.
  let e :
      HomotopyEquiv
        ((normalizedMooreComplex 𝒜).obj (eilenbergMacLaneExtension A k))
        s[eilenbergMacLaneExtension A k] :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  -- Transfer exactness along the quasi-isomorphism supplied by the comparison map.
  exact (exactAt_iff_of_quasiIsoAt e.hom i).mp
    (normalizedMooreComplex_eilenbergMacLaneExtension_exactAt A k i)

end CategoryTheory
