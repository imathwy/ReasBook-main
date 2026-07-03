import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Lemma_12_24_11

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace FilteredComplex

open FilteredObject

/-
Domain-style sampling for Lemma `13.13.8`.
- primary domain: filtered cochain complexes with finite filtrations, their associated graded
  complexes, and canonical truncation maps on the underlying cochain complex;
- sampled owner declarations in this domain:
  `FilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.associatedGraded`,
  `FilteredComplex.associatedGradedMap`,
  `FilteredComplex.underlyingMap`,
  `QuasiIso`,
  `CochainComplex.πTruncGE`,
  `CochainComplex.ιTruncLE`,
  `CochainComplex.truncGEMap`;
- best owner abstraction: the Chapter `12` owner `FilteredComplex 𝒜`, with the finite-filtration
  hypothesis `K.HasFiniteFiltrations`; the associated-graded comparison lives intrinsically on
  filtered-complex morphisms via `associatedGradedMap`, while the canonical truncations live on
  the underlying cochain complex `K.underlying`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`;
- derived API: the associated graded complex `K.associatedGraded`, the associated-graded map
  `associatedGradedMap f`, the owner-level underlying map `underlyingMap f`, and the canonical
  truncation objects/maps on `K.underlying`, `K.underlying.truncGE a`, `K.underlying.truncLE b`,
  `K.underlying.πTruncGE a`, `K.underlying.ιTruncLE b`, and
  `truncGEMap (K.underlying.ιTruncLE b) a`;
- source/core/bridge triage:
  `source-facing`: vanishing of the cohomology of `gr(K^•)` and the bounded filtered truncation
    replacements;
  `core/canonical`: `FilteredComplex`, `HasFiniteFiltrations`, `associatedGraded`,
    `associatedGradedMap`, `QuasiIso`, and the ordinary cochain-complex truncation owners on
    `K.underlying`;
  `bridge/view`: the comparison from a filtered replacement to the canonical underlying
    truncation.

This file therefore keeps the public statements on the intrinsic owner `FilteredComplex 𝒜`,
retains the finite-filtration hypothesis explicitly, and expresses filtered quasi-isomorphism data
by the canonical condition `QuasiIso (associatedGradedMap f)`. The ordinary truncation owners on
`K.underlying` remain proof-level bridge data rather than part of the public API surface. -/

/-- Lemma 13.13.8 (1): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `< a`, then there exists a filtered
quasi-isomorphism from `K` to a filtered complex whose underlying complex is bounded below by
`a`. -/
theorem exists_filteredQuasiIso_to_boundedBelow_of_associatedGradedCohomologyVanishesBelow
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ L.underlying.IsStrictlyGE a := by
  sorry

/-- Lemma 13.13.8 (2): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `> b`, then there exists a filtered
quasi-isomorphism to `K` from a filtered complex whose underlying complex is bounded above by
`b`. -/
theorem exists_filteredQuasiIso_from_boundedAbove_of_associatedGradedCohomologyVanishesAbove
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K),
      QuasiIso (associatedGradedMap g) ∧ M.underlying.IsStrictlyLE b := by
  sorry

/-- Lemma 13.13.8 (3): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology for `|n| ≫ 0`, then there exists a commutative square of filtered
quasi-isomorphisms
`K ⟶ L`, `M ⟶ K`, `M ⟶ N`, `N ⟶ L`
with `L` bounded below, `M` bounded above, and `N` bounded. -/
theorem exists_filteredQuasiIso_square_with_boundedRepresentatives_of_associatedGradedCohomologyEventuallyVanishes
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations)
    (hgr : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ a b : ℤ,
      ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
        (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
        (N : FilteredComplex 𝒜) (_ : N.HasFiniteFiltrations)
        (u : M ⟶ N) (v : N ⟶ L),
        QuasiIso (associatedGradedMap f) ∧
          QuasiIso (associatedGradedMap g) ∧
          QuasiIso (associatedGradedMap u) ∧
          QuasiIso (associatedGradedMap v) ∧
          CommSq u g v f ∧
          L.underlying.IsStrictlyGE a ∧
          M.underlying.IsStrictlyLE b ∧
          N.underlying.IsStrictlyGE a ∧
          N.underlying.IsStrictlyLE b := by
  sorry

end FilteredComplex

end CategoryTheory
