import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap15.Definition_15_59_1

noncomputable section

universe u

namespace CategoryTheory
namespace FilteredCochainComplex

open FilteredComplex

/- Domain-style sampling for Lemma `15.64.2`.
- primary domain: filtered cochain complexes of `R`-modules, their underlying, stage, and
  graded-piece cochain complexes, and filtered free K-flat resolutions;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex (ModuleCat R)`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.gradedPiece`,
  `FilteredComplex.underlyingMap`,
  `FilteredComplex.stageMap`,
  `FilteredComplex.gradedPieceMap`,
  `CochainComplex.IsTermwiseFree`,
  `CochainComplex.IsKFlat`;
- best owner abstraction:
  `source-facing`: `FilteredCochainComplex (ModuleCat R)` together with the Chapter `12`
    stage notation `F^{p} K` and graded-piece notation `gr^{p} K`;
  `core/canonical`: `FilteredComplex (ModuleCat R)` with `underlying`, `F^{p}(-)`, `gr^{p}(-)`,
    `underlyingMap`, `stageMap`, `gradedPieceMap`, and the Chapter `15` owner
    `CochainComplex.IsKFlat` on the resulting cochain complexes;
- primitive data: a filtered cochain complex `P`, a filtered cochain complex `K`, and a morphism
  `φ : P ⟶ K`, plus the termwise-freeness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`;
- derived API: the owner-level K-flatness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`,
  together with the comparison maps induced by `φ`.
- source/core/bridge triage:
  `source-facing`: `exists_filteredFreeResolution`;
  `core/canonical`: the Chapter `12` owner `FilteredComplex (ModuleCat R)`, together with
    `underlying`, `F^{p}(-)`, `gr^{p}(-)`, `underlyingMap`, `stageMap`, `gradedPieceMap`, and
    the Chapter `15` owner `CochainComplex.IsKFlat`;
  `bridge/view`: the induced comparison morphisms `underlyingMap`, `stageMap`, and
    `gradedPieceMap` attached to `φ`.

This file therefore keeps the source-facing filtered-resolution statement on
`FilteredCochainComplex (ModuleCat R)` and reuses the Chapter `12` and Chapter `15` owners
directly for the induced filtered-complex maps and the K-flatness content, without introducing a
parallel local wrapper for filtered K-flat data.
-/

section

variable {R : Type u} [CommRing R]

-- Proof sketch: construct `P^•` by the stepwise free filtered resolution described in the text,
-- starting from a basic filtered complex surjective on the cohomology of `K^•` and all
-- `F^p K^•`, then iteratively kill the remaining cohomology kernels. The resulting filtered
-- complex is termwise free on the underlying complex, on every stage, and on every graded piece;
-- these source-level freeness
-- properties supply the K-flatness content of the underlying complex, every stage, and every
-- graded piece, and the construction makes the underlying, stagewise, and graded-piece
-- comparison maps quasi-isomorphisms.
/-- Lemma `15.64.2` / Stacks `15.64.2`: every filtered complex of `R`-modules admits a morphism
from a filtered complex whose underlying complex, every filtration stage, and every graded piece
are K-flat, which is termwise free on the underlying complex, every filtration stage, and every
graded piece `gr^p(P^•)`,
and which is a quasi-isomorphism on the underlying complex as well as on every filtration stage
and graded piece. -/
lemma exists_filteredFreeResolution
    (K : FilteredCochainComplex (ModuleCat R)) :
    ∃ (P : FilteredCochainComplex (ModuleCat R)) (φ : P ⟶ K),
      P.underlying.IsKFlat ∧
      (∀ p, (F^{p} P).IsKFlat) ∧
      (∀ p, (gr^{p} P).IsKFlat) ∧
      P.underlying.IsTermwiseFree ∧
      (∀ p, (F^{p} P).IsTermwiseFree) ∧
      (∀ p, (gr^{p} P).IsTermwiseFree) ∧
      QuasiIso (underlyingMap φ) ∧
      (∀ p, QuasiIso (stageMap φ p)) ∧
      (∀ p, QuasiIso (gradedPieceMap φ p)) := sorry

end

end FilteredCochainComplex
end CategoryTheory
