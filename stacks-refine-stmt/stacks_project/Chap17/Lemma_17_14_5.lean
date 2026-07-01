import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_14_1

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.14.5:
- primary domain: finite locally free sheaves of modules of constant rank on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank`;
- best owner abstraction:
  the ambient owner category `RingedSpace.Modules X` together with the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ`;
- primitive data:
  only the module sheaves `ℱ`, `𝒢`, the common rank `r`, and the owner instances asserting their
  local rank-`r` trivializations;
- derived API:
  the source-facing comparison `IsIso φ ↔ Epi φ` for a morphism between such sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks Project criterion that a morphism between finite locally free sheaves
  of the same rank is an isomorphism exactly when it is surjective;
- `core/canonical`: the ambient owner `RingedSpace.Modules X` and the owner predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank`;
- `bridge/view`: this file should use those owners directly rather than restating the ambient
  module category by its raw `SheafOfModules (RingedSpace.ringCatSheaf X)` presentation. -/

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}

-- Proof sketch: the forward implication is categorical. For the converse, surjectivity may be
-- checked on stalks, where both source and target become free modules of rank `r` over the local
-- ring `𝒪_{X,x}`; then Algebra, Lemma `10.16.4` upgrades surjectivity to bijectivity, and stalkwise
-- bijectivity implies that `φ` is an isomorphism.
/-- Lemma 17.14.5: for a morphism `φ : \mathcal F \to \mathcal G` of finite locally free
`\mathcal O_X`-modules of the same rank `r` on a ringed space `(X,\mathcal O_X)`, `φ` is an
isomorphism if and only if it is surjective, i.e. an epimorphism. -/
theorem moduleHom_isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r 𝒢]
    (φ : ℱ ⟶ 𝒢) :
    IsIso φ ↔ Epi φ := sorry

end AlgebraicGeometry.RingedSpace
