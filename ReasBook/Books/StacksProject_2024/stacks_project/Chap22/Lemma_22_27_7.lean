import Mathlib.CategoryTheory.ComposableArrows.Basic
import StacksProject_2024.Chap22.Lemma_22_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasAdmissibleCones R A]

-- Semantic recall hits: the Chapter 13 canonical owner
-- `CategoryTheory.ComposableArrows.exists_splitMono_homotopyReplacement` fixes the replacement data
-- as a morphism of composable-arrow chains indexed by `Fin n`. The present Chapter 22 item keeps
-- the same chain owner and edge indexing, but its source-facing extra data is stronger: the
-- vertical comparison map is equipped with a chosen componentwise family of `HomotopyRetract`s,
-- not only the resulting homotopy equivalences.
--
-- Source/core/bridge triage:
-- - `source-facing`: `exists_admissibleMono_replacement_chain`, which keeps the chosen retract
--   witnesses from the Chapter 22 argument;
-- - `core/canonical`: the ladder owner `ι : y ⟶ x` in `ComposableArrows`;
-- - `bridge/view`: the companion theorem below, which forgets the retract data and recovers the
--   canonical componentwise `Comp.homotopyEquivalences` conclusion.

/-- Lemma 22.27.7: if `x : ComposableArrows (Comp(𝒜)) n` is a finite composable chain
`x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ` in `Comp(𝒜)`, then there is a replacement chain
`y₀ ⟶ y₁ ⟶ ⋯ ⟶ yₙ` together with a ladder morphism `ι : y ⟶ x` whose horizontal maps are
admissible monomorphisms and whose components are the projections of chosen homotopy retracts
`r i : HomotopyRetract (y.obj i) (x.obj i)`. In particular, each `ι.app i` is a homotopy
equivalence in `Comp(𝒜)`. -/
@[stacks 09QN]
theorem exists_admissibleMono_replacement_chain
    {n : ℕ}
    (x : ComposableArrows (Comp R A) n) :
    ∃ (y : ComposableArrows (Comp R A) n) (ι : y ⟶ x)
      (r : ∀ i : Fin (n + 1), HomotopyRetract (y.obj i) (x.obj i)),
      (∀ i : Fin n,
        IsAdmissibleMono compForgetToDegreeZero (y.map' i.1 (i.1 + 1))) ∧
      ∀ i : Fin (n + 1), (r i).projection = ι.app i := sorry

/-- Bridge/view form of Lemma `22.27.7`: forgetting the chosen retract witnesses recovers the
canonical componentwise homotopy-equivalence conclusion for the ladder morphism `ι : y ⟶ x`. -/
theorem exists_admissibleMono_replacement_chain_homotopyEquivalences
    {n : ℕ}
    (x : ComposableArrows (Comp R A) n) :
    ∃ (y : ComposableArrows (Comp R A) n) (ι : y ⟶ x),
      (∀ i : Fin n,
        IsAdmissibleMono compForgetToDegreeZero (y.map' i.1 (i.1 + 1))) ∧
      ∀ i : Fin (n + 1), Comp.homotopyEquivalences (ι.app i) := by
  obtain ⟨y, ι, r, hmono, hr⟩ := exists_admissibleMono_replacement_chain x
  refine ⟨y, ι, hmono, ?_⟩
  intro i
  simpa [hr i] using
    (HomotopyRetract.projection_homotopyEquivalences (r i))

end
