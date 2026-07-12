import Mathlib
import StacksProject_2024.Chap31.Lemma_31_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` found the generic irreducible-component API, while local
-- Chapter 31 precedent represents codimension of components by `Order.coheight` on
-- `IrreducibleCloseds`.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- Lemma 31.29.4: with assumptions and notation as in Lemma 31.29.3, if the section
`s : \mathcal O_X \to \mathcal F` is nonzero, then every irreducible component of
`X \setminus U` has codimension `1` in `X`. Components are represented by maximal irreducible
closed subsets contained in the complement of `U`, and codimension is `Order.coheight`. -/
@[stacks 0EBP]
theorem coheight_eq_one_of_mem_irreducibleComponents_compl_rankOneReflexiveSectionIsoLocus
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (hs : s ≠ 0) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    ∀ Z : IrreducibleCloseds X,
      Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ ((U : Set X)ᶜ : Set X)) Z →
        Order.coheight Z = 1 := sorry

end AlgebraicGeometry.Scheme.Modules
