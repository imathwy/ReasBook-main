import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap31.Lemma_31_29_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced affine scheme/global-section API; local Chapter 31
-- precedent fixes the relevant owners as `rankOneReflexiveSectionIsoLocusSet`,
-- `moduleSupport (cokernel s)`, and `rankOneReflexiveSectionPowerDiagram`.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- Remark 31.29.5 (1): for the affine normal-domain situation of the remark, transported to the
scheme-side owner used in Lemmas 31.29.3 and 31.29.4, if `p₁, ..., pᵣ` enumerate the
height-one irreducible closed subsets in the support of the cokernel of
`s : \mathcal O_X → \mathcal F`, then the open `U` where `s` trivializes the rank-one reflexive
module is the complement of their union. For `X = Spec A`, these closed subsets are the
`V(\mathfrak p_i)`. -/
@[stacks 0EBQ]
theorem rankOneReflexiveSectionIsoLocus_eq_compl_iUnion_heightOne_support
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (hs : s ≠ 0) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s)
    {r : ℕ} (p : Fin r → IrreducibleCloseds X)
    (hp_height : ∀ i, Order.coheight (p i) = 1)
    (hp_support : ∀ i, (p i : Set X) ⊆ moduleSupport (cokernel s))
    (hp_complete : ∀ Z : IrreducibleCloseds X,
      Order.coheight Z = 1 → (Z : Set X) ⊆ moduleSupport (cokernel s) →
        ∃ i : Fin r, Z = p i) :
    (U : Set X) = (⋃ i : Fin r, (p i : Set X))ᶜ := sorry

/-- Remark 31.29.5 (2): with the same setup, the structure sheaf on the open where
`s : \mathcal O_X → \mathcal F` trivializes `\mathcal F` is identified with the colimit of the
sequence of reflexive tensor powers
`\mathcal O_X → \mathcal F → \mathcal F^{[2]} → ...`. Taking global sections on `X = Spec A`
gives the displayed formula `Γ(U, \mathcal O_U) = colim M^{[n]}` from the remark. -/
@[stacks 0EBQ]
theorem pushforward_tensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram_of_nonzeroSection
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (hs : s ≠ 0) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    Nonempty
      (((Scheme.Modules.pushforward U.ι).obj
          (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules)) ≅
        colimit (rankOneReflexiveSectionPowerDiagram s)) := sorry

end AlgebraicGeometry.Scheme.Modules
