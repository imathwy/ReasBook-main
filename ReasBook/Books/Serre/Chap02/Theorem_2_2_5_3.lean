import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.Character
import Serre.Chap02.Theorem_2_2_5_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

noncomputable section

section

open CategoryTheory

variable {G : Type} [Group G] [Finite G]

variable {ι : Type v}
variable (π : ι → FDRep ℂ G)

-- Proof sketch: Theorem
-- `irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family` supplies a basis of
-- `classFunctionSubspace G` indexed by `ι`. Evaluating a class function on conjugacy classes
-- identifies that space with the full function space on `ConjClasses G`, whose dimension is the
-- number of conjugacy classes. Comparing the cardinalities of these bases yields the equality.
/-- Theorem 2-2.5-3: for a complete set of pairwise nonisomorphic irreducible complex
representations of a finite group, the number of indices is the number of conjugacy classes of
`G`. -/
theorem card_eq_card_conjClasses_of_complete_irreducible_family
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : ∀ ⦃i j⦄, i ≠ j → ¬ Nonempty (π i ≅ π j))
    (hπ_complete : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ π i)) :
    Nat.card ι = Nat.card (ConjClasses G) := by
  classical
  -- Package the hypotheses into the canonical pairwise/completeness data used by Theorem `2-2.5-2`.
  have hπ_pairwise_cat : PairwiseNonisomorphic π := hπ_pairwise
  let hπ_family : IsCompleteIrreducibleFamily π := {
    isSimple := hπ_simple
    exists_iso := hπ_complete
  }
  -- The dependency theorem gives a basis of class functions indexed by the irreducible family.
  let bπ : Module.Basis ι ℂ (classFunctionSubmodule ℂ G) :=
    irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
      π hπ_pairwise_cat hπ_family
  -- Evaluating a class function on conjugacy classes gives the canonical conjugacy-class basis.
  let bConj : Module.Basis (ConjClasses G) ℂ (classFunctionSubmodule ℂ G) :=
    Module.Basis.ofEquivFun (classFunctionSubmodule.equivFun ℂ G)
  -- Comparing the two bases identifies the irreducible indices with the conjugacy classes.
  exact Nat.card_congr (bπ.indexEquiv bConj)

end

end

end Representation
