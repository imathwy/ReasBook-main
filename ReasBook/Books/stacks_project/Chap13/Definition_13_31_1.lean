import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomotopyCategory

/- Definition 13.31.1: in an abelian category, the textbook notion of a K-injective complex is the
canonical mathlib class `CochainComplex.IsKInjective`. It encodes that every morphism from an
acyclic cochain complex to the given complex is null-homotopic, equivalently zero in the homotopy
category `K(\mathcal A)`. -/
recall CochainComplex.IsKInjective

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "Q" => quotient 𝒜 (up ℤ)

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes in the homotopy category `K(𝒜)`;
-- * sampled owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic`;
-- * best owner abstraction: the canonical owner is the complex `I` with property `I.IsKInjective`;
-- * source/core/bridge triage:
--   `core/canonical`: `I.IsKInjective`;
--   `bridge/view`: the vanishing criterion in `K(𝒜)` for morphisms from acyclic complexes;
-- * primitive data: only the complex `I`;
-- * derived API: the source-facing vanishing characterization below.

-- Proof sketch: combine `isKInjective_iff_rightOrthogonal` with
-- `HomotopyCategory.subcategoryAcyclic C` and rewrite acyclicity using
-- `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic`.
/-- A cochain complex is K-injective exactly when every morphism to it from an acyclic complex
vanishes in the homotopy category. -/
theorem isKInjective_iff_homotopyCategory_from_acyclic_eq_zero
    (I : CochainComplex 𝒜 ℤ) :
    I.IsKInjective ↔
      ∀ (M : CochainComplex 𝒜 ℤ) (_ : M.Acyclic)
        (f : (Q).obj M ⟶ (Q).obj I), f = 0 := by
  rw [isKInjective_iff_rightOrthogonal]
  constructor
  · intro h M hM f
    exact h f ((quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).2 hM)
  · intro h X f hX
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact h M ((quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).1 hX) f

end CochainComplex
