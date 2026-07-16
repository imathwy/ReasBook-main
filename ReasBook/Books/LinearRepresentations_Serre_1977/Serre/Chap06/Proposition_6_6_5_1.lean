import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

section

open Module.End

variable {G : Type u} [Group G]
variable {k : Type w} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- Source/core/bridge triage:
-- * source-facing: `char_isIntegral`.
-- * core/canonical owner: `Representation.character`.
-- * bridge/generalization: `char_isIntegral_of_isOfFinOrder`.
--
-- Proof sketch: if `s` has finite order, then the linear automorphism `ρ s` does as well, so
-- every eigenvalue of `ρ s` is a root of unity and hence integral over `ℤ`. The character value
-- `ρ.character s`, being the trace of `ρ s`, is the sum of those eigenvalues, so it is integral
-- over `ℤ`.

/-- Helper for Proposition 6-6.5-1: every root of the characteristic polynomial of `ρ s` is an
algebraic integer when `s` has finite order. -/
lemma isIntegral_of_charpoly_root_of_isOfFinOrder
    (ρ : Representation k G V) {s : G} (hs : IsOfFinOrder s) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    IsIntegral ℤ μ := by
  -- The finite-order hypothesis forces each characteristic root to be a root of unity.
  have hpow : μ ^ orderOf s = 1 := ρ.charpoly_root_pow_orderOf_eq_one s hμ
  -- A root of unity is integral over `ℤ`.
  exact IsIntegral.of_pow hs.orderOf_pos <| hpow ▸ isIntegral_one

variable [IsAlgClosed k]

/-- If `s` has finite order, then the character value `ρ.character s` is an algebraic integer. -/
theorem char_isIntegral_of_isOfFinOrder
    (ρ : Representation k G V) {s : G} (hs : IsOfFinOrder s) :
    IsIntegral ℤ (ρ.character s) := by
  -- Rewrite the character as a trace, then as the sum of the characteristic roots.
  rw [Representation.character, trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Each root is integral, so their sum is integral as well.
  refine IsIntegral.multiset_sum fun μ hμ ↦ ?_
  exact isIntegral_of_charpoly_root_of_isOfFinOrder ρ hs hμ

end

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [Finite G]

/-- Proposition 6-6.5-1: for a finite group representation, the character value at any group
element is an algebraic integer. -/
theorem char_isIntegral (ρ : Representation ℂ G V) (s : G) :
    IsIntegral ℤ (ρ.character s) := by
  -- In a finite group every element has finite order, so the general lemma applies.
  simpa using char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s)

end

end Representation
