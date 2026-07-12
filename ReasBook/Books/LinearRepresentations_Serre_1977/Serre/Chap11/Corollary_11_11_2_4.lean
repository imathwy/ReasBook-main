import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

section FrobeniusTheorem

variable {G : Type} [Group G] [Finite G]

local instance instFintypeG_c1124 : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the divisibility of the cardinality of the `n`th-power fiber over `c`.
-- * core/canonical owner: `ConjClasses.pow`, the project owner for passing to `n`th powers on
--   conjugacy classes.
-- * bridge/view: evaluate `normalizedConjugacyClassNthRootCharacterSum_isIntegral` on the trivial
--   representation, whose character identifies the source sum with that cardinality.

-- Proof sketch: apply
-- `normalizedConjugacyClassNthRootCharacterSum_isIntegral` to the trivial complex
-- representation of `G`. The resulting algebraic integer is the rational number obtained by
-- dividing the cardinality of `{x : G | x ^ n ∈ c}` by `Nat.gcd (orderOf g) n`, so it must in
-- fact be an integer; equivalently, that cardinality is divisible by `Nat.gcd (orderOf g) n`.
omit [Finite G] in
/-- Helper for Corollary 11-11.2-4: an element lands in the carrier of `c` after taking an
`n`th power exactly when its conjugacy class maps to `c` under `ConjClasses.pow`. -/
lemma pow_mem_carrier_iff_pow_mk_eq
    (n : ℕ+) (c : ConjClasses G) (x : G) :
    x ^ (n : ℕ) ∈ c.carrier ↔ ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c := by
  -- This is the direct interface translation between the source statement and the core owner.
  simp [ConjClasses.pow_mk, ConjClasses.mem_carrier_iff_mk_eq]

/-- Helper for Corollary 11-11.2-4: the `n`th-root character sum for the trivial representation
counts the elements whose `n`th-power conjugacy class is `c`. -/
lemma conjugacyClassNthRootCharacterSum_trivial_eq_card_roots
    (n : ℕ+) (c : ConjClasses G) :
    conjugacyClassNthRootCharacterSum n c (trivial ℂ G ℂ) =
      Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} := by
  classical
  -- Rewrite the filtered character sum as a filtered cardinality.
  rw [conjugacyClassNthRootCharacterSum, Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype
    (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier)]
  · -- The trivial character contributes `1`, so only the root condition remains.
    simp [Representation.character, Representation.trivial, pow_mem_carrier_iff_pow_mk_eq]
  · intro x
    simp [pow_mem_carrier_iff_pow_mk_eq]

/-- Corollary 11-11.2-4: for a conjugacy class `c` and a representative `g ∈ c`, the number of
elements `x ∈ G` whose `n`th-power conjugacy class is `c` is a multiple of
`Nat.gcd (orderOf g) n`; equivalently, the number of `x` such that `x ^ n ∈ c` is such a
multiple. -/
theorem gcd_orderOf_dvd_card_nth_pow_mem_conj_class
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    Nat.gcd (orderOf (g : G)) (n : ℕ) ∣
      Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} := by
  classical
  have hgcd_ne_zero : Nat.gcd (orderOf (g : G)) (n : ℕ) ≠ 0 := by
    exact Nat.gcd_ne_zero_right n.ne_zero
  have h_integral :
      IsIntegral ℤ
        ((Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} : ℂ) /
          Nat.gcd (orderOf (g : G)) (n : ℕ)) := by
    -- Evaluate the source theorem on the trivial representation, so the normalized sum becomes
    -- the normalized cardinality of the `n`th-power fiber.
    have h := normalizedConjugacyClassNthRootCharacterSum_isIntegral n c g (trivial ℂ G ℂ)
    rw [conjugacyClassNthRootCharacterSum_trivial_eq_card_roots] at h
    rw [div_eq_mul_inv, mul_comm]
    exact h
  -- Clear the denominator using the standard rational-integrality criterion.
  exact nat_dvd_of_isIntegral_natCast_div_local
    (m := Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c})
    (d := Nat.gcd (orderOf (g : G)) (n : ℕ))
    hgcd_ne_zero h_integral

end FrobeniusTheorem

end Representation
