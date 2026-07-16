import Mathlib.Algebra.MvPolynomial.Basic
import StacksProject_2024.stacks_project.Chap10.Definition_10_68_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial RingTheory.Sequence

section

variable (k : Type u) [CommRing k] [Nontrivial k]

/-
Domain triage:
* primary domain: regular sequences in commutative polynomial rings;
* sampled owner API: `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `RingTheory.Sequence.isRegular_in_ideal_iff`,
  `IsLocalRing.isRegular_of_perm`;
* core/canonical owner: `RingTheory.Sequence.IsRegular A rs`;
* primitive vs derived split: the primitive data are the ring `k[x, y, z]` and the two explicit
  lists `[x, y * (1 - x), z * (1 - x)]` and `[y * (1 - x), z * (1 - x), x]`; the example theorem
  is the derived source-facing comparison of their regularity behavior;
* layer classification for this file: `source-facing`.
-/

local notation "A" => MvPolynomial (Fin 3) k
local notation "x" => (X (0 : Fin 3) : A)
local notation "y" => (X (1 : Fin 3) : A)
local notation "z" => (X (2 : Fin 3) : A)

-- Proof sketch: use the inductive characterization of regular sequences in
-- `isRegular_cons_iff`. First `x` is a non-zero-divisor in the polynomial ring
-- over a nontrivial commutative ring, and then the images of `y * (1 - x)` and
-- `z * (1 - x)` remain non-zero-divisors after quotienting successively by the
-- preceding elements.
private theorem example10682_isRegular :
    IsRegular A [x, y * (1 - x), z * (1 - x)] := by
  sorry

-- Proof sketch: after quotienting by `y * (1 - x)`, the class of `z * (1 - x)`
-- becomes a zero-divisor, so the reordered list fails the inductive criterion
-- for regularity.
private theorem example10682_reordered_not_regular :
    ¬ IsRegular A [y * (1 - x), z * (1 - x), x] := by
  sorry

/-- Example 10.68.2 (Stacks, Tag `00LG`): in the polynomial ring `k[x, y, z]`,
the sequence `x, y(1 - x), z(1 - x)` is regular, but the reordered sequence
`y(1 - x), z(1 - x), x` is not. -/
theorem example10682_regularSequence_and_reordered_not_regular :
    IsRegular A [x, y * (1 - x), z * (1 - x)] ∧
      ¬ IsRegular A [y * (1 - x), z * (1 - x), x] :=
  ⟨example10682_isRegular k, example10682_reordered_not_regular k⟩

end
