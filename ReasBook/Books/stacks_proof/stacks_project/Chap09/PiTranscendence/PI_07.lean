import Mathlib
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_01

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

/- Domain-style sampling for PI-07:
- primary domain: finite subset sums of a chosen enumeration of the canonical root multiset
  `P.aroots ℂ`;
- sampled owner declarations:
  `Polynomial.aroots`,
  `IsIntegral.add`,
  `isAlgebraic_iff_isIntegral`,
  `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero`;
- best owner abstraction: the canonical root multiset `P.aroots ℂ`, with algebraicity/integrality
  of subset sums as the core/canonical bridge and the common annihilating integer polynomial as the
  source-facing derived API required here;
- primitive data: the root enumeration witness
  `ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ`;
- derived API: a common nonzero `F : ℤ[X]` annihilating all subset sums, and transport of that
  witness to any finite family whose values are such subset sums.

Source/core/bridge triage:
- `source-facing`: the main existence theorem for a common polynomial vanishing on all subset sums
  of the chosen root enumeration;
- `core/canonical`: `P.aroots ℂ` together with the standard algebraicity/integrality API for sums
  of algebraic numbers;
- `bridge/view`: transport of the common annihilating polynomial from the canonical subset-sum
  family to an arbitrary finite family `β` landing in that subset-sum family;
- `layer`: the first theorem remains `source-facing`, while the second theorem is a
  `bridge/view` corollary derived from the first rather than a parallel owner declaration.
-/

section

variable {P : ℤ[X]} {n : ℕ} {a : Fin n → ℂ}

/-- Helper for Theorem PI-07: each entry of a `Fin n`-indexed enumeration of `P.aroots ℂ` is
algebraic over `ℚ`. -/
lemma root_entry_isAlgebraic_rat_of_complex_root_fin_enumeration
    (hP : P ≠ 0) (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (i : Fin n) :
    IsAlgebraic ℚ (a i) := by
  -- Proof comment: convert the chosen entry into a member of the canonical root multiset.
  have hi_mem : a i ∈ P.aroots ℂ := by
    rw [← ha, Multiset.mem_coe]
    simpa [List.mem_ofFn']
  -- Proof comment: membership in `P.aroots ℂ` gives a polynomial equation for `a i`.
  have hi_root : aeval (a i) P = 0 :=
    (Polynomial.mem_aroots.mp hi_mem).2
  -- Proof comment: the same nonzero integer polynomial witnesses algebraicity over `ℤ`,
  -- and the fraction-field bridge moves this to algebraicity over `ℚ`.
  have hi_alg_int : IsAlgebraic ℤ (a i) := ⟨P, hP, hi_root⟩
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hi_alg_int

/-- Helper for Theorem PI-07: every finite subset sum of the enumerated roots is algebraic over
`ℚ`. -/
lemma subset_sum_isAlgebraic_rat_of_complex_root_fin_enumeration
    (hP : P ≠ 0) (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (S : Finset (Fin n)) :
    IsAlgebraic ℚ (S.sum a) := by
  -- Proof comment: first upgrade each summand to an integral element over `ℚ`.
  have h_integral : ∀ i ∈ S, IsIntegral ℚ (a i) := by
    intro i hi
    exact
      (root_entry_isAlgebraic_rat_of_complex_root_fin_enumeration hP ha i).isIntegral
  -- Proof comment: integrality is closed under finite sums, and over a field this is the same as
  -- algebraicity.
  exact (isAlgebraic_iff_isIntegral).2 (IsIntegral.sum a h_integral)

/-- Helper for Theorem PI-07: every finite subset sum of the enumerated roots satisfies a nonzero
integer polynomial. -/
lemma exists_nonzero_int_polynomial_aeval_eq_zero_of_subset_sum_of_complex_root_fin_enumeration
    (hP : P ≠ 0) (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (S : Finset (Fin n)) :
    ∃ f : ℤ[X], f ≠ 0 ∧ aeval (S.sum a) f = 0 := by
  -- Proof comment: apply the integer-annihilator bridge from PI-01 to the algebraic subset sum.
  exact
    exists_nonzero_int_polynomial_aeval_eq_zero_of_isAlgebraic_rat
      (subset_sum_isAlgebraic_rat_of_complex_root_fin_enumeration hP ha S)

/-- Theorem PI-07: let `P ∈ ℤ[X]` be nonzero, and let `a : Fin n → ℂ` enumerate the complex roots
of `P` counted with multiplicity. Then there exists a nonzero polynomial `F ∈ ℤ[X]` such that
every subset sum `∑ i∈S, a i` is a complex root of `F`. -/
theorem exists_nonzero_int_polynomial_aeval_eq_zero_on_subset_sums_of_complex_root_fin_enumeration
    (hP : P ≠ 0) (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ)
    : ∃ F : ℤ[X], F ≠ 0 ∧ ∀ S : Finset (Fin n), aeval (S.sum a) F = 0 := by
  -- Proof comment: choose one nonzero integer annihilator polynomial for each subset sum.
  have hsubset_poly :
      ∀ S : Finset (Fin n), ∃ f : ℤ[X], f ≠ 0 ∧ aeval (S.sum a) f = 0 := by
    intro S
    exact
      exists_nonzero_int_polynomial_aeval_eq_zero_of_subset_sum_of_complex_root_fin_enumeration
        hP ha S
  classical
  choose f hf_nonzero hf_aeval using hsubset_poly
  let subsetFamily : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  let F : ℤ[X] := Finset.prod subsetFamily f
  have hF_nonzero : F ≠ 0 := by
    -- Proof comment: the common witness is a finite product of nonzero factors.
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro S hS
    exact hf_nonzero S
  have hF_annihilates : ∀ S : Finset (Fin n), aeval (S.sum a) F = 0 := by
    intro S
    -- Proof comment: the factor indexed by `S` divides the global product because every subset of
    -- `Fin n` lies in the powerset of `univ`.
    have hS_mem : S ∈ subsetFamily := by
      simpa [subsetFamily] using (Finset.mem_powerset.mpr (Finset.subset_univ S))
    have hdiv : f S ∣ F := by
      simpa [F] using (Finset.dvd_prod_of_mem f hS_mem)
    -- Proof comment: a divisor with zero `aeval` forces the full product to vanish under `aeval`.
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv (hf_aeval S)
  refine ⟨F, hF_nonzero, hF_annihilates⟩

/-- Auxiliary corollary: any finite family whose values are subset sums of the root enumeration in
Theorem PI-07 is annihilated by the same nonzero integer polynomial. This applies in particular to
the nonzero subset-sum family `β` produced by Lemma PI-05. -/
theorem exists_nonzero_int_polynomial_aeval_eq_zero_on_subset_sum_family_of_complex_root_fin_enumeration
    (hP : P ≠ 0) (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ)
    {m : ℕ} (β : Fin m → ℂ)
    (hβ : ∀ j, ∃ S : Finset (Fin n), β j = S.sum a) :
    ∃ F : ℤ[X], F ≠ 0 ∧ ∀ j, aeval (β j) F = 0 := by
  obtain ⟨F, hF, hsubset⟩ :=
    exists_nonzero_int_polynomial_aeval_eq_zero_on_subset_sums_of_complex_root_fin_enumeration
      hP ha
  refine ⟨F, hF, fun j ↦ ?_⟩
  rcases hβ j with ⟨S, hS⟩
  rw [hS]
  exact hsubset S

end
