import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

/- Domain-style sampling for PI-02:
- primary domain: roots of a polynomial over `ℂ`, organized by the canonical multiset
  `Polynomial.aroots`;
- sampled owner declarations:
  `Polynomial.mem_aroots`,
  `Multiset.coe_toList`,
  `List.ofFn_get`,
  `List.mem_ofFn'`;
- best owner abstraction: `P.aroots ℂ` as the canonical multiset of complex roots with
  multiplicity;
- primitive data: the multiset `P.aroots ℂ`;
- derived API: a `Fin`-indexed enumeration of that multiset and recovery of an index for a chosen
  root.

Source/core/bridge triage:
- `source-facing`: existence of a finite enumeration of the complex roots of `P`, and recovery of
  an index for a chosen root in such an enumeration;
- `core/canonical`: `P.aroots ℂ` and membership `α ∈ P.aroots ℂ`;
- `bridge/view`: `Polynomial.mem_aroots` together with the generic tuple/list API
  `List.ofFn_get` and `List.mem_ofFn'`;
- `layer`: theorem (1) remains source-facing derived API from `P.aroots ℂ`, while theorem (2)
  is factored through the canonical membership statement.
-/

/-- Lemma PI-02 (1): an integer polynomial admits a `Fin n`-indexed enumeration of its complex
roots counted with multiplicity. -/
theorem exists_complex_root_fin_enumeration (P : ℤ[X]) :
    ∃ n : ℕ, ∃ a : Fin n → ℂ, (List.ofFn a : Multiset ℂ) = P.aroots ℂ := by
  refine ⟨(P.aroots ℂ).toList.length, (P.aroots ℂ).toList.get, ?_⟩
  change (((List.ofFn (P.aroots ℂ).toList.get : List ℂ) : Multiset ℂ) = P.aroots ℂ)
  rw [List.ofFn_get, Multiset.coe_toList]

/-- If `a : Fin n → ℂ` enumerates `P.aroots ℂ`, then every root recorded by the canonical multiset
of roots appears in that enumeration. -/
theorem exists_index_of_mem_aroots_of_complex_root_fin_enumeration
    {P : ℤ[X]} {n : ℕ} {a : Fin n → ℂ}
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) {α : ℂ} (hα : α ∈ P.aroots ℂ) :
    ∃ i : Fin n, a i = α := by
  rw [← ha, Multiset.mem_coe] at hα
  simpa [List.mem_ofFn'] using hα

/-- Lemma PI-02 (2): if `a : Fin n → ℂ` enumerates the complex roots of a nonzero integer
polynomial `P` with multiplicity, then every complex root of `P` appears in that enumeration. -/
theorem exists_index_of_aeval_eq_zero_of_complex_root_fin_enumeration
    {P : ℤ[X]} (hP : P ≠ 0) {n : ℕ} {a : Fin n → ℂ}
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) {α : ℂ} (hα : Polynomial.aeval α P = 0) :
    ∃ i : Fin n, a i = α :=
  exists_index_of_mem_aroots_of_complex_root_fin_enumeration ha
    ((Polynomial.mem_aroots).2 ⟨hP, hα⟩)
