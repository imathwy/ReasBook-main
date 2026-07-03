import Mathlib
import StacksProject_2024.Chap15.Definition_15_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open KaehlerDifferential

universe u v w

section PBasis

variable (p : ℕ) (k : Type u) (K : Type v)
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/- Domain triage:
- primary domain: `p`-bases of characteristic-`p` field extensions and their characterization via
  the universal derivation `D k K`;
- sampled owner declarations:
  `PIndependent`,
  `IsPBasis`,
  `Module.Basis.mk`,
  `Module.Basis.span_eq`,
  `D k K`;
- best owner abstraction: the source-facing owners are the chapter declarations `PIndependent` and
  `IsPBasis`, while any actual `Module.Basis` witness is derived data supplied canonically by
  `Module.Basis.mk`;
- primitive data: `p`-independence and generation over `pPowerCompositum p k K`;
- derived API: the differential criteria and existence statements below.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma `15.46.2`;
- `core/canonical`: `PIndependent`, `IsPBasis`, `Module.Basis.mk`, and `D k K`;
- `bridge/view`: the textbook basis wording is expressed directly through the owner `IsPBasis`,
  rather than through any parallel local restatement or existential `Module.Basis` wrapper.
-/

-- Proof sketch: identify `k`-derivations of `K` with `K`-linear maps out of `Ω[K⁄k]`, then use
-- the standard characteristic-`p` argument that `p`-restricted monomial relations are detected by
-- derivations.
/-- Lemma 15.46.2 (1): a family in a characteristic-`p` field extension is `p`-independent over
`k` if and only if its differentials are `K`-linearly independent in `Ω[K⁄k]`. -/
theorem pIndependent_iff_linearIndependent_differentials (x : ι → K) :
    PIndependent p k K x ↔
      LinearIndependent K (D k K ∘ x) := sorry

-- Proof sketch: apply Zorn's lemma to enlarge a `p`-independent family to a maximal one, then
-- show that maximal `p`-independent families generate `K` over `k(K^p)`.
/-- Lemma 15.46.2 (2): every `p`-independent family in `K` extends to a `p`-basis of `K` over
`k`. -/
theorem exists_isPBasis_extension (x : ι → K) (hx : PIndependent p k K x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧ IsPBasis p k K y := sorry

-- Proof sketch: start from the empty `p`-independent family and apply the extension statement.
/-- Lemma 15.46.2 (3): the field `K` admits a `p`-basis over `k`. -/
theorem exists_isPBasis :
    ∃ (ι : Type v) (x : ι → K), IsPBasis p k K x := sorry

-- Proof sketch: combine the first equivalence with the spanning criterion for `Ω[K⁄k]`; a
-- `p`-basis gives a linearly independent spanning family of differentials, and conversely such a
-- family is a maximal `p`-independent family.
/-- Lemma 15.46.2 (4): a family is a `p`-basis of `K` over `k` if and only if its differentials
are `K`-linearly independent and span `Ω[K⁄k]`. -/
theorem isPBasis_iff_differentials_formBasis (x : ι → K) :
    IsPBasis p k K x ↔
      LinearIndependent K (D k K ∘ x) ∧
        Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := sorry

end PBasis
