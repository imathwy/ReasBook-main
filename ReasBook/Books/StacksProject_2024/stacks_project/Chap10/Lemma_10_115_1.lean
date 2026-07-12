import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Finset

/- Domain-style sampling for Lemma 10.115.1:
- primary domain: finite ordered families of multi-indices and weighted sums.
- inspected owner declarations: `Finsupp.weight`, `Finsupp.weight_apply`,
  `Finsupp.equivFunOnFinite`, and `MonomialOrder.lex`.
- best owner abstraction: `Finsupp.weight` on `σ →₀ ℕ`; the tuple model `Fin n → ℕ` is only a
  concrete presentation of the same multi-index data.

Primitive-vs-derived split:
- primitive data: a finite ordered index type `σ`, a finite set `N : Finset (σ →₀ ℕ)` of
  multi-indices, and a weight system `e : σ → ℕ`;
- derived API: the coordinate spread `sup - inf'` and the resulting injectivity statement for the
  canonical weight map. -/

/- Source/core/bridge triage for Lemma 10.115.1:
- `source-facing`: the domination inequalities on coordinates and the conclusion that the weighted
  sums distinguish the multi-indices in `N`;
- `core/canonical`: `Finsupp.weight`;
- `bridge/view`: the finite tuple picture recovered from `Finsupp.equivFunOnFinite`. -/

section

variable {σ : Type*}

/-- The spread of the `i`-th coordinate among the multi-indices in a finite set. It is `0` when
the set is empty. -/
def coordinateSpread (N : Finset (σ →₀ ℕ)) (i : σ) : ℕ :=
  if hN : N.Nonempty then N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) else 0

lemma coordinateSpread_eq (N : Finset (σ →₀ ℕ)) (hN : N.Nonempty) (i : σ) :
    coordinateSpread N i = N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) := by
  simp [coordinateSpread, hN]

variable [LinearOrder σ] [Fintype σ]

/-- Lemma 10.115.1: if each weight `e i` dominates the tail weighted by the coordinate spreads of
`N`, then the canonical weighted sums `ν.weight e` distinguish the multi-indices in `N`. -/
-- Proof sketch: let `i` be the first coordinate where `ν` and `ν'` differ. The domination
-- hypothesis makes the contribution of coordinate `i` larger than the total possible contribution
-- of all later coordinates, so equality of weighted sums forces agreement in coordinate `i`;
-- iterate on the tail.
lemma weighted_sum_eq_iff_eq_of_dominating_weights
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (he : ∀ i : σ,
      e i >
        Finset.sum (univ.filter fun j : σ ↦ i < j)
          (fun j ↦ coordinateSpread N j * e j)) :
    ν.weight e = ν'.weight e ↔ ν = ν' := sorry

end
