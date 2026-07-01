import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Submodule

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: prime-quotient filtrations of finite modules over a Noetherian ring;
- `core/canonical`: `RelSeries` over the relation `Submodule.IsQuotientEquivQuotientPrime`;
- `bridge/view`: the chapter shorthand `PrimeCyclicFiltration R M`, retained because it is the
  stable vocabulary used by the immediate Chapter 10 downstream API;
- primitive data: only the relation series itself, with prime factors and successive quotients as
  derived API in later files.
-/

/-- Chapter-shared shorthand for the canonical `RelSeries` owner whose successive quotients are
prime quotients `R ⧸ p`. -/
abbrev PrimeCyclicFiltration :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
    IsQuotientEquivQuotientPrime N₁ N₂}

end

/- Lemma 10.62.1: if `R` is Noetherian and `M` is a finite `R`-module, then there exists a finite
filtration `0 = M₀ ≤ M₁ ≤ ... ≤ Mₙ = M` such that each successive quotient `Mᵢ₊₁ / Mᵢ` is
linearly isomorphic to `R ⧸ pᵢ` for some prime ideal `pᵢ` of `R`. This is exactly the canonical
mathlib theorem `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`. -/
recall IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime
