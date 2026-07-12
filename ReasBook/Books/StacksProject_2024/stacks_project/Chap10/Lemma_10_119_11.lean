import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Ring.KrullDimLE 1 R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

/-
Domain triage:
* primary domain: module length for principal quotients of `R`-submodules inside a finite-
  dimensional fraction-field vector space;
* sampled owner API: `QuotSMulTop`, `QuotSMulTop.congr`, `IsFiniteLength`,
  `Module.length_ne_top_iff`, and the finite-dimensional transport API
  `LinearEquiv.ofFinrankEq`;
* source/core/bridge split: Lemma `10.119.11` is `source-facing`, the quotient owner is
  `QuotSMulTop x M`, the finiteness owner is `IsFiniteLength R`, and the ambient owner abstraction
  is an `R`-submodule of a finite-dimensional `K`-vector space `V`;
* primitive data vs. derived API: the primitive inputs are the submodule `M`, the nonzero element
  `x`, and the ambient finite-dimensional `K`-space; any coordinate presentation
  `V ≃ₗ[K] Fin (finrank K V) → K` is derived from a basis and should not remain the public owner.
-/

-- Proof sketch: the support of `R / xR` is the finite set of maximal ideals containing `x`, since
-- a one-dimensional Noetherian domain has only maximal primes above a nonzero principal ideal.
-- Localize `M / xM` at those maximal ideals and, after choosing a `K`-basis of `V`, transport the
-- localized problem via `QuotSMulTop.congr` to the coordinate model `K^{\oplus r}` where the local
-- one-dimensional statement from Lemma `10.119.9` applies. Transporting back, the quotient has a
-- finite filtration with residue-field subquotients, so its `R`-length is finite.
/-- Lemma 10.119.11: if `R` is a Noetherian domain of Krull dimension at most `1`, `M` is an
`R`-submodule of a finite-dimensional `K`-vector space `V`, and `x ∈ R` is nonzero, then the
quotient `M / xM`, written canonically as `QuotSMulTop x M`, has finite length over `R`. -/
theorem isFiniteLength_quotSMulTop_submodule_of_nonzero
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := by
  sorry

/-- Source-facing numerical form of Lemma 10.119.11. -/
theorem length_submodule_quotient_by_nonzero_lt_top
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M) < ⊤ := by
  exact lt_top_iff_ne_top.mpr <|
    Module.length_ne_top_iff.mpr <|
      isFiniteLength_quotSMulTop_submodule_of_nonzero M hx

end
