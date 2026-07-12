import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/- Domain-style sampling pass.

Primary domain: local commutative algebra of regular local rings and their basic derived
ring-theoretic consequences.

Sampled owner declarations:
* `IsRegularLocalRing` and `IsRegularLocalRing.iff_finrank_cotangentSpace` from mathlib's
  regular-local-ring owner API;
* `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` from the same owner namespace;
* the direct downstream owner use `regularLocalRing_uniqueFactorizationMonoid` in
  `Chap15/Lemma_15_122_2.lean`, which consumes the domain consequence through typeclass search.

Best owner abstraction: the ambient owner is `IsRegularLocalRing R`. The target declaration here is
derived API: the canonical ring-theoretic consequence that such an `R` is a domain.

Primitive vs. derived:
* primitive data: only the owner hypothesis `[IsRegularLocalRing R]`;
* derived API: the instance `IsDomain R`.

Source/core/bridge triage:
* source-facing: the Stacks lemma asserting that a regular local ring is a domain;
* core/canonical: the owner predicate `IsRegularLocalRing R`;
* bridge/view: this file's derived typeclass instance `IsDomain R`. -/

-- Proof sketch: use Krull's intersection theorem to get `⋂ n, (maximalIdeal R)^n = 0`. If
-- `f * g = 0` with both `f` and `g` nonzero, choose maximal integers `a` and `b` such that
-- `f ∈ (maximalIdeal R)^a` and `g ∈ (maximalIdeal R)^b`. Then
-- `f * g = 0 ∈ (maximalIdeal R)^(a + b + 1)`, and Lemma `10.106.1` forces either
-- `f ∈ (maximalIdeal R)^(a + 1)` or `g ∈ (maximalIdeal R)^(b + 1)`, contradicting maximality.
/-- Lemma 10.106.2: any regular local ring is a domain. -/
instance regularLocalRing_isDomain : IsDomain R := sorry

end
