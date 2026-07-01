import Mathlib
import stacks_project.Chap15.Lemma_15_105_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {J : Type u}

/-
Domain-style sampling:
- primary domain: commutative algebra of weak dimension, valuation rings, and localization of
  product rings;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ValuationRing`,
  `IsFractionRing`,
  `IsLocalization`;
- best owner abstraction:
  part `(1)` is genuinely source-facing, but its public owner is still the chapter class
  `HasWeakDimensionLE`, so the target surface should provide that owner directly for the product
  ring;
  part `(2)` is exact-interface reuse of the canonical product-localization `IsLocalization`
  instance, so it should be exposed by direct instance synthesis rather than restated behind a
  duplicate local theorem name.

Primitive-vs-derived split:
- primitive data: the family of valuation rings `A j`, and for part `(2)` the family of fraction
  rings `K j` together with the canonical `CommRing`, `Algebra`, and `IsFractionRing` instances;
- derived API: the product weak-dimension statement in part `(1)`, and the product localization
  statement in part `(2)`, which is already owned canonically by `IsLocalization`.

Source/core/bridge triage:
- `source-facing`: part `(1)`, the Stacks weak-dimension statement for products of valuation
  rings;
- `core/canonical`: `HasWeakDimensionLE`, `ValuationRing`, `IsFractionRing`, and
  `IsLocalization`;
- `bridge/view`: part `(2)` is only a direct specialization of the canonical localization owner,
  so it should stay as direct instance synthesis rather than a parallel wrapper theorem.
-/

variable {A : J → Type v}
variable [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)]

-- Proof sketch: apply Lemma `15.105.18` to the product ring `∏ j, A j`. A finitely generated ideal
-- in a product ring is the product of its component ideals by Proposition `10.89.2`, each component
-- ideal in a valuation ring is principal by Lemma `10.50.15`, and principal idempotent ideals are
-- direct summands, hence flat. This gives weak dimension at most `1`.
/-- Lemma 15.105.19 (1): the product of a family of valuation rings has weak dimension at most
`1`. -/
instance : HasWeakDimensionLE ((j : J) → A j) 1 := by
  sorry

variable {K : J → Type w}
variable [∀ j, CommRing (K j)] [∀ j, Algebra (A j) (K j)] [∀ j, IsFractionRing (A j) (K j)]

-- Proof sketch: for each factor `j`, `K j` is the localization of `A j` at the nonzerodivisors of
-- `A j`. The canonical product-localization `IsLocalization` instance then identifies the product
-- `∀ j, K j` as the localization of `∀ j, A j` at the product submonoid of componentwise
-- nonzerodivisors. The field structure on each fraction ring is derived from `IsFractionRing`, so
-- it does not belong in the public hypotheses for this direct localization recall.
/- Lemma 15.105.19 (2): if each `K j` is a fraction ring of `A j`, then the canonical map
`((j : J) → A j) → ((j : J) → K j)` is the localization at the product submonoid of componentwise
nonzerodivisors. This is direct instance inference from the canonical product-localization owner
in mathlib. -/
#synth IsLocalization (Submonoid.pi Set.univ fun j ↦ nonZeroDivisors (A j)) ((j : J) → K j)

end
