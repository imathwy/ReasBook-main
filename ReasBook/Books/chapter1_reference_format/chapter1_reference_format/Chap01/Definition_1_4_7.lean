import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v w

/- Definition 1.4.7: a family `x : ι → V` of vectors in a `K`-vector space is linearly
independent when the canonical predicate `LinearIndependent K x` holds; linearly dependent means
that this predicate fails. -/
recall LinearIndependent {ι : Type u} (K : Type v) {V : Type w} (x : ι → V) [Semiring K]
  [AddCommMonoid V] [Module K V] : Prop

/- For a finite index type, linear independence is equivalent to the textbook condition that every
linear relation `∑ i, λ i • x i = 0` has all coefficients equal to `0`. -/
recall Fintype.linearIndependent_iff {ι : Type u} {K : Type v} {V : Type w} [Ring K]
  [AddCommGroup V] [Module K V] {x : ι → V} [Fintype ι] :
  LinearIndependent K x ↔ ∀ g : ι → K, ∑ i, g i • x i = 0 → ∀ i : ι, g i = 0
