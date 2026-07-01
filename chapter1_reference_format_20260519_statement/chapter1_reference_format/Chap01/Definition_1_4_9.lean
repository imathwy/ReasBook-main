import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Definition 1.4.9: a basis of a vector space is the canonical mathlib notion
`Module.Basis I K V`, namely an indexed family of vectors giving unique finitely supported
coordinates for every vector. -/
recall Module.Basis (I : Type v) (K : Type u) (V : Type w) [Semiring K] [AddCommMonoid V]
  [Module K V] : Type (max (max u v) w)

/- The vectors in a basis are linearly independent. -/
recall Module.Basis.linearIndependent {I : Type v} {K : Type u} {V : Type w} [Semiring K]
  [AddCommMonoid V] [Module K V] (b : Module.Basis I K V) : LinearIndependent K b

section

variable {I : Type v} {K : Type u} {V : Type w} [Semiring K] [AddCommMonoid V] [Module K V]

/-- Every vector in a module has a unique finitely supported coordinate family with respect to a
basis. -/
-- Proof sketch: use `b.repr x` for existence, with `b.linearCombination_repr x` giving the
-- required equality; for uniqueness, apply `b.repr` to a candidate equality and use that
-- `b.repr` is inverse to `Finsupp.linearCombination K b`.
theorem Module.Basis.existsUnique_finsupp_linearCombination (b : Module.Basis I K V) (x : V) :
    ∃! l : I →₀ K, Finsupp.linearCombination K b l = x := by
  refine ⟨b.repr x, b.linearCombination_repr x, ?_⟩
  intro l hl
  simpa [hl] using (b.repr_linearCombination l).symm

end
