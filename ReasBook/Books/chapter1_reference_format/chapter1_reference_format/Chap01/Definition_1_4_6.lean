import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) [Semiring K] {V : Type v} [AddCommMonoid V] [Module K V] (A : Set V)

/- Definition 1.4.6 is `core/canonical`: a family of generators of a `K`-module `V` is expressed
directly by the canonical proposition that the span of the subset is the whole space. -/
#check (Submodule.span K A = ⊤)
