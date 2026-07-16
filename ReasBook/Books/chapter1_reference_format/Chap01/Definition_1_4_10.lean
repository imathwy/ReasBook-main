import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.4.10: a `K`-vector space is finite-dimensional when it satisfies the canonical
mathlib predicate `FiniteDimensional K V`; equivalently, it admits finitely many generators, and
it is infinite-dimensional exactly when this predicate fails. -/
recall FiniteDimensional (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V]
  [Module K V] : Prop

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/- The finite-generation reformulation is already the canonical theorem `Module.finite_def`; for a
vector space, it identifies `FiniteDimensional K V` with finite generation of the top subspace. -/
#check (Module.finite_def : FiniteDimensional K V ↔ (⊤ : Submodule K V).FG)
