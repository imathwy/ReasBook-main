import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open IntermediateField

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 9.26.11:
- primary domain: finitely generated field extensions and their relative algebraic closures;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `fg_top_iff`,
  `algebraicClosure`,
  `mem_algebraicClosure_iff`;
- owner abstraction: `Algebra.EssFiniteType k K` for finite generation, together with the
  canonical intermediate field `algebraicClosure k K`;
- primitive data: no new local data, since the theorem is about the existing owner object
  `algebraicClosure k K`;
- derived API: only the source-facing finite-dimensionality statement below.

Source/core/bridge triage:
- `source-facing`: Lemma 9.26.11 itself, asserting that the relative algebraic closure is finite
  over the base field for finitely generated extensions;
- `core/canonical`: the owner hypothesis `Algebra.EssFiniteType k K` and the canonical relative
  algebraic closure `algebraicClosure k K`;
- `bridge/view`: the identification of the textbook `FG` formulation with the owner hypothesis via
  `fg_top_iff`, already provided upstream.

The refined file keeps the theorem directly on `algebraicClosure k K`, without introducing any
parallel local wrapper for the same intermediate field, and reuses the upstream bridge from
`(⊤ : IntermediateField k K).FG` to `Algebra.EssFiniteType k K`. -/

/-- Lemma 9.26.11: if `K/k` is a finitely generated field extension, then the relative algebraic
closure of `k` in `K` is finite over `k`. The source-facing theorem uses the canonical owner
`[Algebra.EssFiniteType k K]` for finite generation. -/
-- Proof sketch: choose a transcendence basis of `K/k`; then Lemma 9.26.10 identifies every finite
-- subextension of `algebraicClosure k K` with a finite extension of the corresponding rational
-- function field of uniformly bounded degree. This bounds the degrees of all finite intermediate
-- subextensions of `algebraicClosure k K / k`, from which finite-dimensionality follows.
lemma finiteDimensional_algebraicClosure [Algebra.EssFiniteType k K] :
    FiniteDimensional k (algebraicClosure k K) := sorry

end
