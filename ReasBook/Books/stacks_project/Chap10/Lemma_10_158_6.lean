import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

-- Proof sketch: rewrite formal smoothness using `Algebra.formallySmooth_iff`. Over the field `K`,
-- every `K`-module is free and hence projective, so the projectivity of `Ω[K⁄k]` is automatic.
-- This leaves exactly the vanishing condition on the first cotangent homology module.
/-- Lemma 10.158.6: for a field extension `K/k`, `K` is formally smooth over `k` if and only if
the first cotangent homology `H_1(L_{K/k})` vanishes. In the canonical mathlib formulation, this
vanishing is expressed as `Subsingleton (H1Cotangent k K)`. -/
theorem formallySmooth_iff_subsingleton_h1Cotangent_of_field :
    Algebra.FormallySmooth k K ↔ Subsingleton (Algebra.H1Cotangent k K) := by
  rw [Algebra.formallySmooth_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨inferInstance, h⟩

end

end Algebra
