import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

section

variable {n : ℕ}

/- Domain-style sampling for standard smooth presentations with prescribed generators:
* primary domain: standard smooth commutative algebra and submersive presentations;
* sampled owner declarations:
  `Algebra.IsStandardSmooth.out`,
  `Algebra.SubmersivePresentation.reindex`,
  `Algebra.SubmersivePresentation.comp`,
  `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`;
* best owner abstraction:
  `Algebra.IsStandardSmooth` is the ambient owner providing a chosen `SubmersivePresentation`, and
  `SubmersivePresentation.reindex` is the canonical bridge for normalizing the distinguished
  Jacobian variables to a `Fin c`-summand;
* primitive vs. derived:
  the primitive source-facing data are the standard smooth owner, the chosen finite family
  `e : Fin n ↪ A`, and the distinguished variable-selection map `P.map`. The inequality
  `n ≤ c` is auxiliary bookkeeping used only to identify the first `n` distinguished variables
  inside the chosen owner `P`.

Source/core/bridge triage:
* source-facing: a standard smooth presentation of `A` in which a prescribed finite family of
  elements of `A` appears among the distinguished Jacobian generators;
* core/canonical owner: `Algebra.IsStandardSmooth` and `SubmersivePresentation`;
* bridge/view: the coordinate presentation indexed by `Fin c ⊕ Fin m` with
  `P.map = Sum.inl` is the canonical reindexing of an arbitrary `SubmersivePresentation` along the
  distinguished range of `P.map`.

Primitive data are the standard smooth owner, the chosen finite family `e : Fin n ↪ A`, and the
distinguished variables selected by the primitive field `P.map`. The index inequality `n ≤ c` is
derived only after choosing the canonical `P.map = Sum.inl` presentation and is used solely to
place the prescribed family inside the first `c` distinguished variables.
-/
-- Proof sketch: choose a submersive presentation of `A` over `R`, enumerate the prescribed finite
-- subset by `e : Fin n ↪ A`, lift those elements to polynomials in the chosen generators, and
-- adjoin new variables `x₁, …, xₙ` together with relations `xᵢ - hᵢ`. Reindex the resulting
-- submersive presentation so that the Jacobian variables are exactly the `Fin c`-summand. Then
-- the first `n` of those distinguished variables map to the chosen elements.
/-- Lemma 16.3.6: if `R → A` is standard smooth and `e : Fin n ↪ A` enumerates a finite subset
of cardinality `n`, then `A` admits a submersive presentation
`R[x₁, ..., x_{c + m}] / (f₁, ..., f_c)` whose distinguished Jacobian variables are the first
`c`, with `n ≤ c`, and whose first `n` distinguished generators map to the prescribed
elements `e i`. This is a bridge theorem on the canonical owner `Algebra.IsStandardSmooth`,
not a second owner abstraction. -/
theorem IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators
    [IsStandardSmooth R A] (e : Fin n ↪ A) :
    ∃ c m, ∃ P : SubmersivePresentation R A (Fin c ⊕ Fin m) (Fin c),
      P.map = Sum.inl ∧
        ∃ h : n ≤ c, ∀ i : Fin n, P.val (.inl (Fin.castLE h i)) = e i := sorry

end

end Algebra
