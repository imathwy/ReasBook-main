import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage:
* primary domain: formal smoothness of commutative algebras, especially polynomial algebras;
* sampled owner declarations:
  `Algebra.FormallySmooth`,
  `Algebra.mvPolynomial`,
  `Algebra.FormallySmooth.iff_split_surjection`,
  and the chapter-level recall items `Definition_10_138_1` and `Remark_10_138_6`;
* layer: `core/canonical`, since the source statement is exactly the upstream owner instance for the
  polynomial algebra;
* primitive data: only the base ring `R` and variable type `σ`;
* derived API: the `Algebra.FormallySmooth R (MvPolynomial σ R)` instance itself.

There is no source-facing extra structure to package here, so the right refinement is direct recall
of the owner instance rather than a local wrapper or an anonymous `inferInstance` check.
-/
section

variable (R : Type u) (σ : Type v) [CommRing R]

/- Lemma 10.138.4: for any family of variables `σ`, the polynomial ring `R[σ]`, formalized as
`MvPolynomial σ R`, is formally smooth over `R`. This is exactly the canonical mathlib instance
`Algebra.FormallySmooth R (MvPolynomial σ R)`. -/
recall Algebra.mvPolynomial

end
