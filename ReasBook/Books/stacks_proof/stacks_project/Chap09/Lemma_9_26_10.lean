import Mathlib
import StacksProject_2024.Chap09.Definition_9_26_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {k' : Type v}
variable [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] FractionRing.isScalarTower_liftAlgebra

open scoped MvRatFunc

/- Domain-style sampling for Lemma 9.26.10:
- primary domain: algebraic field extensions and the induced extension on rational function fields;
- sampled owner declarations:
  `MvPolynomial.algebraMvPolynomial`,
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial`;
- owner abstraction: the induced fraction-field algebra coming from the canonical algebra
  `MvPolynomial (Fin r) k →ₐ[k] MvPolynomial (Fin r) k'`, together with the mathlib owner theorem
  `rank_fractionRing_mvPolynomial`;
- primitive data: only the finite extension `k'/k` and the number of variables `r`;
- derived API: the finite-dimensional degree equality below.

Source/core/bridge triage:
- `source-facing`: the equality of degrees of rational function field extensions in `r` variables;
- `core/canonical`: `rank_fractionRing_mvPolynomial` plus the canonical `FractionRing.liftAlgebra`
  interface;
- `bridge/view`: the passage from rank to `finrank` by `Cardinal.toNat`.

The refined file keeps the public statement directly on the canonical owner theorem and uses only a
local module instance for elaboration support. -/

open Algebra.IsAlgebraic

noncomputable local instance (r : ℕ) : Module k⟮X_(Fin r)⟯ k'⟮X_(Fin r)⟯ :=
  (FractionRing.liftAlgebra (MvPolynomial (Fin r) k) k'⟮X_(Fin r)⟯).toModule

/-- Lemma 9.26.10: for a finite field extension `k'/k`, the induced extension of rational
function fields in `r` variables has degree `[k' : k]`, hence is finite. The source-facing
statement is derived from the canonical owner theorem `rank_fractionRing_mvPolynomial`, using the
standard induced fraction-field algebra `FractionRing.liftAlgebra`. -/
@[stacks 0G1M]
lemma finrank_fractionRing_mvPolynomial_eq_finrank (r : ℕ) :
    Module.finrank k⟮X_(Fin r)⟯ k'⟮X_(Fin r)⟯ = Module.finrank k k' := by
  simpa only [Module.finrank, Cardinal.toNat_lift] using
    congrArg Cardinal.toNat (rank_fractionRing_mvPolynomial (Fin r))

end
