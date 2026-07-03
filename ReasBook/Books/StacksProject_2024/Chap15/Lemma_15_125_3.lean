import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Valuation.ValuationRing
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely presented module decompositions over generalized valuation rings;
- sampled owner declarations:
  `PreValuationRing`,
  `PreValuationRing.iff_ideal_total`,
  `principalIdeal`;
- best owner abstraction: this item remains `source-facing`, with the ambient generalized
  valuation-ring hypothesis carried directly by the canonical owner `PreValuationRing R`; the
  cyclic quotient summands should use the chapter owner `principalIdeal` rather than restating
  `Ideal.span ({f} : Set R)`. The bridge from the ideal-order formulation to this owner is
  `PreValuationRing.iff_ideal_total`; the stronger PID structure theorem
  `Module.equiv_free_prod_directSum` is only a downstream specialization and would change the
  theorem's semantics by introducing a free part, so the decomposition here should stay on the
  canonical `LinearEquiv`/`DirectSum` surface instead of collapsing to that later view or
  introducing a local package;
- primitive data vs. derived API:
  primitive data is the ambient ring `R` together with the finitely presented `R`-module `M`;
  derived API is the finite index `n`, the family `f : Fin n → R`, and the resulting linear
  equivalence from `M` to the direct sum of the corresponding principal quotient modules.

Source/core/bridge triage:
- `source-facing`: the existence of a finite cyclic-quotient decomposition for `M`;
- `core/canonical`: `PreValuationRing`, `principalIdeal`, and `LinearEquiv`;
- `bridge/view`: `PreValuationRing.iff_ideal_total`, relating the source's ideal-order language to
  the canonical owner `PreValuationRing`.
-/

section

variable {R : Type u} [CommRing R] [PreValuationRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: if `R` is subsingleton, then every `R`-module is subsingleton, so one may take
-- `n = 0` and the unique linear equivalence to the empty direct sum. Otherwise, argue by induction
-- on the dimension of `M / maximalIdeal R • ⊤` over the residue field of the local ring coming
-- from `PreValuationRing R`. Choose a lift whose annihilator is the annihilator of `M`, split off
-- the corresponding cyclic summand using the principal-pure lifting criterion of
-- Lemma `15.125.1`, and conclude that the resulting annihilator ideal is principal because `M` is
-- finitely presented.
/-- Lemma 15.125.3: if `R` is a generalized valuation ring in the canonical sense
`PreValuationRing R`, then every finitely presented `R`-module is linearly isomorphic to a finite
direct sum of principal quotient modules `R ⧸ (fᵢ)`. -/
theorem finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] ⨁ i : Fin n, R ⧸ principalIdeal (f i)) := sorry

end
