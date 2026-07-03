import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.MvPolynomial.Basic
import StacksProject_2024.Chap15.Lemma_15_21_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]
variable (n : ℕ)
local notation "P" => MvPolynomial (Fin n) R
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
variable [Module.FinitePresentation (MvPolynomial (Fin n) R) M]

/- Domain triage:
- primary domain: flatness descent for modules finitely presented over a polynomial `R`-algebra
  along an injective integral base change `R → S`;
- sampled owner declarations:
  `Module.Flat`,
  `Module.FinitePresentation`,
  `MvPolynomial (Fin n) R`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat R M`, with the polynomial
  arity `n` kept explicit because it is not inferable from the module arguments;
- primitive data: the injective integral algebra map `R → S`, the polynomial owner ring `P`,
  the `P`-module structure on `M`, and the finite-presentation hypothesis
  `[Module.FinitePresentation P M]`;
- derived API: the base-change flatness hypothesis and flatness conclusion for the canonical
  restricted-scalar `R`-module `RestrictScalars R P M`.

Layering:
- `source-facing`: the polynomial finite-presentation descent statement from the source text;
- `core/canonical`: `Module.Flat` and `Module.FinitePresentation`;
- `bridge/view`: the Chapter 15 finite-base-change descent theorem
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
  this file is the source-facing polynomial finite-presentation specialization feeding into that
  bridge, not a second flatness owner.
-/

-- Proof sketch: choose a finite presentation of `M` over `R[x_1, ..., x_n]`, spread the finitely
-- many coefficients to a finitely generated `ℤ`-subalgebra `R₀ ⊆ R` and a finite `R₀`-subalgebra
-- `S₀ ⊆ S`, descend flatness of `S ⊗[R] RestrictScalars R P M` to some stage by finite
-- presentation, apply Lemma `15.21.5` to `R₀ → S₀`, and then recover flatness of
-- `RestrictScalars R P M` over `R` by base change via Lemma `10.39.7`.
/-- Lemma 15.21.6: let `R → S` be an injective integral ring map, and let `M` be a finitely
presented `P`-module, where `P = R[x₁, …, xₙ]` is formalized by `MvPolynomial (Fin n) R`.
If the base change `S ⊗[R] (RestrictScalars R P M)` is flat over `S`, then the restricted
`R`-module `RestrictScalars R P M` is flat over `R`. -/
theorem flat_of_injective_algebraMap_of_isIntegral_of_flat_tensorProduct_of_finitePresentation_mvPolynomial
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] RestrictScalars R P M)) :
    Module.Flat R (RestrictScalars R P M) := sorry

end
