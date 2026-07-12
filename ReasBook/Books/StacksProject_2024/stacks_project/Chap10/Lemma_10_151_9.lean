import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {n : ℕ}
variable [Algebra (MvPolynomial (Fin n) k) A]
variable [IsScalarTower k (MvPolynomial (Fin n) k) A]
variable [FiniteType (MvPolynomial (Fin n) k) A]

open KaehlerDifferential MvPolynomial

local notation "P" => MvPolynomial (Fin n) k

/- Domain-style sampling for Lemma 10.151.9:
- primary domain: finite-type étale criteria over a polynomial algebra over a field, combining the
  canonical étale owner with maximal-local dimension and Kähler-differential generation data;
- sampled owner declarations:
  `Algebra.Etale`,
  `etale_iff_flat_and_gUnramified`,
  `KaehlerDifferential.mvPolynomialBasis`,
  `ringKrullDim_localizationAtMaximal_mvPolynomial`;
- best owner abstraction: the core/canonical owner is `Algebra.Etale P A`; the local dimension
  clause on `MaximalSpectrum A` and the spanning condition for the coordinate differentials are
  bridge/view data encoding the source criterion, not a second owner abstraction;
- primitive data vs. derived API: the primitive source-facing data are the maximal-local dimension
  requirement and the generating family `D k A (algebraMap P A (X i))`. Unramifiedness, flatness,
  regular-locality, and finite presentation are derived owner-level consequences routed through
  `Etale`, `GUnramified`, and the chapter’s regular-local API.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion below;
- `core/canonical`: `Algebra.Etale P A`;
- `bridge/view`: the maximal-spectrum local-dimension clause and the coordinate-differential span
  clause.
-/

-- Proof sketch: for the forward implication, étaleness gives unramifiedness and flatness. The
-- exact sequence for Kähler differentials of `k → k[x₁, …, xₙ] → A` identifies
-- `Ω[A⁄MvPolynomial (Fin n) k]` with the quotient of `Ω[A⁄k]` by the span of the coordinate
-- differentials, so unramifiedness forces that span to be all of `Ω[A⁄k]`. Quasi-finiteness of an
-- étale map over the `n`-dimensional polynomial algebra then gives the dimension formula for the
-- maximal local rings. For the reverse implication, the spanning condition forces the relative
-- differential module over `MvPolynomial (Fin n) k` to vanish, hence the map is unramified; the
-- local dimension condition and the regularity criterion make every maximal localization regular,
-- yielding flatness, and Lemma `10.151.8` then upgrades flatness plus unramified finite
-- presentation to étaleness.
/-- Lemma 10.151.9: for a finite type `k[x_1, \ldots, x_n]`-algebra `A`, the structural map
`k[x_1, \ldots, x_n] → A` is étale if and only if the local ring `A_m` has Krull dimension `n`
for every maximal ideal `m ⊂ A`, and the differentials of the images of the coordinate variables
generate `Ω[A⁄k]` as an `A`-module. -/
theorem etale_mvPolynomial_iff_localRingDimension_eq_and_coordinateDifferentials_span :
    Etale P A ↔
      ((∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n) ∧
        Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤) := sorry

end

end Algebra
