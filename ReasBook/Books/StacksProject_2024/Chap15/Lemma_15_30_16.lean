import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.Basic
import stacks_project.Chap10.Lemma_10_24_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial
open scoped BigOperators

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain triage:
- primary domain: regular elements in multivariable polynomial rings, with the coefficient
  hypothesis organized by the Chapter 10 localization-family owner;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `away_localization_family_map_injective_iff_smul_family_map_injective`,
  `koszulLinearForm`,
  `regular_permutations_subsequences_polynomial_tfae`,
  `IsRegular`;
- best owner abstraction: the canonical injectivity hypothesis is the Chapter 10 owner
  `awayLocalizationFamilyMap R a`; the textbook tuple-multiplication map is only a bridge/view via
  the equivalence theorem from `Lemma_10_24_4`, while the Chapter 15 tuple owner
  `koszulLinearForm` stays auxiliary because this item is about the source-facing polynomial linear
  form itself rather than the Koszul complex owner;
- primitive data: a finite coefficient family `a : Fin n → R`;
- derived API: the regularity of the linear form `∑ i, C (a i) * X i`.

Layering:
- `source-facing`: the regularity of the linear form `∑ i, C (a i) * X i`;
- `core/canonical`: the owner map `awayLocalizationFamilyMap R a`;
- `bridge/view`: `away_localization_family_map_injective_iff_smul_family_map_injective`.
-/

/-- Lemma 15.30.16: if the canonical map from `R` to the family of away localizations at the
coefficients `a_i` is injective, equivalently if the map `R → R^n`, `x ↦ (x a_i)_i`, is
injective, then the linear form `∑ i, a_i t_i` is a nonzerodivisor in the polynomial ring
`R[t_0, ..., t_{n-1}]`. -/
theorem isRegular_linearForm_of_injective_awayLocalizationFamilyMap (a : Fin n → R)
    (h : Function.Injective (awayLocalizationFamilyMap R a)) :
    IsRegular (∑ i, C (a i) * X i) := by
  sorry

end
