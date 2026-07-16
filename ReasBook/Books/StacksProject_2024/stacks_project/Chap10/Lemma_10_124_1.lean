import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Lemma_10_121_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [FiniteDimensional (FractionRing A) (FractionRing B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/- Domain-style sampling:
- primary domain: one-dimensional Noetherian local domains, local orders of vanishing, and the
  residue-field-degree weighted sum over maximal localizations of a finite-type algebra with finite
  fraction-field extension;
- sampled owner declarations:
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `Ring.ordFrac`,
  `Ring.ordFrac_eq_ord`,
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`,
  `Module.Finite`;
- best owner abstraction: `Ring.ordFrac` is the canonical valuation owner, and
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac` is the chapter owner for the weighted
  maximal-spectrum sum, while
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension` is the owner for the
  semilocality conclusion; this file should expose only the source-facing ring-level
  reformulations in terms of `Ring.ord`, not a parallel public owner for that sum;
- source/core/bridge triage:
  `source-facing`: the semilocality conclusion for `B`, together with the textbook inequality and
    equality criterion for the weighted sum of local orders of an element `x : A`;
  `core/canonical`: `Ring.ordFrac`, `Module.finrank`, and the chapter theorem
    `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`, together with the semilocality
    owner `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`;
  `bridge/view`: `Ring.ordFrac_eq_ord` translates the fraction-field owner to the ring-level local
    orders that appear in the source statement;
- primitive data: the algebra tower and the chosen element `x : A`;
- derived API: finiteness of `MaximalSpectrum B`, the induced residue-field extensions, and the
  canonical weighted maximal-spectrum sum.
-/

/- Lemma 10.124.1 first asserts that `B` is semilocal. This is exactly the chapter owner theorem
`finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`. -/
recall finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension

-- Proof sketch: let `B'` be the integral closure of `A` in `B`, choose the finite intermediate
-- `A`-subalgebra `C ⊂ B'` supplied by Lemma `10.123.14`, and apply Lemma `10.121.8` to `C`. The
-- localizations of `C` at the primes lying under the maximal ideals of `B` agree with the
-- corresponding localizations of `B`, while the extra maximal ideals of `C` contribute a
-- nonnegative remainder term, giving the inequality. The source-facing hypotheses
-- `x ∈ maximalIdeal A` and `x ≠ 0` are not part of this canonical inequality statement; they
-- appear only in the later equality criterion.
/-- The weighted sum of local orders of `x` over the maximal ideals of `B` is bounded above by the
fraction-field degree times its order on `A`. -/
theorem sum_residueFieldDegree_mul_local_ord_le_fractionFieldDegree_mul_ord
    (x : A) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    ∑ m : MaximalSpectrum B,
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) x)) ≤
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
  sorry

-- Proof sketch: the inequality above comes from the finite intermediate subalgebra `C`. Equality
-- holds exactly when there are no extra maximal ideals of `C` beyond those coming from maximal
-- ideals of `B`; then `C → B` induces a bijection on maximal ideals and is an isomorphism after
-- localizing at each maximal ideal, forcing `B = C`, hence `B` is finite over `A`. Conversely, if
-- `A → B` is finite, the equality is exactly Lemma `10.121.8` applied to `B`. The source-facing
-- hypotheses are the primitive conditions `x ∈ maximalIdeal A` and `x ≠ 0`, rather than the
-- derived inequalities `0 < Ring.ord A x` and `Ring.ord A x < ⊤`.
/-- Lemma 10.124.1: for a finite-type extension of domains `A ⊂ B` with `A` a one-dimensional
Noetherian local domain and finite fraction-field extension, once the semilocality conclusion for
`B` is recalled above, equality between the global order term `[Frac(B) : Frac(A)] ord_A(x)` and
the weighted sum of local orders over the maximal ideals of `B` holds exactly when `A → B` is
finite, for `x ∈ maximalIdeal A` nonzero. -/
theorem sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_iff_moduleFinite
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    ∑ m : MaximalSpectrum B,
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) x)) =
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x ↔
      Module.Finite A B := by
  sorry

end
