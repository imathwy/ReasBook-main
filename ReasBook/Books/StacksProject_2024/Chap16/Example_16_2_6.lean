import Mathlib
import stacks_project.Chap10.Definition_10_17_1
import stacks_project.Chap15.Lemma_15_94_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial PrimeSpectrum

universe u

noncomputable section

namespace Algebra

/-
Domain-style sampling for Example 16.2.6:
- primary domain: commutative algebra and affine smooth loci for finitely presented quotient maps;
- sampled owner declarations:
  `Algebra.smoothLocus`,
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth`,
  `Algebra.isOpen_smoothLocus`,
  `Algebra.singularIdeal`;
- best owner abstraction: `Algebra.smoothLocus` for the quotient map `R → A`;
- primitive data: the public owner declarations
  `smoothCounterexamplePolynomialRing k`,
  `smoothCounterexampleRelationIdeal k`,
  `smoothCounterexampleR k`,
  `smoothCounterexampleA k`,
  `smoothCounterexampleX k`,
  `smoothCounterexampleYInR k i`,
  `smoothCounterexampleY k i`;
- derived API: the identification of `smoothLocus R A` with `⋃ i, D(yᵢ)` and the resulting
  non-compactness.
- minimal coefficient assumptions from the sampled owners: `CommRing k` for the quotient
  presentation and smooth-locus description, with `Nontrivial k` needed only for the
  non-compactness statement.

Source/core/bridge triage:
- source-facing: the two public theorems describing the smooth locus and its non-compactness;
- core/canonical: `Algebra.smoothLocus`, `PrimeSpectrum.basicOpen`, and
  `Algebra.FinitePresentation.quotient`;
- bridge/view: the internal `Option ℕ+` presentation, with `none` representing `x` and `some i`
  representing `yᵢ`. This keeps the source indexing `y₁, y₂, …` explicit rather than silently
  reindexing by all of `ℕ`, while the public theorem surface is expressed through the source-facing
  owners listed above.
-/

/-- The ambient polynomial ring `k[x, yᵢ \mid i : ℕ+]` for Example 16.2.6, modeled by letting
`none` index `x` and `some i` index `yᵢ`. -/
def smoothCounterexamplePolynomialRing (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (Option ℕ+) k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexamplePolynomialRing k) := by
  delta smoothCounterexamplePolynomialRing
  infer_instance

/-- The polynomial variable `x` in the ambient ring of Example 16.2.6. -/
private def smoothCounterexampleXPolynomial (k : Type u) [CommRing k] :
    smoothCounterexamplePolynomialRing k :=
  X (none : Option ℕ+)

/-- The polynomial variable `yᵢ` in the ambient ring of Example 16.2.6. -/
private def smoothCounterexampleYPolynomial (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexamplePolynomialRing k :=
  X (some i)

/-- The defining ideal `(x yᵢ \mid i \ge 1)` of the source ring `R` in Example 16.2.6. -/
def smoothCounterexampleRelationIdeal (k : Type u) [CommRing k] :
    Ideal (smoothCounterexamplePolynomialRing k) :=
  Ideal.span (Set.range fun i : ℕ+ ↦
    smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i)

/-- The source ring
`R = k[x, y₁, y₂, y₃, ...] / (x yᵢ \mid i \ge 1)` from Example 16.2.6. -/
def smoothCounterexampleR (k : Type u) [CommRing k] : Type u :=
  smoothCounterexamplePolynomialRing k ⧸ smoothCounterexampleRelationIdeal k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexampleR k) := by
  delta smoothCounterexampleR
  infer_instance

/-- The class of `x` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleX (k : Type u) [CommRing k] : smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleXPolynomial k)

/-- The class of `yᵢ` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleYInR (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleYPolynomial k i)

/-- The principal ideal `(x)` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleXIdeal (k : Type u) [CommRing k] :
    Ideal (smoothCounterexampleR k) :=
  principalIdeal (smoothCounterexampleX k)

/-- The target ring `A = R / (x)` from Example 16.2.6. -/
def smoothCounterexampleA (k : Type u) [CommRing k] : Type u :=
  smoothCounterexampleR k ⧸ smoothCounterexampleXIdeal k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexampleA k) := by
  delta smoothCounterexampleA
  infer_instance

instance (k : Type u) [CommRing k] :
    Algebra (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  exact Ideal.Quotient.algebra _

/-- The class of `yᵢ` in the target ring `A` of Example 16.2.6. -/
def smoothCounterexampleY (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleA k :=
  Ideal.Quotient.mk (smoothCounterexampleXIdeal k) (smoothCounterexampleYInR k i)

open scoped PrimeSpectrum

/-- The quotient map `R → A = R / (x)` in Example 16.2.6 is finitely presented. -/
instance smoothCounterexampleFinitePresentation (k : Type u) [CommRing k] :
    FinitePresentation (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  let _ : Module (smoothCounterexampleR k) (smoothCounterexampleR k) :=
    @Semiring.toModule (smoothCounterexampleR k) inferInstance
  have hfg : (smoothCounterexampleXIdeal k).FG := by
    simpa [smoothCounterexampleXIdeal, principalIdeal] using
      (Submodule.fg_span_singleton (smoothCounterexampleX k))
  simpa [smoothCounterexampleA] using
    (FinitePresentation.quotient hfg :
      FinitePresentation (smoothCounterexampleR k)
        ((smoothCounterexampleR k) ⧸ smoothCounterexampleXIdeal k))

-- Proof sketch: away from `y_i`, the relation `x y_i = 0` forces `x = 0`, so on `D(y_i)` the
-- quotient `A` agrees with the corresponding localization of `R` and is smooth there. Conversely,
-- if all `y_i` vanish at a prime of `A`, the fiber still carries infinitely many singular
-- directions coming from the countable family of relations `x y_i`, so the map is not smooth at
-- that prime.
/-- Example 16.2.6: for
`R = k[x, y₁, y₂, y₃, ...] / (x y_i \mid i \ge 1)` and `A = R / (x)`, the smooth locus of the
ring map `R → A` is exactly `⋃_i D(y_i)`. -/
theorem smoothCounterexample_smoothLocus_eq_iUnion_basicOpen
    (k : Type u) [CommRing k] :
    smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) =
      ⋃ i : ℕ+, D(smoothCounterexampleY k i) := sorry

-- Proof sketch: if the displayed union were compact, then in the spectral space `Spec(A)` it
-- would be a finite union of basic opens. But any finite subunion `⋃_{i ∈ s} D(y_i)` misses a
-- prime containing all `y_i` with `i ∉ s`, so no finite subcover exists.
/-- The smooth locus in the counterexample is not quasi-compact, equivalently not compact as a
subset of `Spec(A)`. -/
theorem smoothCounterexample_smoothLocus_not_isCompact
    (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ IsCompact (smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)) := sorry

end Algebra
