import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Example_10_119_5
import StacksProject_2024.Chap10.Lemma_10_162_13
import StacksProject_2024.Chap10.Proposition_10_162_16
import StacksProject_2024.Chap10.Remark_10_119_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped PthPowerSubfield

/- 
Domain-style sampling:
- primary domain: Chapter 10 commutative algebra of `N-1`/`N-2`/Nagata conditions for discrete
  valuation rings and their finite overrings;
- sampled owner declarations:
  `IsN1Ring`,
  `IsN2Ring`,
  `NagataRing`,
  `finitePthPowerCoefficientSubring`;
- best owner abstraction: the public owners are already `IsN1Ring`, `IsN2Ring`, and `NagataRing`,
  while Example `10.119.5` contributes the concrete source-facing DVR
  `finitePthPowerCoefficientSubring k p` and its canonical finite overring `A[f]`;
- primitive vs. derived: primitive data are the DVR `A := finitePthPowerCoefficientSubring k p`,
  the finite overring `A[f]`, and the hypothesis `¬ FiniteDimensional (k^[p]) k`; generic
  finite-extension reductions are derived bridge API and should stay companion-only.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

-- Proof sketch: a discrete valuation ring is Noetherian and has only two prime ideals, namely
-- `(0)` and the maximal ideal. The quotient by the maximal ideal is a field, hence `N-2`, so the
-- Nagata condition is equivalent to requiring the quotient by `(0)`, i.e. `R` itself, to be
-- `N-2`.
/-- Example 10.162.17 (1): a discrete valuation ring is Nagata if and only if it is `N-2`. -/
theorem nagataRing_iff_isN2Ring_of_isDiscreteValuationRing :
    NagataRing R ↔ IsN2Ring R := by
  constructor
  · intro hR
    letI : NagataRing R := hR
    letI : UniversallyJapaneseRing R := inferInstance
    infer_instance
  · intro hR
    -- The reverse implication is the DVR-specific quotient-by-primes argument:
    -- `R` is Noetherian, `R ⧸ maximalIdeal R` is a field, and the `p = (0)` branch identifies
    -- with the given `N-2` hypothesis.
    sorry

end

section

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

local notation "A" => finitePthPowerCoefficientSubring k p

-- Proof sketch: choose `f ∉ A` from Example `10.119.5`. If `A` were Nagata, then the finite
-- overring `A[f]` would also be Nagata by Proposition `10.162.16`; since `A[f]` is a local
-- domain, Lemma `10.162.13` would make it analytically unramified, contradicting Remark
-- `10.119.6`.
/-- Example 10.162.17 (2): if `k / k^p` is infinite, then the discrete valuation ring
`A := finitePthPowerCoefficientSubring k p` from Example `10.119.5` is not Nagata. -/
theorem finitePthPowerCoefficientSubring_not_nagataRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ NagataRing ↥A := by
  intro hA
  obtain ⟨f, hf⟩ := exists_not_mem_finitePthPowerCoefficientSubring k p hnfd
  letI : NagataRing ↥A := hA
  letI : Module.Finite ↥A ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  letI : NagataRing ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
    nagataRing_of_finiteType ↥A
  exact
    finitePthPowerCoefficientAdjoinSubring_not_isAnalyticallyUnramified k p hf inferInstance

-- Proof sketch: combine the source-facing non-Nagata statement with part `(1)`.
/-- For the DVR `A := finitePthPowerCoefficientSubring k p` of Example `10.119.5`, infinite
`k / k^p` also forces failure of `N-2`. -/
theorem finitePthPowerCoefficientSubring_not_isN2Ring
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ IsN2Ring ↥A := by
  intro hA
  exact
    finitePthPowerCoefficientSubring_not_nagataRing k p hnfd
      ((nagataRing_iff_isN2Ring_of_isDiscreteValuationRing ↥A).2 hA)

end

section

variable (A : Type u) [CommRing A]

-- Proof sketch: if `A` were Nagata, then in particular it would be `N-2` by the first clause.
-- The example argues that for the specific finite extension `A ⊂ R = A[f]`, the ring `R` is not
-- `N-1`; this contradicts the Nagata property for finite domain extensions.
/-- Companion reduction: a finite domain extension of a Nagata ring cannot fail `N-1`. -/
theorem discreteValuationRing_not_nagataRing_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ NagataRing A := by
  intro hA
  letI : NagataRing A := hA
  letI : NagataRing R := nagataRing_of_finiteType A
  exact hR inferInstance

section

variable [IsDomain A] [IsDiscreteValuationRing A]

-- Proof sketch: combine the previous theorem with
-- `nagataRing_iff_isN2Ring_of_isDiscreteValuationRing`.
/-- A discrete valuation ring with a finite domain extension failing `N-1` is also not `N-2`. -/
theorem discreteValuationRing_not_isN2Ring_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ IsN2Ring A := by
  intro hA
  exact
    discreteValuationRing_not_nagataRing_of_finite_extension_not_isN1Ring
      A R hR
      ((nagataRing_iff_isN2Ring_of_isDiscreteValuationRing A).2 hA)

end

end
