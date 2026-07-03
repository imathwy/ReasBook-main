import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_1_2_1 (from Items/Chap01) -/
open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u

/-- The subset of `ℚ` cut out by the half-open real interval `(a, b]`. -/
def rationalRightClosedInterval (a b : ℝ) : Set ℚ :=
  ((↑) : ℚ → ℝ) ⁻¹' Ioc a b

/-- The family of subsets of `ℚ` of the form `(a, b] ∩ ℚ` with `a ≤ b`. -/
def rationalRightClosedIntervalFamily : Set (Set ℚ) :=
  {s | ∃ a b : ℝ, a ≤ b ∧ s = rationalRightClosedInterval a b}

/-- The image in `ℝ` of a set of rationals. -/
private def rationalRealImage (s : Set ℚ) : Set ℝ :=
  ((↑) : ℚ → ℝ) '' s

/-- The interval length attached to a set of rationals, computed from the infimum and supremum of
its real image and defined to be `0` on the empty set. -/
private noncomputable def rationalIntervalLength (s : Set ℚ) : ℝ≥0∞ :=
  if s = ∅ then 0 else ENNReal.ofReal (sSup (rationalRealImage s) - sInf (rationalRealImage s))

-- Proof sketch: unfold `rationalIntervalLength` and use the `if` branch for `s = ∅`.
/-- The interval-length function vanishes on the empty set. -/
private theorem rationalIntervalLength_empty :
    rationalIntervalLength ∅ = 0 := sorry

-- Proof sketch: express each member of the finite disjoint family as `(a, b] ∩ ℚ`, order the
-- endpoints, and use finite additivity of interval lengths under disjoint concatenation.
/-- The interval-length function is finitely additive on finite pairwise disjoint unions whose
union is again a rational half-open interval. -/
private theorem rationalIntervalLength_sUnion (I : Finset (Set ℚ))
    (hI : ↑I ⊆ rationalRightClosedIntervalFamily)
    (hdis : PairwiseDisjoint (I : Set (Set ℚ)) id)
    (hmem : ⋃₀ ↑I ∈ rationalRightClosedIntervalFamily) :
    rationalIntervalLength (⋃₀ ↑I) = ∑ u ∈ I, rationalIntervalLength u := sorry

/-- The additive content on rational half-open intervals defined by interval length. -/
noncomputable def rationalIntervalContent :
    AddContent ℝ≥0∞ rationalRightClosedIntervalFamily :=
  { toFun := rationalIntervalLength
    empty' := rationalIntervalLength_empty
    sUnion' := rationalIntervalLength_sUnion }

-- Proof sketch: compute the infimum and supremum of `(a, b] ∩ ℚ` inside `ℝ`; density of `ℚ`
-- gives `sInf = a` and `sSup = b`, so the definition reduces to `b - a`.
/-- The rational interval content assigns the length `b - a` to `(a, b] ∩ ℚ`. -/
theorem rationalIntervalContent_apply (a b : ℝ) (hab : a ≤ b) :
    rationalIntervalContent (rationalRightClosedInterval a b) = ENNReal.ofReal (b - a) := sorry

-- Proof sketch: intersections of half-open intervals remain half-open, and set differences split
-- into finite disjoint unions of half-open intervals after intersecting with `ℚ`.
/-- Exercise 1.2.1 (1): The family of sets `(a, b] ∩ ℚ` with `a ≤ b` is a semiring of sets on
`ℚ`. -/
instance rationalRightClosedIntervalFamily_isSetSemiring :
    IsSetSemiring rationalRightClosedIntervalFamily := sorry

-- Proof sketch: for an increasing sequence of rational half-open intervals with union again in the
-- family, the left endpoints decrease, the right endpoints increase, and the corresponding lengths
-- converge to the limiting interval length.
/-- Exercise 1.2.1 (2): The interval-length content on the rational half-open-interval semiring is
lower semicontinuous. -/
instance rationalIntervalContent_isLowerSemicontinuous :
    AddContent.IsLowerSemicontinuous rationalIntervalContent := sorry

-- Proof sketch: for a decreasing sequence of rational half-open intervals with nonempty finite
-- mass at some stage, the endpoints converge monotonically to the limiting interval and the
-- lengths converge from above.
/-- Exercise 1.2.1 (3): The interval-length content on the rational half-open-interval semiring is
upper semicontinuous. -/
instance rationalIntervalContent_isUpperSemicontinuous :
    AddContent.IsUpperSemicontinuous rationalIntervalContent := sorry

-- Proof sketch: decompose `(0, 1] ∩ ℚ` into the disjoint countable union of singleton rational
-- sets; each singleton has length `0`, but the whole interval has length `1`.
/-- Exercise 1.2.1 (4): The interval-length content on `(a, b] ∩ ℚ` fails countable additivity on
disjoint unions in the semiring, so it is not a premeasure. -/
theorem rationalIntervalContent_not_isPremeasureOn :
    ¬ rationalIntervalContent.IsSigmaSubadditive :=
  sorry

/-! ### Definition_1_2 (from Items/Chap01) -/
/-- Definition 1.2: A sigma-algebra (or sigma-field) on `Ω` is the canonical mathlib notion
`MeasurableSpace Ω`; its measurable sets are closed under complements and countable unions, and
therefore contain `Ω` itself. -/
recall MeasurableSpace
