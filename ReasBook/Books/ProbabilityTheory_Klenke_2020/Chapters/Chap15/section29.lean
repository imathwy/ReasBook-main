

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_29 (from Items/Chap15) -/
open Complex MeasureTheory
open scoped BigOperators Topology

universe u

-- Proof sketch: the forward implication follows from continuity of `charFun`, positivity of the
-- finite Gram sums, and `charFun_zero`. For the converse implication, apply the locally compact
-- abelian version of Bochner's theorem to `EuclideanSpace ℝ (Fin d)`, which is canonically
-- self-dual.
/-- Theorem 15.29 (1): a continuous function on `ℝ^d` is the characteristic function of a
probability distribution if and only if it is positive semidefinite and has value `1` at `0`. -/
theorem exists_probabilityMeasure_charFun_eq_iff {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : Continuous φ) :
    (∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) = φ) ↔
      IsPositiveSemidefiniteFunction φ ∧ φ 0 = 1 := sorry

/-- The multiplicative-group form of Definition 15.27: a complex-valued function on a commutative
group is positive semidefinite if every finite quotient-kernel matrix is positive semidefinite. -/
def IsPositiveSemidefiniteMulFunction {H : Type*} [CommGroup H] (φ : H → ℂ) : Prop :=
  IsPositiveSemidefiniteFunction (φ ∘ Additive.toMul)

/-- Bridge between the multiplicative-group and additive-group formulations of positive
semidefiniteness. -/
theorem isPositiveSemidefiniteMulFunction_iff {H : Type*} [CommGroup H] {φ : H → ℂ} :
    IsPositiveSemidefiniteMulFunction φ ↔
      IsPositiveSemidefiniteFunction (φ ∘ Additive.toMul) :=
  Iff.rfl

section LocallyCompactAbelian

variable {G : Type u} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalAddGroup G]

/-- The characteristic function of a probability measure on an additive topological abelian group,
viewed as a function on the Pontryagin dual. -/
noncomputable def pontryaginCharFun
    (μ : ProbabilityMeasure G) (χ : PontryaginDual (Multiplicative G)) : ℂ :=
  ∫ x, (χ (Multiplicative.ofAdd x) : ℂ) ∂(μ : Measure G)

-- Proof sketch: for the forward implication, combine continuity of characteristic functions with
-- the positive-semidefiniteness criterion above and evaluate at `0`. For the converse implication,
-- apply Bochner's theorem on the locally compact abelian group `G`, with `φ` interpreted as a
-- continuous positive-definite function on the Pontryagin dual.
/-- Theorem 15.29 (2): the same characterization holds for a locally compact abelian group `G`,
where the characteristic function of a probability measure on `G` is viewed on the Pontryagin dual
`PontryaginDual (Multiplicative G)`. -/
theorem exists_probabilityMeasure_pontryaginCharFun_eq_iff [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ) :
    (∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) ↔
      IsPositiveSemidefiniteMulFunction φ ∧ φ 1 = 1 := sorry

end LocallyCompactAbelian
