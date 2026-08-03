module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.MetricSpace.Bounded

public section

/- Proposition 45.2 (1). A subset of `EuclideanSpace ℝ (Fin n)` is compact if
and only if it is closed and bounded. This is the finite-dimensional Heine–Borel
theorem. -/
#check fun (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n))) ↦
  (Metric.isCompact_iff_isClosed_bounded :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s)

/-- Helper for Proposition 45.2: restricting polynomials to an infinite subset of a
topological integral domain is injective. -/
lemma Polynomial.toContinuousMapOnAlgHom_injective_of_infinite
    {R : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R] [IsTopologicalRing R]
    {s : Set R} (hs : s.Infinite) :
    Function.Injective (Polynomial.toContinuousMapOnAlgHom s) := by
  intro p q hpq
  -- Equality of the bundled maps gives equality of evaluations throughout `s`.
  apply Polynomial.eq_of_infinite_eval_eq
  refine hs.mono ?_
  intro x hx
  let x' : s := ⟨x, hx⟩
  have hpoint := congrArg (fun f : C(s, R) ↦ f x') hpq
  simpa only [Set.mem_setOf_eq, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] using hpoint

/-- Helper for Proposition 45.2: polynomial monomials restricted to an infinite real set
remain linearly independent as continuous maps. -/
private lemma linearIndependent_monomialContinuousMaps {s : Set ℝ} (hs : s.Infinite) :
    LinearIndependent ℝ (fun n : ℕ ↦ (Polynomial.monomial n 1).toContinuousMapOn s) := by
  -- Record scalar compatibility using the pointwise module structure on continuous maps.
  have hscalar (r : ℝ) (p : Polynomial ℝ) :
      (Polynomial.toContinuousMapOnAlgHom s : Polynomial ℝ →+ C(s, ℝ)) (r • p) =
        r • (Polynomial.toContinuousMapOnAlgHom s : Polynomial ℝ →+ C(s, ℝ)) p := by
    ext x
    exact Polynomial.eval_smul r p x
  -- The underlying additive homomorphism computes as polynomial restriction.
  have hadd_apply (p : Polynomial ℝ) :
      (Polynomial.toContinuousMapOnAlgHom s : Polynomial ℝ →+ C(s, ℝ)) p =
        p.toContinuousMapOn s := rfl
  -- Transport the monomial basis through the injective additive restriction map.
  have hmapped :=
    (Polynomial.basisMonomials ℝ).linearIndependent.map_of_injective_injectiveₛ
      (fun r : ℝ ↦ r)
      (Polynomial.toContinuousMapOnAlgHom s : Polynomial ℝ →+ C(s, ℝ))
      Function.injective_id
      (Polynomial.toContinuousMapOnAlgHom_injective_of_infinite hs) hscalar
  -- Put the transported family into the explicit monomial normal form used by the statement.
  have hfamily :
      (⇑(Polynomial.toContinuousMapOnAlgHom s : Polynomial ℝ →+ C(s, ℝ)) ∘
          (Polynomial.basisMonomials ℝ : ℕ → Polynomial ℝ)) =
        fun n : ℕ ↦ (Polynomial.monomial n 1).toContinuousMapOn s := by
    funext n
    rw [Polynomial.coe_basisMonomials]
    exact hadd_apply _
  rw [hfamily] at hmapped
  exact hmapped

/-- The continuous real-valued functions on `[0, 1]`, with the uniform metric,
do not form a proper metric space. -/
theorem continuousMap_not_properSpace :
    ¬ ProperSpace C(Set.Icc (0 : ℝ) 1, ℝ) := by
  intro hproper
  -- Properness supplies local compactness, so Riesz's theorem makes the space finite-dimensional.
  letI : ProperSpace C(Set.Icc (0 : ℝ) 1, ℝ) := hproper
  letI : FiniteDimensional ℝ C(Set.Icc (0 : ℝ) 1, ℝ) :=
    FiniteDimensional.of_locallyCompactSpace ℝ
  -- The restricted monomials form an infinite independent family, contradicting finite dimension.
  have hinterval : (Set.Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite zero_lt_one
  exact Module.Finite.not_linearIndependent_of_infinite _
    (linearIndependent_monomialContinuousMaps hinterval)

/-- Proposition 45.2 (2). The compactness criterion by closedness and boundedness
fails for real-valued continuous functions on the compact interval `[0, 1]`, equipped
with the uniform metric. -/
theorem continuousMap_compact_analogue_fails :
    ¬ ∀ 𝓕 : Set C(Set.Icc (0 : ℝ) 1, ℝ),
      IsCompact 𝓕 ↔ IsClosed 𝓕 ∧ Bornology.IsBounded 𝓕 := by
  intro h
  apply continuousMap_not_properSpace
  exact ⟨fun f r ↦ (h (Metric.closedBall f r)).mpr
    ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall⟩⟩

end
