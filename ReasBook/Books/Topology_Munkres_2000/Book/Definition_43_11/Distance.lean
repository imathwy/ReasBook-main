module

public import Topology_Munkres_2000.Book.Notation_43_4.Quotient
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic

public section

universe u

open scoped CauchySequences Topology

namespace CauchySequences.Quotient

variable {X : Type u} [PseudoMetricSpace X]

/-- Helper for Definition 43.11: the limiting pointwise distance between two Cauchy sequence
representatives. -/
noncomputable def representativeDistance (x y : X̃) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ ↦ dist (x.1 n) (y.1 n))

/-- Helper for Definition 43.11: pointwise distances between Cauchy sequences tend to their
representative distance. -/
theorem representativeDistance_tendsto (x y : X̃) :
    Filter.Tendsto (fun n : ℕ ↦ dist (x.1 n) (y.1 n)) Filter.atTop
      (𝓝 (representativeDistance x y)) := by
  apply CauchySeq.tendsto_limUnder
  exact uniformContinuous_dist.comp_cauchySeq <|
    CauchySeq.prodMk (mem_cauchySequences.mp x.2) (mem_cauchySequences.mp y.2)

/-- Helper for Definition 43.11: equivalent representatives have the same limiting pointwise
distance. -/
theorem representativeDistance_congr {x x' y y' : X̃}
    (hx : x ∼ x') (hy : y ∼ y') :
    representativeDistance x y = representativeDistance x' y' := by
  have hdist : Filter.Tendsto
      (fun n : ℕ ↦ dist (dist (x.1 n) (y.1 n)) (dist (x'.1 n) (y'.1 n)))
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ dist_dist_dist_le _ _ _ _)
    simpa using Filter.Tendsto.add (CauchySequences.equivalent_tendsto hx)
      (CauchySequences.equivalent_tendsto hy)
  apply tendsto_nhds_unique (representativeDistance_tendsto x y)
  exact (tendsto_iff_of_dist hdist).mpr (representativeDistance_tendsto x' y')

/-- Helper for Definition 43.11: the canonical distance on equivalence classes of Cauchy
sequences. -/
noncomputable instance instDist : Dist (CauchySequences.Quotient X) where
  dist p q := _root_.Quotient.liftOn₂' p q representativeDistance fun _ _ _ _ hx hy ↦
    representativeDistance_congr (CauchySequences.setoid_rel_iff_equivalent.mp hx)
      (CauchySequences.setoid_rel_iff_equivalent.mp hy)

/-- Helper for Definition 43.11: the quotient distance is the limiting pointwise distance of
representatives. -/
@[simp]
theorem dist_mk (x y : X̃) :
    dist (⟦x⟧ : CauchySequences.Quotient X) ⟦y⟧ = representativeDistance x y := by
  -- Evaluating the quotient lift on representatives recovers its defining function.
  rfl

/-- Helper for Definition 43.11: the quotient distance vanishes on the diagonal. -/
theorem dist_self (p : CauchySequences.Quotient X) : dist p p = 0 := by
  -- Reduce to a representative, whose pointwise self-distance is constantly zero.
  refine Quotient.inductionOn' p fun x ↦ ?_
  rw [dist_mk]
  apply tendsto_nhds_unique (representativeDistance_tendsto x x)
  simpa only [_root_.dist_self] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0))

/-- Helper for Definition 43.11: the quotient distance is symmetric. -/
theorem dist_comm (p q : CauchySequences.Quotient X) : dist p q = dist q p := by
  -- On representatives, symmetry identifies the two pointwise distance sequences.
  refine Quotient.inductionOn₂' p q fun x y ↦ ?_
  rw [dist_mk, dist_mk]
  apply tendsto_nhds_unique (representativeDistance_tendsto x y)
  have pointwiseDistance_comm :
      (fun n : ℕ ↦ dist (x.1 n) (y.1 n)) = (fun n : ℕ ↦ dist (y.1 n) (x.1 n)) := by
    funext n
    exact _root_.dist_comm _ _
  rw [pointwiseDistance_comm]
  exact representativeDistance_tendsto y x

/-- Helper for Definition 43.11: the quotient distance satisfies the triangle inequality. -/
theorem dist_triangle (p q r : CauchySequences.Quotient X) :
    dist p r ≤ dist p q + dist q r := by
  -- Pass the pointwise triangle inequality to the limits of three representatives.
  refine Quotient.inductionOn₃' p q r fun x y z ↦ ?_
  rw [dist_mk, dist_mk, dist_mk]
  have sum_tendsto : Filter.Tendsto
      (fun n : ℕ ↦ dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n)) Filter.atTop
      (nhds (representativeDistance x y + representativeDistance y z)) :=
    (representativeDistance_tendsto x y).add (representativeDistance_tendsto y z)
  exact le_of_tendsto_of_tendsto' (representativeDistance_tendsto x z) sum_tendsto
    (fun n ↦ _root_.dist_triangle _ _ _)

/-- Helper for Definition 43.11: zero quotient distance is equivalent to equality of equivalence
classes. -/
theorem dist_eq_zero_iff (p q : CauchySequences.Quotient X) : dist p q = 0 ↔ p = q := by
  -- Equality of represented classes is exactly convergence of their pointwise distance to zero.
  refine Quotient.inductionOn₂' p q fun x y ↦ ?_
  rw [dist_mk, mk_eq_mk_iff]
  constructor
  · intro h
    have distance_tendsto_zero : Filter.Tendsto
        (fun n : ℕ ↦ dist (x.1 n) (y.1 n)) Filter.atTop (nhds 0) := by
      simpa only [h] using representativeDistance_tendsto x y
    rw [CauchySequences.equivalent_iff]
    rw [Metric.tendsto_atTop] at distance_tendsto_zero
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using distance_tendsto_zero
  · intro h
    exact tendsto_nhds_unique (representativeDistance_tendsto x y)
      (CauchySequences.equivalent_tendsto h)


end CauchySequences.Quotient

end
