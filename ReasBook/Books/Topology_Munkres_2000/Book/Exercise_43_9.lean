module

public import Topology_Munkres_2000.Book.Definition_43_11.Metric
public import Topology_Munkres_2000.Book.Definition_43_12.Embedding
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Isometry

public section

open Filter Set
open scoped Topology

universe u

variable {X : Type u} [MetricSpace X]

/- Part (a) of Exercise 43.9: pointwise-distance convergence defines an equivalence
relation on the Cauchy sequences in `X`, and the limiting representative
distance is well defined on their quotient and makes it a metric space. -/
#check CauchySequences.Equivalent
#check CauchySequences.equivalentEquivalence
#check CauchySequences.Quotient
#check CauchySequences.Quotient.representativeDistance_congr
#check CauchySequences.Quotient.dist_mk
#synth MetricSpace (CauchySequences.Quotient X)

namespace CauchySequences.Quotient

/-- Helper for Exercise 43.9: throughout this exercise the quotient carries the
topology induced by its limiting-distance metric. -/
noncomputable local instance metricTopology : TopologicalSpace (CauchySequences.Quotient X) :=
  instMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper for Exercise 43.9 (b): the map sending a point to the class of its constant
Cauchy sequence is an isometric embedding. -/
theorem inclusion_isometry : Isometry (inclusion : X → CauchySequences.Quotient X) := by
  -- Constant representatives have the constant pointwise-distance sequence.
  apply Isometry.of_dist_eq
  intro x y
  rw [inclusion_apply, inclusion_apply, dist_mk]
  apply tendsto_nhds_unique (representativeDistance_tendsto _ _)
  simpa only [CauchySequences.constant_apply] using tendsto_const_nhds

/-- Helper for Exercise 43.9: an eventual upper bound on distances from a constant
point bounds the limiting representative distance. -/
lemma representativeDistance_constant_le_of_eventually (a : X) (x : X̃) (r : ℝ)
    (h : ∀ᶠ n in atTop, dist a (x.1 n) ≤ r) :
    representativeDistance (CauchySequences.constant a) x ≤ r := by
  -- Pass the eventual pointwise estimate to the limit defining the quotient distance.
  apply le_of_tendsto (representativeDistance_tendsto (CauchySequences.constant a) x)
  simpa only [CauchySequences.constant_apply] using h

/-- Helper for Exercise 43.9 (c), “indeed”: the images of the terms of every representing
Cauchy sequence converge to the equivalence class represented by that sequence. -/
theorem tendsto_inclusion_mk (x : X̃) :
    Tendsto (fun n ↦ inclusion (x.1 n)) atTop (𝓝 (⟦x⟧ : CauchySequences.Quotient X)) := by
  -- A Cauchy tail controls the limiting distance from each late term to the class of `x`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (mem_cauchySequences.mp x.2) (ε / 2)
    (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbound : ∀ᶠ m in atTop, dist (x.1 n) (x.1 m) ≤ ε / 2 := by
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (hN n hn m hm).le
  calc
    dist (inclusion (x.1 n)) (⟦x⟧ : CauchySequences.Quotient X) =
        representativeDistance (CauchySequences.constant (x.1 n)) x := by
          rw [inclusion_apply, dist_mk]
    _ ≤ ε / 2 := representativeDistance_constant_le_of_eventually (x.1 n) x (ε / 2) hbound
    _ < ε := half_lt_self hε

/-- Helper for Exercise 43.9 (c): the image of the canonical inclusion is dense in the
quotient of Cauchy sequences. -/
theorem denseRange_inclusion : DenseRange (inclusion : X → CauchySequences.Quotient X) := by
  -- Every represented class is a sequential limit of points in the inclusion's range.
  rw [denseRange_iff_closure_range]
  apply eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn' with
  | _ x =>
      apply mem_closure_of_tendsto (tendsto_inclusion_mk x)
      exact Eventually.of_forall fun n ↦ mem_range_self (x.1 n)

end CauchySequences.Quotient

/-- Helper for Exercise 43.9: a sequence in a metric subspace is Cauchy when it
stays asymptotically at distance zero from an ambient Cauchy sequence. -/
lemma cauchySeq_subtype_of_cauchySeq_of_tendsto_dist_zero {Z : Type u} [MetricSpace Z]
    {A : Set Z} {u : ℕ → Z} {v : ℕ → A} (hu : CauchySeq u)
    (huv : Tendsto (fun n ↦ dist (u n) (v n : Z)) atTop (𝓝 0)) : CauchySeq v := by
  -- Split a late pair through the two nearby ambient points and use the Cauchy bound for `u`.
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨Nu, hNu⟩ := Metric.cauchySeq_iff.mp hu (ε / 3) (by linarith)
  obtain ⟨Nv, hNv⟩ := Metric.tendsto_atTop.mp huv (ε / 3) (by linarith)
  refine ⟨max Nu Nv, fun m hm n hn ↦ ?_⟩
  have hmu : dist (u m) (v m : Z) < ε / 3 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
      hNv m (le_trans (le_max_right _ _) hm)
  have hnu : dist (u n) (v n : Z) < ε / 3 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
      hNv n (le_trans (le_max_right _ _) hn)
  have huu : dist (u m) (u n) < ε / 3 :=
    hNu m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  calc
    dist (v m) (v n) = dist (v m : Z) (v n : Z) := rfl
    _ ≤ dist (v m : Z) (u m) + dist (u m) (v n : Z) := dist_triangle _ _ _
    _ ≤ dist (v m : Z) (u m) + (dist (u m) (u n) + dist (u n) (v n : Z)) :=
      add_le_add_right (dist_triangle (u m) (u n) (v n : Z)) (dist (v m : Z) (u m))
    _ < ε := by
      rw [dist_comm (v m : Z) (u m)]
      linarith

/-- Helper for Exercise 43.9: a dense subset contains a point arbitrarily close
to every point of the ambient metric space. -/
lemma exists_subtype_dist_lt_of_dense {Z : Type u} [MetricSpace Z] {A : Set Z}
    (hA : Dense A) (z : Z) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, dist z (a : Z) < ε := by
  -- Package the point supplied by density as an element of the subtype.
  obtain ⟨a, ha, hdist⟩ := hA.exists_dist_lt z hε
  exact ⟨⟨a, ha⟩, hdist⟩

/-- Helper for Exercise 43.9 (d): a metric space with a dense subset in which every
Cauchy sequence converges in the ambient space is complete. -/
theorem completeSpace_of_dense_cauchySeq_tendsto {Z : Type u} [MetricSpace Z]
    {A : Set Z} (hA : Dense A)
    (hconv : ∀ u : ℕ → A, CauchySeq u → ∃ z : Z, Tendsto (fun n ↦ (u n : Z)) atTop (𝓝 z)) :
    CompleteSpace Z := by
  -- Approximate an arbitrary Cauchy sequence by points of the dense subset at vanishing distance.
  classical
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have happrox : ∀ n : ℕ, ∃ a : A, dist (u n) (a : Z) < 1 / (n + 1 : ℝ) := by
    intro n
    apply exists_subtype_dist_lt_of_dense hA (u n)
    positivity
  choose v hv using happrox
  have hdist : Tendsto (fun n ↦ dist (u n) (v n : Z)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hv n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hvCauchy : CauchySeq v :=
    cauchySeq_subtype_of_cauchySeq_of_tendsto_dist_zero hu hdist
  obtain ⟨z, hvz⟩ := hconv v hvCauchy
  refine ⟨z, ?_⟩
  -- Convergence transfers from the approximating sequence because the pointwise distance vanishes.
  exact (tendsto_iff_of_dist hdist).mpr hvz

namespace CauchySequences.Quotient

/-- Helper for Exercise 43.9: the completeness argument uses the topology
induced by the quotient's limiting-distance metric. -/
noncomputable local instance completenessMetricTopology :
    TopologicalSpace (CauchySequences.Quotient X) :=
  instMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper for Exercise 43.9: a Cauchy sequence in the range of the canonical
inclusion is represented termwise by one Cauchy sequence in `X`. -/
lemma exists_cauchyRepresentative_of_range
    (u : ℕ → Set.range (inclusion : X → CauchySequences.Quotient X)) (hu : CauchySeq u) :
    ∃ x : X̃, ∀ n, inclusion (x.1 n) = (u n : CauchySequences.Quotient X) := by
  -- Choose preimages termwise, then reflect the Cauchy estimates through the isometry.
  classical
  have hpreimage : ∀ n, ∃ a : X, inclusion a = (u n : CauchySequences.Quotient X) := by
    intro n
    exact u n |>.property
  choose a ha using hpreimage
  have haCauchy : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    calc
      dist (a m) (a n) = dist (inclusion (a m)) (inclusion (a n)) :=
        (inclusion_isometry.dist_eq (a m) (a n)).symm
      _ = dist (u m) (u n) := by
        rw [ha m, ha n]
        rfl
      _ < ε := hN m hm n hn
  exact ⟨⟨a, mem_cauchySequences.mpr haCauchy⟩, ha⟩

/-- Helper for Exercise 43.9: every Cauchy sequence in the canonical dense range
converges in the quotient. -/
lemma rangeCauchySeq_tendsto
    (u : ℕ → Set.range (inclusion : X → CauchySequences.Quotient X)) (hu : CauchySeq u) :
    ∃ z : CauchySequences.Quotient X,
      Tendsto (fun n ↦ (u n : CauchySequences.Quotient X)) atTop (𝓝 z) := by
  -- The lifted representative converges to its own quotient class by part (c).
  obtain ⟨x, hx⟩ := exists_cauchyRepresentative_of_range u hu
  refine ⟨⟦x⟧, ?_⟩
  apply (tendsto_inclusion_mk x).congr'
  exact Eventually.of_forall hx

/-- Exercise 43.9 (e): the metric quotient of Cauchy sequences is complete. -/
noncomputable instance instCompleteSpace : CompleteSpace (CauchySequences.Quotient X) := by
  -- Apply the dense-subset criterion to the canonical range.
  apply completeSpace_of_dense_cauchySeq_tendsto denseRange_inclusion
  intro u hu
  exact rangeCauchySeq_tendsto u hu

end CauchySequences.Quotient
