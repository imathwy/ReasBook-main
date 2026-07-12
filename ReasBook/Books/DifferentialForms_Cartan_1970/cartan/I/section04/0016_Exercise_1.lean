import Mathlib.Analysis.Complex.Exponential
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.PiTopology

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace PowerSeries

open Filter
open scoped Topology
open scoped Uniformity

-- Domain sampling / source-core-bridge triage:
-- * primary domain: the order topology on one-variable formal power series and its induced
--   continuity/completeness statements.
-- * core/canonical owners sampled: `PowerSeries.order`,
--   `PowerSeries.WithPiTopology.instTopologicalSpace`,
--   `PowerSeries.WithPiTopology.denseRange_toPowerSeries`,
--   `PowerSeries.WithPiTopology.instCompleteSpace`.
-- * source-facing primitive data here: the Bourbaki-style distance `orderDist`.
-- * derived API here: the induced metric-space structure and the bridge from that metric topology
--   to the canonical `WithPiTopology` topology/uniformity.

variable {R : Type*}

section Metric

variable [Ring R]

/-- Exercise 1 (1): for formal power series, the distance is `0` on the diagonal and `exp (-k)`
when the order of the difference is `k`. -/
def orderDist (S T : R⟦X⟧) : ℝ :=
  letI : DecidableEq R⟦X⟧ := Classical.decEq _
  if S = T then 0 else Real.exp (-((S - T).order.toNat : ℝ))

/-- Away from the diagonal, `orderDist` is the exponential of minus the order of the difference. -/
theorem orderDist_eq_exp_neg_order_toNat {S T : R⟦X⟧} (h : S ≠ T) :
    orderDist S T = Real.exp (-((S - T).order.toNat : ℝ)) := by
  simp [orderDist, h]

theorem orderDist_self (S : R⟦X⟧) : orderDist S S = 0 := by
  simp [orderDist]

/-- Helper for Exercise 1: the exponential terms coming from finite orders are antitone in the
order bound. -/
theorem exp_neg_toNat_le_of_le {m n : ℕ∞} (hn : n ≠ ⊤) (hmn : m ≤ n) :
    Real.exp (-((n.toNat : ℕ) : ℝ)) ≤ Real.exp (-((m.toNat : ℕ) : ℝ)) := by
  -- Convert the order comparison to a comparison on natural truncations, then use monotonicity
  -- of the real exponential function.
  have htoNat : m.toNat ≤ n.toNat := ENat.toNat_le_toNat hmn hn
  rw [Real.exp_le_exp]
  exact neg_le_neg (mod_cast htoNat)

theorem orderDist_comm (S T : R⟦X⟧) : orderDist S T = orderDist T S := by
  by_cases h : S = T
  · subst h
    simp [orderDist]
  · have h' : T ≠ S := fun hTS ↦ h hTS.symm
    rw [orderDist_eq_exp_neg_order_toNat h, orderDist_eq_exp_neg_order_toNat h']
    have horder : (S - T).order.toNat = (T - S).order.toNat := by
      simpa [sub_eq_add_neg, add_comm] using congrArg ENat.toNat (order_neg (T - S))
    rw [horder]

@[simp] theorem orderDist_eq_zero {S T : R⟦X⟧} : orderDist S T = 0 ↔ S = T := by
  constructor
  · intro h
    by_contra hne
    rw [orderDist_eq_exp_neg_order_toNat hne] at h
    exact (ne_of_gt (Real.exp_pos _)) h
  · rintro rfl
    exact orderDist_self _

/-- Helper for Exercise 1: `orderDist` is nonnegative. -/
theorem orderDist_nonneg (S T : R⟦X⟧) : 0 ≤ orderDist S T := by
  by_cases h : S = T
  · simp [h, orderDist]
  · rw [orderDist_eq_exp_neg_order_toNat h]
    positivity

/-- Helper for Exercise 1: the distance attached to the order valuation is nonarchimedean. -/
theorem orderDist_nonarchimedean (S T U : R⟦X⟧) :
    orderDist S U ≤ max (orderDist S T) (orderDist T U) := by
  by_cases hSU : S = U
  · subst hSU
    have hnonneg : 0 ≤ max (orderDist S T) (orderDist T S) :=
      (orderDist_nonneg S T).trans (le_max_left _ _)
    simpa [orderDist_self] using hnonneg
  by_cases hST : S = T
  · subst hST
    simpa [orderDist_self] using (le_max_right (0 : ℝ) (orderDist S U))
  by_cases hTU : T = U
  · subst hTU
    simpa [orderDist_self] using (le_max_left (orderDist S T) (0 : ℝ))
  -- Route correction: compare orders through the valuation inequality
  -- `min_order_le_order_add` before translating back to the exponential metric.
  rw [orderDist_eq_exp_neg_order_toNat hSU, orderDist_eq_exp_neg_order_toNat hST,
    orderDist_eq_exp_neg_order_toNat hTU]
  have hmin :
      min (S - T).order (T - U).order ≤ (S - U).order := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (min_order_le_order_add (S - T) (T - U))
  have hSU_finite : (S - U).order ≠ ⊤ := by
    intro htop
    exact hSU (sub_eq_zero.mp (order_eq_top.mp htop))
  by_cases hle : (S - T).order ≤ (T - U).order
  · have hST_SU : (S - T).order ≤ (S - U).order := by
      simpa [min_eq_left hle] using hmin
    have hdist : Real.exp (-(((S - U).order.toNat : ℕ) : ℝ)) ≤
        Real.exp (-(((S - T).order.toNat : ℕ) : ℝ)) :=
      exp_neg_toNat_le_of_le hSU_finite hST_SU
    refine hdist.trans ?_
    exact le_max_left _ _
  · have hTU_ST : (T - U).order ≤ (S - T).order := le_of_not_ge hle
    have hTU_SU : (T - U).order ≤ (S - U).order := by
      simpa [min_eq_right hTU_ST] using hmin
    have hdist : Real.exp (-(((S - U).order.toNat : ℕ) : ℝ)) ≤
        Real.exp (-(((T - U).order.toNat : ℕ) : ℝ)) :=
      exp_neg_toNat_le_of_le hSU_finite hTU_SU
    refine hdist.trans ?_
    exact le_max_right _ _

theorem orderDist_triangle (S T U : R⟦X⟧) :
    orderDist S U ≤ orderDist S T + orderDist T U := by
  -- First use the stronger ultrametric estimate, then bound the maximum by the sum.
  refine (orderDist_nonarchimedean S T U).trans ?_
  refine max_le_iff.mpr ?_
  constructor
  · linarith [orderDist_nonneg T U]
  · linarith [orderDist_nonneg S T]

/-- Exercise 1 (2): `orderDist` defines a metric space structure on formal power series. -/
@[reducible] def orderDistMetricSpace : MetricSpace R⟦X⟧ where
  dist := orderDist
  dist_self := orderDist_self
  dist_comm := orderDist_comm
  dist_triangle := orderDist_triangle
  eq_of_dist_eq_zero := orderDist_eq_zero.mp

namespace OrderDist

/-- The metric-space structure attached to `orderDist`, exposed through a scope so downstream
statements can use the ordinary topological and uniform APIs without repeating a local `letI`. -/
scoped instance : MetricSpace R⟦X⟧ := orderDistMetricSpace

end OrderDist

end Metric

section UniformityPrelude

open scoped PowerSeries.OrderDist
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

variable [Ring R]

/-- Helper for Exercise 1: agreement of the first `n + 1` coefficients is exactly the closed
metric ball condition at radius `exp (-(n + 1))`. -/
theorem orderDist_le_exp_neg_succ_iff {S T : R⟦X⟧} (n : ℕ) :
    orderDist S T ≤ Real.exp (-((n + 1 : ℕ) : ℝ)) ↔
      ∀ m < n + 1, coeff m S = coeff m T := by
  by_cases hST : S = T
  · subst hST
    constructor
    · intro _
      intro m hm
      rfl
    · intro _
      simpa [orderDist] using (le_of_lt (Real.exp_pos (-((n + 1 : ℕ) : ℝ))))
  · rw [orderDist_eq_exp_neg_order_toNat hST]
    rw [Real.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
    constructor
    · intro hdist m hm
      have hlt : m < (S - T).order.toNat := lt_of_lt_of_le hm hdist
      have hcoeff : coeff m (S - T) = 0 := coeff_of_lt_order_toNat _ hlt
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hcoeff)
    · intro hcoeff
      have horder : ↑(n + 1) ≤ (S - T).order := by
        refine nat_le_order (S - T) (n + 1) ?_
        intro m hm
        simpa [sub_eq_add_neg, hcoeff m hm]
      have htoNat : n + 1 ≤ (S - T).order.toNat :=
        ENat.toNat_le_toNat horder (by
          intro htop
          exact hST (sub_eq_zero.mp (order_eq_top.mp htop)))
      exact htoNat

/-- Helper for Exercise 1: agreement of the first `n` coefficients is exactly the closed
metric ball condition at radius `exp (-n)`. -/
theorem orderDist_le_exp_neg_iff {S T : R⟦X⟧} (n : ℕ) :
    orderDist S T ≤ Real.exp (-((n : ℕ) : ℝ)) ↔
      ∀ m < n, coeff m S = coeff m T := by
  cases n with
  | zero =>
      constructor
      · intro _ m hm
        exact (Nat.not_lt_zero _ hm).elim
      · intro _
        -- For the empty prefix condition, it is enough to note that `orderDist` is always at
        -- most `1`.
        by_cases hST : S = T
        · subst hST
          simp [orderDist]
        · rw [orderDist_eq_exp_neg_order_toNat hST]
          have hle : -(((S - T).order.toNat : ℕ) : ℝ) ≤ 0 := by
            have hnonneg : 0 ≤ (((S - T).order.toNat : ℕ) : ℝ) := by
              exact_mod_cast Nat.zero_le (S - T).order.toNat
            linarith
          simpa using Real.exp_le_exp.mpr hle
  | succ n =>
      -- The successor case is the previously established `n + 1` threshold lemma.
      simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using
        (orderDist_le_exp_neg_succ_iff (R := R) (S := S) (T := T) n)

/-- Helper for Exercise 1: every one-variable multi-index is the singleton at its degree. -/
theorem unique_index_eq_single (d : Unit →₀ ℕ) : d = Finsupp.single () (d ()) := by
  apply Finsupp.ext
  intro u
  cases u
  simp

/-- Helper for Exercise 1: the first `n` one-variable indices form a finite set of
coordinates in the product presentation. -/
def prefixIndices (n : ℕ) : Finset (Unit →₀ ℕ) :=
  (Finset.range n).image fun m => Finsupp.single () m

/-- Helper for Exercise 1: membership in `prefixIndices n` means that the index degree is
strictly less than `n`. -/
theorem mem_prefixIndices_iff {n : ℕ} {d : Unit →₀ ℕ} :
    d ∈ prefixIndices n ↔ d () < n := by
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨m, hm, hdm⟩
    subst hdm
    simpa [prefixIndices] using hm
  · intro hd
    refine Finset.mem_image.mpr ?_
    refine ⟨d (), by simpa [prefixIndices] using hd, ?_⟩
    exact (unique_index_eq_single d).symm

section OrderDistUniformity

/-- Helper for Exercise 1: the metric uniformity coming from `orderDist` has the prefix-agreement
basis. -/
theorem orderDist_uniformity_hasBasis_prefix :
    (𝓤 (R⟦X⟧)).HasBasis (fun _ : ℕ => True) fun n =>
      { p : R⟦X⟧ × R⟦X⟧ | ∀ m < n, coeff m p.1 = coeff m p.2 } := by
  let r : ℝ := Real.exp (-1)
  have hr0 : 0 < r := by
    positivity
  have hr1 : r < 1 := by
    simpa [r] using Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
  have hMetric :
      (𝓤 (R⟦X⟧)).HasBasis (fun _ : ℕ => True) fun n =>
        { p : R⟦X⟧ × R⟦X⟧ | orderDist p.1 p.2 ≤ r ^ n } := by
    exact Metric.uniformity_basis_dist_le_pow (α := R⟦X⟧) hr0 hr1
  refine hMetric.congr (fun _ => Iff.rfl) ?_
  intro n _
  -- Rewrite the metric threshold `r ^ n` as `exp (-n)` and apply the valuation/prefix bridge.
  ext p
  have hpow :
      r ^ n = Real.exp (-((n : ℕ) : ℝ)) := by
    change Real.exp (-1) ^ n = Real.exp (-((n : ℕ) : ℝ))
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa [hpow] using (orderDist_le_exp_neg_iff (R := R) (S := p.1) (T := p.2) n)

end OrderDistUniformity

section WithPiUniformity

variable [UniformSpace R] [DiscreteUniformity R]

/-- Helper for Exercise 1: the product uniformity on one-variable coefficient functions over a
discrete coefficient space is generated by agreement on finitely many coefficients. -/
theorem coeffFunction_uniformity_hasBasis_finite :
    (𝓤 (R⟦X⟧)).HasBasis (fun s : Finset (Unit →₀ ℕ) => True) fun s =>
      { p : R⟦X⟧ × R⟦X⟧ | ∀ d ∈ s, p.1 d = p.2 d } := by
  let hEmbed := UniformOnFun.isUniformEmbedding_toFun_finite (α := Unit →₀ ℕ) (β := R)
  have hEq :
      (𝓤 (R⟦X⟧)) =
        𝓤 (UniformOnFun (Unit →₀ ℕ) R {s : Set (Unit →₀ ℕ) | s.Finite}) := by
    have hId :
        (𝓤 (R⟦X⟧)) =
          Filter.comap (fun x : ((Unit →₀ ℕ) → R) × ((Unit →₀ ℕ) → R) ↦ x)
            (𝓤 ((Unit →₀ ℕ) → R)) := by
      simpa [PowerSeries, MvPowerSeries] using
        (Filter.comap_id' :
          Filter.comap (fun x : ((Unit →₀ ℕ) → R) × ((Unit →₀ ℕ) → R) ↦ x)
            (𝓤 ((Unit →₀ ℕ) → R)) = 𝓤 ((Unit →₀ ℕ) → R)).symm
    have hFinite :
        Filter.comap (fun x : ((Unit →₀ ℕ) → R) × ((Unit →₀ ℕ) → R) ↦ x)
            (𝓤 ((Unit →₀ ℕ) → R)) =
          𝓤 (UniformOnFun (Unit →₀ ℕ) R {s : Set (Unit →₀ ℕ) | s.Finite}) := by
      simpa [UniformOnFun.toFun, UniformOnFun.ofFun] using hEmbed.comap_uniformity
    exact hId.trans hFinite
  rw [hEq]
  have hDiscrete :
      (𝓤 R).HasBasis (fun _ : Unit => True) fun _ : Unit => (SetRel.id : Set (R × R)) := by
    simpa [DiscreteUniformity.eq_principal_setRelId] using
      (hasBasis_principal (SetRel.id : Set (R × R)))
  let hFinite :=
    UniformOnFun.hasBasis_uniformity_of_covering_of_basis
      (α := Unit →₀ ℕ) (β := R) (𝔖 := {s : Set (Unit →₀ ℕ) | s.Finite})
      (t := fun s : Finset (Unit →₀ ℕ) => (s : Set (Unit →₀ ℕ)))
      (p := fun _ : Unit => True) (V := fun _ : Unit => (SetRel.id : Set (R × R)))
      (ht := fun s => s.finite_toSet)
      (hdir := by
        intro s t
        refine ⟨s ∪ t, ?_, ?_⟩ <;> simp)
      (hex := by
        intro s hs
        refine ⟨hs.toFinset, ?_⟩
        intro d hd
        simpa using hd)
      hDiscrete
  refine hFinite.to_hasBasis
    (fun i _ => ⟨i.1, trivial, by
      intro p hp
      simpa [UniformOnFun.gen, SetRel.id] using hp⟩)
    (fun s _ => ⟨(s, ()), trivial, by
      intro p hp
      simpa [UniformOnFun.gen, SetRel.id] using hp⟩)

/-- Helper for Exercise 1: the canonical `WithPiTopology` uniformity has the same
prefix-agreement basis as the order metric uniformity. -/
theorem withPi_uniformity_hasBasis_prefix :
    (𝓤 (R⟦X⟧)).HasBasis (fun _ : ℕ => True) fun n =>
      { p : R⟦X⟧ × R⟦X⟧ | ∀ m < n, coeff m p.1 = coeff m p.2 } := by
  refine (coeffFunction_uniformity_hasBasis_finite (R := R)).to_hasBasis ?_ ?_
  · intro s _
    refine ⟨s.sup (fun d => d ()) + 1, trivial, ?_⟩
    intro p hp d hd
    -- The finite set `s` is controlled by a long enough initial prefix.
    have hdlt : d () < s.sup (fun e => e ()) + 1 :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun e => e ()) hd)
    have hprefix := hp (d ()) hdlt
    rw [unique_index_eq_single d]
    simpa [PowerSeries.coeff] using hprefix
  · intro n _
    refine ⟨prefixIndices n, trivial, ?_⟩
    intro p hp m hm
    -- Conversely, the prefix index set records exactly the coefficients below `n`.
    have hmem : Finsupp.single () m ∈ prefixIndices n :=
      (mem_prefixIndices_iff (n := n) (d := Finsupp.single () m)).2 (by simpa using hm)
    simpa [PowerSeries.coeff] using hp (Finsupp.single () m) hmem

/-- Helper for Exercise 1: the order metric and the canonical coefficientwise product uniformity
coincide. -/
theorem orderDist_uniformity_eq_withPi_uniformity :
    orderDistMetricSpace.toUniformSpace = instUniformSpace R := by
  refine UniformSpace.ext ?_
  exact (orderDist_uniformity_hasBasis_prefix (R := R)).eq_of_same_basis
    (withPi_uniformity_hasBasis_prefix (R := R))

end WithPiUniformity

end UniformityPrelude

section TopologicalBridge

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [Ring R] [TopologicalSpace R] [hd : DiscreteTopology R]

/-- The metric topology defined by `orderDist` agrees with the canonical `WithPiTopology`
topology on formal power series over a discrete coefficient ring. -/
theorem orderDistMetricSpace_toTopologicalSpace_eq_withPi :
    orderDistMetricSpace.toUniformSpace.toTopologicalSpace =
      instTopologicalSpace R := by
  cases hd.eq_bot
  letI : UniformSpace R := ⊥
  letI : DiscreteUniformity R := inferInstance
  -- Once the uniform structures agree, the induced topologies agree by functoriality.
  simpa using congrArg (fun u : UniformSpace R⟦X⟧ => u.toTopologicalSpace)
    (orderDist_uniformity_eq_withPi_uniformity (R := R))

end TopologicalBridge

section TopologicalContinuity

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [Ring R]

/-- Exercise 1 (3): addition is continuous for the topology induced by `orderDist`. -/
theorem continuous_add_orderDist :
    Continuous (fun p : R⟦X⟧ × R⟦X⟧ ↦ p.1 + p.2) := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  let htop : orderDistMetricSpace.toUniformSpace.toTopologicalSpace = instTopologicalSpace R :=
    orderDistMetricSpace_toTopologicalSpace_eq_withPi
  rw [htop]
  letI : TopologicalSpace R⟦X⟧ := instTopologicalSpace R
  letI : IsTopologicalRing R⟦X⟧ := instIsTopologicalRing R
  simpa using (continuous_add : Continuous (fun p : R⟦X⟧ × R⟦X⟧ ↦ p.1 + p.2))

/-- Exercise 1 (3), multiplication case: multiplication is continuous for the topology induced by
`orderDist`. -/
theorem continuous_mul_orderDist :
    Continuous (fun p : R⟦X⟧ × R⟦X⟧ ↦ p.1 * p.2) := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  let htop : orderDistMetricSpace.toUniformSpace.toTopologicalSpace = instTopologicalSpace R :=
    orderDistMetricSpace_toTopologicalSpace_eq_withPi
  rw [htop]
  letI : TopologicalSpace R⟦X⟧ := instTopologicalSpace R
  letI : IsTopologicalRing R⟦X⟧ := instIsTopologicalRing R
  simpa using (continuous_mul : Continuous (fun p : R⟦X⟧ × R⟦X⟧ ↦ p.1 * p.2))

end TopologicalContinuity

section DenseRange

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [CommRing R]

/-- Exercise 1 (4): the inclusion of polynomials into power series has dense image for the
topology induced by `orderDist`. -/
theorem denseRange_toPowerSeries_orderDist :
    DenseRange (Polynomial.toPowerSeries : Polynomial R → R⟦X⟧) := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  let htop : orderDistMetricSpace.toUniformSpace.toTopologicalSpace = instTopologicalSpace R :=
    orderDistMetricSpace_toTopologicalSpace_eq_withPi
  rw [htop]
  simpa using denseRange_toPowerSeries R

end DenseRange

section UniformBridge

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [Ring R] [UniformSpace R] [DiscreteUniformity R]

/-- The uniform space induced by `orderDistMetricSpace` agrees with the canonical
`WithPiTopology` uniform structure on formal power series over a discrete coefficient ring. -/
theorem orderDistMetricSpace_toUniformSpace_eq_withPi :
    orderDistMetricSpace.toUniformSpace = instUniformSpace R := by
  -- This is the packaged public statement; the actual basis comparison was proved earlier.
  exact orderDist_uniformity_eq_withPi_uniformity (R := R)

end UniformBridge

section Completeness

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [Ring R]

/-- Exercise 1 (5): the metric space defined by `orderDist` is complete. -/
theorem completeSpace_orderDist :
    CompleteSpace R⟦X⟧ := by
  letI : UniformSpace R := ⊥
  letI : DiscreteUniformity R := inferInstance
  let hunif : orderDistMetricSpace.toUniformSpace = instUniformSpace R :=
    orderDistMetricSpace_toUniformSpace_eq_withPi
  rw [hunif]
  letI : UniformSpace R⟦X⟧ := instUniformSpace R
  simpa using (instCompleteSpace R : CompleteSpace R⟦X⟧)

end Completeness

section Derivative

open scoped PowerSeries.OrderDist
open PowerSeries.WithPiTopology

variable [CommRing R]

/-- Exercise 1 (6): formal differentiation is continuous for the metric topology defined by
`orderDist`. -/
theorem continuous_derivative_orderDist :
    Continuous (d⁄dX R : R⟦X⟧ → R⟦X⟧) := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  let htop : orderDistMetricSpace.toUniformSpace.toTopologicalSpace = instTopologicalSpace R :=
    orderDistMetricSpace_toTopologicalSpace_eq_withPi
  rw [htop]
  letI : TopologicalSpace R⟦X⟧ := instTopologicalSpace R
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro n
  letI : IsTopologicalSemiring R := inferInstance
  have hcoeff :
      Tendsto (fun x : R⟦X⟧ ↦ coeff (n + 1) x * (n + 1 : R)) (nhds f)
        (nhds (coeff (n + 1) f * (n + 1 : R))) :=
    ((continuous_coeff R (n + 1)).mul continuous_const).continuousAt
  simpa [coeff_derivative] using hcoeff

end Derivative

end PowerSeries
