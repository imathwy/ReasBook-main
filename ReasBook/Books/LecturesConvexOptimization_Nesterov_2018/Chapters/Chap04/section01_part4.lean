import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_1_2 (from Chap04) -/
universe u

/- Proposition 4.1.2 lies in the cubic-regularization monotonicity domain.

Relevant owner declarations sampled before refinement:
* `Antitone` and `antitone_nat_of_succ_le` from mathlib;
* `antitone_nat_iff_succ_le` in `Chap01/Definition_1_4_1`;
* `RelaxedRegularizedNewtonIteration` in `Chap04/Definition_4_1_5`, the chapter owner of the
  iterate sequence, regularization sequence, and update law;
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Chap04/Definition_4_1_16`, the canonical
  acceptance predicate at a fixed iterate.

Best owner abstraction:
* source-facing: the monotonicity statement for a relaxed regularized Newton trajectory;
* core/canonical: `Antitone (fun k ↦ f (method k))`;
* bridge/view: the successor-step inequality `f (method (k + 1)) ≤ f (method k)`.

Primitive data:
* a relaxed regularized Newton trajectory `method`;
* the accepted-step membership
  `M_k ∈ RegularizedNewton.acceptingParameters f stepMap modelValue x_k`;
* the on-trajectory underestimator inequality `\tilde f_{M_k}(x_k) ≤ f(x_k)`.

Derived API:
* the one-step decrease `f (method (k + 1)) ≤ f (method k)`;
* the antitone objective-value sequence.

This proposition therefore reuses the chapter owner
`RelaxedRegularizedNewtonIteration` instead of restating the iterate sequence, regularization
sequence, and update law as parallel primitive arguments. -/

open RegularizedNewton

variable {X : Type u}

/-- Proposition 4.1.2: if the iterates satisfy `x_{k+1} = T_{M_k}(x_k)`, each accepted trial
point satisfies `f (T_{M_k}(x_k)) ≤ \tilde f_{M_k}(x_k)`, and the visited model values
`\tilde f_{M_k}(x_k)` underestimate `f(x_k)` along the trajectory, then the objective values
decrease stepwise: `f(x_{k+1}) ≤ f(x_k)` for every `k`. -/
theorem objective_values_nonincreasing
    {f : X → ℝ}
    {stepMap : ℝ → X → X}
    {modelValue : ℝ → X → ℝ}
    {L : ℝ}
    (method : RelaxedRegularizedNewtonIteration stepMap L)
    (haccept :
      ∀ k : ℕ,
        method.regularization k ∈ acceptingParameters f stepMap modelValue (method k))
    (modelValue_le_objective :
      ∀ k : ℕ, modelValue (method.regularization k) (method k) ≤ f (method k))
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  rw [method.x_succ k]
  exact le_trans
    ((mem_acceptingParameters_iff
      f stepMap modelValue (method k) (method.regularization k)).1 (haccept k))
    (modelValue_le_objective k)

/-- If each visited model value underestimates the objective along the trajectory, then the
objective values form an antitone sequence. -/
theorem objective_antitone
    {f : X → ℝ}
    {stepMap : ℝ → X → X}
    {modelValue : ℝ → X → ℝ}
    {L : ℝ}
    (method : RelaxedRegularizedNewtonIteration stepMap L)
    (haccept :
      ∀ k : ℕ,
        method.regularization k ∈ acceptingParameters f stepMap modelValue (method k))
    (modelValue_le_objective :
      ∀ k : ℕ, modelValue (method.regularization k) (method k) ≤ f (method k)) :
    Antitone (fun k ↦ f (method k)) :=
  antitone_nat_of_succ_le fun k ↦ by
    simpa using
      objective_values_nonincreasing
        method
        haccept
        modelValue_le_objective
        k

/-! ### Theorem_4_1_2 (from Chap04) -/
open Filter
open scoped CubicRegularizationModelNotation Gradient LevelSetNotation Topology
open scoped CubicRegularizationResidual

noncomputable section

universe u

/- Theorem 4.1.2 splits into a proper-space asymptotic layer and a local-optimality layer whose
first-order owner is intrinsic, while the source-facing second-order consequence is still
expressed in the Euclidean Hessian-matrix view.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the trajectory;
* the canonical sublevel-set owner `𝓛[f](α)`, recalled in `Definition_4_1_1`;
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for the open-convex `C²`
  Hessian-Lipschitz region;
* `cubicRegularizationLocalOptimalityMeasure` in `Definition_4_1_4`, already used downstream
  through the textbook surface `μ[M](x)` when `f` and `L` are ambient;
* `cubicRegularization_localOptimalityMeasure_tendsto_zero` in `Theorem_4_1_1`, the chapter
  owner theorem for `μ[L](xᵢ) → 0` along the cubic-regularization trajectory;
* `MapClusterPt.exists_seq_tendsto` from mathlib, the canonical bridge from cluster points to
  convergent subsequences.

Best owner abstractions:
* source-facing: the convergence and cluster-point consequences for a
  `CubicRegularizationMethod`;
* core/canonical: `𝓛[f](α)`, `HessianLipschitzOn`,
  `cubicRegularizationLocalOptimalityMeasure`,
  `cubicRegularization_localOptimalityMeasure_tendsto_zero`, and the direct `MapClusterPt`
  predicate;
* bridge/view: the feasible-region level set `𝓕 ∩ 𝓛[f]((f x̄))` and the local
  notation `μ[M](x)` from `Definition_4_1_4` for the owner measure when `f` and `L` are fixed.

Primitive data:
* a cubic-regularization method and the underestimator condition along its trajectory;
* feasibility of the trajectory inside `𝓕`;
* boundedness of the feasible sublevel set `𝓕 ∩ 𝓛[f]((f (method i₀)))`;
* the lower-bound and Hessian-control hypotheses needed by the owner theorem
  `cubicRegularization_localOptimalityMeasure_tendsto_zero`;
* pointwise continuity data only for the source-facing quantity being evaluated at a cluster
  point.

Derived API:
* convergence of the objective values;
* nonemptiness and connectedness of the cluster-point set;
* convergence `μ_L(xᵢ) → 0` along the trajectory, via
  `cubicRegularization_localOptimalityMeasure_tendsto_zero`;
* value convergence and stationarity at cluster points;
* second-order positivity at cluster points after supplying the canonical pointwise `C²`
  Hessian-symmetry bridge.

This file therefore keeps only those theorem-level consequences and reuses the existing owner
declarations instead of carrying parallel local wrappers for level sets, cluster-point sets,
least-eigenvalue terms, or `μ_M`. The bounded-level-set asymptotics are stated over the proper
ambient-space layer coming from the trajectory owner, while the local-optimality consequences are
split into an intrinsic operator statement and a Euclidean matrix-view conclusion. -/

section CubicRegularizationLocalOptimality

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

variable {f : E → ℝ} {L : ℝ}

local notation:max "μ[" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f L M x

/-- Helper for Theorem 4.1.2: for a self-adjoint operator, the quadratic value at any unit vector
dominates the bottom of the real spectrum. -/
theorem sInf_spectrum_le_reApplyInnerSelf_of_unit
    {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) {d : E} (hd : ‖d‖ = 1) :
    sInf (spectrum ℝ T) ≤ inner ℝ (T d) d := by
  have hd_mem : d ∈ Metric.sphere (0 : E) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hd
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere (0 : E) 1
  obtain ⟨x0, hx0, hmin⟩ :=
    hcompact.exists_isMinOn ⟨d, hd_mem⟩ T.reApplyInnerSelf_continuous.continuousOn
  have hx0_norm : ‖x0‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx0
  have hx0_ne : x0 ≠ 0 := by
    intro hx0_zero
    simp [hx0_zero] at hx0_norm
  have hspec :
      T.rayleighQuotient x0 ∈ spectrum ℝ T := by
    have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : E) ‖x0‖) x0 := by
      simpa [hx0_norm] using hmin
    have hvec :=
      hT.hasEigenvector_of_isLocalExtrOn hx0_ne (Or.inl hmin'.localize)
    have hspec_lin :
        T.rayleighQuotient x0 ∈ spectrum ℝ (T : E →ₗ[ℝ] E) := by
      exact (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
    simpa [ContinuousLinearMap.spectrum_eq] using hspec_lin
  have hsInf_le :
      sInf (spectrum ℝ T) ≤ T.rayleighQuotient x0 :=
    csInf_le (spectrum.isCompact T).bddBelow hspec
  have hrayleigh_le :
      T.rayleighQuotient x0 ≤ inner ℝ (T d) d := by
    calc
      T.rayleighQuotient x0 = T.reApplyInnerSelf x0 := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          hx0_norm]
        ring
      _ = inner ℝ (T x0) x0 := by
        simpa using ContinuousLinearMap.reApplyInnerSelf_apply T x0
      _ ≤ inner ℝ (T d) d := by
        simpa using hmin hd_mem
  exact hsInf_le.trans hrayleigh_le

/-- Vanishing of the local-optimality measure forces first-order stationarity. -/
-- Proof sketch: when `L + M > 0`, the gradient term in `μ[M](x)` is nonnegative. If the maximum
-- is `0`, that term must vanish, hence `∇ f x = 0`.
theorem gradient_eq_zero_of_cubicRegularizationLocalOptimalityMeasure_eq_zero
    {M : ℝ} (hLM : 0 < L + M)
    {x : E} (hμ : μ[M](x) = 0) :
    ∇ f x = 0 := by
  -- The gradient contribution is squeezed to `0` by the vanishing of the maximum defining `μ`.
  have hsqrt_le_zero :
      Real.sqrt ((2 / (L + M)) * ‖∇ f x‖) ≤ 0 := by
    rw [← hμ]
    exact sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure f L M x
  have hsqrt_eq_zero :
      Real.sqrt ((2 / (L + M)) * ‖∇ f x‖) = 0 :=
    le_antisymm hsqrt_le_zero (Real.sqrt_nonneg _)
  have hscaled_nonneg : 0 ≤ (2 / (L + M)) * ‖∇ f x‖ := by
    positivity
  have hscaled_eq_zero : (2 / (L + M)) * ‖∇ f x‖ = 0 := by
    have hsquare_eq_zero :
        (Real.sqrt ((2 / (L + M)) * ‖∇ f x‖)) ^ 2 = 0 := by
      simpa [hsqrt_eq_zero]
    rw [Real.sq_sqrt hscaled_nonneg] at hsquare_eq_zero
    exact hsquare_eq_zero
  have hcoeff_ne : (2 / (L + M)) ≠ 0 := by
    positivity
  have hnorm_eq_zero : ‖∇ f x‖ = 0 :=
    (mul_eq_zero.mp hscaled_eq_zero).resolve_left hcoeff_ne
  exact norm_eq_zero.mp hnorm_eq_zero

/-- Under a pointwise `C²` hypothesis, vanishing of the local-optimality measure forces positivity
of the intrinsic Hessian operator `hessian f x`. -/
-- Proof sketch: with `2 * L + M > 0`, the second term in `μ[M](x)` shows that the least spectral
-- value of `hessian f x` is nonnegative. The hypothesis `ContDiffAt ℝ 2 f x` supplies the
-- canonical symmetry of the Hessian, so the real-spectrum nonnegativity criterion yields
-- `(hessian f x).IsPositive`.
theorem hessian_isPositive_of_cubicRegularizationLocalOptimalityMeasure_eq_zero
    {M : ℝ} (h2LM : 0 < 2 * L + M)
    {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hμ : μ[M](x) = 0) :
    (hessian f x).IsPositive := by
  -- The second component of `μ` forces the bottom of the Hessian spectrum to be nonnegative.
  have hspectral_le_zero :
      -(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x)) ≤ 0 := by
    rw [← hμ]
    exact scaledNegLeastHessianEigenvalue_le_cubicRegularizationLocalOptimalityMeasure
      f L M x
  have hsInf_nonneg : 0 ≤ sInf (spectrum ℝ (hessian f x)) := by
    have hcoeff_pos : 0 < 2 / (2 * L + M) := by
      positivity
    nlinarith
  have hselfAdjoint : IsSelfAdjoint (hessian f x) :=
    hessian_isSelfAdjoint_of_contDiffAt f x hf
  have hquad_nonneg : ∀ z : E, 0 ≤ inner ℝ (hessian f x z) z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      let u : E := ‖z‖⁻¹ • z
      have hu_unit : ‖u‖ = 1 := by
        simp [u, norm_smul, hnorm_pos.ne']
      have hu_lower :
          sInf (spectrum ℝ (hessian f x)) ≤ inner ℝ (hessian f x u) u :=
        sInf_spectrum_le_reApplyInnerSelf_of_unit hselfAdjoint hu_unit
      have hu_nonneg : 0 ≤ inner ℝ (hessian f x u) u :=
        le_trans hsInf_nonneg hu_lower
      have hu_eq :
          inner ℝ (hessian f x u) u =
            (‖z‖⁻¹ : ℝ) * ((‖z‖⁻¹ : ℝ) * inner ℝ (hessian f x z) z) := by
        simp [u, inner_smul_left, inner_smul_right, mul_assoc]
      rw [hu_eq] at hu_nonneg
      have hfactor_pos : 0 < (‖z‖⁻¹ : ℝ) * ‖z‖⁻¹ := by
        positivity
      nlinarith
  exact (ContinuousLinearMap.isPositive_iff' _).2 ⟨hselfAdjoint, hquad_nonneg⟩

end CubicRegularizationLocalOptimality

section

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [ProperSpace X]

variable {f : X → ℝ}
variable {stepMap : ℝ → X → X}
variable {L0 L : ℝ} {x0 : X}

/-- Helper for Theorem 4.1.2: the objective values along a cubic-regularization method are
monotone decreasing. -/
theorem cubicRegularization_objective_antitone
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (hunder :
      ∀ i : ℕ, f̄[f; (method.regularization i)]((method i)) ≤ f (method i)) :
    Antitone (fun k ↦ f (method k)) :=
  antitone_nat_of_succ_le fun k ↦ by
    -- The accepted-parameter owner gives the one-step comparison `f(x_{k+1}) ≤ f̄_k(x_k)`.
    have haccepted :
        f (stepMap (method.regularization k) (method k)) ≤
          f̄[f; (method.regularization k)]((method k)) := by
      exact
        (RegularizedNewton.mem_acceptedParameters_iff
          f
          stepMap
          (fun M x ↦ f̄[f; M](x))
          L0
          L
          (method k)
          (method.regularization k)).1
          (method.regularization_mem_acceptedParameters k) |>.2
    calc
      f (method (k + 1))
          = f (stepMap (method.regularization k) (method k)) := by
              rw [method.x_succ k, method.step_apply_eq_stepMap k (method k)]
      _ ≤ f̄[f; (method.regularization k)]((method k)) := haccepted
      _ ≤ f (method k) := hunder k

/-- Helper for Theorem 4.1.2: every tail iterate lies in the feasible sublevel set determined by
the reference iterate `x_{i₀}`. -/
theorem cubicRegularization_tail_mem_feasible_levelSet
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (hunder :
      ∀ i : ℕ, f̄[f; (method.regularization i)]((method i)) ≤ f (method i))
    {𝓕 : Set X} (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i0 : ℕ) :
    ∀ ⦃i : ℕ⦄, i0 ≤ i → method i ∈ 𝓕 ∩ 𝓛[f]((f (method i0))) := by
  -- Monotonicity of the objective puts each tail iterate into the same feasible level set.
  intro i hi
  have hmono := cubicRegularization_objective_antitone method hunder
  refine ⟨hmem i, ?_⟩
  exact hmono hi

/-- Theorem 4.1.2 (1): if a cubic-regularization trajectory has a bounded feasible level set
`𝓕 ∩ 𝓛[f]((f (x_{i₀})))`, then the objective values `f(x_i)` converge to some limit `f*`. This
uses only the proper-pseudometric owner layer behind the textbook `ℝⁿ` specialization. -/
-- Proof sketch: specialize `objective_antitone` with the on-trajectory comparison
-- `hunder` to make `f (method i)` monotone nonincreasing.
-- Since the tail of the trajectory lies in the bounded feasible level set
-- `𝓕 ∩ 𝓛[f]((f (method i₀)))`, properness makes its closure compact. Continuity of `f` then
-- gives a lower bound on the tail, and the monotone convergence theorem yields the limit.
theorem cubicRegularization_objective_values_tendsto
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (hunder :
      ∀ i : ℕ, f̄[f; (method.regularization i)]((method i)) ≤ f (method i))
    (hf_cont : Continuous f)
    {𝓕 : Set X} (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i0 : ℕ)
    (hbounded : Bornology.IsBounded (𝓕 ∩ 𝓛[f]((f (method i0)))))
    :
    ∃ fStar : ℝ, Tendsto (fun i ↦ f (method i)) atTop (𝓝 fStar) := by
  let tailSet : Set X := 𝓕 ∩ 𝓛[f]((f (method i0)))
  have hmono := cubicRegularization_objective_antitone method hunder
  have htail :
      ∀ ⦃i : ℕ⦄, i0 ≤ i → method i ∈ tailSet := by
    simpa [tailSet] using
      cubicRegularization_tail_mem_feasible_levelSet method hunder hmem i0
  have hcompact : IsCompact (closure tailSet) := by
    simpa [tailSet] using hbounded.isCompact_closure
  have hbddBelow : BddBelow (Set.range fun i : ℕ ↦ f (method i)) := by
    rcases (hcompact.image hf_cont).bddBelow with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rintro _ ⟨i, rfl⟩
    by_cases hi : i0 ≤ i
    · exact hc ⟨method i, subset_closure (htail hi), rfl⟩
    · exact le_trans
        (hc ⟨method i0, subset_closure (htail le_rfl), rfl⟩)
        (hmono (le_of_not_ge hi))
  refine ⟨sInf (Set.range fun i : ℕ ↦ f (method i)), ?_⟩
  simpa [sInf_range] using tendsto_atTop_ciInf hmono hbddBelow

/-- Theorem 4.1.2 (2): under the same bounded feasible-level-set hypothesis, the set `X*` of
limit points of the cubic-regularization trajectory is nonempty. -/
-- Proof sketch: by monotonicity, every tail iterate belongs to `𝓕 ∩ 𝓛[f]((f (method i₀)))`;
-- apply the compactness of the closure of that bounded set in the proper ambient space to obtain
-- a convergent subsequence, and interpret its limit as a cluster point of the trajectory.
theorem cubicRegularization_limitPoints_nonempty
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (hunder :
      ∀ i : ℕ, f̄[f; (method.regularization i)]((method i)) ≤ f (method i))
    {𝓕 : Set X} (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i0 : ℕ)
    (hbounded : Bornology.IsBounded (𝓕 ∩ 𝓛[f]((f (method i0)))))
    :
    Set.Nonempty {xStar : X | MapClusterPt xStar atTop method} := by
  let tailSet : Set X := 𝓕 ∩ 𝓛[f]((f (method i0)))
  have htail :
      ∀ ⦃i : ℕ⦄, i0 ≤ i → method i ∈ tailSet := by
    simpa [tailSet] using
      cubicRegularization_tail_mem_feasible_levelSet method hunder hmem i0
  have hcompact : IsCompact (closure tailSet) := by
    simpa [tailSet] using hbounded.isCompact_closure
  have htail_eventually : ∀ᶠ i : ℕ in atTop, method i ∈ closure tailSet := by
    have hge : ∀ᶠ i : ℕ in atTop, i0 ≤ i :=
      Filter.eventually_atTop.2 ⟨i0, fun i hi ↦ hi⟩
    filter_upwards [hge] with i hi
    show method i ∈ closure tailSet
    exact subset_closure (htail hi)
  rcases hcompact.exists_mapClusterPt_of_frequently htail_eventually.frequently with
    ⟨xStar, _, hxStar⟩
  exact ⟨xStar, hxStar⟩

/-- Helper for Theorem 4.1.2: every cluster point of a sequence that is eventually contained in a
closed set also belongs to that closed set. -/
theorem clusterPointSet_subset_of_eventually_mem_closed
    {u : ℕ → X} {K : Set X} (hK_closed : IsClosed K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K) :
    {x : X | MapClusterPt x atTop u} ⊆ K := by
  -- A cluster point sees every eventual tail property through the closed-set closure rule.
  intro x hx
  exact hK_closed.mem_of_mapClusterPt hx hmem

/-- Helper for Theorem 4.1.2: if a compact tail has all its cluster points inside an open set,
then the whole tail eventually enters that open set. -/
theorem eventually_mem_of_clusterPointSet_subset_open_of_eventually_mem_compact
    {u : ℕ → X} {K U : Set X} (hK : IsCompact K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K)
    (hU_open : IsOpen U)
    (hcluster : {x : X | MapClusterPt x atTop u} ⊆ U) :
    ∀ᶠ n : ℕ in atTop, u n ∈ U := by
  by_contra hnot
  -- If the tail failed to enter `U`, compactness would produce a cluster point in `K ∩ Uᶜ`.
  have hfreq_notU : ∃ᶠ n : ℕ in atTop, u n ∈ Uᶜ := by
    simpa [Set.mem_compl_iff] using (Filter.not_eventually.mp hnot)
  have hfreq_compact : ∃ᶠ n : ℕ in atTop, u n ∈ K ∩ Uᶜ := by
    simpa [Set.mem_inter_iff] using hmem.and_frequently hfreq_notU
  have hcompact_compl : IsCompact (K ∩ Uᶜ) :=
    hK.inter_right hU_open.isClosed_compl
  rcases hcompact_compl.exists_mapClusterPt_of_frequently hfreq_compact with
    ⟨x, hxKU, hxcluster⟩
  exact hxKU.2 (hcluster hxcluster)

/-- Helper for Theorem 4.1.2: if a tail stays in a disjoint two-set cover and visits both sides
frequently, then consecutive iterates cross from one side to the other infinitely often. -/
theorem frequently_flips_of_frequently_mem_disjoint_cover
    {u : ℕ → X} {s t : Set X}
    (hcover : ∀ᶠ n : ℕ in atTop, u n ∈ s ∪ t)
    (hst : Disjoint s t)
    (hs : ∃ᶠ n : ℕ in atTop, u n ∈ s)
    (ht : ∃ᶠ n : ℕ in atTop, u n ∈ t) :
    ∃ᶠ n : ℕ in atTop,
      (u n ∈ s ∧ u (n + 1) ∈ t) ∨ (u n ∈ t ∧ u (n + 1) ∈ s) := by
  classical
  let flip : ℕ → Prop :=
    fun n ↦ (u n ∈ s ∧ u (n + 1) ∈ t) ∨ (u n ∈ t ∧ u (n + 1) ∈ s)
  by_cases hflip : ∃ᶠ n : ℕ in atTop, flip n
  · exact hflip
  · have hno_flip :
        ∀ᶠ n : ℕ in atTop, ¬ flip n :=
      Filter.not_frequently.mp hflip
    -- Once a tail index lands in one side, the no-flip hypothesis forces all later indices to
    -- stay there, contradicting the frequent visits to the opposite side.
    rcases Filter.eventually_atTop.1 (hcover.and hno_flip) with ⟨N, hN⟩
    rcases Filter.frequently_atTop.1 hs N with ⟨n, hnN, hns⟩
    rcases Filter.frequently_atTop.1 ht (max N n) with ⟨m, hmNn, hmt⟩
    have hstay_s : ∀ {k : ℕ}, N ≤ k → u k ∈ s → u (k + 1) ∈ s := by
      intro k hkN hks
      have hk_data := hN k hkN
      have hk_cover_next : u (k + 1) ∈ s ∪ t :=
        (hN (k + 1) (le_trans hkN (Nat.le_succ k))).1
      have hk_no_flip :
          ¬ flip k :=
        hk_data.2
      have hk1_not_t : u (k + 1) ∉ t := by
        intro hk1t
        dsimp [flip] at hk_no_flip
        exact hk_no_flip (Or.inl ⟨hks, hk1t⟩)
      rcases hk_cover_next with hk1s | hk1t
      · exact hk1s
      · exact False.elim (hk1_not_t hk1t)
    have htail_s : ∀ d : ℕ, u (n + d) ∈ s := by
      intro d
      induction d with
      | zero =>
          simpa using hns
      | succ d ih =>
          have hkN : N ≤ n + d := le_trans hnN (Nat.le_add_right n d)
          simpa [Nat.add_assoc] using hstay_s hkN ih
    have hnm : n ≤ m := le_trans (le_max_right N n) hmNn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hms : u (n + d) ∈ s := htail_s d
    exact False.elim (hst.le_bot ⟨hms, hmt⟩)

/-- Helper for Theorem 4.1.2: points lying in opposite `δ`-thickenings of sets whose mutual
distance is everywhere larger than `3δ` must stay at distance larger than `δ`. -/
theorem lt_dist_of_mem_thickening_of_forall_dist_gt
    {A B : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, 3 * δ < dist a b)
    {x y : X}
    (hx : x ∈ Metric.thickening δ A)
    (hy : y ∈ Metric.thickening δ B) :
    δ < dist x y := by
  -- Pull back to witnesses in `A` and `B`, then compare the outer distance by the triangle
  -- inequality.
  rcases (Metric.mem_thickening_iff).1 hx with ⟨a, haA, hxa⟩
  rcases (Metric.mem_thickening_iff).1 hy with ⟨b, hbB, hyb⟩
  have hab_gt : 3 * δ < dist a b := hsep a haA b hbB
  have hab_le : dist a b ≤ dist a x + dist x y + dist y b := by
    calc
      dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
      _ ≤ dist a x + (dist x y + dist y b) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist a x + dist x y + dist y b := by ring
  have hax_lt : dist a x < δ := by
    simpa [dist_comm] using hxa
  have hyb_lt : dist y b < δ := hyb
  nlinarith

/-- Helper for Theorem 4.1.2: a sequence with compact tail and vanishing successive distances has
connected cluster-point set. -/
theorem clusterPointSet_isConnected_of_tendsto_dist_zero_on_compact_tail
    {u : ℕ → X} {K : Set X} (hK : IsCompact K)
    (hmem : ∀ᶠ n : ℕ in atTop, u n ∈ K)
    (hstep :
      Tendsto (fun n : ℕ ↦ dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    IsConnected {x : X | MapClusterPt x atTop u} := by
  let C : Set X := {x : X | MapClusterPt x atTop u}
  have hC_subset : C ⊆ K :=
    clusterPointSet_subset_of_eventually_mem_closed hK.isClosed hmem
  have hC_compact : IsCompact C :=
    hK.of_isClosed_subset isClosed_setOf_clusterPt hC_subset
  have hC_nonempty : C.Nonempty := by
    -- Compactness of the ambient tail provides at least one cluster point.
    rcases hK.exists_mapClusterPt_of_frequently hmem.frequently with ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  refine ⟨hC_nonempty, ?_⟩
  -- Route correction: connectedness is proved by a compact-tail no-oscillation contradiction,
  -- not by a direct abstract connectedness shortcut.
  by_contra hC_not_preconnected
  rw [IsPreconnected] at hC_not_preconnected
  push_neg at hC_not_preconnected
  rcases hC_not_preconnected with
    ⟨U, V, hU_open, hV_open, hC_cover, hCU_nonempty, hCV_nonempty, hC_inter_empty⟩
  let A : Set X := C ∩ U
  let B : Set X := C ∩ V
  have hA_nonempty : A.Nonempty := by
    simpa [A] using hCU_nonempty
  have hB_nonempty : B.Nonempty := by
    simpa [B] using hCV_nonempty
  have hA_eq : A = C ∩ Vᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxV
      have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hx.1, ⟨hx.2, hxV⟩⟩
      have hxEmpty : x ∈ (∅ : Set X) := by
        rwa [hC_inter_empty] at hxCUV
      exact hxEmpty.elim
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hC_cover hx.1 with hxU | hxV
      · exact hxU
      · exact False.elim (hx.2 hxV)
  have hB_eq : B = C ∩ Uᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxU
      have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hx.1, ⟨hxU, hx.2⟩⟩
      have hxEmpty : x ∈ (∅ : Set X) := by
        rwa [hC_inter_empty] at hxCUV
      exact hxEmpty.elim
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hC_cover hx.1 with hxU | hxV
      · exact False.elim (hx.2 hxU)
      · exact hxV
  have hA_compact : IsCompact A := by
    rw [hA_eq]
    exact hC_compact.inter_right hV_open.isClosed_compl
  have hB_compact : IsCompact B := by
    rw [hB_eq]
    exact hC_compact.inter_right hU_open.isClosed_compl
  have hAB_disjoint : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxB
    have hxCUV : x ∈ C ∩ (U ∩ V) := ⟨hxA.1, ⟨hxA.2, hxB.2⟩⟩
    have hxEmpty : x ∈ (∅ : Set X) := by
      rwa [hC_inter_empty] at hxCUV
    exact hxEmpty.elim
  obtain ⟨r, hr_pos, hsep⟩ :=
    Metric.exists_pos_forall_lt_edist hA_compact hB_compact.isClosed hAB_disjoint
  let δ : ℝ := (r : ℝ) / 3
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hsep_dist : ∀ a ∈ A, ∀ b ∈ B, 3 * δ < dist a b := by
    intro a haA b hbB
    have hr_lt : (r : ℝ) < dist a b := by
      simpa [edist_dist] using hsep a haA b hbB
    dsimp [δ] at *
    nlinarith
  let UA : Set X := Metric.thickening δ A
  let UB : Set X := Metric.thickening δ B
  have hUA_open : IsOpen UA := by
    simpa [UA] using (Metric.isOpen_thickening : IsOpen (Metric.thickening δ A))
  have hUB_open : IsOpen UB := by
    simpa [UB] using (Metric.isOpen_thickening : IsOpen (Metric.thickening δ B))
  have hA_subset_UA : A ⊆ UA := by
    simpa [UA] using Metric.self_subset_thickening hδ_pos A
  have hB_subset_UB : B ⊆ UB := by
    simpa [UB] using Metric.self_subset_thickening hδ_pos B
  have hUAUB_disjoint : Disjoint UA UB := by
    refine Set.disjoint_left.2 ?_
    intro x hxUA hxUB
    have hlt : δ < dist x x := by
      exact lt_dist_of_mem_thickening_of_forall_dist_gt hδ_pos hsep_dist hxUA hxUB
    have : δ < 0 := by
      simpa using hlt
    exact not_lt_of_ge hδ_pos.le this
  have hC_subset_union : C ⊆ UA ∪ UB := by
    intro x hxC
    rcases hC_cover hxC with hxU | hxV
    · exact Or.inl (hA_subset_UA ⟨hxC, hxU⟩)
    · exact Or.inr (hB_subset_UB ⟨hxC, hxV⟩)
  have htail_union : ∀ᶠ n : ℕ in atTop, u n ∈ UA ∪ UB :=
    eventually_mem_of_clusterPointSet_subset_open_of_eventually_mem_compact
      hK
      hmem
      (hUA_open.union hUB_open)
      hC_subset_union
  obtain ⟨a, haA⟩ := hA_nonempty
  obtain ⟨b, hbB⟩ := hB_nonempty
  have hfreq_UA : ∃ᶠ n : ℕ in atTop, u n ∈ UA := by
    -- Any cluster point in `A` forces infinitely many visits to every neighborhood of `A`.
    have ha_nhds : UA ∈ 𝓝 a :=
      hUA_open.mem_nhds (hA_subset_UA haA)
    exact (show MapClusterPt a atTop u from haA.1).frequently ha_nhds
  have hfreq_UB : ∃ᶠ n : ℕ in atTop, u n ∈ UB := by
    -- The same applies to a cluster point in `B`.
    have hb_nhds : UB ∈ 𝓝 b :=
      hUB_open.mem_nhds (hB_subset_UB hbB)
    exact (show MapClusterPt b atTop u from hbB.1).frequently hb_nhds
  have hflip :
      ∃ᶠ n : ℕ in atTop,
        (u n ∈ UA ∧ u (n + 1) ∈ UB) ∨ (u n ∈ UB ∧ u (n + 1) ∈ UA) :=
    frequently_flips_of_frequently_mem_disjoint_cover
      htail_union
      hUAUB_disjoint
      hfreq_UA
      hfreq_UB
  have hstep_small : ∀ᶠ n : ℕ in atTop, dist (u (n + 1)) (u n) < δ :=
    hstep (Iio_mem_nhds hδ_pos)
  have hstep_large :
      ∃ᶠ n : ℕ in atTop, δ < dist (u (n + 1)) (u n) := by
    -- Crossing between the two thickened pieces forces a uniform positive jump.
    refine hflip.mono ?_
    intro n hn
    rcases hn with hAB | hBA
    · simpa [dist_comm] using
        (lt_dist_of_mem_thickening_of_forall_dist_gt
          hδ_pos
          hsep_dist
          hAB.1
          hAB.2)
    · exact
        lt_dist_of_mem_thickening_of_forall_dist_gt
          hδ_pos
          hsep_dist
          hBA.2
          hBA.1
  have hstep_not_large : ∀ᶠ n : ℕ in atTop, ¬ δ < dist (u (n + 1)) (u n) := by
    filter_upwards [hstep_small] with n hsmall
    exact not_lt_of_ge hsmall.le
  exact (Filter.not_frequently.mpr hstep_not_large) hstep_large

/-- Theorem 4.1.2 (3): if the feasible level set `𝓕 ∩ 𝓛[f]((f (x_{i₀})))` is bounded and the
step sizes `dist (x_{i+1}, x_i)` tend to zero, then the set `X*` of limit points of the
trajectory is connected. In the original Euclidean model this is exactly the norm convergence
`‖x_{i+1} - x_i‖ → 0`. -/
-- Proof sketch: the bounded feasible level-set hypothesis confines the tail of the sequence to a
-- compact region, while the vanishing increments rule out jumps between disjoint compact
-- subsets. A standard compactness argument then gives connectedness of the cluster-point set.
theorem cubicRegularization_limitPoints_isConnected
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (hunder :
      ∀ i : ℕ, f̄[f; (method.regularization i)]((method i)) ≤ f (method i))
    {𝓕 : Set X} (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i0 : ℕ)
    (hbounded : Bornology.IsBounded (𝓕 ∩ 𝓛[f]((f (method i0)))))
    (hstep_tendsto_zero :
      Tendsto (fun i ↦ dist (method (i + 1)) (method i)) atTop (𝓝 0)) :
    IsConnected {xStar : X | MapClusterPt xStar atTop method} := by
  let tailSet : Set X := 𝓕 ∩ 𝓛[f]((f (method i0)))
  have hcompact : IsCompact (closure tailSet) := by
    simpa [tailSet] using hbounded.isCompact_closure
  have htail_eventually : ∀ᶠ i : ℕ in atTop, method i ∈ closure tailSet := by
    -- Monotonicity traps the whole tail in the bounded feasible level set, hence in its closure.
    have htail :
        ∀ ⦃i : ℕ⦄, i0 ≤ i → method i ∈ tailSet := by
      simpa [tailSet] using
        cubicRegularization_tail_mem_feasible_levelSet method hunder hmem i0
    have hge : ∀ᶠ i : ℕ in atTop, i0 ≤ i :=
      Filter.eventually_atTop.2 ⟨i0, fun i hi ↦ hi⟩
    filter_upwards [hge] with i hi
    exact subset_closure (htail hi)
  -- Route correction: instantiate the generic compact-tail no-oscillation lemma proved above.
  simpa [tailSet] using
    clusterPointSet_isConnected_of_tendsto_dist_zero_on_compact_tail
      (u := method)
      (K := closure tailSet)
      hcompact
      htail_eventually
      hstep_tendsto_zero

end

section

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

variable {f : X → ℝ}
variable {stepMap : ℝ → X → X}
variable {L0 L : ℝ} {x0 : X}

/-- Theorem 4.1.2 (4): every limit point `x* ∈ X*` attains the limiting objective value `f*`. -/
-- Proof sketch: use the canonical mathlib bridge `MapClusterPt.exists_seq_tendsto` to extract a
-- convergent subsequence from the cluster-point hypothesis, then combine continuity of `f` at
-- `x*` with convergence of the scalar sequence `f(x_i) → f*`.
theorem cubicRegularization_clusterPoint_value_eq_limit
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    {fStar : ℝ}
    (hlimit : Tendsto (fun i ↦ f (method i)) atTop (𝓝 fStar))
    {xStar : X} (hxStar : MapClusterPt xStar atTop method)
    (hf_cont : ContinuousAt f xStar) :
    f xStar = fStar := by
  -- Extract a convergent subsequence from the cluster-point hypothesis and compare its two limits.
  rcases hxStar.exists_seq_tendsto with ⟨ψ, hsubseq, hψ_tendsto⟩
  have hlimit_subseq :
      Tendsto (fun n ↦ f (method (ψ n))) atTop (𝓝 fStar) := by
    simpa [Function.comp] using hlimit.comp hψ_tendsto
  have hpoint_subseq :
      Tendsto (fun n ↦ f (method (ψ n))) atTop (𝓝 (f xStar)) :=
    hf_cont.tendsto.comp hsubseq
  exact tendsto_nhds_unique hpoint_subseq hlimit_subseq

end

section

variable {X : Type u}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [FiniteDimensional ℝ X]

variable {f : X → ℝ} {L : NNReal}
variable {stepMap : ℝ → X → X} {L0 : ℝ} {x0 : X}

variable {fStar : ℝ} {𝓕 : Set X}

local notation:max "μ[" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f (L : ℝ) M x

/-- Theorem 4.1.2 (5): every limit point `x* ∈ X*` that lies in the Hessian-Lipschitz owner
domain `𝓕` is stationary, i.e. `∇ f(x*) = 0`. This first-order conclusion lives on the intrinsic
finite-dimensional real inner-product-space layer. -/
-- Proof sketch: first invoke the chapter owner theorem
-- `cubicRegularization_localOptimalityMeasure_tendsto_zero` under the standing cubic-
-- regularization owner hypotheses to get `μ[L](xᵢ) → 0`; that owner theorem derives the
-- residual-cube descent estimate and the needed least-Hessian-eigenvalue lower bound from
-- `method`, so neither appears as separate public data here.
-- Then pass to a convergent subsequence
-- witnessing `MapClusterPt xStar atTop method`; the owner hypothesis
-- `[HessianLipschitzOn L 𝓕 f]` and the on-set assumption `x* ∈ 𝓕` supply the needed local `C²`
-- continuity bridge for `μ[L]` at `x*`, so `μ[L](x*) = 0`. Finally apply
-- `gradient_eq_zero_of_cubicRegularizationLocalOptimalityMeasure_eq_zero`.
theorem cubicRegularization_clusterPoint_gradient_eq_zero
    [HessianLipschitzOn L 𝓕 f]
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (hf_lower : ∀ z : X, fStar ≤ f z)
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    {xStar : X}
    (hxStar : MapClusterPt xStar atTop method)
    (hxStar_mem : xStar ∈ 𝓕) :
    ∇ f xStar = 0 := by
  let hreg : HessianLipschitzOn L 𝓕 f := inferInstance
  have hxStar_contDiff : ContDiffAt ℝ 2 f xStar :=
    hreg.contDiffAt hxStar_mem
  have hgrad_diff : DifferentiableAt ℝ (∇ f) xStar := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
      hxStar_contDiff.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) xStar :=
      hfderiv.differentiableAt one_ne_zero
    simpa [gradient] using
      (((InnerProductSpace.toDual ℝ X).symm).comp_differentiableAt_iff).2 hfdiff
  have hgrad_cont : ContinuousAt (∇ f) xStar :=
    hgrad_diff.continuousAt
  rcases hxStar.tendsto_subseq with ⟨ψ, hψ_mono, hψ_tendsto⟩
  have hμ_tendsto :
      Tendsto (fun i ↦ μ[(L : ℝ)](method i)) atTop (𝓝 0) :=
    cubicRegularization_localOptimalityMeasure_tendsto_zero
      (method := method)
      (fStar := fStar)
      hf_lower
      hmem
  have hμ_subseq :
      Tendsto (fun n ↦ μ[(L : ℝ)](method (ψ n))) atTop (𝓝 0) := by
    simpa [Function.comp] using hμ_tendsto.comp hψ_mono.tendsto_atTop
  let a : ℝ := 2 / ((L : ℝ) + (L : ℝ))
  have ha_pos : 0 < a := by
    dsimp [a]
    have hL_pos : 0 < (L : ℝ) :=
      lt_of_lt_of_le method.L0_pos method.L0_le_L
    positivity
  have hsqrt_bound :
      ∀ n : ℕ,
        Real.sqrt (a * ‖∇ f (method (ψ n))‖) ≤ μ[(L : ℝ)](method (ψ n)) := by
    intro n
    simpa [a] using
      sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
        f (L : ℝ) (L : ℝ) (method (ψ n))
  have hsqrt_tendsto :
      Tendsto (fun n ↦ Real.sqrt (a * ‖∇ f (method (ψ n))‖)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hμ_subseq
      ?_
      ?_
    · intro n
      exact Real.sqrt_nonneg _
    · intro n
      exact hsqrt_bound n
  have hscaled_tendsto :
      Tendsto (fun n ↦ a * ‖∇ f (method (ψ n))‖) atTop (𝓝 0) := by
    have hsq_tendsto :
        Tendsto
          (fun n ↦
            Real.sqrt (a * ‖∇ f (method (ψ n))‖) *
              Real.sqrt (a * ‖∇ f (method (ψ n))‖))
          atTop
          (𝓝 0) := by
      simpa using hsqrt_tendsto.mul hsqrt_tendsto
    convert hsq_tendsto using 1
    ext n
    rw [show
        Real.sqrt (a * ‖∇ f (method (ψ n))‖) *
            Real.sqrt (a * ‖∇ f (method (ψ n))‖) =
          (Real.sqrt (a * ‖∇ f (method (ψ n))‖)) ^ 2 by ring]
    rw [Real.sq_sqrt]
    positivity
  have hscaled_cont :
      ContinuousAt (fun x ↦ a * ‖∇ f x‖) xStar :=
    hgrad_cont.norm.const_mul a
  have hscaled_subseq :
      Tendsto (fun n ↦ a * ‖∇ f (method (ψ n))‖) atTop (𝓝 (a * ‖∇ f xStar‖)) :=
    hscaled_cont.tendsto.comp hψ_tendsto
  have hscaled_eq_zero : a * ‖∇ f xStar‖ = 0 :=
    tendsto_nhds_unique hscaled_subseq hscaled_tendsto
  have ha_ne : a ≠ 0 := by
    positivity
  have hnorm_eq_zero : ‖∇ f xStar‖ = 0 :=
    (mul_eq_zero.mp hscaled_eq_zero).resolve_left ha_ne
  exact norm_eq_zero.mp hnorm_eq_zero

/-- Intrinsic companion to Theorem 4.1.2 (6): every limit point `x* ∈ X*` in the
Hessian-Lipschitz owner domain `𝓕` has positive Hessian operator. This is the canonical
finite-dimensional owner theorem underlying the Euclidean matrix-view corollary. -/
-- Proof sketch: use `cubicRegularization_localOptimalityMeasure_tendsto_zero` exactly as in the
-- gradient theorem to get `μ[L](x*) = 0` at the cluster point, then apply the intrinsic owner
-- theorem `hessian_isPositive_of_cubicRegularizationLocalOptimalityMeasure_eq_zero`; the pointwise
-- `C²` hypothesis again comes from `[HessianLipschitzOn L 𝓕 f]` together with `x* ∈ 𝓕`.
theorem cubicRegularization_clusterPoint_hessian_isPositive
    [HessianLipschitzOn L 𝓕 f]
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (hf_lower : ∀ z : X, fStar ≤ f z)
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    {xStar : X}
    (hxStar : MapClusterPt xStar atTop method)
    (hxStar_mem : xStar ∈ 𝓕) :
    (hessian f xStar).IsPositive := by
  let hreg : HessianLipschitzOn L 𝓕 f := inferInstance
  have hxStar_contDiff : ContDiffAt ℝ 2 f xStar :=
    hreg.contDiffAt hxStar_mem
  rcases hxStar.tendsto_subseq with ⟨ψ, hψ_mono, hψ_tendsto⟩
  have hμ_tendsto :
      Tendsto (fun i ↦ μ[(L : ℝ)](method i)) atTop (𝓝 0) :=
    cubicRegularization_localOptimalityMeasure_tendsto_zero
      (method := method)
      (fStar := fStar)
      hf_lower
      hmem
  have hμ_subseq :
      Tendsto (fun n ↦ μ[(L : ℝ)](method (ψ n))) atTop (𝓝 0) := by
    simpa [Function.comp] using hμ_tendsto.comp hψ_mono.tendsto_atTop
  have hL_pos : 0 < (L : ℝ) :=
    lt_of_lt_of_le method.L0_pos method.L0_le_L
  by_contra hnot_pos
  have hselfAdjoint : IsSelfAdjoint (hessian f xStar) :=
    hessian_isSelfAdjoint_of_contDiffAt f xStar hxStar_contDiff
  have hnot_quad : ¬ ∀ z : X, 0 ≤ inner ℝ (hessian f xStar z) z := by
    intro hquad
    exact hnot_pos <|
      (ContinuousLinearMap.isPositive_iff' _).2 ⟨hselfAdjoint, hquad⟩
  obtain ⟨d, hd_neg⟩ := not_forall.mp hnot_quad
  have hd_neg : inner ℝ (hessian f xStar d) d < 0 := not_le.mp hd_neg
  have hd_ne : d ≠ 0 := by
    intro hd0
    simp [hd0] at hd_neg
  let u : X := ‖d‖⁻¹ • d
  have hu_unit : ‖u‖ = 1 := by
    have hnorm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
    simp [u, norm_smul, hnorm_pos.ne', abs_of_pos (inv_pos.mpr hnorm_pos)]
  have hu_neg : inner ℝ (hessian f xStar u) u < 0 := by
    have hnorm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
    have hu_eq :
        inner ℝ (hessian f xStar u) u =
          (‖d‖⁻¹ : ℝ) * ((‖d‖⁻¹ : ℝ) * inner ℝ (hessian f xStar d) d) := by
      simp [u, inner_smul_left, inner_smul_right, mul_assoc]
    rw [hu_eq]
    have hfactor_pos : 0 < (‖d‖⁻¹ : ℝ) * ‖d‖⁻¹ := by
      positivity
    nlinarith
  have hhess_cont : ContinuousAt (hessian f) xStar :=
    (HessianLipschitzOn.continuousOn_hessian hreg).continuousAt
      (hreg.isOpen.mem_nhds hxStar_mem)
  have hquad_cont :
      ContinuousAt (fun y ↦ inner ℝ (hessian f y u) u) xStar := by
    fun_prop
  have hquad_tendsto :
      Tendsto (fun n ↦ inner ℝ (hessian f (method (ψ n)) u) u) atTop
        (𝓝 (inner ℝ (hessian f xStar u) u)) :=
    hquad_cont.tendsto.comp hψ_tendsto
  set qStar : ℝ := inner ℝ (hessian f xStar u) u
  have hqStar_neg : qStar < 0 := by
    simpa [qStar] using hu_neg
  have hquad_eventually :
      ∀ᶠ n in atTop, inner ℝ (hessian f (method (ψ n)) u) u < qStar / 2 := by
    have hmem_nhds : Set.Iio (qStar / 2) ∈ 𝓝 qStar := by
      apply Iio_mem_nhds
      linarith
    exact hquad_tendsto hmem_nhds
  let δ : ℝ := (2 / (2 * (L : ℝ) + (L : ℝ))) * (-(qStar / 2))
  have hδ_pos : 0 < δ := by
    have hcoeff_pos : 0 < 2 / (2 * (L : ℝ) + (L : ℝ)) := by
      positivity
    have hhalf_pos : 0 < -(qStar / 2) := by
      linarith
    dsimp [δ]
    nlinarith
  have hμ_eventually_lt :
      ∀ᶠ n in atTop, μ[(L : ℝ)](method (ψ n)) < δ :=
    hμ_subseq (Iio_mem_nhds hδ_pos)
  have hδ_le_measure :
      ∀ᶠ n in atTop, δ ≤ μ[(L : ℝ)](method (ψ n)) := by
    filter_upwards [hquad_eventually] with n hn
    have hcontDiff_n : ContDiffAt ℝ 2 f (method (ψ n)) :=
      hreg.contDiffAt (hmem (ψ n))
    have hsInf_le_quad :
        sInf (spectrum ℝ (hessian f (method (ψ n)))) ≤
          inner ℝ (hessian f (method (ψ n)) u) u :=
      sInf_spectrum_le_reApplyInnerSelf_of_unit
        (hT := hessian_isSelfAdjoint_of_contDiffAt f _ hcontDiff_n)
        hu_unit
    have hquad_bound :
        -(qStar / 2) ≤ -sInf (spectrum ℝ (hessian f (method (ψ n)))) := by
      linarith
    have hterm_lower :
        δ ≤
          -(2 / (2 * (L : ℝ) + (L : ℝ))) *
            sInf (spectrum ℝ (hessian f (method (ψ n)))) := by
      dsimp [δ]
      have hrew :
          -(2 / (2 * (L : ℝ) + (L : ℝ))) *
              sInf (spectrum ℝ (hessian f (method (ψ n)))) =
            (2 / (2 * (L : ℝ) + (L : ℝ))) *
              (-sInf (spectrum ℝ (hessian f (method (ψ n))))) := by
        ring
      rw [hrew]
      gcongr
    exact le_trans hterm_lower
      (by
        simpa using
          scaledNegLeastHessianEigenvalue_le_cubicRegularizationLocalOptimalityMeasure
            f (L : ℝ) (L : ℝ) (method (ψ n)))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hδ_le_measure, hμ_eventually_lt] with n hle hlt
    exact (not_le_of_gt hlt) hle
  have hne : NeBot (atTop : Filter ℕ) := inferInstance
  exact hne.ne (eventually_false_iff_eq_bot.mp hfalse)

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {f : E → ℝ} {L : NNReal}
variable {stepMap : ℝ → E → E} {L0 : ℝ} {x0 : E}

variable {fStar : ℝ} {𝓕 : Set E}

/-- Theorem 4.1.2 (6): every limit point `x* ∈ X*` lying in the Hessian-Lipschitz owner domain
`𝓕` has positive semidefinite Hessian, i.e. `∇² f(x*) ⪰ 0`. This is the Euclidean matrix-view
bridge of the intrinsic second-order positivity conclusion. -/
-- Proof sketch: use `cubicRegularization_localOptimalityMeasure_tendsto_zero` as in part `(5)`
-- to get `μ[L](x*) = 0` at the cluster point. Then apply the intrinsic cluster-point owner theorem
-- `cubicRegularization_clusterPoint_hessian_isPositive` and transport that positivity to the
-- Euclidean matrix statement `(∇² f x*) ⪰ 0`; the required pointwise `C²` hypothesis is supplied
-- internally by `[HessianLipschitzOn L 𝓕 f]` together with `x* ∈ 𝓕`.
theorem cubicRegularization_clusterPoint_hessian_posSemidef
    [HessianLipschitzOn L 𝓕 f]
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (hf_lower : ∀ z : E, fStar ≤ f z)
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    {xStar : E}
    (hxStar : MapClusterPt xStar atTop method)
    (hxStar_mem : xStar ∈ 𝓕) :
    (∇² f xStar).PosSemidef := by
  -- Transport the intrinsic positive-operator statement to the Euclidean Hessian matrix.
  have hH :
      (hessian f xStar).IsPositive :=
    cubicRegularization_clusterPoint_hessian_isPositive
      (method := method)
      (fStar := fStar)
      hf_lower
      hmem
      hxStar
      hxStar_mem
  exact Matrix.isPositive_toEuclideanLin_iff.mp <| by
    simpa [hessianMatrix_toEuclideanLin] using hH.toLinearMap

end

end

/-! ### Definition_4_1_3 (from Chap04) -/
open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

section CubicRegularizationResidual

variable {E : Type u} [NormedAddCommGroup E]

/-- The cubic-regularization residual attached to a trial point `y` is the function
`x ↦ ‖x - y‖`; when `y = T_M(x)` this is the textbook residual `r_M(x)`. -/
def cubicRegularizationResidual
    (trialPoint : E) : E → ℝ :=
  fun x ↦ ‖x - trialPoint‖

namespace CubicRegularizationResidual

scoped notation:max "r[" trialPoint "]" => cubicRegularizationResidual trialPoint

end CubicRegularizationResidual

open scoped CubicRegularizationResidual

/-- Expanding `r[trialPoint] x` recovers the norm `‖x - trialPoint‖`. -/
@[simp] theorem cubicRegularizationResidual_eq_norm_sub
    (trialPoint x : E) :
    r[trialPoint] x = ‖x - trialPoint‖ :=
  rfl

end CubicRegularizationResidual

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open SetConstrainedMinimizationProblem

/- Definition 4.1.3 lies in the cubic-regularization / global minimization domain.

Sampled owner-style declarations:
* `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the upstream quadratic Taylor-model
  owner reused here;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_3` and
  `Chap01/Definition_1_3_7`, the canonical whole-space owner and its optimal value;
* `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, the attained-minimum bridge
  from a global minimizer to the canonical owner optimal value;
* `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet`, the owner-level upper
  bound by each trial value;
* `constrainedArgmin` and `mem_constrainedArgmin_iff`, the chapter's canonical argmin owner on a
  feasible set, specialized here to `Set.univ`.

Source/core/bridge triage:
* source-facing: the cubic model `m_x^M(y)`, its global minimizers
  `argmin[Set.univ] (cubicRegularizationQuadraticApproximation f M x)`, and the displayed minimum
  value realized by the whole-space minimization problem attached to that model;
* core/canonical: the owner function `cubicRegularizationQuadraticApproximation f M x`, the
  source-facing bridge `cubicRegularizationProblem f M x`, and
  `(cubicRegularizationProblem f M x).optimalValue`;
* bridge/view: the attained-minimum / `toReal` lemmas recovering the textbook real value from an
  explicit minimizer or, under positive regularization, from bounded-below coercivity.

Primitive data:
* the objective `f`;
* the regularization parameter `M`;
* the base point `x`.

Derived API:
* pointwise evaluation of the cubic model;
* the canonical whole-space minimization problem for that model;
* global minimality of a trial point via `argmin[Set.univ] ...` or `IsMinOn`;
* the owner-valued optimality equality and upper-bound theorems;
* the real-valued bridges recovering the textbook minimum at an explicit minimizer or, for
  `M > 0`, the real lower bound against every trial point.

This refinement keeps the source-facing cubic model and minimum semantics, uses the canonical
Chapter 1 owner `SetConstrainedMinimizationProblem.optimalValue` for the minimum-value layer,
keeps `argmin[Set.univ] ...` for the minimizer layer, and exposes only thin `toReal` bridges
instead of a parallel local real-valued `sInf` owner. -/

/-- The cubic-regularized second-order Taylor model of `f` centered at `x`, obtained by adding
the cubic penalty to `secondOrderTaylorModelAt f x`. -/
def cubicRegularizationQuadraticApproximation
    (f : E → ℝ) (M : ℝ) (x : E) : E → ℝ :=
  fun y ↦ secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ)

/-- Evaluating `cubicRegularizationQuadraticApproximation f M x` at `y` recovers the textbook
cubic model formula. -/
@[simp] theorem cubicRegularizationQuadraticApproximation_apply
    (f : E → ℝ) (M : ℝ) (x y : E) :
    cubicRegularizationQuadraticApproximation f M x y =
      secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) :=
  rfl

/-- The unconstrained minimization problem whose objective is the cubic-regularized second-order
Taylor model centered at `x`. -/
abbrev cubicRegularizationProblem
    (f : E → ℝ) (M : ℝ) (x : E) : SetConstrainedMinimizationProblem E :=
  unconstrained (cubicRegularizationQuadraticApproximation f M x)

/- Source-facing Lean notation for the textbook cubic model `m_x^M(y)` and its minimum-value
layers `Φ_M(x)` and `\bar f_M(x)`. -/
namespace CubicRegularizationModelNotation

scoped notation:max "m[" f:arg "; " M:arg "](" x:arg ")" =>
  cubicRegularizationQuadraticApproximation f M x

scoped notation:max "m[" f:arg "; " M:arg "](" x:arg "; " y:arg ")" =>
  cubicRegularizationQuadraticApproximation f M x y

scoped notation:max "Φ[" f:arg "; " M:arg "](" x:arg ")" =>
  SetConstrainedMinimizationProblem.optimalValue (cubicRegularizationProblem f M x)

scoped notation:max "f̄[" f:arg "; " M:arg "](" x:arg ")" =>
  EReal.toReal (SetConstrainedMinimizationProblem.optimalValue (cubicRegularizationProblem f M x))

end CubicRegularizationModelNotation

open scoped CubicRegularizationModelNotation

/-- A global minimizer of the cubic model realizes the canonical owner optimal value. -/
theorem cubicRegularizationProblem_optimalValue_eq_of_isMinOn
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    Φ[f; M](x) = (m[f; M](x; y) : EReal) := by
  simpa [cubicRegularizationProblem] using
    (cubicRegularizationProblem f M x).optimalValue_eq_of_isMinOn (by simp) hy

/-- Definition 4.1.3: any point of
`argmin[Set.univ] (m[f; M](x))` realizes the displayed minimum value `\bar f_M(x)` through the
canonical owner optimal value. -/
theorem cubicRegularizationProblem_optimalValue_eq_of_mem_argmin
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    Φ[f; M](x) = (m[f; M](x; y) : EReal) := by
  exact cubicRegularizationProblem_optimalValue_eq_of_isMinOn
    (mem_constrainedArgmin_iff.mp hy).2

/-- A global minimizer of the cubic model realizes the textbook real value `\bar f_M(x)`. -/
theorem cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    f̄[f; M](x) = m[f; M](x; y) := by
  rw [cubicRegularizationProblem_optimalValue_eq_of_isMinOn hy]
  exact EReal.toReal_coe _

/-- Any point of the global minimizer set of the cubic model realizes the textbook real value
`\bar f_M(x)`. -/
theorem cubicRegularizationProblem_optimalValue_toReal_eq_of_mem_argmin
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    f̄[f; M](x) = m[f; M](x; y) := by
  exact cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn
    (mem_constrainedArgmin_iff.mp hy).2

/-- The canonical owner optimal value is bounded above by the cubic model at every trial point,
with no extra coercivity hypothesis. -/
theorem cubicRegularizationProblem_optimalValue_le_quadraticApproximation
    {f : E → ℝ} {M : ℝ} {x z : E} :
    Φ[f; M](x) ≤ (m[f; M](x; z) : EReal) := by
  simpa [cubicRegularizationProblem] using
    (cubicRegularizationProblem f M x).optimalValue_le_of_mem_feasibleSet (by simp)

/-- Helper for Definition 4.1.3: the cubic model dominates a scalar cubic polynomial in the
radius `‖y - x‖`. -/
lemma cubic_regularization_model_ge_radius_polynomial
    {f : E → ℝ} {M : ℝ} {x y : E} :
    f x - ‖∇ f x‖ * ‖y - x‖ - (‖hessian f x‖ / 2) * ‖y - x‖ ^ (2 : ℕ) +
      (M / 6) * ‖y - x‖ ^ (3 : ℕ) ≤
        m[f; M](x; y) := by
  -- Bound the linear Taylor term from below by the gradient norm times the radius.
  have hgrad_abs :
      |inner ℝ (∇ f x) (y - x)| ≤ ‖∇ f x‖ * ‖y - x‖ := by
    simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f x) (y - x)
  have hgrad_lower :
      -(‖∇ f x‖ * ‖y - x‖) ≤ inner ℝ (∇ f x) (y - x) := by
    exact (abs_le.mp hgrad_abs).1
  -- Bound the quadratic Taylor term from below by the Hessian operator norm times the squared
  -- radius.
  have hhess_abs :
      |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ) := by
    have hinner :
        |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x (y - x)‖ * ‖y - x‖ := by
      simpa [real_inner_comm] using abs_real_inner_le_norm (hessian f x (y - x)) (y - x)
    calc
      |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x (y - x)‖ * ‖y - x‖ := hinner
      _ ≤ (‖hessian f x‖ * ‖y - x‖) * ‖y - x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ) := by
        ring
  have hhess_lower :
      -(‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ)) ≤
        inner ℝ (hessian f x (y - x)) (y - x) := by
    exact (abs_le.mp hhess_abs).1
  -- Rewriting the model exposes a scalar cubic polynomial whose coefficients are controlled by
  -- the two norm bounds above.
  rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
  nlinarith

/-- Helper for Definition 4.1.3: a nonnegative linear term is controlled by a positive cubic term
up to an explicit constant. -/
lemma linear_term_le_cubic_term_add_constant
    {a ε r : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hr : 0 ≤ r) :
    a * r ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
  by_cases hsmall : r ≤ a / ε + 1
  · -- On the bounded region, the constant term already dominates the linear growth.
    calc
      a * r ≤ a * (a / ε + 1) := by
        gcongr
      _ ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
        have hnonneg : 0 ≤ ε * r ^ (3 : ℕ) := by
          positivity
        linarith
  · -- Outside that region, the cubic term dominates the linear term directly.
    have hlarge : a / ε + 1 < r := lt_of_not_ge hsmall
    have hratio2 : a / ε ≤ r ^ (2 : ℕ) := by
      nlinarith
    have hmul : a ≤ ε * r ^ (2 : ℕ) := by
      have htmp : ε * (a / ε) ≤ ε * r ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hratio2 (le_of_lt hε)
      calc
        a = ε * (a / ε) := by
          rw [mul_div_assoc', mul_comm ε a, mul_div_cancel_right₀ a hε.ne']
        _ ≤ ε * r ^ (2 : ℕ) := htmp
    have hmulr : a * r ≤ (ε * r ^ (2 : ℕ)) * r := by
      gcongr
    calc
      a * r ≤ (ε * r ^ (2 : ℕ)) * r := hmulr
      _ = ε * r ^ (3 : ℕ) := by
        ring
      _ ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
        have hnonneg : 0 ≤ a * (a / ε + 1) := by
          positivity
        linarith

/-- Helper for Definition 4.1.3: a nonnegative quadratic term is controlled by a positive cubic
term up to an explicit constant. -/
lemma quadratic_term_le_cubic_term_add_constant
    {b ε r : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hr : 0 ≤ r) :
    b * r ^ (2 : ℕ) ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
  by_cases hsmall : r ≤ b / ε + 1
  · -- On the bounded region, the quadratic term is absorbed into the explicit constant.
    have hr2 : r ^ (2 : ℕ) ≤ (b / ε + 1) ^ (2 : ℕ) := by
      nlinarith
    calc
      b * r ^ (2 : ℕ) ≤ b * (b / ε + 1) ^ (2 : ℕ) := by
        gcongr
      _ ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
        have hnonneg : 0 ≤ ε * r ^ (3 : ℕ) := by
          positivity
        linarith
  · -- Outside that region, one power of `r` is enough for the cubic term to dominate.
    have hlarge : b / ε + 1 < r := lt_of_not_ge hsmall
    have hratio : b / ε ≤ r := by
      linarith
    have hmul : b ≤ ε * r := by
      have htmp : ε * (b / ε) ≤ ε * r := by
        exact mul_le_mul_of_nonneg_left hratio (le_of_lt hε)
      calc
        b = ε * (b / ε) := by
          rw [mul_div_assoc', mul_comm ε b, mul_div_cancel_right₀ b hε.ne']
        _ ≤ ε * r := htmp
    have hmulr2 : b * r ^ (2 : ℕ) ≤ (ε * r) * r ^ (2 : ℕ) := by
      gcongr
    calc
      b * r ^ (2 : ℕ) ≤ (ε * r) * r ^ (2 : ℕ) := hmulr2
      _ = ε * r ^ (3 : ℕ) := by
        ring
      _ ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
        have hnonneg : 0 ≤ b * (b / ε + 1) ^ (2 : ℕ) := by
          positivity
        linarith

/-- For positive regularization, the cubic model is bounded below on the ambient space. -/
theorem cubicRegularizationQuadraticApproximation_bddBelow
    {f : E → ℝ} {M : ℝ} {x : E} (hM : 0 < M) :
    BddBelow (Set.range (m[f; M](x))) := by
  let ε : ℝ := M / 12
  let C₁ : ℝ := ‖∇ f x‖ * (‖∇ f x‖ / ε + 1)
  let C₂ : ℝ := (‖hessian f x‖ / 2) * ((‖hessian f x‖ / 2) / ε + 1) ^ (2 : ℕ)
  refine ⟨f x - C₁ - C₂, ?_⟩
  rintro z ⟨y, rfl⟩
  -- First reduce the model to the scalar radius polynomial from the source proof skeleton.
  have hpoly :=
    cubic_regularization_model_ge_radius_polynomial (f := f) (M := M) (x := x) (y := y)
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hgrad_nonneg : 0 ≤ ‖∇ f x‖ := norm_nonneg _
  have hhess_nonneg : 0 ≤ ‖hessian f x‖ / 2 := by
    positivity
  have hr_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
  -- Then absorb the linear and quadratic radius terms into two copies of the positive cubic term.
  have hlin :
      ‖∇ f x‖ * ‖y - x‖ ≤ ε * ‖y - x‖ ^ (3 : ℕ) + C₁ := by
    simpa [C₁] using
      linear_term_le_cubic_term_add_constant
        (a := ‖∇ f x‖) (ε := ε) (r := ‖y - x‖) hgrad_nonneg hε hr_nonneg
  have hquad :
      (‖hessian f x‖ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ ε * ‖y - x‖ ^ (3 : ℕ) + C₂ := by
    simpa [C₂] using
      quadratic_term_le_cubic_term_add_constant
        (b := ‖hessian f x‖ / 2) (ε := ε) (r := ‖y - x‖) hhess_nonneg hε hr_nonneg
  have hεeq : (M / 6 : ℝ) = ε + ε := by
    dsimp [ε]
    ring
  rw [hεeq] at hpoly
  -- The remaining scalar inequality gives the global lower bound on the whole range.
  nlinarith [hpoly, hlin, hquad]

/-- Positive regularization makes the canonical owner optimal value finite from below. -/
theorem cubicRegularizationProblem_optimalValue_ne_bot
    {f : E → ℝ} {M : ℝ} {x : E} (hM : 0 < M) :
    Φ[f; M](x) ≠ ⊥ := by
  have hbdd : BddBelow (Set.range (m[f; M](x))) :=
    cubicRegularizationQuadraticApproximation_bddBelow hM
  rcases hbdd with ⟨m, hm⟩
  have hlower : (m : EReal) ≤ Φ[f; M](x) := by
    change (m : EReal) ≤
      sInf ((fun y : E ↦ (m[f; M](x; y) : EReal)) '' Set.univ)
    refine le_csInf ?_ ?_
    · exact ⟨_, ⟨x, by simp, rfl⟩⟩
    · rintro _ ⟨y, -, rfl⟩
      change ((m : ℝ) : EReal) ≤ (m[f; M](x; y) : EReal)
      exact EReal.coe_le_coe_iff.mpr (hm (Set.mem_range_self y))
  intro hbot
  rw [hbot] at hlower
  simp at hlower

/-- For positive regularization, the real part of the canonical owner optimal value is bounded
above by the cubic model at every trial point `y` without supplying a minimizer. -/
theorem cubicRegularizationProblem_optimalValue_toReal_le_quadraticApproximation
    {f : E → ℝ} {M : ℝ} {x y : E} (hM : 0 < M) :
    f̄[f; M](x) ≤ m[f; M](x; y) := by
  have hle : Φ[f; M](x) ≤ (m[f; M](x; y) : EReal) :=
    cubicRegularizationProblem_optimalValue_le_quadraticApproximation
  have hopt_ne_top : Φ[f; M](x) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (EReal.coe_ne_top (m[f; M](x; y))) hle
  simpa using
    EReal.toReal_le_toReal hle
      (cubicRegularizationProblem_optimalValue_ne_bot hM)
      (EReal.coe_ne_top (m[f; M](x; y)))
