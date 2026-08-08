import Mathlib
import ProbabilityTheory_Klenke_2020.Chap15.Theorem_15_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A complex-valued function on `ℝ^d` is partially continuous at `0` if its restriction to each
coordinate axis is continuous at the origin. -/
def PartiallyContinuousAtZero (f : E → ℂ) : Prop :=
  ∀ i : Fin d, ContinuousAt (fun t : ℝ ↦ f (EuclideanSpace.single i t)) 0

-- Proof sketch: unfold `PartiallyContinuousAtZero`; one of its coordinate-axis continuity clauses
-- is exactly the desired statement.
/-- Partial continuity at `0` yields continuity along each coordinate axis through the origin. -/
theorem PartiallyContinuousAtZero.continuousAt_coordinate
    {f : E → ℂ} (hf : PartiallyContinuousAtZero f) (i : Fin d) :
    ContinuousAt (fun t : ℝ ↦ f (EuclideanSpace.single i t)) 0 :=
  hf i

-- Proof sketch: use tightness of the weakly convergent sequence of probability measures, apply the
-- equicontinuity criterion for characteristic functions from Theorem 15.21, and then combine
-- pointwise convergence with equicontinuity via Lemma 15.22 to upgrade to uniform convergence on
-- each compact set.
/-- Theorem 15.23 (1): if probability measures on `ℝ^d` converge weakly to `P`, then their
characteristic functions converge to `charFun P` uniformly on every compact set. -/
theorem charFun_tendstoUniformlyOn_of_tendsto
    {P : ProbabilityMeasure E} {Ps : ℕ → ProbabilityMeasure E}
    (hP : Tendsto Ps atTop (𝓝 P)) :
    ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ charFun (Ps n) t) (charFun P) atTop K := by
  let F : ℕ → E → ℂ := fun n t ↦ charFun (Ps n : Measure E) t
  have h_pointwise :
      ∀ t : E, Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (charFun P t)) := by
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hP
  have h_measures :
      (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) =
        Set.range (fun n ↦ ((Ps n : ProbabilityMeasure E) : Measure E)) := by
    ext μ
    constructor
    · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Ps n, ⟨n, rfl⟩, rfl⟩
  have h_charFunP_cont : ContinuousAt (charFun (P : Measure E)) 0 := by
    fun_prop
  have h_pointwise_measure :
      ∀ t : E,
        Tendsto (fun n ↦ charFun (((Ps n : ProbabilityMeasure E) : Measure E)) t) atTop
          (𝓝 (charFun (P : Measure E) t)) := by
    simpa using h_pointwise
  have h_tight_range : IsTightMeasureSet (Set.range fun n ↦ ((Ps n : ProbabilityMeasure E) : Measure E)) := by
    exact isTightMeasureSet_of_tendsto_charFun h_charFunP_cont h_pointwise_measure
  have h_tight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) := by
    rw [h_measures]
    exact h_tight_range
  have h_charFuns :
      charFun '' (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) = Set.range F := by
    ext φ
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      rcases hμ with ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(Ps n : Measure E), ⟨Ps n, ⟨n, rfl⟩, rfl⟩, rfl⟩
  have h_eqcont_set : (Set.range F).UniformEquicontinuous := by
    rw [← h_charFuns]
    exact
      tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous (Set.range Ps) h_tight
  have h_eqcont_range : UniformEquicontinuous ((↑) : Set.range F → E → ℂ) := h_eqcont_set
  have h_eqcont : UniformEquicontinuous F :=
    (uniformEquicontinuous_iff_range.2 h_eqcont_range)
  intro K hK
  let 𝔖 : Set (Set E) := {K}
  have h𝔖 : ⋃₀ 𝔖 = K := by
    simp [𝔖]
  have h_uniform :
      Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) atTop
        (𝓝 <| UniformOnFun.ofFun 𝔖 (charFun (P : Measure E))) := by
    refine
      (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' ?_ ?_ atTop (charFun (P : Measure E))).2 ?_
    · intro L hL
      rcases Set.mem_singleton_iff.mp hL with rfl
      simpa using hK
    · intro L hL
      exact (h_eqcont.uniformEquicontinuousOn L).equicontinuousOn
    · rw [h𝔖]
      rw [tendsto_pi_nhds]
      intro x
      simpa [F] using h_pointwise x
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at h_uniform
  simpa [F, 𝔖] using h_uniform K (by simp [𝔖])

-- Proof sketch: first use the coordinate-axis continuity assumption to apply the one-dimensional
-- tightness argument to each marginal and deduce tightness of the sequence on `ℝ^d`. Then extract
-- a weak limit by Prokhorov compactness, identify its characteristic function with `f` by
-- pointwise convergence and Lévy's characterization theorem, and conclude that the whole sequence
-- converges weakly to that probability measure.
/-- Theorem 15.23 (2): if the characteristic functions of `Ps n` converge pointwise to a function
`f` that is partially continuous at `0`, then `f` is the characteristic function of a probability
measure `Q` and `Ps` converges weakly to `Q`. -/
theorem exists_probabilityMeasure_of_tendsto_charFun
    (Ps : ℕ → ProbabilityMeasure E) {f : E → ℂ}
    (hφ : ∀ t : E,
      Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t)))
    (hf : PartiallyContinuousAtZero f) :
    ∃ Q : ProbabilityMeasure E, (∀ t : E, charFun Q t = f t) ∧ Tendsto Ps atTop (𝓝 Q) := sorry

end
