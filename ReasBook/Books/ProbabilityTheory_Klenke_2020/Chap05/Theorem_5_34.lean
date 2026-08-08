import Mathlib
import ProbabilityTheory_Klenke_2020.Chap05.Definition_5_33

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u}

/-- Additivity identifies each interval count with the corresponding increment of the associated
counting process `t ↦ N_(0,t]`. -/
theorem poissonIntervalCount_increment_eq_sub
    {NI : NNReal → NNReal → Ω → ℕ}
    (hadditive : ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω)
    {s t : NNReal} (hst : s ≤ t) :
    NI s t = fun ω ↦ NI 0 t ω - NI 0 s ω := by
  ext ω
  rw [hadditive 0 s t bot_le hst]
  simp

variable [MeasurableSpace Ω]

/-- The source-facing interval-count side of Theorem 5.34: a family `NI s t` indexed by half-open
intervals `(s,t]` satisfies the textbook axioms `(P1)`--`(P5)`. The chapter's core owner
abstraction remains `IsPoissonProcess`; this predicate is the bridge layer used to relate the
textbook interval-count formulation to that owner object. The zero-time axiom `(P1)` is kept as a
derived theorem, since for `ℕ`-valued interval counts it already follows from additivity `(P2)` by
taking `r = s = t`, and the monotonicity of the associated counting process `t ↦ NI 0 t` is
derived from the same additivity. -/
def HasPoissonIntervalCountProperties
    (α : NNReal) (P : Measure Ω) (NI : NNReal → NNReal → Ω → ℕ) : Prop :=
  (∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω) ∧
    HasIndepIncrements (fun t ω ↦ NI 0 t ω) P ∧
    (∀ s t, s ≤ t → IdentDistrib (NI s t) (NI 0 (t - s)) P P) ∧
    (Tendsto
        (fun h : NNReal ↦ (P {ω | NI 0 h ω = 1}).toReal / (h : ℝ))
        (𝓝 0) (𝓝 (α : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦ (P {ω | 2 ≤ NI 0 h ω}).toReal / (h : ℝ))
        (𝓝 0) (𝓝 (0 : ℝ)))

/-- For `ℕ`-valued interval counts, the textbook zero-time axiom `(P1)` follows from additivity
`(P2)` by taking `r = s = t`. -/
theorem HasPoissonIntervalCountProperties.zero
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ s, NI s s = 0 := by
  intro s
  ext ω
  have hω := congrFun ((hNI.1 s s s le_rfl le_rfl)) ω
  have hω' : NI s s ω + 0 = NI s s ω + NI s s ω := by simpa using hω
  simpa using (Nat.add_left_cancel hω').symm

/-- `(P2)` on the interval-count side of Theorem 5.34. -/
theorem HasPoissonIntervalCountProperties.additive
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω := by
  rcases hNI with ⟨hadditive, -, -, -⟩
  exact hadditive

/-- Additivity of interval counts makes the associated counting process `t ↦ N_(0,t]`
nondecreasing. -/
theorem HasPoissonIntervalCountProperties.mono
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    Monotone (fun t ω ↦ NI 0 t ω) := by
  intro s t hst ω
  have hω := congrFun (hNI.additive 0 s t bot_le hst) ω
  exact Nat.le.intro hω.symm

/-- `(P3)` on the interval-count side of Theorem 5.34, expressed in the owner API
`HasIndepIncrements`. -/
theorem HasPoissonIntervalCountProperties.indepIncrements
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    HasIndepIncrements (fun t ω ↦ NI 0 t ω) P := by
  rcases hNI with ⟨-, hindep, -, -⟩
  exact hindep

/-- The interval-count axioms already force the ambient measure to be a probability measure,
because independent increments over a constant time sequence yield an independent family. -/
theorem HasPoissonIntervalCountProperties.isProbabilityMeasure
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    IsProbabilityMeasure P := by
  let hconst : Monotone (fun _ : ℕ ↦ (0 : NNReal)) := fun _ _ _ ↦ le_rfl
  exact (hNI.indepIncrements.nat hconst).isProbabilityMeasure

/-- `(P4)` on the interval-count side of Theorem 5.34. -/
theorem HasPoissonIntervalCountProperties.stationary
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ s t, s ≤ t → IdentDistrib (NI s t) (NI 0 (t - s)) P P := by
  rcases hNI with ⟨-, -, hstationary, -⟩
  exact hstationary

/-- `(P5)` on the interval-count side of Theorem 5.34. -/
theorem HasPoissonIntervalCountProperties.smallTime
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    Tendsto
        (fun h : NNReal ↦ (P {ω | NI 0 h ω = 1}).toReal / (h : ℝ))
        (𝓝 0) (𝓝 (α : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦ (P {ω | 2 ≤ NI 0 h ω}).toReal / (h : ℝ))
        (𝓝 0) (𝓝 (0 : ℝ)) := by
  rcases hNI with ⟨-, -, -, hsmall⟩
  exact hsmall

/-- The textbook interval-indexed independence axiom follows from the canonical independent
increments field via `HasIndepIncrements.nat`. -/
theorem poissonIntervalCount_independent
    {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hadditive : ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω)
    (hindep : HasIndepIncrements (fun t ω ↦ NI 0 t ω) P)
    (u : ℕ → NNReal) (hu : Monotone u) :
    iIndepFun (fun i ω ↦ NI (u i) (u (i + 1)) ω) P := by
  have h := hindep.nat hu
  have hEq :
      (fun i ω ↦ NI (u i) (u (i + 1)) ω) =
        fun i ω ↦ NI 0 (u (i + 1)) ω - NI 0 (u i) ω := by
    funext i ω
    exact congrFun (poissonIntervalCount_increment_eq_sub hadditive (hu (Nat.le_succ i))) ω
  simpa [hEq] using h

-- Proof sketch: the short-interval asymptotics in `(P5)` identify the source parameter `α` with
-- the mean unit-interval count, and the remaining axioms show that `t ↦ N_(0,t]` starts at `0`,
-- has independent increments, and satisfies the Poisson increment law with intensity `α`.
/-- For an interval-count family satisfying `(P1)`--`(P5)`, the intensity parameter appearing in
`(P5)` agrees with the mean unit-interval count `E[N_(0,1]]`. -/
theorem poissonIntervalCount_mean_unit_interval_count_eq
    {α : NNReal} {P : Measure Ω}
    (NI : NNReal → NNReal → Ω → ℕ)
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    P[fun ω ↦ (NI 0 1 ω : ℝ)] = (α : ℝ) := sorry

/-- Theorem 5.34, converse direction: a Poisson process induces an interval-count family on
half-open intervals `(s,t]` satisfying `(P1)`--`(P5)`, with genuine interval counts because the
owner object is now a nondecreasing counting process. -/
theorem IsPoissonProcess.hasPoissonIntervalCountProperties
    {P : Measure Ω} {N : NNReal → Ω → ℕ} {α : NNReal}
    (hN : IsPoissonProcess α P N) :
    HasPoissonIntervalCountProperties α P (fun s t ω ↦ N t ω - N s ω) := by
  sorry

/-- Process-form reformulation of Theorem 5.34: a process `N` is Poisson with intensity `α` if and
only if it starts at `0` and its interval-increment family `(s,t] ↦ N t - N s` satisfies the
textbook axioms `(P1)`--`(P5)`. The companion theorem
`poissonIntervalCount_mean_unit_interval_count_eq` identifies `α` with the mean unit-interval
count `E[N_(0,1]]` on the interval-count side. -/
theorem isPoissonProcess_iff_hasPoissonIntervalCountProperties
    {P : Measure Ω} {N : NNReal → Ω → ℕ} {α : NNReal} :
    IsPoissonProcess α P N ↔
      N 0 = 0 ∧
        HasPoissonIntervalCountProperties α P (fun s t ω ↦ N t ω - N s ω) := by
  sorry

/-- Forward implication in Theorem 5.34: an interval-count family on half-open intervals `(s,t]`
satisfying `(P1)`--`(P5)` induces a Poisson process `t ↦ N_(0,t]` with intensity `α`; the
counting-process monotonicity is derived from additivity rather than stored separately. -/
theorem isPoissonProcess_of_hasPoissonIntervalCountProperties
    {P : Measure Ω} (NI : NNReal → NNReal → Ω → ℕ) {α : NNReal}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    IsPoissonProcess α P (fun t ω ↦ NI 0 t ω) := by
  sorry
