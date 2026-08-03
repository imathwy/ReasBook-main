import Mathlib
import BauschkeLean.Chap01.Corollary_1_45
import BauschkeLean.Chap01.Theorem_1_46
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap18.Proposition_18_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityLocus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: `sourceDifferentiabilitySet f` is the textbook locus of points `x ∈ cont f`
  where the finite-valued representative of `f` is Fréchet differentiable.
- `core/canonical`: Proposition 18.1 owns the pointwise predicate
  `HasSymmetricSecondDifferenceBound f x ε` characterizing that differentiability under convexity.
- `bridge/view`: the theorem
  `mem_sourceDifferentiabilitySet_iff_forall_pos_hasSymmetricSecondDifferenceBound`
  identifies the source-facing locus with that owner predicate, and the thin coercion bridge
  `sourceDifferentiabilitySetInClosure f` views that locus inside the complete metric subtype
  `closure (effectiveDomain f)`.
-/

/-- The source Fréchet-differentiability locus of `f`: continuity points `x ∈ cont f` where the
finite-valued representative of `f` is Fréchet differentiable. -/
def sourceDifferentiabilitySet (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  cont f ∩ {x | DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x}

omit [CompleteSpace H] in
/-- Membership in the source differentiability locus means source continuity together with
Fréchet differentiability of the finite-valued representative. -/
@[simp] theorem mem_sourceDifferentiabilitySet_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ sourceDifferentiabilitySet f ↔
      x ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x :=
  Iff.rfl

/-- Under convexity, membership in the source differentiability locus is exactly source continuity
together with the canonical Chapter 18 symmetric second-difference bounds at every positive
tolerance. -/
theorem mem_sourceDifferentiabilitySet_iff_forall_pos_hasSymmetricSecondDifferenceBound
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x : H} :
    x ∈ sourceDifferentiabilitySet f ↔
      x ∈ cont f ∧ ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε := by
  rw [mem_sourceDifferentiabilitySet_iff]
  constructor
  · rintro ⟨hxcont, hdiff⟩
    refine ⟨hxcont, ?_⟩
    intro ε
    let εhalf : Set.Ioi (0 : ℝ) := ⟨(ε : ℝ) / 2, by
      change (0 : ℝ) < (ε : ℝ) / 2
      exact half_pos (show (0 : ℝ) < (ε : ℝ) from ε.2)⟩
    rcases
        (differentiableAt_toReal_iff_forall_pos_exists_pos_symmetricSecondDifference_lt
          f hconv hxcont).1 hdiff εhalf with
      ⟨η, hη⟩
    -- Proposition 18.1 gives the pointwise sphere estimate; package it back into the owner-level
    -- `HasSymmetricSecondDifferenceBound` predicate using the auxiliary half-tolerance.
    refine (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ε).2 ?_
    refine ⟨η, εhalf, ?_, ?_⟩
    · dsimp [εhalf]
      exact half_lt_self ε.2
    · intro y hy
      have hy_norm : ‖y‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hy
      simpa [εhalf] using hη y hy_norm
  · rintro ⟨hxcont, hbound⟩
    refine ⟨hxcont, ?_⟩
    refine
      (differentiableAt_toReal_iff_forall_pos_exists_pos_symmetricSecondDifference_lt
        f hconv hxcont).2 ?_
    intro ε
    rcases
        (hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere f x ε).1 (hbound ε) with
      ⟨η, ε', hε'lt, hη⟩
    refine ⟨η, ?_⟩
    intro y hy_norm
    have hy_sphere : y ∈ Metric.sphere (0 : H) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_norm
    exact lt_of_lt_of_le (hη y hy_sphere) (by
      exact_mod_cast mul_le_mul_of_nonneg_left hε'lt.le η.2.le)

/-- Under convexity, the source differentiability locus is exactly the intersection of the
canonical Chapter 18 sublevel sets `S_ε`. -/
theorem sourceDifferentiabilitySet_eq_iInter_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    sourceDifferentiabilitySet f =
      ⋂ ε : Set.Ioi (0 : ℝ), symmetricSecondDifferenceSublevelSet f ε := by
  -- Route correction: use explicit membership in one fixed positive sublevel set to recover the
  -- shared continuity component, rather than asking `simp` to reconstruct it across the whole
  -- intersection.
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro ε
    rcases
        (mem_sourceDifferentiabilitySet_iff_forall_pos_hasSymmetricSecondDifferenceBound
          f hconv).1 hx with
      ⟨hxcont, hbound⟩
    exact (mem_symmetricSecondDifferenceSublevelSet_iff f ε x).2 ⟨hxcont, hbound ε⟩
  · intro hx
    rw [Set.mem_iInter] at hx
    let ε1 : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
    have hx1 : x ∈ symmetricSecondDifferenceSublevelSet f ε1 := hx ε1
    have hxcont : x ∈ cont f :=
      (mem_symmetricSecondDifferenceSublevelSet_iff f ε1 x).1 hx1 |>.1
    have hbound : ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε := by
      intro ε
      exact (mem_symmetricSecondDifferenceSublevelSet_iff f ε x).1 (hx ε) |>.2
    exact
      (mem_sourceDifferentiabilitySet_iff_forall_pos_hasSymmetricSecondDifferenceBound
        f hconv).2 ⟨hxcont, hbound⟩

omit [CompleteSpace H] in
/-- Enlarging the tolerance preserves the Chapter 18 symmetric second-difference bound. -/
theorem HasSymmetricSecondDifferenceBound.mono
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {ε₁ ε₂ : Set.Ioi (0 : ℝ)}
    (h : HasSymmetricSecondDifferenceBound f x ε₁)
    (hε : (ε₁ : ℝ) ≤ (ε₂ : ℝ)) :
    HasSymmetricSecondDifferenceBound f x ε₂ := by
  rcases h with ⟨η, hη⟩
  refine ⟨η, lt_of_lt_of_le hη ?_⟩
  exact_mod_cast hε

omit [CompleteSpace H] in
/-- The Chapter 18 sublevel sets `S_ε` are monotone in the tolerance parameter `ε`. -/
theorem symmetricSecondDifferenceSublevelSet_mono
    (f : H → Set.Ioi (⊥ : EReal)) {ε₁ ε₂ : Set.Ioi (0 : ℝ)}
    (hε : (ε₁ : ℝ) ≤ (ε₂ : ℝ)) :
    symmetricSecondDifferenceSublevelSet f ε₁ ⊆ symmetricSecondDifferenceSublevelSet f ε₂ := by
  intro x hx
  rcases hx with ⟨hxcont, hbound⟩
  exact ⟨hxcont, hbound.mono f hε⟩

/-- Under convexity, the source differentiability locus is already the countable intersection of
the canonical Chapter 18 sublevel sets at tolerances `(n + 1)⁻¹`. This is the bridge from the
source `⋂ ε > 0` presentation to the Chapter 1 Baire-category owner
`dense_isGδ_iInter_of_dense_open`. -/
theorem sourceDifferentiabilitySet_eq_iInter_nat_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    sourceDifferentiabilitySet f =
      ⋂ n : ℕ,
        symmetricSecondDifferenceSublevelSet f
          ⟨1 / (n + 1 : ℝ), by
            change (0 : ℝ) < 1 / (n + 1 : ℝ)
            positivity⟩ := by
  -- The sampled tolerances `(n + 1)⁻¹` form a cofinal positive sequence, so the full
  -- `⋂ ε > 0` presentation reduces to a countable intersection.
  ext x
  rw [sourceDifferentiabilitySet_eq_iInter_symmetricSecondDifferenceSublevelSet f hconv]
  constructor
  · intro hx
    rw [Set.mem_iInter] at hx ⊢
    intro n
    let εn : Set.Ioi (0 : ℝ) := ⟨1 / (n + 1 : ℝ), by
      change (0 : ℝ) < 1 / (n + 1 : ℝ)
      positivity⟩
    simpa [εn] using hx εn
  · intro hx
    rw [Set.mem_iInter] at hx ⊢
    intro ε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (ε : ℝ) by exact ε.2)
    let εn : Set.Ioi (0 : ℝ) := ⟨1 / (n + 1 : ℝ), by
      change (0 : ℝ) < 1 / (n + 1 : ℝ)
      positivity⟩
    have hxn : x ∈ symmetricSecondDifferenceSublevelSet f εn := by
      simpa [εn] using hx n
    exact symmetricSecondDifferenceSublevelSet_mono (f := f) hn.le hxn

/-- The source differentiability locus viewed inside `closure (effectiveDomain f)` via the
canonical coercion bridge. -/
abbrev sourceDifferentiabilitySetInClosure (f : H → Set.Ioi (⊥ : EReal)) :
    Set (closure (effectiveDomain f)) :=
  Subtype.val ⁻¹' sourceDifferentiabilitySet f

omit [CompleteSpace H] in
/-- Membership in the closure-subtype view of the source differentiability locus is exactly the
ambient source differentiability condition. -/
@[simp] theorem mem_sourceDifferentiabilitySetInClosure_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : closure (effectiveDomain f)) :
    x ∈ sourceDifferentiabilitySetInClosure f ↔
      (x : H) ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x :=
  Iff.rfl

/-- Under convexity, the closure-subtype view of the source differentiability locus is the
countable intersection of the corresponding closure-subtype views of the canonical Chapter 18
sublevel sets at tolerances `(n + 1)⁻¹`. -/
theorem sourceDifferentiabilitySetInClosure_eq_iInter_nat_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    sourceDifferentiabilitySetInClosure f =
      ⋂ n : ℕ,
        Subtype.val ⁻¹'
          symmetricSecondDifferenceSublevelSet f
            ⟨1 / (n + 1 : ℝ), by
              change (0 : ℝ) < 1 / (n + 1 : ℝ)
              positivity⟩ := by
  -- Pull the ambient countable-intersection description back along the canonical subtype
  -- coercion `Subtype.val`.
  ext x
  simp [sourceDifferentiabilitySetInClosure,
    sourceDifferentiabilitySet_eq_iInter_nat_symmetricSecondDifferenceSublevelSet, hconv]

end DifferentiabilityLocus

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 18 3: the sampled tolerance `(n + 1)⁻¹` is positive. -/
private lemma one_div_nat_add_one_pos (n : ℕ) : 0 < 1 / (n + 1 : ℝ) := by
  positivity

/-- Helper for Theorem 18 3: a convex source function with one continuity point has
`cont f = interior (effectiveDomain f)`. -/
private theorem cont_eq_interior_effectiveDomain_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) :
    cont f = interior (effectiveDomain f) := by
  let _ := (inferInstance : CompleteSpace H)
  rcases hcont with ⟨x₀, hx₀⟩
  have hx₀_dom : x₀ ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hx₀
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv hx₀_dom
  have hfinite :
      ∃ ρ : ℝ, 0 < ρ ∧
        sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤ := by
    rcases hx₀ with ⟨ρ, hρ, hball, hcont₀⟩
    have hsource_cont :
        ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x₀ ρ ⊆ effectiveDomain f ∧
          ContinuousAt (fun y ↦ (f y : EReal).toReal) x₀ := by
      exact ⟨ρ, hρ, hball, hcont₀⟩
    rcases (List.TFAE.out htfae 1 3).mp hsource_cont with ⟨ρ, hρ, hsup⟩
    exact ⟨ρ, hρ, hsup⟩
  ext x
  constructor
  · -- Every source continuity point has a whole ball inside the effective domain.
    exact mem_interior_effectiveDomain_of_mem_cont
  · intro hx
    rcases hfinite with ⟨ρ₀, hρ₀, hsup₀⟩
    rcases
        (convex_locallyLipschitzNear_on_interior_of_finiteSupBall f hconv
          ⟨ρ₀, hρ₀, hsup₀⟩
          x hx) with
      ⟨_, ρ, hρ, hball, hlip⟩
    refine ⟨ρ, hρ, hball, ?_⟩
    have hx_ball : x ∈ Metric.ball x ρ := by
      simp [Metric.mem_ball, hρ]
    exact hlip.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hx_ball)

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: every continuity point admits a smaller ball on which the
finite-valued representative is Lipschitz. -/
private theorem exists_lipschitz_ball_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ cont f) :
    ∃ β : NNReal, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball x ρ ⊆ effectiveDomain f ∧
      LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ) := by
  have hxdom : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hx
  rcases hx with ⟨ρ, hρ, hball, hcontx⟩
  have hcontBall :
      ∃ ρ > 0,
        Metric.ball x ρ ⊆ effectiveDomain f ∧
          ContinuousAt (fun z ↦ (f z : EReal).toReal) x := by
    exact ⟨ρ, hρ, hball, hcontx⟩
  -- Read clause (1) of the local convex-regularity `TFAE` from the continuity clause (2).
  exact
    (List.TFAE.out
      (convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
        f hconv hxdom)
      1 0).mp hcontBall

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: every point of a Lipschitz ball belongs to the source continuity set
`cont f`. -/
private lemma mem_cont_of_mem_ball_of_lipschitzOnWith_ball
    (f : H → Set.Ioi (⊥ : EReal)) {x z : H} {ρ : ℝ} {β : NNReal}
    (hball : Metric.ball x ρ ⊆ effectiveDomain f)
    (hlip : LipschitzOnWith β (fun y ↦ (f y : EReal).toReal) (Metric.ball x ρ))
    (hz : z ∈ Metric.ball x ρ) :
    z ∈ cont f := by
  refine ⟨ρ - dist z x, ?_, ?_, ?_⟩
  · -- The point `z` sits strictly inside the ball, so there is still room to the boundary.
    rw [Metric.mem_ball] at hz
    linarith
  · -- A smaller ball around `z` stays inside the original effective-domain ball.
    intro y hy
    apply hball
    rw [Metric.mem_ball] at hy hz ⊢
    have htriangle : dist y x ≤ dist y z + dist z x := dist_triangle y z x
    linarith
  · -- The Lipschitz bound on the ambient ball upgrades to continuity at every interior point.
    exact hlip.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: a uniform spherewise symmetric second-difference bound strictly below
`ε` packages directly into the owner predicate `HasSymmetricSecondDifferenceBound`. -/
private lemma hasSymmetricSecondDifferenceBound_of_forall_mem_sphere_quotient_lt_real
    (f : H → Set.Ioi (⊥ : EReal)) {z : H}
    (ε : Set.Ioi (0 : ℝ)) (η : Set.Ioi (0 : ℝ)) {M : ℝ} (hMε : M < (ε : ℝ))
    (hpointwise :
      ∀ y ∈ Metric.sphere (0 : H) 1,
        (((f (z + (η : ℝ) • y) : EReal) + (f (z - (η : ℝ) • y) : EReal) -
              2 * (f z : EReal)) / (η : ℝ)) <
          ((M : ℝ) : EReal)) :
    HasSymmetricSecondDifferenceBound f z ε := by
  let ε' : Set.Ioi (0 : ℝ) :=
    ⟨((max M 0) + (ε : ℝ)) / 2, by
      have hmax_nonneg : 0 ≤ max M 0 := le_max_right M 0
      exact div_pos (add_pos_of_nonneg_of_pos hmax_nonneg ε.2) zero_lt_two⟩
  have hε'lt : (ε' : ℝ) < (ε : ℝ) := by
    -- The midpoint between `max M 0` and `ε` stays strictly below `ε`.
    have hmax_lt : max M 0 < (ε : ℝ) := by
      exact max_lt_iff.mpr ⟨hMε, ε.2⟩
    dsimp [ε']
    linarith
  have hMleε' : (M : ℝ) ≤ (ε' : ℝ) := by
    -- The midpoint also lies above `M`, providing the strict margin needed for the supremum.
    have hMlemax : (M : ℝ) ≤ max M 0 := le_max_left _ _
    have hmax_lt : max M 0 < (ε : ℝ) := by
      exact max_lt_iff.mpr ⟨hMε, ε.2⟩
    have hmax_lt' : max M 0 < (ε' : ℝ) := by
      dsimp [ε']
      nlinarith
    exact hMlemax.trans hmax_lt'.le
  refine (hasSymmetricSecondDifferenceBound_iff f z ε).mpr ?_
  refine ⟨η, ?_⟩
  have hsSup_le :
      sSup (symmetricSecondDifferenceQuotientSet f z η) ≤ (((ε' : ℝ) : EReal)) := by
    -- Bound each sampled quotient by the midpoint margin and then pass to the supremum.
    refine sSup_le_iff.mpr ?_
    intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    exact (hpointwise y hy).le.trans (by exact_mod_cast hMleε')
  exact lt_of_le_of_lt hsSup_le (by exact_mod_cast hε'lt)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: choose a positive closed subball around `x` that sits inside both
ambient balls used in the local Ekeland construction. -/
private theorem exists_closed_subball_inside_two_balls
    (x : H) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧ R < ρ ∧
      Metric.closedBall x R ⊆ Metric.ball x r ∧
      Metric.closedBall x R ⊆ Metric.ball x ρ := by
  let R : ℝ := min (r / 2) (ρ / 2)
  have hR_pos : 0 < R := by
    -- Halving both radii leaves a positive minimum.
    dsimp [R]
    refine lt_min ?_ ?_
    · positivity
    · positivity
  have hRr : R < r := by
    -- The chosen radius is at most `r / 2`, hence strictly smaller than `r`.
    have hle : R ≤ r / 2 := by
      dsimp [R]
      exact min_le_left _ _
    linarith
  have hRρ : R < ρ := by
    -- The same estimate holds relative to the Lipschitz radius `ρ`.
    have hle : R ≤ ρ / 2 := by
      dsimp [R]
      exact min_le_right _ _
    linarith
  refine ⟨R, hR_pos, hRr, hRρ, ?_, ?_⟩
  · -- Any point of the smaller closed ball lies in the larger open `r`-ball.
    intro y hy
    exact Metric.closedBall_subset_ball hRr hy
  · -- The same closed ball also stays inside the local Lipschitz ball.
    intro y hy
    exact Metric.closedBall_subset_ball hRρ hy

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: after shrinking inside the local Lipschitz ball, the finite-valued
representative oscillates by at most any prescribed absolute tolerance on the resulting closed
subball. -/
private theorem exists_closed_subball_with_small_toReal_oscillation
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {r ρ : ℝ} {β : NNReal}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hlip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ))
    {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧ R < ρ ∧
      Metric.closedBall x R ⊆ Metric.ball x r ∧
      Metric.closedBall x R ⊆ Metric.ball x ρ ∧
      ∀ u ∈ Metric.closedBall x R,
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ c := by
  let R : ℝ := min (min (r / 2) (ρ / 2)) (c / ((β : ℝ) + 1))
  have hR_pos : 0 < R := by
    -- Shrink simultaneously inside both ambient balls and below the oscillation scale `c`.
    dsimp [R]
    refine lt_min ?_ ?_
    · exact lt_min (half_pos hr) (half_pos hρ)
    · exact div_pos hc (by positivity)
  have hRr : R < r := by
    have hR_le : R ≤ r / 2 := by
      dsimp [R]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hRρ : R < ρ := by
    have hR_le : R ≤ ρ / 2 := by
      dsimp [R]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hR_c : R ≤ c / ((β : ℝ) + 1) := by
    dsimp [R]
    exact min_le_right _ _
  refine ⟨R, hR_pos, hRr, hRρ, ?_, ?_, ?_⟩
  · -- The radius choice keeps the closed ball inside the prescribed `r`-ball.
    intro u hu
    exact Metric.closedBall_subset_ball hRr hu
  · -- The same shrinking keeps the closed ball inside the local Lipschitz ball.
    intro u hu
    exact Metric.closedBall_subset_ball hRρ hu
  · intro u hu
    have hxρ : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ
    have huρ : u ∈ Metric.ball x ρ := Metric.closedBall_subset_ball hRρ hu
    have hβ_nonneg : 0 ≤ (β : ℝ) := by
      exact_mod_cast β.2
    have hdist :
        dist ((f u : EReal).toReal) ((f x : EReal).toReal) ≤ (β : ℝ) * dist u x := by
      simpa using hlip.dist_le_mul u huρ x hxρ
    have hβR_le : (β : ℝ) * R ≤ c := by
      have hβ_le : (β : ℝ) ≤ (β : ℝ) + 1 := by
        linarith
      have hβR_le' : (β : ℝ) * R ≤ ((β : ℝ) + 1) * R := by
        exact mul_le_mul_of_nonneg_right hβ_le hR_pos.le
      have hβp1R_le : ((β : ℝ) + 1) * R ≤ c := by
        have hden_pos : 0 < (β : ℝ) + 1 := by positivity
        simpa [mul_comm] using (le_div_iff₀ hden_pos).mp hR_c
      exact hβR_le'.trans hβp1R_le
    have habs :
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ (β : ℝ) * R := by
      have hdist' : dist u x ≤ R := hu
      calc
        |(f u : EReal).toReal - (f x : EReal).toReal|
            = dist ((f u : EReal).toReal) ((f x : EReal).toReal) := by
                rw [Real.dist_eq]
        _ ≤ (β : ℝ) * dist u x := hdist
        _ ≤ (β : ℝ) * R := mul_le_mul_of_nonneg_left hdist' hβ_nonneg
    exact habs.trans hβR_le

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: the finite-valued representative of `f` is bounded below on every
closed subball contained in a local Lipschitz ball. -/
private theorem bddBelow_toReal_range_on_closed_subball_of_lipschitzOnWith_ball
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {ρ R : ℝ} {β : NNReal}
    (hρ : 0 < ρ) (hclosed_ρ : Metric.closedBall x R ⊆ Metric.ball x ρ)
    (hlip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ)) :
    BddBelow
      (Set.range fun z : Metric.closedBall x R ↦ (((f z : EReal).toReal : ℝ) : EReal)) := by
  refine ⟨((((f x : EReal).toReal - (β : ℝ) * ρ : ℝ) : EReal)), ?_⟩
  rintro _ ⟨z, rfl⟩
  have hxρ : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ
  have hzρ : (z : H) ∈ Metric.ball x ρ := hclosed_ρ z.2
  have hβ_nonneg : 0 ≤ (β : ℝ) := by
    exact_mod_cast β.2
  have hdist :
      dist ((f z : EReal).toReal) ((f x : EReal).toReal) ≤ (β : ℝ) * dist (z : H) x := by
    simpa using hlip.dist_le_mul (z : H) hzρ x hxρ
  have hdistρ : dist (z : H) x < ρ := by
    exact hzρ
  have habs :
      |(f z : EReal).toReal - (f x : EReal).toReal| ≤ (β : ℝ) * ρ := by
    calc
      |(f z : EReal).toReal - (f x : EReal).toReal|
          = dist ((f z : EReal).toReal) ((f x : EReal).toReal) := by
              rw [Real.dist_eq]
      _ ≤ (β : ℝ) * dist (z : H) x := hdist
      _ ≤ (β : ℝ) * ρ := by
            exact mul_le_mul_of_nonneg_left hdistρ.le hβ_nonneg
  have hlower_real : (f x : EReal).toReal - (β : ℝ) * ρ ≤ (f z : EReal).toReal := by
    nlinarith [abs_le.mp habs]
  change ((((f x : EReal).toReal - (β : ℝ) * ρ : ℝ) : EReal)) ≤
      ((((f z : EReal).toReal : ℝ) : EReal))
  exact_mod_cast hlower_real

/-- Helper for Theorem 18 3: the explicit closed-subball quadratic barrier is the quadratic
distance penalty minus the finite-valued representative. -/
private noncomputable def closed_subball_quadratic_barrier
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (δ : ℝ) {R : ℝ}
    (u : Metric.closedBall x R) : EReal :=
  (((δ * dist (u : H) x ^ 2 - (f u : EReal).toReal : ℝ) : EReal))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: the closed-subball quadratic barrier is proper because it is
real-valued everywhere on the closed-ball subtype and the center belongs to its domain. -/
private theorem isProper_closed_subball_quadratic_barrier
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {R δ : ℝ} (hR : 0 < R) :
    ERealFunction.IsProper (closed_subball_quadratic_barrier (f := f) x δ (R := R)) := by
  constructor
  · -- The barrier is real-valued on the closed-ball subtype, so it never equals `⊥`.
    intro u
    change (((δ * dist (u : H) x ^ 2 - (f u : EReal).toReal : ℝ) : EReal)) ≠ ⊥
    exact EReal.coe_ne_bot _
  · -- The center of the closed ball provides a point in the domain.
    refine ⟨⟨x, by simpa [Metric.mem_closedBall] using le_of_lt hR⟩, ?_⟩
    rw [ERealFunction.mem_dom_iff_ne_top]
    simp [closed_subball_quadratic_barrier]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: the closed-subball quadratic barrier is lower semicontinuous because
its real-valued core is continuous on the closed-ball subtype. -/
private theorem lowerSemicontinuous_closed_subball_quadratic_barrier
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {ρ R δ : ℝ} {β : NNReal}
    (hclosed_ρ : Metric.closedBall x R ⊆ Metric.ball x ρ)
    (hlip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ)) :
    LowerSemicontinuous (closed_subball_quadratic_barrier (f := f) x δ (R := R)) := by
  let g : Metric.closedBall x R → ℝ := fun u ↦
    δ * dist (u : H) x ^ 2 - (f u : EReal).toReal
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro u
    have huρ : (u : H) ∈ Metric.ball x ρ := hclosed_ρ u.2
    have htoReal :
        ContinuousAt (fun z ↦ (f z : EReal).toReal) (u : H) :=
      hlip.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds huρ)
    have htoReal_sub :
        ContinuousAt (fun v : Metric.closedBall x R ↦ (f v : EReal).toReal) u :=
      htoReal.comp continuous_subtype_val.continuousAt
    have hdist :
        ContinuousAt (fun v : Metric.closedBall x R ↦ dist (v : H) x) u :=
      (continuous_subtype_val.dist continuous_const).continuousAt
    -- The barrier core is the quadratic distance term minus the pulled-back `toReal` term.
    simpa [g] using ((hdist.pow 2).const_mul δ).sub htoReal_sub
  simpa [closed_subball_quadratic_barrier, g] using
    (continuous_coe_real_ereal.comp hg).lowerSemicontinuous

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: the oscillation control on the closed subball bounds the quadratic
barrier from below. -/
private theorem bddBelow_closed_subball_quadratic_barrier
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {R δ : ℝ}
    (hδ : 0 ≤ δ)
    {c : ℝ}
    (hosc :
      ∀ u ∈ Metric.closedBall x R,
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ c) :
    BddBelow (Set.range (closed_subball_quadratic_barrier (f := f) x δ (R := R))) := by
  refine ⟨(((-((f x : EReal).toReal + c) : ℝ) : EReal)), ?_⟩
  rintro _ ⟨u, rfl⟩
  have huosc := hosc u u.2
  have hu_upper : (f u : EReal).toReal ≤ (f x : EReal).toReal + c := by
    nlinarith [abs_le.mp huosc]
  have hquad_nonneg : 0 ≤ δ * dist (u : H) x ^ 2 := by
    exact mul_nonneg hδ (sq_nonneg _)
  have hreal :
      -((f x : EReal).toReal + c) ≤ δ * dist (u : H) x ^ 2 - (f u : EReal).toReal := by
    nlinarith
  change (((-((f x : EReal).toReal + c) : ℝ) : EReal)) ≤
      ((((δ * dist (u : H) x ^ 2 - (f u : EReal).toReal : ℝ) : EReal)))
  exact_mod_cast hreal

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: the center of an oscillation-controlled closed subball is an
approximate minimizer for the explicit quadratic barrier. -/
private theorem closed_subball_quadratic_barrier_center_approx_minimizer
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {R c δ : ℝ}
    (hR : 0 < R) (_hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hosc :
      ∀ u ∈ Metric.closedBall x R,
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ c) :
    let xK : Metric.closedBall x R := ⟨x, by
      simpa [Metric.mem_closedBall] using le_of_lt hR⟩
    closed_subball_quadratic_barrier (f := f) x δ xK ≤
      (c : EReal) +
        sInf (Set.range (closed_subball_quadratic_barrier (f := f) x δ (R := R))) := by
  let xK : Metric.closedBall x R := ⟨x, by
    simpa [Metric.mem_closedBall] using le_of_lt hR⟩
  let S := Set.range (closed_subball_quadratic_barrier (f := f) x δ (R := R))
  have hS_nonempty : S.Nonempty := ⟨closed_subball_quadratic_barrier (f := f) x δ xK, ⟨xK, rfl⟩⟩
  have hlower :
      (((-((f x : EReal).toReal + c) : ℝ) : EReal)) ≤ sInf S := by
    -- The oscillation bound makes `-f(x) - c` a lower bound for every barrier value.
    refine le_csInf hS_nonempty ?_
    intro b hb
    rcases hb with ⟨u, rfl⟩
    have huosc := hosc u u.2
    have hu_upper : (f u : EReal).toReal ≤ (f x : EReal).toReal + c := by
      nlinarith [abs_le.mp huosc]
    have hquad_nonneg : 0 ≤ δ * dist (u : H) x ^ 2 := by
      exact mul_nonneg hδ (sq_nonneg _)
    have hreal :
        -((f x : EReal).toReal + c) ≤ δ * dist (u : H) x ^ 2 - (f u : EReal).toReal := by
      nlinarith
    change (((-((f x : EReal).toReal + c) : ℝ) : EReal)) ≤
        ((((δ * dist (u : H) x ^ 2 - (f u : EReal).toReal : ℝ) : EReal)))
    exact_mod_cast hreal
  have hsum :
      (((-((f x : EReal).toReal + c) : ℝ) : EReal)) + (c : EReal) =
        (((-(f x : EReal).toReal : ℝ) : EReal)) := by
    have hsum_real : (-((f x : EReal).toReal + c)) + c = -(f x : EReal).toReal := by
      ring
    exact_mod_cast hsum_real
  have hcenter :
      closed_subball_quadratic_barrier (f := f) x δ xK =
        (((-(f x : EReal).toReal : ℝ) : EReal)) := by
    -- At the center the quadratic term vanishes.
    simp [closed_subball_quadratic_barrier, xK]
  have hshift :
      (((-(f x : EReal).toReal : ℝ) : EReal)) ≤ (c : EReal) + sInf S := by
    have hcancel :
        (((-(f x : EReal).toReal : ℝ) : EReal)) =
          (c : EReal) + (((-((f x : EReal).toReal + c) : ℝ) : EReal)) := by
      symm
      simpa [add_comm] using hsum
    calc
      (((-(f x : EReal).toReal : ℝ) : EReal))
          = (c : EReal) + (((-((f x : EReal).toReal + c) : ℝ) : EReal)) := hcancel
      _ ≤ (c : EReal) + sInf S := add_le_add_right hlower (c : EReal)
  simpa [xK, hcenter] using hshift

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: after rewriting the first Ekeland inequality at the center of the
closed subball, the quadratic penalty plus the linear Ekeland term is bounded by the oscillation
margin `c`. -/
private theorem closed_subball_penalty_le_of_first_ekeland_inequality
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {R c δ γ : ℝ}
    (hosc :
      ∀ u ∈ Metric.closedBall x R,
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ c)
    {zK : Metric.closedBall x R}
    (hfirst :
      (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal +
            γ * dist (zK : H) x : ℝ) : EReal)) ≤
        (((-(f x : EReal).toReal : ℝ) : EReal))) :
    δ * dist (zK : H) x ^ 2 + γ * dist (zK : H) x ≤ c := by
  have hz_upper :
      (f zK : EReal).toReal - (f x : EReal).toReal ≤ c := by
    -- The oscillation control provides the upper bound needed to isolate the penalty terms.
    exact (abs_le.mp (hosc (zK : H) zK.2)).2
  have hfirst_real :
      δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal + γ * dist (zK : H) x ≤
        -(f x : EReal).toReal := by
    -- All terms are finite real casts, so the `EReal` inequality reduces to a real one.
    exact_mod_cast hfirst
  -- Move the finite values of `f` to the right-hand side and use the oscillation estimate.
  nlinarith

/-- Helper for Theorem 18 3: the concrete quadratic-plus-linear penalty estimate forces the
ambient Ekeland point strictly inside the quarter-radius subball. -/
private theorem dist_lt_quarter_of_closed_subball_penalty
    {R c δ γ d : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hγ : 0 < γ)
    (hδ : δ = 16 * c / R ^ 2)
    (hpenalty : δ * d ^ 2 + γ * d ≤ c) :
    d < R / 4 := by
  by_contra hd_ge
  have hquarter_le : R / 4 ≤ d := by
    linarith
  have hquarter_pos : 0 < R / 4 := by
    positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hquarter_pos hquarter_le
  have hδ_nonneg : 0 ≤ δ := by
    rw [hδ]
    positivity
  have hquarter_sq_le : (R / 4) ^ 2 ≤ d ^ 2 := by
    nlinarith
  have hR_sq_ne : R ^ 2 ≠ 0 := by
    nlinarith
  have hquarter_eq : δ * (R / 4) ^ 2 = c := by
    -- The chosen coefficient `δ = 16 c / R^2` is calibrated so that the quarter-radius gives
    -- exactly the oscillation margin.
    rw [hδ]
    field_simp [hR_sq_ne]
    ring
  have hc_le_quadratic : c ≤ δ * d ^ 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_left hquarter_sq_le hδ_nonneg
    simpa [hquarter_eq] using hmul
  have hlinear_pos : 0 < γ * d := by
    exact mul_pos hγ hd_pos
  have hstrict : c < δ * d ^ 2 + γ * d := by
    nlinarith
  exact (not_lt_of_ge hpenalty) hstrict

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 18 3: once the first Ekeland inequality is rewritten in concrete form, the
oscillation bound on the closed subball forces the barrier point into the strict quarter-radius
ball around the center. -/
private theorem ekeland_barrier_point_dist_lt_quarter
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} {R c δ βE : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hβE : 0 < βE)
    (hδ : δ = 16 * c / R ^ 2)
    (hosc :
      ∀ u ∈ Metric.closedBall x R,
        |(f u : EReal).toReal - (f x : EReal).toReal| ≤ c)
    {zK : Metric.closedBall x R}
    (hfirst :
      (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal +
            (c / βE) * dist (zK : H) x : ℝ) : EReal)) ≤
        (((-(f x : EReal).toReal : ℝ) : EReal))) :
    dist (zK : H) x < R / 4 := by
  have hpenalty :
      δ * dist (zK : H) x ^ 2 + (c / βE) * dist (zK : H) x ≤ c :=
    closed_subball_penalty_le_of_first_ekeland_inequality f hosc hfirst
  -- The calibrated quadratic coefficient turns that concrete penalty bound into the source
  -- quarter-radius estimate needed for the `z ± η • y` perturbations.
  exact
    dist_lt_quarter_of_closed_subball_penalty hR hc
      (by positivity : 0 < c / βE) hδ hpenalty

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: the quadratic penalty in the source `z ± η • y` test contributes
exactly `2 * δ * η^2` after the cross terms cancel. -/
private lemma closed_subball_quadratic_barrier_pm_eta_expansion
    (x z y : H) (δ η : ℝ) (hy : ‖y‖ = 1) :
    δ * dist (z + η • y) x ^ 2 + δ * dist (z - η • y) x ^ 2 -
        2 * (δ * dist z x ^ 2) =
      2 * δ * η ^ 2 := by
  have hplus :
      dist (z + η • y) x ^ 2 = ‖(z - x) + η • y‖ ^ 2 := by
    rw [dist_eq_norm]
    congr 1
    abel_nf
  have hminus :
      dist (z - η • y) x ^ 2 = ‖(z - x) - η • y‖ ^ 2 := by
    rw [dist_eq_norm]
    congr 1
    abel_nf
  have hsmul_sq : ‖η • y‖ ^ 2 = η ^ 2 := by
    rw [norm_smul, hy, mul_one, Real.norm_eq_abs]
    exact sq_abs η
  have hnorm :
      dist (z + η • y) x ^ 2 + dist (z - η • y) x ^ 2 - 2 * dist z x ^ 2 = 2 * η ^ 2 := by
    have hadd := norm_add_sq_real (z - x) (η • y)
    have hsub := norm_sub_sq_real (z - x) (η • y)
    rw [hplus, hminus, dist_eq_norm] at *
    nlinarith [hadd, hsub, hsmul_sq]
  calc
    δ * dist (z + η • y) x ^ 2 + δ * dist (z - η • y) x ^ 2 - 2 * (δ * dist z x ^ 2)
        = δ * (dist (z + η • y) x ^ 2 + dist (z - η • y) x ^ 2 - 2 * dist z x ^ 2) := by ring
    _ = δ * (2 * η ^ 2) := by rw [hnorm]
    _ = 2 * δ * η ^ 2 := by ring

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: a point lying strictly inside the quarter-radius subball admits a
fixed positive step size, bounded simultaneously by `R / 4` and `R^2 / 16`, whose unit-sphere
perturbations in both signs stay inside the ambient closed subball. -/
private theorem ekeland_pm_step_mem_closed_subball
    (x z : H) {R : ℝ} (hR : 0 < R) (hz : dist z x < R / 4) :
    ∃ η : Set.Ioi (0 : ℝ),
      (η : ℝ) ≤ R / 4 ∧
      (η : ℝ) ≤ R ^ 2 / 16 ∧
      ∀ y ∈ Metric.sphere (0 : H) 1,
        z + (η : ℝ) • y ∈ Metric.closedBall x R ∧
          z - (η : ℝ) • y ∈ Metric.closedBall x R := by
  have hquarter_pos : 0 < R / 4 := by positivity
  have hsquare_pos : 0 < R ^ 2 / 16 := by
    nlinarith [hR]
  let η : Set.Ioi (0 : ℝ) := ⟨min (R / 4) (R ^ 2 / 16), lt_min hquarter_pos hsquare_pos⟩
  refine ⟨η, min_le_left _ _, min_le_right _ _, ?_⟩
  intro y hy
  have hy_norm : ‖y‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using hy
  have hη_le_quarter : (η : ℝ) ≤ R / 4 := min_le_left _ _
  have hη_pos : 0 < (η : ℝ) := η.2
  have hplus_dist :
      dist (z + (η : ℝ) • y) z = (η : ℝ) := by
    rw [dist_eq_norm]
    have hrewrite : z + (η : ℝ) • y - z = (η : ℝ) • y := by
      abel_nf
    rw [hrewrite, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hη_pos.le]
  have hminus_dist :
      dist (z - (η : ℝ) • y) z = (η : ℝ) := by
    rw [dist_eq_norm]
    have hrewrite : z - (η : ℝ) • y - z = -((η : ℝ) • y) := by
      abel_nf
    rw [hrewrite, norm_neg, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hη_pos.le]
  constructor
  · -- The positive perturbation stays in the ambient closed ball by a triangle estimate.
    rw [Metric.mem_closedBall]
    calc
      dist (z + (η : ℝ) • y) x ≤ dist (z + (η : ℝ) • y) z + dist z x := dist_triangle _ _ _
      _ = (η : ℝ) + dist z x := by rw [hplus_dist]
      _ ≤ R / 4 + R / 4 := add_le_add hη_le_quarter hz.le
      _ ≤ R := by linarith
  · -- The negative perturbation satisfies the same estimate.
    rw [Metric.mem_closedBall]
    calc
      dist (z - (η : ℝ) • y) x ≤ dist (z - (η : ℝ) • y) z + dist z x := dist_triangle _ _ _
      _ = (η : ℝ) + dist z x := by rw [hminus_dist]
      _ ≤ R / 4 + R / 4 := add_le_add hη_le_quarter hz.le
      _ ≤ R := by linarith

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: once the center and both sampled endpoints are finite, the
symmetric second-difference quotient is the cast of the corresponding real quotient. -/
private lemma symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    (η : Set.Ioi (0 : ℝ))
    (hplus : x + (η : ℝ) • y ∈ effectiveDomain f)
    (hminus : x - (η : ℝ) • y ∈ effectiveDomain f) :
    (((f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
        2 * (f x : EReal)) / (η : ℝ)) =
      (((((f (x + (η : ℝ) • y) : EReal).toReal +
          (f (x - (η : ℝ) • y) : EReal).toReal -
          2 * (f x : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hplus_top : (f (x + (η : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hplus)
  have hplus_bot : (f (x + (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (η : ℝ) • y) : EReal) from
      (f (x + (η : ℝ) • y)).2)
  have hminus_top :
      (f (x - (η : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hminus)
  have hminus_bot :
      (f (x - (η : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x - (η : ℝ) • y) : EReal) from
      (f (x - (η : ℝ) • y)).2)
  have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := by
    rfl
  -- Rewrite each finite `EReal` value as a real cast and collapse the quotient to real algebra.
  rw [← EReal.coe_toReal hplus_top hplus_bot, ← EReal.coe_toReal hminus_top hminus_bot,
    htwo, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_div]
  simp

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: specializing the strict Ekeland inequality to the symmetric
competitors `z ± η • y` replaces the subtype distance by the ambient step size `η`. -/
private lemma ekeland_strict_inequalities_at_pm_competitors
    {x z y : H} {R c βE : ℝ} {η : Set.Ioi (0 : ℝ)}
    (hy : y ∈ Metric.sphere (0 : H) 1)
    (hplusK : z + (η : ℝ) • y ∈ Metric.closedBall x R)
    (hminusK : z - (η : ℝ) • y ∈ Metric.closedBall x R)
    {zK : Metric.closedBall x R} (hzK : (zK : H) = z)
    {Φ : Metric.closedBall x R → EReal}
    (hstrict :
      ∀ ⦃u : Metric.closedBall x R⦄, u ≠ zK →
        Φ zK < Φ u + ((((c / βE) * dist u zK : ℝ)) : EReal)) :
    let wplus : Metric.closedBall x R := ⟨z + (η : ℝ) • y, hplusK⟩
    let wminus : Metric.closedBall x R := ⟨z - (η : ℝ) • y, hminusK⟩
    Φ zK < Φ wplus + ((((c / βE) * (η : ℝ) : ℝ)) : EReal) ∧
      Φ zK < Φ wminus + ((((c / βE) * (η : ℝ) : ℝ)) : EReal) := by
  let wplus : Metric.closedBall x R := ⟨z + (η : ℝ) • y, hplusK⟩
  let wminus : Metric.closedBall x R := ⟨z - (η : ℝ) • y, hminusK⟩
  have hy_norm : ‖y‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using hy
  have hwplus_dist : dist wplus zK = (η : ℝ) := by
    change dist (z + (η : ℝ) • y) (zK : H) = (η : ℝ)
    rw [hzK, dist_eq_norm]
    have hrewrite : z + (η : ℝ) • y - z = (η : ℝ) • y := by
      abel_nf
    rw [hrewrite, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg η.2.le]
  have hminus_dist : dist wminus zK = (η : ℝ) := by
    change dist (z - (η : ℝ) • y) (zK : H) = (η : ℝ)
    rw [hzK, dist_eq_norm]
    have hrewrite : z - (η : ℝ) • y - z = -((η : ℝ) • y) := by
      abel_nf
    rw [hrewrite, norm_neg, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg η.2.le]
  have hwplus_ne : wplus ≠ zK := by
    intro hEq
    have : (η : ℝ) = 0 := by
      simpa [wplus, hEq] using hwplus_dist.symm
    exact η.2.ne' this
  have hminus_ne : wminus ≠ zK := by
    intro hEq
    have : (η : ℝ) = 0 := by
      simpa [wminus, hEq] using hminus_dist.symm
    exact η.2.ne' this
  -- Apply the strict Ekeland inequality separately to the positive and negative competitors.
  dsimp [wplus, wminus]
  constructor
  · simpa [hwplus_dist] using hstrict (u := wplus) hwplus_ne
  · simpa [hminus_dist] using hstrict (u := wminus) hminus_ne

omit [CompleteSpace H] in
/-- Helper for Theorem 18 3: summing the two strict competitor inequalities and rewriting the
quadratic barrier terms yields the desired symmetric second-difference quotient bound. -/
private lemma pointwise_symmetric_second_difference_lt_of_ekeland_barrier_point
    (f : H → Set.Ioi (⊥ : EReal)) {x z y : H} {δ c βE : ℝ} {η : Set.Ioi (0 : ℝ)}
    (hy : y ∈ Metric.sphere (0 : H) 1)
    (hzdom : z ∈ effectiveDomain f)
    (hplusdom : z + (η : ℝ) • y ∈ effectiveDomain f)
    (hminusdom : z - (η : ℝ) • y ∈ effectiveDomain f)
    (hplus :
      (((δ * dist z x ^ 2 - (f z : EReal).toReal : ℝ) : EReal)) <
        (((δ * dist (z + (η : ℝ) • y) x ^ 2 -
              (f (z + (η : ℝ) • y) : EReal).toReal : ℝ) : EReal) +
          ((((c / βE) * (η : ℝ) : ℝ)) : EReal)))
    (hminus :
      (((δ * dist z x ^ 2 - (f z : EReal).toReal : ℝ) : EReal)) <
        (((δ * dist (z - (η : ℝ) • y) x ^ 2 -
              (f (z - (η : ℝ) • y) : EReal).toReal : ℝ) : EReal) +
          ((((c / βE) * (η : ℝ) : ℝ)) : EReal))) :
    (((f (z + (η : ℝ) • y) : EReal) + (f (z - (η : ℝ) • y) : EReal) -
          2 * (f z : EReal)) / (η : ℝ)) <
      (((2 * δ * (η : ℝ) + 2 * c / βE : ℝ)) : EReal) := by
  have hy_norm : ‖y‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using hy
  have hplus_real :
      δ * dist z x ^ 2 - (f z : EReal).toReal <
        (δ * dist (z + (η : ℝ) • y) x ^ 2 - (f (z + (η : ℝ) • y) : EReal).toReal) +
          (c / βE) * (η : ℝ) := by
    exact_mod_cast hplus
  have hminus_real :
      δ * dist z x ^ 2 - (f z : EReal).toReal <
        (δ * dist (z - (η : ℝ) • y) x ^ 2 - (f (z - (η : ℝ) • y) : EReal).toReal) +
          (c / βE) * (η : ℝ) := by
    exact_mod_cast hminus
  have hsum :
      (δ * dist z x ^ 2 - (f z : EReal).toReal) +
          (δ * dist z x ^ 2 - (f z : EReal).toReal) <
        ((δ * dist (z + (η : ℝ) • y) x ^ 2 - (f (z + (η : ℝ) • y) : EReal).toReal) +
            (c / βE) * (η : ℝ)) +
          ((δ * dist (z - (η : ℝ) • y) x ^ 2 - (f (z - (η : ℝ) • y) : EReal).toReal) +
            (c / βE) * (η : ℝ)) := by
    exact add_lt_add hplus_real hminus_real
  have hquad :
      δ * dist (z + (η : ℝ) • y) x ^ 2 + δ * dist (z - (η : ℝ) • y) x ^ 2 -
          2 * (δ * dist z x ^ 2) =
        2 * δ * (η : ℝ) ^ 2 := by
    simpa using
      closed_subball_quadratic_barrier_pm_eta_expansion x z y δ (η : ℝ) hy_norm
  have hraw :
      (f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal <
        2 * δ * (η : ℝ) ^ 2 + 2 * (c / βE) * (η : ℝ) := by
    nlinarith [hsum, hquad]
  have hquot_real :
      (((f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal) / (η : ℝ)) <
        (2 * δ * (η : ℝ) + 2 * c / βE) := by
    have hrhs :
        (2 * δ * (η : ℝ) + 2 * c / βE) * (η : ℝ) =
          2 * δ * (η : ℝ) ^ 2 + 2 * (c / βE) * (η : ℝ) := by
      ring
    refine (div_lt_iff₀ η.2).2 ?_
    simpa [hrhs] using hraw
  have hquot_coe :
      (((((f (z + (η : ℝ) • y) : EReal).toReal +
            (f (z - (η : ℝ) • y) : EReal).toReal -
            2 * (f z : EReal).toReal) / (η : ℝ)) : ℝ) : EReal) <
        (((2 * δ * (η : ℝ) + 2 * c / βE : ℝ)) : EReal) := by
    exact_mod_cast hquot_real
  -- Replace the symmetric second-difference quotient by its real-cast normal form.
  simpa [symmetric_second_difference_eq_coe_toReal_of_mem_effectiveDomain
      (f := f) (x := z) (y := y) hzdom η hplusdom hminusdom] using hquot_coe

/-- Helper for Theorem 18 3: the calibrated source constants keep the final uniform bound
strictly below the target tolerance `ε`. -/
private lemma ekeland_barrier_bound_lt_epsilon
    {ε c δ βE R : ℝ} (hε : 0 < ε)
    (hc : c = ε / 4) (hδ : δ = 16 * c / R ^ 2) (hβE : βE = 8 * c / ε)
    (hR : 0 < R) {η : ℝ} (hη : η ≤ R ^ 2 / 16) :
    2 * δ * η + 2 * c / βE < ε := by
  have hc_pos : 0 < c := by
    rw [hc]
    positivity
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hR_sq_pos : 0 < R ^ 2 := by positivity
  have hR_sq_ne : R ^ 2 ≠ 0 := by positivity
  have hdelta_term_le : 2 * δ * η ≤ 2 * c := by
    rw [hδ]
    field_simp [hR_sq_ne]
    nlinarith [hη, hc_nonneg]
  have hratio_eq : 2 * c / βE = ε / 4 := by
    rw [hβE, hc]
    field_simp [hε.ne']
    ring
  calc
    2 * δ * η + 2 * c / βE ≤ 2 * c + ε / 4 := by
      rw [hratio_eq]
      gcongr
    _ = 3 * ε / 4 := by rw [hc]; ring
    _ < ε := by nlinarith

/-- Helper for Theorem 18 3: on a local Lipschitz ball, the source-faithful Ekeland barrier
construction should produce a nearby point with a uniform spherewise symmetric second-difference
bound strictly below the target tolerance. -/
private theorem exists_ekeland_barrier_point_in_lipschitz_ball
    (f : H → Set.Ioi (⊥ : EReal)) (ε : Set.Ioi (0 : ℝ)) {x : H} {r ρ : ℝ}
    {β : NNReal}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hball : Metric.ball x ρ ⊆ effectiveDomain f)
    (hlip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x ρ)) :
    ∃ z : H, z ∈ Metric.ball x r ∧ z ∈ Metric.ball x ρ ∧
      ∃ η : Set.Ioi (0 : ℝ), ∃ M : ℝ, M < (ε : ℝ) ∧
        ∀ y ∈ Metric.sphere (0 : H) 1,
          (((f (z + (η : ℝ) • y) : EReal) + (f (z - (η : ℝ) • y) : EReal) -
                2 * (f z : EReal)) / (η : ℝ)) <
            ((M : ℝ) : EReal) := by
  -- Route correction: the inward-distance estimate from the first Ekeland inequality is now
  -- isolated in `ekeland_barrier_point_dist_lt_quarter`. The remaining source step is to apply
  -- the strict variational inequality to the two competitors `z ± η • y`, sum the resulting
  -- inequalities, rewrite the quadratic terms with
  -- `closed_subball_quadratic_barrier_pm_eta_expansion`, and then choose `M < ε`.
  let c : ℝ := (ε : ℝ) / 4
  have hc : 0 < c := by
    have hε : 0 < (ε : ℝ) := ε.2
    dsimp [c]
    nlinarith
  rcases exists_closed_subball_with_small_toReal_oscillation f hr hρ hlip hc with
    ⟨R, hR, hRr, hRρ, hclosed_r, hclosed_ρ, hosc⟩
  let _ : CompleteSpace (Metric.closedBall x R) :=
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall x R)).completeSpace_coe
  let xK : Metric.closedBall x R := ⟨x, by simpa [Metric.mem_closedBall] using le_of_lt hR⟩
  let δ : ℝ := 16 * c / R ^ 2
  let βE : ℝ := 8 * c / (ε : ℝ)
  let Φ : Metric.closedBall x R → EReal := closed_subball_quadratic_barrier (f := f) x δ
  have hδ : δ = 16 * c / R ^ 2 := rfl
  have hβE : βE = 8 * c / (ε : ℝ) := rfl
  have hδ_nonneg : 0 ≤ δ := by
    rw [hδ]
    positivity
  have hβE_pos : 0 < βE := by
    rw [hβE]
    have hnum : 0 < 8 * c := by
      nlinarith [hc]
    exact div_pos hnum ε.2
  have hxK_dom : xK ∈ ERealFunction.dom Φ := by
    rw [ERealFunction.mem_dom_iff_ne_top]
    simp [Φ, closed_subball_quadratic_barrier, xK]
  have hxK_approx : Φ xK ≤ (c : EReal) + sInf (Set.range Φ) := by
    -- The center of the oscillation-controlled closed ball is an approximate minimizer.
    simpa [Φ, xK] using
      closed_subball_quadratic_barrier_center_approx_minimizer
        (f := f) (x := x) (R := R) (c := c) (δ := δ) hR hc.le hδ_nonneg hosc
  have hproperΦ : ERealFunction.IsProper Φ := by
    simpa [Φ] using
      isProper_closed_subball_quadratic_barrier (f := f) (x := x) (R := R) (δ := δ) hR
  have hlscΦ : LowerSemicontinuous Φ := by
    simpa [Φ] using
      lowerSemicontinuous_closed_subball_quadratic_barrier
        (f := f) (x := x) (ρ := ρ) (R := R) (δ := δ) (β := β) hclosed_ρ hlip
  have hbddΦ : BddBelow (Set.range Φ) := by
    dsimp [Φ]
    exact
      bddBelow_closed_subball_quadratic_barrier
        (f := f) (x := x) (R := R) (δ := δ) hδ_nonneg hosc
  rcases
      exists_ekeland_variational_point
        Φ hproperΦ hlscΦ hbddΦ hc.le hβE_pos hxK_dom hxK_approx with
    ⟨zK, hfirst, _, hstrict⟩
  have hzball_r : (zK : H) ∈ Metric.ball x r := hclosed_r zK.2
  have hzball_ρ : (zK : H) ∈ Metric.ball x ρ := hclosed_ρ zK.2
  have hzdom : (zK : H) ∈ effectiveDomain f := hball hzball_ρ
  have hfirst_concrete :
      (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal +
            (c / βE) * dist (zK : H) x : ℝ) : EReal)) ≤
        (((-(f x : EReal).toReal : ℝ) : EReal)) := by
    -- Rewrite the first Ekeland inequality using the explicit barrier and the center value.
    have hfirst_expanded :
        ((((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal : ℝ) : EReal)) +
            ((((c / βE) * dist x (zK : H) : ℝ)) : EReal)) ≤
          (((-(f x : EReal).toReal : ℝ) : EReal)) := by
      simpa [Φ, xK, closed_subball_quadratic_barrier] using hfirst
    have hfirst_real :
        δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal +
            (c / βE) * dist x (zK : H) ≤
          -(f x : EReal).toReal := by
      -- All barrier values are finite real casts, so the Ekeland inequality reduces to a real one.
      exact_mod_cast hfirst_expanded
    have hfirst_concrete' :
        (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal +
              (c / βE) * dist x (zK : H) : ℝ) : EReal)) ≤
          (((-(f x : EReal).toReal : ℝ) : EReal)) := by
      exact_mod_cast hfirst_real
    simpa [dist_comm] using hfirst_concrete'
  have hz_quarter : dist (zK : H) x < R / 4 :=
    ekeland_barrier_point_dist_lt_quarter
      (f := f) hR hc hβE_pos hδ hosc hfirst_concrete
  rcases ekeland_pm_step_mem_closed_subball x (zK : H) hR hz_quarter with
    ⟨η, hη_le_quarter, hη_le_sq, hpm⟩
  refine ⟨(zK : H), hzball_r, hzball_ρ, η, 2 * δ * (η : ℝ) + 2 * c / βE, ?_, ?_⟩
  · -- The calibrated constants force the final uniform bound to stay below `ε`.
    exact
      ekeland_barrier_bound_lt_epsilon
        (hε := ε.2) (hc := rfl) (hδ := hδ) (hβE := hβE) hR hη_le_sq
  · intro y hy
    rcases hpm y hy with ⟨hplusK, hminusK⟩
    have hplusdom : (zK : H) + (η : ℝ) • y ∈ effectiveDomain f :=
      hball (hclosed_ρ hplusK)
    have hminusdom : (zK : H) - (η : ℝ) • y ∈ effectiveDomain f :=
      hball (hclosed_ρ hminusK)
    have hstrict_pm :=
      ekeland_strict_inequalities_at_pm_competitors
        (hy := hy) hplusK hminusK (zK := zK) rfl (Φ := Φ) hstrict
    rcases hstrict_pm with ⟨hplus_raw, hminus_raw⟩
    have hplus :
        (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal : ℝ) : EReal)) <
          (((δ * dist ((zK : H) + (η : ℝ) • y) x ^ 2 -
                (f ((zK : H) + (η : ℝ) • y) : EReal).toReal : ℝ) : EReal) +
            ((((c / βE) * (η : ℝ) : ℝ)) : EReal)) := by
      simpa [Φ, closed_subball_quadratic_barrier] using hplus_raw
    have hminus :
        (((δ * dist (zK : H) x ^ 2 - (f zK : EReal).toReal : ℝ) : EReal)) <
          (((δ * dist ((zK : H) - (η : ℝ) • y) x ^ 2 -
                (f ((zK : H) - (η : ℝ) • y) : EReal).toReal : ℝ) : EReal) +
            ((((c / βE) * (η : ℝ) : ℝ)) : EReal)) := by
      simpa [Φ, closed_subball_quadratic_barrier] using hminus_raw
    -- Sum the two specialized strict inequalities and rewrite the barrier algebra once.
    exact
      pointwise_symmetric_second_difference_lt_of_ekeland_barrier_point
        (f := f) (x := x) (z := (zK : H)) (y := y) (δ := δ) (c := c) (βE := βE)
        (η := η) hy hzdom hplusdom hminusdom hplus hminus

/-- Helper for Theorem 18 3: every continuity point can be approximated by points of the Chapter
18 sublevel set `S_ε` inside any prescribed ball. -/
private theorem exists_mem_symmetricSecondDifferenceSublevelSet_ball_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (ε : Set.Ioi (0 : ℝ)) {x : H} (hx : x ∈ cont f) {r : ℝ} (hr : 0 < r) :
    ∃ z, z ∈ Metric.ball x r ∧ z ∈ symmetricSecondDifferenceSublevelSet f ε := by
  rcases exists_lipschitz_ball_of_mem_cont f hconv hx with ⟨β, ρ, hρ, hball, hlip⟩
  rcases
      exists_ekeland_barrier_point_in_lipschitz_ball
        f ε hr hρ hball hlip with
    ⟨z, hzball, hzρ, η, M, hMε, hpointwise⟩
  have hzcont : z ∈ cont f :=
    mem_cont_of_mem_ball_of_lipschitzOnWith_ball f hball hlip hzρ
  -- Route correction: the outer local theorem is now just packaging. The only remaining blocker is
  -- the source-faithful Ekeland barrier point that supplies the spherewise quotient estimate.
  refine ⟨z, hzball, ?_⟩
  refine (mem_symmetricSecondDifferenceSublevelSet_iff f ε z).2 ⟨hzcont, ?_⟩
  exact
    hasSymmetricSecondDifferenceBound_of_forall_mem_sphere_quotient_lt_real
      (f := f) (ε := ε) (η := η) hMε hpointwise

/-- Helper for Theorem 18 3: every interior effective-domain point belongs to the closure of the
Chapter 18 sublevel set `S_ε`. -/
private theorem interior_effectiveDomain_subset_closure_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) (ε : Set.Ioi (0 : ℝ)) :
    interior (effectiveDomain f) ⊆ closure (symmetricSecondDifferenceSublevelSet f ε) := by
  intro x hx
  have hxcont : x ∈ cont f := by
    rw [cont_eq_interior_effectiveDomain_of_exists_continuityPoint f hconv hcont]
    exact hx
  -- Use the local Ekeland neighborhood-production lemma to witness every neighborhood of `x`.
  rw [Metric.mem_closure_iff]
  intro r hr
  rcases
      exists_mem_symmetricSecondDifferenceSublevelSet_ball_of_mem_cont
        f hconv ε hxcont hr with
    ⟨z, hzball, hzS⟩
  refine ⟨z, hzS, ?_⟩
  simpa [Metric.mem_ball, dist_comm] using hzball

/-- Helper for Theorem 18 3: the closure-subtype pullback of `S_ε` is dense in
`closure (effectiveDomain f)`. -/
private theorem dense_preimage_symmetricSecondDifferenceSublevelSet_in_closure
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) (ε : Set.Ioi (0 : ℝ)) :
    Dense (Subtype.val ⁻¹' symmetricSecondDifferenceSublevelSet f ε :
      Set (closure (effectiveDomain f))) := by
  rw [Subtype.dense_iff]
  have hinter_nonempty : (interior (effectiveDomain f)).Nonempty := by
    rcases hcont with ⟨x, hx⟩
    exact ⟨x, mem_interior_effectiveDomain_of_mem_cont hx⟩
  have hclosure_eq :
      closure (interior (effectiveDomain f)) = closure (effectiveDomain f) := by
    simpa using
      hconv.convex_effectiveDomain.closure_interior_eq_closure_of_nonempty_interior
        hinter_nonempty
  have hambient :
      closure (effectiveDomain f) ⊆ closure (symmetricSecondDifferenceSublevelSet f ε) := by
    calc
      closure (effectiveDomain f) = closure (interior (effectiveDomain f)) := by
        exact hclosure_eq.symm
      _ ⊆ closure (closure (symmetricSecondDifferenceSublevelSet f ε)) := by
        exact
          closure_mono
            (interior_effectiveDomain_subset_closure_symmetricSecondDifferenceSublevelSet
              f hconv hcont ε)
      _ = closure (symmetricSecondDifferenceSublevelSet f ε) := by
        rw [closure_closure]
  have himage :
      (((↑) : closure (effectiveDomain f) → H) ''
          (Subtype.val ⁻¹' symmetricSecondDifferenceSublevelSet f ε :
            Set (closure (effectiveDomain f)))) =
        symmetricSecondDifferenceSublevelSet f ε := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact hz'
    · intro hz
      have hzcont : z ∈ cont f :=
        (mem_symmetricSecondDifferenceSublevelSet_iff f ε z).1 hz |>.1
      have hzdom : z ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hzcont
      exact ⟨⟨z, subset_closure hzdom⟩, hz, rfl⟩
  -- The subtype image is exactly the ambient set because every point of `S_ε` already lies in the
  -- effective domain, hence in its closure.
  simpa [himage] using hambient

/- Source/core/bridge triage:
- `source-facing`: Theorem 18.3 concerns `sourceDifferentiabilitySetInClosure f`, the source
  differentiability locus of `f` viewed inside `closure (effectiveDomain f)` through the coercion
  bridge.
- `core/canonical`: the primitive Chapter 18 owner is
  `HasSymmetricSecondDifferenceBound f x ε`, with the sampled project declarations
  `cont f`, `HasSymmetricSecondDifferenceBound f x ε`,
  `symmetricSecondDifferenceSublevelSet f ε`, and
  `dense_isGδ_iInter_of_dense_open`.
- `bridge/view`: the source-facing differentiability locus is connected to the canonical open-set
  owner by
  `sourceDifferentiabilitySet_eq_iInter_symmetricSecondDifferenceSublevelSet`, and
  the countable bridge
  `sourceDifferentiabilitySetInClosure_eq_iInter_nat_symmetricSecondDifferenceSublevelSet`
  is the corresponding closure-subtype view used by the Baire-category owner.
-/

-- Proof sketch: for each `ε > 0`, use Ekeland's variational principle with the barrier from the
-- proof to produce differentiability points in
-- `symmetricSecondDifferenceSublevelSet f ε` near any point of `cont f`. Proposition 18.2 makes
-- each `symmetricSecondDifferenceSublevelSet f ε` open, and the bridge theorem
-- `sourceDifferentiabilitySetInClosure_eq_iInter_nat_symmetricSecondDifferenceSublevelSet`
-- rewrites
-- the source differentiability locus in terms of those canonical open sets;
-- `hcont` gives nonempty interior of `effectiveDomain f`;
-- convexity then yields
-- `closure (interior (effectiveDomain f)) = closure (effectiveDomain f)`. Baire category is then
-- the canonical Chapter 1 owner `dense_isGδ_iInter_of_dense_open` applied in the complete metric
-- subtype via `sourceDifferentiabilitySetInClosure f`.
/-- Theorem 18 3: if a convex `]-∞,+∞]`-valued function on a real Hilbert space has a nonempty
continuity set `cont f`, then the points where its finite-valued representative is Fréchet
differentiable in the source sense `x ∈ cont f` form a dense `Gδ` subset of
`closure (effectiveDomain f)`. -/
theorem dense_isGδ_differentiableAt_toReal_in_closure_effectiveDomain_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) :
    Dense (sourceDifferentiabilitySetInClosure f) ∧
    IsGδ (sourceDifferentiabilitySetInClosure f) := by
  let _ : CompleteSpace (closure (effectiveDomain f)) :=
    (isClosed_closure : IsClosed (closure (effectiveDomain f))).completeSpace_coe
  let εn : ℕ → Set.Ioi (0 : ℝ) := fun n ↦
    ⟨1 / (n + 1 : ℝ), one_div_nat_add_one_pos n⟩
  let C : ℕ → Set (closure (effectiveDomain f)) := fun n ↦
    Subtype.val ⁻¹' symmetricSecondDifferenceSublevelSet f (εn n)
  have h_open : ∀ n, IsOpen (C n) := by
    intro n
    -- Proposition 18.2 gives openness in the ambient space, and the subtype view is a preimage.
    exact
      (isOpen_symmetricSecondDifferenceSublevelSet f hconv (εn n)).preimage
        continuous_subtype_val
  have h_dense : ∀ n, Dense (C n) := by
    intro n
    -- Density is the ambient closure statement transferred to the closure subtype.
    exact dense_preimage_symmetricSecondDifferenceSublevelSet_in_closure f hconv hcont (εn n)
  -- Rewrite the source differentiability locus as the sampled countable intersection and apply
  -- the Chapter 1 Baire-category owner.
  simpa [C, εn,
    sourceDifferentiabilitySetInClosure_eq_iInter_nat_symmetricSecondDifferenceSublevelSet, hconv]
    using dense_isGδ_iInter_of_dense_open C h_open h_dense

/-- If a convex source function has a nonempty continuity set, then it admits one ambient source
differentiability point. This is the existential corollary of Theorem 18.3 used in
Proposition 18.4. -/
theorem exists_source_differentiability_point_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) :
    ∃ x : H, x ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
  rcases hcont with ⟨x0, hx0⟩
  let x0_closure : closure (effectiveDomain f) :=
    ⟨x0, subset_closure (mem_effectiveDomain_of_mem_cont hx0)⟩
  let _ : Nonempty (closure (effectiveDomain f)) := ⟨x0_closure⟩
  have hdense :
      Dense (sourceDifferentiabilitySetInClosure f) :=
    (dense_isGδ_differentiableAt_toReal_in_closure_effectiveDomain_of_exists_continuityPoint
      f hconv ⟨x0, hx0⟩).1
  -- Choose one point from the dense differentiability locus in the closure subtype and unpack it
  -- back to the ambient space.
  rcases hdense.nonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa using (mem_sourceDifferentiabilitySetInClosure_iff f x).1 hx

end EkelandLebourgTheorem

end ERealFunction
