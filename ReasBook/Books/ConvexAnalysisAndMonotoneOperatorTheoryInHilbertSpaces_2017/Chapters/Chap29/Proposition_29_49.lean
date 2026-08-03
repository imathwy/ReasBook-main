import BauschkeLean.Chap05.Proposition_5_13
import BauschkeLean.Chap08.Proposition_8_37
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap14.Proposition_14_15
import BauschkeLean.Chap29.Proposition_29_41

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology

-- Declarations for this item are statement-stage skeletons only.
--
-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic convex sublevel-set
-- owners, so this file keeps the project-local Chapter 29 owner
-- `continuousConvexSubgradientProjector`, the canonical lower-level-set owner `lowerLevelSet`,
-- and the Chapter 5 relaxed-iteration owner `relaxedOperatorIteration` on the public statement
-- surface.

universe u v

namespace ERealFunction

noncomputable section

variable {H : Type u} {I : Type v}

/-- The common feasibility set `C = ⋂ i, lev_{≤ 0} fᵢ` for a finite family of real-valued
functions. -/
def cyclicSubgradientProjectorConstraintSet (f : I → H → ℝ) : Set H :=
  ⋂ j : I, lowerLevelSet (f j).toEReal.asEReal 0

/-- Membership in the common feasibility set means belonging to each zero lower level set. -/
theorem mem_cyclicSubgradientProjectorConstraintSet_iff
    (f : I → H → ℝ) {x : H} :
    x ∈ cyclicSubgradientProjectorConstraintSet f ↔
      ∀ j : I, x ∈ lowerLevelSet (f j).toEReal.asEReal 0 := by
  simp [cyclicSubgradientProjectorConstraintSet]

/-- A nonempty common feasibility set yields a nonempty zero lower level set for each component
function. -/
theorem lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty
    (f : I → H → ℝ) (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty) (j : I) :
    (lowerLevelSet (f j).toEReal.asEReal 0).Nonempty := by
  rcases hC with ⟨x, hx⟩
  exact ⟨x, Set.mem_iInter.1 hx j⟩

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The window-control hypothesis `(29.80)`: there is a positive window length `m` such that every
index of the finite family occurs at least once in each block
`idx n, idx (n + 1), …, idx (n + m - 1)`. -/
def HasWindowControl (idx : ℕ → I) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ j : I, ∀ n : ℕ, ∃ k < m, idx (n + k) = j

namespace HasWindowControl

/-- Window control implies that the control sequence is surjective onto the family indices. -/
theorem surjective {idx : ℕ → I} (h : HasWindowControl idx) : Function.Surjective idx := by
  rcases h with ⟨m, _, h⟩
  intro j
  rcases h j 0 with ⟨k, _, hk⟩
  exact ⟨k, by simpa using hk⟩

end HasWindowControl

/-- Uniform relaxation control for Proposition 29.49: the parameters `λₙ` admit positive margins
from `0` and `2`, witnessed by explicit constants. -/
structure HasUniformRelaxationMargins (lam : ℕ → ℝ) where
  ε : ℝ
  δ : ℝ
  epsilon_pos : 0 < ε
  delta_pos : 0 < δ
  epsilon_le : ∀ n : ℕ, ε ≤ lam n
  le_two_sub_delta : ∀ n : ℕ, lam n ≤ 2 - δ

namespace HasUniformRelaxationMargins

/-- Uniform positive margins from `0` and `2` force each relaxation parameter to lie in `]0, 2[`.
-/
theorem mem_Ioo {lam : ℕ → ℝ} (h : HasUniformRelaxationMargins lam) (n : ℕ) :
    lam n ∈ Set.Ioo (0 : ℝ) 2 := by
  refine ⟨lt_of_lt_of_le h.epsilon_pos (h.epsilon_le n), ?_⟩
  exact lt_of_le_of_lt (h.le_two_sub_delta n) (sub_lt_self 2 h.delta_pos)

/-- Uniform positive margins from `0` and `2` give the closed interval hypothesis used by the
Chapter 5 relaxed-iteration theorem. -/
theorem mem_Icc {lam : ℕ → ℝ} (h : HasUniformRelaxationMargins lam) (n : ℕ) :
    lam n ∈ Set.Icc (0 : ℝ) 2 := by
  exact ⟨le_of_lt (h.mem_Ioo n).1, le_of_lt (h.mem_Ioo n).2⟩

end HasUniformRelaxationMargins

/-- The family of subgradient projectors `Gᵢ` attached to the continuous convex functions `fᵢ`
and the chosen selections `sᵢ` of `∂ fᵢ`. -/
noncomputable def cyclicSubgradientProjectorFamily
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal)) :
    I → H → H :=
  fun j ↦
    continuousConvexSubgradientProjector
      (f j) 0 (hcont j) (hconv j)
      (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty f hC j)
      (s j)

/-- Each component projector has the expected zero lower level set as its fixed-point set. -/
theorem fixedPoints_cyclicSubgradientProjectorFamily_eq_lowerLevelSet
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (j : I) :
    Function.fixedPoints (cyclicSubgradientProjectorFamily f hcont hconv hC s j) =
      lowerLevelSet (f j).toEReal.asEReal 0 := by
  simpa [cyclicSubgradientProjectorFamily] using
    continuousConvexSubgradientProjector_fixedPoints_eq_lowerLevelSet
      (f j) 0 (hcont j) (hconv j)
      (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty f hC j)
      (s j)

/-- The common fixed-point set of the whole projector family is exactly the feasibility set `C`. -/
theorem iInter_fixedPoints_cyclicSubgradientProjectorFamily_eq_constraintSet
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal)) :
    (⋂ j : I, Function.fixedPoints (cyclicSubgradientProjectorFamily f hcont hconv hC s j)) =
      cyclicSubgradientProjectorConstraintSet f := by
  ext x
  simp [cyclicSubgradientProjectorConstraintSet,
    fixedPoints_cyclicSubgradientProjectorFamily_eq_lowerLevelSet]

/-- The operator sequence `G_{idx n}` from Proposition 29.49. -/
noncomputable def controlledSubgradientProjectorSequence
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (idx : ℕ → I) :
    ℕ → H → H :=
  fun n ↦ cyclicSubgradientProjectorFamily f hcont hconv hC s (idx n)

/-- Each controlled projector is firmly quasinonexpansive. -/
theorem firmlyQuasinonexpansive_controlledSubgradientProjectorSequence
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (idx : ℕ → I) :
    ∀ n : ℕ,
      FirmlyQuasinonexpansive
        (controlledSubgradientProjectorSequence f hcont hconv hC s idx n) := by
  intro n
  simpa [controlledSubgradientProjectorSequence, cyclicSubgradientProjectorFamily] using
    firmlyQuasinonexpansive_continuousConvexSubgradientProjector
      (f (idx n)) 0 (hcont (idx n)) (hconv (idx n))
      (lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty
        f hC (idx n))
      (s (idx n))

/-- If the control sequence covers every family index, the common fixed-point set of the controlled
sequence is exactly the feasibility set `C`. -/
theorem iInter_fixedPoints_controlledSubgradientProjectorSequence_eq_constraintSet
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (idx : ℕ → I)
    (hidx : Function.Surjective idx) :
    (⋂ n : ℕ, Function.fixedPoints
      (controlledSubgradientProjectorSequence f hcont hconv hC s idx n)) =
      cyclicSubgradientProjectorConstraintSet f := by
  ext x
  constructor
  · intro hx
    rw [mem_cyclicSubgradientProjectorConstraintSet_iff]
    intro j
    rcases hidx j with ⟨n, hn⟩
    have hxk :
        x ∈ Function.fixedPoints
          (controlledSubgradientProjectorSequence f hcont hconv hC s idx n) :=
      Set.mem_iInter.1 hx n
    have hxidx :
        x ∈ Function.fixedPoints
          (cyclicSubgradientProjectorFamily f hcont hconv hC s (idx n)) := by
      simpa [controlledSubgradientProjectorSequence] using hxk
    have hxj :
        x ∈ Function.fixedPoints (cyclicSubgradientProjectorFamily f hcont hconv hC s j) := by
      simpa [hn] using hxidx
    rw [fixedPoints_cyclicSubgradientProjectorFamily_eq_lowerLevelSet
      f hcont hconv hC s j] at hxj
    exact hxj
  · intro hx
    refine Set.mem_iInter.2 fun n ↦ ?_
    have hfamily :
        x ∈
          ⋂ j : I, Function.fixedPoints
            (cyclicSubgradientProjectorFamily f hcont hconv hC s j) := by
      rw [iInter_fixedPoints_cyclicSubgradientProjectorFamily_eq_constraintSet f hcont hconv hC s]
      exact hx
    simpa [controlledSubgradientProjectorSequence] using Set.mem_iInter.1 hfamily (idx n)

/-- Helper for Proposition 29.49: each textbook case reduces to boundedness of every component on
every bounded subset of `H`. -/
theorem upperBoundOnEveryBoundedSet_of_supercoerciveConjugate_of_continuous_convex
    (f : H → ℝ)
    (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hsuper : Supercoercive (f.toEReal.asEReal∗)) :
    ∀ B : Set H, Bornology.IsBounded B →
      ∃ M : ℝ, ∀ x ∈ B, (f x : EReal) ≤ M := by
  let hf : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have hboundedConj :
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, (f.toEReal∗[hf]).asEReal∗ u ≤ M :=
    (supercoercive_iff_conjugate_boundedOnEveryBoundedSet
      (f := f.toEReal∗[hf]) (hf := gammaZeroConjugate_mem_gammaZero hf)).1 hsuper
  intro B hB
  rcases hboundedConj B hB with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hx
  have hx_biconj :
      (((f.toEReal∗[hf])∗[gammaZeroConjugate_mem_gammaZero hf] x : Set.Ioi (⊥ : EReal)) :
        EReal) ≤ M := by
    -- Reinterpret the bounded conjugate estimate using the packaged `Γ₀`-conjugate notation.
    simpa [gammaZeroConjugate_apply] using hM x hx
  have hpoint :
      (((f.toEReal∗[hf])∗[gammaZeroConjugate_mem_gammaZero hf] x : Set.Ioi (⊥ : EReal)) :
        EReal) = (f x : EReal) := by
    -- Fenchel--Moreau transports the biconjugate value back to the original real-valued function.
    simpa [gammaZeroConjugate_apply, Function.toEReal_apply] using
      congrFun (biconjugate_eq_of_mem_gammaZero hf) x
  rw [← hpoint]
  exact hx_biconj

omit [CompleteSpace H] in
/-- Helper for Proposition 29.49: a real upper bound on a metric ball gives a finite `EReal`
supremum for the image of that ball. -/
lemma finite_sup_ball_lt_top_of_real_upper_bound
    (f : H → ℝ) {x₀ : H} {ρ M : ℝ}
    (hM : ∀ y ∈ Metric.ball x₀ ρ, f y ≤ M) :
    sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤ := by
  have hsSup_le :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) ≤ M := by
    -- The real upper bound controls every point in the `EReal` image of the ball.
    refine sSup_le ?_
    intro a ha
    rcases ha with ⟨y, hy, rfl⟩
    change ((f y : ℝ) : EReal) ≤ (M : EReal)
    exact_mod_cast hM y hy
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top M)

omit [CompleteSpace H] in
/-- Helper for Proposition 29.49: coercing a convex real-valued function through `toEReal`
preserves convexity on its effective domain. -/
lemma convexOn_toEReal_of_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function stays finite after the canonical `toEReal` coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Effective-domain membership is automatic because the domain is all of `H`.
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    -- Rewrite the convexity inequality back to the original real-valued function.
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * f x + (1 - a) * f y : ℝ) : EReal)
    exact_mod_cast hreal

omit [CompleteSpace H] in
/-- Helper for Proposition 29.49: a uniform upper bound on the doubled ball controls the
oscillation on the inner ball, so the real image of the inner ball is bounded. -/
lemma bounded_image_of_upper_bound_on_buffer_ball
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f)
    {x₀ : H} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ y ∈ Metric.ball x₀ (2 * R), f y ≤ M) :
    Bornology.IsBounded (f '' Metric.ball x₀ R) := by
  let η : EReal := sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ (2 * R))
  let C : ℝ := (1 / 2 : ℝ) * (η.toReal - (f x₀ : EReal).toReal)
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOn_toEReal_of_convexOn_univ f hconv
  have hx₀_dom : x₀ ∈ effectiveDomain f.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hη : η < ⊤ := by
    -- The real upper bound on the larger ball gives a finite `EReal` supremum there.
    simpa [η] using finite_sup_ball_lt_top_of_real_upper_bound f hM
  have htwoR : 0 < 2 * R := by
    positivity
  have hhalf0 : 0 < (1 / 2 : ℝ) := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hhalf_twoR : (1 / 2 : ℝ) * (2 * R) = R := by ring
  have hC_nonneg : 0 ≤ C := by
    have hx₀_ball : x₀ ∈ Metric.ball x₀ ((1 / 2 : ℝ) * (2 * R)) := by
      have hhalf_twoR' : 0 < (1 / 2 : ℝ) * (2 * R) := by
        simpa [hhalf_twoR] using hR
      exact Metric.mem_ball_self hhalf_twoR'
    have hosc :=
      oscillation_bound_on_smaller_ball
        (f := f.toEReal) (x := x₀) hconv_toEReal htwoR hx₀_dom hη hhalf0 hhalf1
        hx₀_ball
        (by simp [Function.effectiveDomain_toEReal])
    -- Evaluating the oscillation estimate at the center shows the radius is nonnegative.
    simpa [C, η, Function.toEReal_apply] using hosc
  have hsubset :
      f '' Metric.ball x₀ R ⊆ Metric.closedBall (f x₀) C := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hosc :=
      oscillation_bound_on_smaller_ball
        (f := f.toEReal) (x := x) hconv_toEReal htwoR hx₀_dom hη hhalf0 hhalf1
        (by simpa [Metric.mem_ball, hhalf_twoR] using hx)
        (by simp [Function.effectiveDomain_toEReal])
    -- The oscillation estimate is exactly the closed-ball membership around `f x₀`.
    simpa [Metric.mem_closedBall, Real.dist_eq, C, η, Function.toEReal_apply] using hosc
  exact Metric.isBounded_closedBall.subset hsubset

/-- Helper for Proposition 29.49: each textbook case reduces to boundedness of every component on
every bounded subset of `H`. -/
theorem boundedOnEveryBoundedSet_of_supercoerciveConjugate_of_continuous_convex
    (f : H → ℝ)
    (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hsuper : Supercoercive (f.toEReal.asEReal∗))
    (B : Set H)
    (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (f '' B) := by
  have hupper :=
    upperBoundOnEveryBoundedSet_of_supercoerciveConjugate_of_continuous_convex
      f hcont hconv hsuper
  by_cases hBempty : B.Nonempty
  · rcases hBempty with ⟨x₀, hx₀⟩
    rcases hB.subset_ball x₀ with ⟨R, hR⟩
    have hRpos : 0 < R := by
      simpa [Metric.mem_ball] using hR hx₀
    rcases hupper (Metric.ball x₀ (2 * R)) Metric.isBounded_ball with ⟨M, hM⟩
    have hball_bounded :
        Bornology.IsBounded (f '' Metric.ball x₀ R) := by
      -- Route correction: the conjugate transport is already closed, so only the oscillation
      -- bridge from the doubled ball to the inner-ball image remains here.
      have hM_real : ∀ y ∈ Metric.ball x₀ (2 * R), f y ≤ M := by
        intro y hy
        exact_mod_cast hM y hy
      exact bounded_image_of_upper_bound_on_buffer_ball (f := f) hconv hRpos hM_real
    exact hball_bounded.subset <| by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hR hx, rfl⟩
  · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
    simpa [hB']

/-- Helper for Proposition 29.49: in finite dimension, a convex real-valued function is bounded on
every bounded subset. -/
theorem boundedOnEveryBoundedSet_of_convex_finiteDimensional_local
    [FiniteDimensional ℝ H]
    (f : H → ℝ)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (B : Set H)
    (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (f '' B) := by
  have hcont : Continuous f := hconv.locallyLipschitz.continuous
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  have hcompact : IsCompact (closure B) := by
    simpa [isClosed_closure.closure_eq] using hB.isCompact_closure
  have himageCompact : IsCompact (f '' closure B) := hcompact.image hcont
  -- The compact image of the closure controls the original bounded image.
  exact himageCompact.isBounded.subset <| by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, subset_closure hx, rfl⟩

/-- Helper for Proposition 29.49: each textbook case reduces to boundedness of every component on
every bounded subset of `H`. -/
theorem boundedOnEveryBoundedSet_of_cyclicCase
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hcase :
      (∀ j : I, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((f j) '' B)) ∨
      (∀ j : I, Supercoercive ((f j).toEReal.asEReal∗)) ∨
      FiniteDimensional ℝ H) :
    ∀ j : I, ∀ B : Set H,
      Bornology.IsBounded B → Bornology.IsBounded ((f j) '' B) := by
  intro j B hB
  rcases hcase with hbounded | hsuper | hfd
  · -- Branch (i): the required boundedness is already one of the assumptions.
    exact hbounded j B hB
  · -- Branch (ii): supercoercivity of the conjugate gives a bounded image on each bounded set.
    exact
      boundedOnEveryBoundedSet_of_supercoerciveConjugate_of_continuous_convex
        (f j) (hcont j) (hconv j) (hsuper j) B hB
  · -- Branch (iii): finite dimensionality gives boundedness of convex real-valued functions.
    letI : FiniteDimensional ℝ H := hfd
    exact boundedOnEveryBoundedSet_of_convex_finiteDimensional_local (f j) (hconv j) B hB

/-- Helper for Proposition 29.49: a strictly monotone map on `ℕ` gains at least one unit on each
successor step, hence at least `r` units over a window of length `r`. -/
theorem add_le_apply_of_strictMono_nat {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ a r : ℕ, φ a + r ≤ φ (a + r)
  | a, 0 => by simpa
  | a, r + 1 => by
      -- Step the window length forward once and use strict monotonicity at the successor.
      have hprev : φ a + r ≤ φ (a + r) := add_le_apply_of_strictMono_nat hφ a r
      have hstep : φ (a + r) + 1 ≤ φ (a + r + 1) := by
        exact Nat.succ_le_of_lt (hφ (Nat.lt_succ_self (a + r)))
      simpa [Nat.add_assoc] using le_trans (Nat.add_le_add_right hprev 1) hstep

/-- Helper for Proposition 29.49: the norm of a finite orbit gap is bounded by the sum of the
intermediate step norms. -/
theorem norm_sub_le_sum_stepNorms
    (x : ℕ → H) :
    ∀ n k : ℕ,
      ‖x (n + k) - x n‖ ≤
        ∑ j ∈ Finset.range k, ‖x (n + j + 1) - x (n + j)‖
  | n, 0 => by
      -- The empty window contains no displacement.
      simp
  | n, k + 1 => by
      -- Split the `(k + 1)`-step gap into the first `k` steps and the final increment.
      have hsplit :
          x (n + (k + 1)) - x n =
            (x (n + k) - x n) + (x (n + (k + 1)) - x (n + k)) := by
        abel_nf
      calc
        ‖x (n + (k + 1)) - x n‖
            = ‖(x (n + k) - x n) + (x (n + (k + 1)) - x (n + k))‖ := by
                rw [hsplit]
        _ ≤ ‖x (n + k) - x n‖ + ‖x (n + (k + 1)) - x (n + k)‖ := norm_add_le _ _
        _ ≤
            (∑ j ∈ Finset.range k, ‖x (n + j + 1) - x (n + j)‖) +
              ‖x (n + (k + 1)) - x (n + k)‖ := by
                gcongr
                exact norm_sub_le_sum_stepNorms x n k
        _ = ∑ j ∈ Finset.range (k + 1), ‖x (n + j + 1) - x (n + j)‖ := by
              simp [Finset.sum_range_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Proposition 29.49: if the successive differences of an orbit tend strongly to `0`,
then every fixed-length window sum of step norms also tends to `0`. -/
theorem tendsto_zero_windowStepNormSum
    (x : ℕ → H)
    (hstep :
      Tendsto (fun n ↦ x (n + 1) - x n) atTop (nhds (0 : H))) :
    ∀ r : ℕ,
      Tendsto
        (fun n ↦ ∑ j ∈ Finset.range r, ‖x (n + j + 1) - x (n + j)‖)
        atTop (nhds (0 : ℝ)) := by
  have hstepNorm :
      Tendsto (fun n ↦ ‖x (n + 1) - x n‖) atTop (nhds (0 : ℝ)) := by
    simpa using hstep.norm
  intro r
  induction r with
  | zero =>
      -- The empty window sum is identically zero.
      simp
  | succ r ihr =>
      -- Extend the window by one shifted step and add the corresponding limits.
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ihr.add (hstepNorm.comp (Filter.tendsto_add_atTop_nat r))

/-- Helper for Proposition 29.49: subtracting a strongly null error sequence preserves a weak
limit after transport to `WeakSpace`. -/
theorem tendstoWeaklyOfSubTendstoZeroSeq
    {aSeq bSeq : ℕ → H} {a : H}
    (ha :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n)) atTop
        (nhds (toWeakSpace ℝ H a)))
    (hsub : Tendsto (fun n ↦ aSeq n - bSeq n) atTop (nhds (0 : H))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (bSeq n)) atTop
      (nhds (toWeakSpace ℝ H a)) := by
  -- Send the strong error to `WeakSpace`, then subtract it from the known weak limit.
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n - bSeq n)) atTop
        (nhds (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsub
  simpa [sub_sub_cancel] using ha.sub hsubWeak

/-- Helper for Proposition 29.49: the relaxed orbit has vanishing successive increments once the
Chapter 5 weighted square estimate is combined with the uniform relaxation margins. -/
theorem incrementTendstoZero_of_uniformMargins
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (idx : ℕ → I)
    (hidx : HasWindowControl idx)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (lam : ℕ → ℝ)
    (hlam_uniform : HasUniformRelaxationMargins lam)
    (x0 : H) :
    Tendsto
      (fun n ↦
        relaxedOperatorIteration
          (controlledSubgradientProjectorSequence f hcont hconv hC s idx) lam x0 (n + 1) -
          relaxedOperatorIteration
            (controlledSubgradientProjectorSequence f hcont hconv hC s idx) lam x0 n)
      atTop (nhds (0 : H)) := by
  let T := controlledSubgradientProjectorSequence f hcont hconv hC s idx
  let x := relaxedOperatorIteration T lam x0
  let residualSq : ℕ → ℝ :=
    fun n ↦ ‖T n (x n) - x n‖ ^ 2
  let residualWeight : ℕ → ℝ :=
    fun n ↦ lam n * (2 - lam n) * residualSq n
  have hfirm :
      ∀ n : ℕ, FirmlyQuasinonexpansive (T n) :=
    firmlyQuasinonexpansive_controlledSubgradientProjectorSequence
      f hcont hconv hC s idx
  have hnonempty :
      (⋂ n : ℕ, Function.fixedPoints (T n)).Nonempty := by
    rw [iInter_fixedPoints_controlledSubgradientProjectorSequence_eq_constraintSet
      f hcont hconv hC s idx (HasWindowControl.surjective hidx)]
    simpa [T] using hC
  have hlam_Icc : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2 := fun n ↦ hlam_uniform.mem_Icc n
  have hresidualWeight_nonneg : ∀ n : ℕ, 0 ≤ residualWeight n := by
    intro n
    dsimp [residualWeight, residualSq]
    exact
      mul_nonneg
        (mul_nonneg (hlam_Icc n).1 (sub_nonneg.mpr (hlam_Icc n).2))
        (sq_nonneg ‖T n (x n) - x n‖)
  have hpartial :
      ∀ N : ℕ, ∑ k ∈ Finset.range N, residualWeight k ≤
        Metric.infDist x0 (⋂ n : ℕ, Function.fixedPoints (T n)) ^ 2 := by
    intro N
    cases N with
    | zero =>
        -- The empty sum is controlled by the nonnegativity of the initial squared distance.
        simpa [residualWeight] using
          (sq_nonneg (Metric.infDist x0 (⋂ n : ℕ, Function.fixedPoints (T n))))
    | succ n =>
        have hbound :=
          sq_infDist_le_sq_infDist_sub_sum_of_relaxedOperatorIteration
            T lam x0 hfirm hnonempty hlam_Icc n
        have hdist_nonneg :
            0 ≤ Metric.infDist (x (n + 1)) (⋂ n : ℕ, Function.fixedPoints (T n)) ^ 2 :=
          sq_nonneg _
        -- Move the nonnegative left-hand distance term across the inequality to recover the
        -- bounded partial sums of the weighted residual squares.
        have hsum :
            ∑ k ∈ Finset.range (n + 1), residualWeight k ≤
              Metric.infDist x0 (⋂ n : ℕ, Function.fixedPoints (T n)) ^ 2 := by
          nlinarith [hbound, hdist_nonneg]
        simpa [T, x, residualWeight, residualSq] using hsum
  have hresidualWeight_summable : Summable residualWeight :=
    summable_of_sum_range_le hresidualWeight_nonneg hpartial
  have hscaledResidual_summable :
      Summable (fun n ↦ (hlam_uniform.ε * hlam_uniform.δ) * residualSq n) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hresidualWeight_summable
    · intro n
      dsimp [residualSq]
      exact mul_nonneg (mul_nonneg hlam_uniform.epsilon_pos.le hlam_uniform.delta_pos.le) (sq_nonneg _)
    · intro n
      dsimp [residualWeight, residualSq]
      have hlam_lower : hlam_uniform.ε ≤ lam n := hlam_uniform.epsilon_le n
      have hdelta_lower : hlam_uniform.δ ≤ 2 - lam n := by
        linarith [hlam_uniform.le_two_sub_delta n]
      have hsq_nonneg : 0 ≤ ‖T n (x n) - x n‖ ^ 2 := sq_nonneg _
      have hprod_le : hlam_uniform.ε * hlam_uniform.δ ≤ lam n * (2 - lam n) := by
        exact
          mul_le_mul hlam_lower hdelta_lower hlam_uniform.delta_pos.le
            (hlam_Icc n).1
      exact mul_le_mul_of_nonneg_right hprod_le hsq_nonneg
  have hεδ_ne : hlam_uniform.ε * hlam_uniform.δ ≠ 0 :=
    mul_ne_zero hlam_uniform.epsilon_pos.ne' hlam_uniform.delta_pos.ne'
  have hresidualSq_summable : Summable residualSq := by
    refine (summable_mul_left_iff hεδ_ne).1 ?_
    simpa [residualSq, mul_comm, mul_left_comm, mul_assoc] using hscaledResidual_summable
  have hresidualSq_tendsto :
      Tendsto residualSq atTop (nhds (0 : ℝ)) :=
    hresidualSq_summable.tendsto_atTop_zero
  have hresidualNorm_tendsto :
      Tendsto (fun n ↦ ‖T n (x n) - x n‖) atTop (nhds (0 : ℝ)) := by
    have hsqrt_tendsto :
        Tendsto (fun n ↦ Real.sqrt (residualSq n)) atTop (nhds (Real.sqrt 0)) := by
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hresidualSq_tendsto
    -- Taking square roots converts the summable square decay back to decay of the residual norms.
    simpa [residualSq, Real.sqrt_zero, Real.sqrt_sq_eq_abs] using hsqrt_tendsto
  have hstepNorm_tendsto :
      Tendsto (fun n ↦ ‖x (n + 1) - x n‖) atTop (nhds (0 : ℝ)) := by
    have hscaled :
        Tendsto
          (fun n ↦ (2 - hlam_uniform.δ) * ‖T n (x n) - x n‖)
          atTop (nhds ((2 - hlam_uniform.δ) * 0)) := by
      exact tendsto_const_nhds.mul hresidualNorm_tendsto
    have hupper :
        ∀ᶠ n : ℕ in atTop,
          ‖x (n + 1) - x n‖ ≤ (2 - hlam_uniform.δ) * ‖T n (x n) - x n‖ := by
      refine Eventually.of_forall fun n ↦ ?_
      have hrec :
          x (n + 1) - x n =
            lam n • (T n (x n) - x n) := by
        simpa [T, x] using relaxedOperatorIteration_sub_eq_smul_residual T lam x0 n
      rw [hrec, norm_smul, Real.norm_of_nonneg (hlam_Icc n).1]
      exact mul_le_mul_of_nonneg_right (hlam_uniform.le_two_sub_delta n) (norm_nonneg _)
    exact
      squeeze_zero'
        (Eventually.of_forall fun n ↦ norm_nonneg _)
        hupper
        (by simpa using hscaled)
  -- Convert norm decay of the increments back to strong convergence to `0`.
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr <| by
    simpa [T, x] using hstepNorm_tendsto

/-- Helper for Proposition 29.49: along a window-controlled subsequence, one can shift each block
to a prescribed index without changing the weak limit. -/
theorem tendstoWeakly_of_windowControlledSubsequence
    (idx : ℕ → I)
    (hidx : HasWindowControl idx)
    (i : I)
    (x : ℕ → H)
    (z : H)
    {φ : ℕ → ℕ}
    (hφmono : StrictMono φ)
    (hφtendsto :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (φ n))) atTop (nhds (toWeakSpace ℝ H z)))
    (hstep : Tendsto (fun n ↦ x (n + 1) - x n) atTop (nhds (0 : H))) :
    ∃ p : ℕ → ℕ,
      StrictMono p ∧
      (∀ n : ℕ, idx (p n) = i) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (p n))) atTop (nhds (toWeakSpace ℝ H z)) := by
  rcases hidx with ⟨m, hm_pos, hcover⟩
  let ψ : ℕ → ℕ := fun n ↦ φ (n * m)
  have hmul_mono : StrictMono (fun n : ℕ ↦ n * m) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_right hab hm_pos
  have hψmono : StrictMono ψ := hφmono.comp hmul_mono
  have hψtendsto :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (ψ n))) atTop (nhds (toWeakSpace ℝ H z)) := by
    simpa [ψ, Function.comp] using hφtendsto.comp hmul_mono.tendsto_atTop
  have hk_exists : ∀ n : ℕ, ∃ k < m, idx (ψ n + k) = i := by
    intro n
    exact hcover i (ψ n)
  choose k hk_lt hk_idx using hk_exists
  let p : ℕ → ℕ := fun n ↦ ψ n + k n
  have hpmono : StrictMono p := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    have hgap : ψ n + m ≤ ψ (n + 1) := by
      simpa [ψ, Nat.succ_mul] using add_le_apply_of_strictMono_nat hφmono (n * m) m
    have hlt_to_next : p n < ψ (n + 1) := by
      exact lt_of_lt_of_le (Nat.add_lt_add_left (hk_lt n) (ψ n)) hgap
    exact lt_of_lt_of_le hlt_to_next (Nat.le_add_right (ψ (n + 1)) (k (n + 1)))
  have hwindow_tendsto :
      Tendsto
        (fun n ↦ ∑ j ∈ Finset.range m, ‖x (n + j + 1) - x (n + j)‖)
        atTop (nhds (0 : ℝ)) :=
    tendsto_zero_windowStepNormSum x hstep m
  have hgap_norm_bound :
      ∀ n : ℕ,
        ‖x (ψ n) - x (p n)‖ ≤
          ∑ j ∈ Finset.range m, ‖x (ψ n + j + 1) - x (ψ n + j)‖ := by
    intro n
    have hsum_le :
        ∑ j ∈ Finset.range (k n), ‖x (ψ n + j + 1) - x (ψ n + j)‖ ≤
          ∑ j ∈ Finset.range m, ‖x (ψ n + j + 1) - x (ψ n + j)‖ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (hk_lt n).le) ?_
      intro j _ _
      exact norm_nonneg _
    calc
      ‖x (ψ n) - x (p n)‖ = ‖x (p n) - x (ψ n)‖ := by rw [norm_sub_rev]
      _ ≤ ∑ j ∈ Finset.range (k n), ‖x (ψ n + j + 1) - x (ψ n + j)‖ := by
            simpa [p] using norm_sub_le_sum_stepNorms x (ψ n) (k n)
      _ ≤ ∑ j ∈ Finset.range m, ‖x (ψ n + j + 1) - x (ψ n + j)‖ := hsum_le
  have hgap_norm_tendsto :
      Tendsto (fun n ↦ ‖x (ψ n) - x (p n)‖) atTop (nhds (0 : ℝ)) := by
    have hupper :
        ∀ᶠ n : ℕ in atTop,
          ‖x (ψ n) - x (p n)‖ ≤
            ∑ j ∈ Finset.range m, ‖x (ψ n + j + 1) - x (ψ n + j)‖ :=
      Eventually.of_forall hgap_norm_bound
    exact
      squeeze_zero'
        (Eventually.of_forall fun n ↦ norm_nonneg _)
        hupper
        (by simpa using hwindow_tendsto.comp hψmono.tendsto_atTop)
  have hgap_tendsto :
      Tendsto (fun n ↦ x (ψ n) - x (p n)) atTop (nhds (0 : H)) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hgap_norm_tendsto
  refine ⟨p, hpmono, hk_idx, ?_⟩
  -- The shifted subsequence keeps the same weak limit because the block shift tends strongly to
  -- zero.
  simpa [p, ψ, Function.comp] using tendstoWeaklyOfSubTendstoZeroSeq hψtendsto hgap_tendsto

/-- Helper for Proposition 29.49: every weak sequential cluster point of the relaxed controlled
subgradient-projector orbit belongs to the common feasibility set `C`. -/
theorem mem_constraintSet_of_weakSequentialClusterPt
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (hcase :
      (∀ j : I, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((f j) '' B)) ∨
      (∀ j : I, Supercoercive ((f j).toEReal.asEReal∗)) ∨
      FiniteDimensional ℝ H)
    (idx : ℕ → I)
    (hidx : HasWindowControl idx)
    (lam : ℕ → ℝ)
    (hlam_uniform : HasUniformRelaxationMargins lam)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (x0 : H)
    {z : H}
    (hz :
      IsSequentialClusterPt
        (fun n ↦
          toWeakSpace ℝ H
            (relaxedOperatorIteration
              (controlledSubgradientProjectorSequence f hcont hconv hC s idx) lam x0 n))
        (toWeakSpace ℝ H z)) :
    z ∈ cyclicSubgradientProjectorConstraintSet f := by
  let T := controlledSubgradientProjectorSequence f hcont hconv hC s idx
  let x := relaxedOperatorIteration T lam x0
  have hbounded :=
    boundedOnEveryBoundedSet_of_cyclicCase f hcont hconv hcase
  have hstep :
      Tendsto (fun n ↦ x (n + 1) - x n) atTop (nhds (0 : H)) := by
    simpa [T, x] using
      incrementTendstoZero_of_uniformMargins
        f hcont hconv hC idx hidx s lam hlam_uniform x0
  rcases hz.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
  rw [mem_cyclicSubgradientProjectorConstraintSet_iff]
  intro i
  rcases
      tendstoWeakly_of_windowControlledSubsequence
        idx hidx i x z hφmono hφtendsto hstep
    with ⟨p, hpmono, hpidx, hptendsto⟩
  have hinc_subseq :
      Tendsto (fun n ↦ x (p n + 1) - x (p n)) atTop (nhds (0 : H)) := by
    simpa [Function.comp] using hstep.comp hpmono.tendsto_atTop
  have hresidualNorm_tendsto :
      Tendsto
        (fun n ↦ ‖cyclicSubgradientProjectorFamily f hcont hconv hC s i (x (p n)) - x (p n)‖)
        atTop
        (nhds (0 : ℝ)) := by
    have hscaled :
        Tendsto
          (fun n ↦
            (hlam_uniform.ε)⁻¹ *
              ‖x (p n + 1) - x (p n)‖)
          atTop
          (nhds ((hlam_uniform.ε)⁻¹ * 0)) := by
      exact tendsto_const_nhds.mul (by simpa using hinc_subseq.norm)
    have hupper :
        ∀ᶠ n : ℕ in atTop,
          ‖cyclicSubgradientProjectorFamily f hcont hconv hC s i (x (p n)) - x (p n)‖ ≤
            (hlam_uniform.ε)⁻¹ * ‖x (p n + 1) - x (p n)‖ := by
      refine Eventually.of_forall fun n ↦ ?_
      have hstep_eq :
          x (p n + 1) - x (p n) =
            lam (p n) •
              (cyclicSubgradientProjectorFamily f hcont hconv hC s i (x (p n)) - x (p n)) := by
        simpa [T, x, controlledSubgradientProjectorSequence, hpidx n] using
          relaxedOperatorIteration_sub_eq_smul_residual T lam x0 (p n)
      have hmul_lower :
          hlam_uniform.ε *
              ‖cyclicSubgradientProjectorFamily f hcont hconv hC s i (x (p n)) - x (p n)‖ ≤
            ‖x (p n + 1) - x (p n)‖ := by
        rw [hstep_eq, norm_smul, Real.norm_of_nonneg (hlam_uniform.mem_Icc (p n)).1]
        exact
          mul_le_mul_of_nonneg_right (hlam_uniform.epsilon_le (p n))
            (norm_nonneg _)
      exact (le_inv_mul_iff₀ hlam_uniform.epsilon_pos).2 hmul_lower
    exact
      squeeze_zero'
        (Eventually.of_forall fun n ↦ norm_nonneg _)
        hupper
        (by simpa using hscaled)
  have hresidual_tendsto :
      Tendsto
        (fun n ↦
          cyclicSubgradientProjectorFamily f hcont hconv hC s i (x (p n)) - x (p n))
        atTop
        (nhds (0 : H)) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hresidualNorm_tendsto
  -- Proposition 29.41(8) closes the `i`th lower-level-set membership once the shifted subsequence
  -- has weak limit `z` and vanishing projector residual.
  simpa [cyclicSubgradientProjectorFamily] using
    mem_lowerLevelSet_of_subgradientProjector_residual_tendsto_zero_of_tendsto_weakly
      (f := f i) (ξ := 0) (hcont := hcont i) (hconv := hconv i)
      (hC := lowerLevelSet_nonempty_of_cyclicSubgradientProjectorConstraintSet_nonempty f hC i)
      (s := s i) (hbounded := hbounded i)
      (xSeq := fun n ↦ x (p n)) (xbar := z) hresidual_tendsto hptendsto

/-- Proposition 29.49: let `(fᵢ)ᵢ` be a finite family of continuous convex functions on the real
Hilbert space `H`, let
`C = ⋂ i, lev_{≤ 0} fᵢ` be nonempty, and assume either that all `fᵢ` are bounded on every bounded
subset of `H`, or that all Fenchel conjugates are supercoercive in the canonical owner form
`Supercoercive ((fᵢ.toEReal).asEReal∗)`, or that `H` is finite-dimensional. If `idx : ℕ → I`
satisfies the window-control condition `(29.80)`, if the relaxation parameters are bounded away
from both `0` and `2` and hence lie in `]0, 2[`, and if `xₙ` is the Chapter 5 relaxed iteration
driven by the subgradient projectors `G_{idx n}`, then `xₙ` converges weakly to a point of `C`. -/
theorem exists_tendsto_weakly_to_constraintSet_of_cyclic_relaxed_subgradientProjectorIterates
    (f : I → H → ℝ)
    (hcont : ∀ j : I, Continuous (f j))
    (hconv : ∀ j : I, _root_.ConvexOn ℝ Set.univ (f j))
    (hC : (cyclicSubgradientProjectorConstraintSet f).Nonempty)
    (hcase :
      (∀ j : I, ∀ B : Set H,
        Bornology.IsBounded B → Bornology.IsBounded ((f j) '' B)) ∨
      (∀ j : I, Supercoercive ((f j).toEReal.asEReal∗)) ∨
      FiniteDimensional ℝ H)
    (idx : ℕ → I)
    (hidx : HasWindowControl idx)
    (lam : ℕ → ℝ)
    (hlam_uniform : HasUniformRelaxationMargins lam)
    (s : ∀ j : I, Selection (∂ (f j).toEReal))
    (x0 : H) :
    ∃ x ∈ cyclicSubgradientProjectorConstraintSet f,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (relaxedOperatorIteration
              (controlledSubgradientProjectorSequence f hcont hconv hC s idx) lam x0 n))
        atTop (nhds (toWeakSpace ℝ H x)) := by
  let T := controlledSubgradientProjectorSequence f hcont hconv hC s idx
  have hfirm :
      ∀ n : ℕ, FirmlyQuasinonexpansive (T n) :=
    firmlyQuasinonexpansive_controlledSubgradientProjectorSequence
      f hcont hconv hC s idx
  have hnonempty :
      (⋂ n : ℕ, Function.fixedPoints (T n)).Nonempty := by
    rw [iInter_fixedPoints_controlledSubgradientProjectorSequence_eq_constraintSet
      f hcont hconv hC s idx (HasWindowControl.surjective hidx)]
    simpa [T] using hC
  have hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n ↦
              toWeakSpace ℝ H
                (relaxedOperatorIteration T lam x0 n))
            (toWeakSpace ℝ H z) →
          z ∈ ⋂ n : ℕ, Function.fixedPoints (T n) := by
    intro z hz
    rw [iInter_fixedPoints_controlledSubgradientProjectorSequence_eq_constraintSet
      f hcont hconv hC s idx (HasWindowControl.surjective hidx)]
    exact
      mem_constraintSet_of_weakSequentialClusterPt
        f hcont hconv hC hcase idx hidx lam hlam_uniform s x0 hz
  -- Apply Proposition 5.13(vi) to the controlled projector sequence once every weak cluster point
  -- is known to lie in the common fixed-point set.
  rcases
      exists_tendsto_weakly_to_commonFixedPoint_of_relaxedOperatorIteration
        T lam x0 hfirm hnonempty (fun n ↦ hlam_uniform.mem_Icc n) hcluster
    with ⟨x, hx, hx_tendsto⟩
  rw [iInter_fixedPoints_controlledSubgradientProjectorSequence_eq_constraintSet
    f hcont hconv hC s idx (HasWindowControl.surjective hidx)] at hx
  exact ⟨x, hx, by simpa [T] using hx_tendsto⟩

end

end ERealFunction
