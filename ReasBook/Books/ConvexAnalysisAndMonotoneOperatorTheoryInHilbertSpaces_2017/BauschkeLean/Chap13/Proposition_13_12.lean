import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap12.Definition_12_5
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 12: an affine-defect bound `⟪x,u⟫ - f x ≤ μ` is equivalent to the
minorant inequality `⟪x,u⟫ - μ ≤ f x`. -/
lemma affine_defect_le_real_iff
    (f : H → EReal) (x u : H) (μ : ℝ) :
    ((((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ (μ : EReal)) ↔
      (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ f x) := by
  constructor
  · intro h
    -- Move the real ordinate `μ` to the right-hand side of the affine-defect inequality.
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (μ : EReal) + f x) :=
      (EReal.sub_le_iff_le_add
        (a := (((⟪x, u⟫_ℝ : ℝ) : EReal)))
        (b := f x)
        (c := (μ : EReal))
        (.inr (EReal.coe_ne_top μ))
        (.inr (EReal.coe_ne_bot μ))).1 h
    -- Subtracting the same real scalar recovers the minorant form.
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ f x) :=
      EReal.sub_le_of_le_add' h'
    simpa [EReal.coe_sub] using h''
  · intro h
    -- Rewrite the minorant inequality back as a bound on the affine defect.
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ f x) := by
      simpa [EReal.coe_sub] using h
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x + (μ : EReal)) :=
      (EReal.sub_le_iff_le_add
        (a := (((⟪x, u⟫_ℝ : ℝ) : EReal)))
        (b := (μ : EReal))
        (c := f x)
        (.inl (EReal.coe_ne_bot μ))
        (.inl (EReal.coe_ne_top μ))).1 h'
    exact EReal.sub_le_of_le_add' h''

-- Proof sketch: expand epigraph membership into `conjugate f u ≤ μ`, unfold the supremum
-- definition of `conjugate f u`, and rewrite the resulting pointwise inequalities into the affine
-- minorant form `⟪x,u⟫ - μ ≤ f x`.
/-- Proposition 13 12: clause (i). A point `(u, μ)` lies in the epigraph of the conjugate if
and only if the continuous affine functional `x ↦ ⟪x, u⟫ - μ` is a minorant of `f`. -/
theorem mem_epigraph_conjugate_iff
    (f : H → EReal) (u : H) (μ : ℝ) :
    (u, μ) ∈ epigraph f∗ ↔
      ∀ x : H, (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ f x) := by
  rw [mem_epigraph_iff, conjugate_apply]
  constructor
  · intro h x
    -- Specializing the supremum bound to one point gives the desired affine minorant inequality.
    have hx : ((((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ (μ : EReal)) :=
      le_trans (le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x) h
    exact (affine_defect_le_real_iff f x u μ).1 hx
  · intro h
    -- Reassembling the pointwise inequalities with `iSup_le` reconstructs the epigraph bound.
    refine iSup_le fun x ↦ ?_
    exact (affine_defect_le_real_iff f x u μ).2 (h x)

/-- A slope `u` belongs to the domain of `f*` exactly when `f` admits a continuous affine
minorant with that slope. -/
theorem mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope
    (f : H → EReal) (u : H) :
    u ∈ dom f∗ ↔ HasContinuousAffineMinorantWithSlope f u := by
  constructor
  · intro hu
    have hnot : ¬ ∀ μ : ℝ, (μ : EReal) < f∗ u := by
      intro hμ
      exact (mem_dom_iff_ne_top _ _).1 hu <| (EReal.eq_top_iff_forall_lt (f∗ u)).2 hμ
    rcases not_forall.mp hnot with ⟨μ, hμ⟩
    have hmem : (u, μ) ∈ epigraph f∗ := by
      rw [mem_epigraph_iff]
      exact le_of_not_gt hμ
    refine ⟨-μ, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (mem_epigraph_conjugate_iff f u μ).1 hmem
  · rintro ⟨η, hη⟩
    have hmem : (u, -η) ∈ epigraph f∗ := by
      refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hη
    rw [mem_dom_iff]
    exact lt_of_le_of_lt ((mem_epigraph_iff _ _ _).1 hmem)
      (EReal.coe_lt_top (-η))

-- Proof sketch: the pointwise bridge `u ∈ dom (conjugate f) ↔ HasContinuousAffineMinorantWithSlope
-- f u` identifies the absence of continuous affine minorants with `dom (conjugate f) = ∅`, which
-- is equivalent to `conjugate f = fun _ ↦ ⊤`.
/-- Proposition 13.12 (2): clause (ii). The conjugate is identically `+∞` exactly when `f`
admits no continuous affine minorant. -/
theorem conjugate_eq_top_iff_no_continuousAffineMinorant
    (f : H → EReal) :
    f∗ = (fun _ : H ↦ (⊤ : EReal)) ↔
      ¬ ∃ u : H, HasContinuousAffineMinorantWithSlope f u := by
  constructor
  · intro htop
    rintro ⟨u, hu⟩
    have hu' : u ∈ dom f∗ :=
      (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).2 hu
    exact (mem_dom_iff_ne_top _ _).1 hu' <| by
      simpa using congrFun htop u
  · intro hminorant
    ext u
    by_contra hu
    exact hminorant ⟨u,
      (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).1
        ((mem_dom_iff_ne_top _ _).2 hu)⟩

/-- Helper for Proposition 13 12: points in a closed ball satisfy a uniform lower bound on their
inner product with any fixed slope vector. -/
lemma inner_ge_neg_mul_norm_of_mem_closedBall
    {u x : H} {R : ℝ} (hx : x ∈ Metric.closedBall (0 : H) R) :
    -R * ‖u‖ ≤ ⟪x, u⟫_ℝ := by
  -- Membership in the closed ball gives the norm bound needed for Cauchy-Schwarz.
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hneg_inner : -⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := by
    simpa [inner_neg_left, norm_neg] using real_inner_le_norm (-x) u
  have hnorm : ‖x‖ * ‖u‖ ≤ R * ‖u‖ :=
    mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
  linarith

-- Proof sketch: if `dom (conjugate f)` is nonempty, the domain bridge above gives a continuous
-- affine minorant `x ↦ ⟪x,u⟫ + η` of `f`. On a bounded set `C`, Cauchy-Schwarz bounds `⟪x,u⟫`
-- uniformly from below, yielding a real constant `m` with `m ≤ f x` for all `x ∈ C`.
/-- Proposition 13.12 (3): clause (iii). If the conjugate has nonempty domain, then `f` is bounded
below on every bounded subset of the Hilbert space. -/
theorem exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
    (f : H → EReal) (hdom : (dom f∗).Nonempty) (C : Set H) (hC : Bornology.IsBounded C) :
    ∃ m : ℝ, ∀ x ∈ C, (m : EReal) ≤ f x := by
  rcases hdom with ⟨u, hu⟩
  rcases (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).1 hu with ⟨η, hη⟩
  rcases hC.subset_closedBall (0 : H) with ⟨R, hR⟩
  refine ⟨η - R * ‖u‖, ?_⟩
  intro x hx
  -- The bounded set sits in one closed ball, so the affine slope term has a uniform lower bound.
  have hx_ball : x ∈ Metric.closedBall (0 : H) R :=
    hR hx
  have hinner : -R * ‖u‖ ≤ ⟪x, u⟫_ℝ :=
    inner_ge_neg_mul_norm_of_mem_closedBall hx_ball
  have hminor : (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ f x) :=
    hη x
  -- Adding the intercept `η` upgrades the inner-product bound to a bound on the affine minorant.
  have hreal : η - R * ‖u‖ ≤ ⟪x, u⟫_ℝ + η := by
    linarith
  have hcoe : (((η - R * ‖u‖ : ℝ) : EReal) ≤ (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) :=
    (EReal.coe_le_coe_iff).2 hreal
  exact hcoe.trans hminor

end Conjugation

end ERealFunction
