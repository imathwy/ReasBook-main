import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_4 (from Chap07) -/
universe u

open scoped InnerProductSpace Pointwise

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Local abbreviation for the polar-set construction used in this exercise file. -/
private abbrev polarSet (C : Set 𝓗) : Set 𝓗 :=
  setOf fun u : 𝓗 ↦ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1

local postfix:100 "ᵒ⊙" => polarSet

/-- Helper for Exercise 7.4: membership in the local polar set is equivalent to the pointwise
inner-product bound `⟪x, u⟫ ≤ 1` on `C`. -/
private lemma mem_polarSet_iff_forall_inner_le_one {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊙ ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1 := by
  -- Unfold the local `polarSet` abbreviation to express membership as a supremum bound.
  change sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1 ↔
      ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1
  rw [sSup_le_iff]
  constructor
  · intro hu x hx
    -- The supremum bound specializes to the image point corresponding to `x ∈ C`.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) :=
      hu _ (Set.mem_image_of_mem _ hx)
    exact_mod_cast hxu
  · intro hu a ha
    -- Conversely, every point of the image set comes from some `x ∈ C`.
    rcases ha with ⟨x, hx, rfl⟩
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) := by
      exact_mod_cast hu x hx
    simpa using hxu

/-- Helper for Exercise 7.4: dilating the primal set by `γ` is equivalent to dilating the test
vector by `γ` inside the polar-set membership condition. -/
private lemma mem_polarSet_smul_set_iff (C : Set 𝓗) (γ : ℝ) {u : 𝓗} :
    u ∈ (γ • C)ᵒ⊙ ↔ γ • u ∈ Cᵒ⊙ := by
  -- Rewrite both sides into the textbook pointwise inequality form.
  rw [mem_polarSet_iff_forall_inner_le_one, mem_polarSet_iff_forall_inner_le_one]
  constructor
  · intro hu x hx
    -- Testing the left-hand condition at `γ • x` transfers the scalar to the second slot.
    have hsmul : γ • x ∈ γ • C := Set.smul_mem_smul_set hx
    simpa [real_inner_smul_left, real_inner_smul_right, mul_comm] using hu (γ • x) hsmul
  · intro hu y hy
    -- Every point of `γ • C` has the form `γ • x` with `x ∈ C`.
    rcases Set.mem_smul_set.mp hy with ⟨x, hx, rfl⟩
    simpa [real_inner_smul_left, real_inner_smul_right, mul_comm] using hu x hx

-- Proof sketch: prove both inclusions by rewriting membership with
-- the defining inequality of the local notation `Cᵒ⊙`; for `u ∈ (γ • C)ᵒ⊙`,
-- the condition `⟪γ • x, u⟫ ≤ 1` is equivalent to `⟪x, γ • u⟫ ≤ 1`, and
-- positivity of `γ` identifies `u ∈ γ⁻¹ • Cᵒ⊙`.
/-- Exercise 7.4: for a positive scalar `γ`, the polar set of the dilation `γ • C` is the dilation
of the polar set by the reciprocal scalar `γ⁻¹`. -/
theorem polarSet_smul_eq_inv_smul_polarSet
    (C : Set 𝓗) {γ : ℝ} (hγ : 0 < γ) :
    (γ • C)ᵒ⊙ = γ⁻¹ • Cᵒ⊙ := by
  ext u
  -- Route correction: finish at the membership level, then rewrite inverse-scalar membership.
  rw [Set.mem_inv_smul_set_iff₀ (ne_of_gt hγ)]
  -- The core equivalence is exactly the scalar-transfer helper above.
  exact mem_polarSet_smul_set_iff (C := C) (γ := γ)

/-! ### Theorem_7_4 (from Chap07) -/
universe u

open scoped InnerProductSpace

/-- A point `p` is a best approximation to `x` from `C` when it lies in `C` and realizes the
distance from `x` to `C`. -/
abbrev IsBestApproximation {X : Type u} [PseudoMetricSpace X] (x : X) (C : Set X) (p : X) : Prop :=
  p ∈ C ∧ dist x p = Metric.infDist x C

-- Proof sketch: unfold `IsBestApproximation`.
/-- A best approximation is exactly a point of `C` whose distance to `x` equals `Metric.infDist x
C`. -/
theorem isBestApproximation_iff_mem_and_dist_eq_infDist {X : Type u} [PseudoMetricSpace X]
    (x : X) (C : Set X) (p : X) :
    IsBestApproximation x C p ↔ p ∈ C ∧ dist x p = Metric.infDist x C :=
  Iff.rfl

/-- A set is Chebyshev when every point of the ambient space has a unique best approximation in
that set. -/
def IsChebyshev {X : Type u} [PseudoMetricSpace X] (C : Set X) : Prop :=
  ∀ x : X, ∃! p : X, IsBestApproximation x C p

-- Proof sketch: unfold `IsChebyshev`.
/-- A set is Chebyshev exactly when each point admits a unique best approximation from the set. -/
theorem isChebyshev_iff_forall_existsUnique_bestApproximation {X : Type u} [PseudoMetricSpace X]
    (C : Set X) :
    IsChebyshev C ↔ ∀ x : X, ∃! p : X, IsBestApproximation x C p :=
  Iff.rfl

/-- For a Chebyshev set, the projection point of `x` onto `C` is the unique best approximation in
the ambient space. -/
noncomputable def projectionPoint {X : Type u} [PseudoMetricSpace X] (C : Set X) (hC : IsChebyshev C)
    (x : X) : X :=
  (hC x).choose

-- Proof sketch: use the defining choice of `projectionPoint` from the unique best approximation
-- supplied by `hC x`.
/-- The chosen projection point is a best approximation. -/
theorem projectionPoint_isBestApproximation {X : Type u} [PseudoMetricSpace X] (C : Set X)
    (hC : IsChebyshev C) (x : X) :
    IsBestApproximation x C (projectionPoint C hC x) :=
  (hC x).choose_spec.1

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Theorem 7.4: a point of `C` whose norm distance realizes the subtype infimum is a
best approximation in the project API. -/
private theorem isBestApproximation_of_mem_and_norm_eq_iInf {C : Set 𝓗} {x p : 𝓗}
    (hpC : p ∈ C) (hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) : IsBestApproximation x C p := by
  -- Rewrite the metric distance to a set as the subtype infimum from the minimizer theorem.
  constructor
  · exact hpC
  rw [Metric.infDist_eq_iInf]
  simpa [dist_eq_norm] using hpmin

/-- Helper for Theorem 7.4: every point admits at least one best approximation in a nonempty
closed convex set. -/
private theorem exists_isBestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃ p : 𝓗, IsBestApproximation x C p := by
  intro x
  -- Apply the Hilbert projection theorem and translate its conclusion to `IsBestApproximation`.
  rcases exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x with
    ⟨p, hpC, hpmin⟩
  exact ⟨p, isBestApproximation_of_mem_and_norm_eq_iInf hpC hpmin⟩

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 7.4: convexity forces two best approximations to coincide. -/
private theorem eq_of_isBestApproximation_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C)
    {x p q : 𝓗}
    (hp : IsBestApproximation x C p) (hq : IsBestApproximation x C q) : p = q := by
  -- Rewrite both best-approximation statements to the minimizer equality used by the projection
  -- characterization theorem.
  have hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp.2
  have hqmin : ‖x - q‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hq.2
  have hp_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hpmin q hq.1
  have hq_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hq.1).mp hqmin p hp.1
  have hq_inner' : 0 ≤ ⟪x - q, q - p⟫_ℝ := by
    rw [show q - p = -(p - q) by abel, inner_neg_right]
    exact neg_nonneg.mpr hq_inner
  have hp_expand :
      ⟪x - p, q - p⟫_ℝ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
    calc
      ⟪x - p, q - p⟫_ℝ = ⟪(x - q) + (q - p), q - p⟫_ℝ := by
        congr 1
        abel
      _ = ⟪x - q, q - p⟫_ℝ + ⟪q - p, q - p⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, sq]
  have hpq_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rw [hp_expand] at hp_inner
    nlinarith
  have hpq_eq : q - p = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp <| le_antisymm hpq_sq (sq_nonneg ‖q - p‖)
  exact (sub_eq_zero.mp hpq_eq).symm

-- Proof sketch: this is the Hilbert-space projection theorem specialized to nonempty closed convex
-- sets.
/-- A nonempty closed convex subset of a complete real Hilbert space is Chebyshev. -/
theorem isChebyshev_of_nonempty_isClosed_convex {𝓗 : Type u} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    IsChebyshev C := by
  -- Combine the Hilbert projection theorem for existence with the convex minimizer uniqueness.
  intro x
  rcases exists_isBestApproximation_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex x with
    ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (eq_of_isBestApproximation_of_convex hC_convex hp hq).symm

/-- The `EReal`-valued supremum of the functional `x ↦ ⟪x, u⟫` on `C`. -/
noncomputable abbrev innerSupremumOn {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (C : Set 𝓗) (u : 𝓗) : EReal :=
  sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

-- Proof sketch: unfold `innerSupremumOn`.
/-- The inner-product supremum on `C` is the supremum of the image of `C` under `x ↦ ⟪x, u⟫`. -/
theorem innerSupremumOn_eq_sSup_image {𝓗 : Type u} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℝ 𝓗] (C : Set 𝓗) (u : 𝓗) :
    innerSupremumOn C u = sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) :=
  rfl

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- The support points of `C` are the points of `C` at which some nonzero direction attains the
support value of `C`. -/
noncomputable def supportPoints (C : Set 𝓗) : Set 𝓗 :=
  {x : 𝓗 | x ∈ C ∧ ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u = (⟪x, u⟫_ℝ : EReal)}

-- Proof sketch: unfold `supportPoints` and simplify the resulting membership statement.
/-- A point belongs to `supportPoints C` exactly when it lies in `C` and some nonzero direction
attains the support value of `C` at that point. -/
theorem mem_supportPoints_iff {C : Set 𝓗} {x : 𝓗} :
    x ∈ supportPoints C ↔ x ∈ C ∧ ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u = (⟪x, u⟫_ℝ : EReal) :=
  Iff.rfl

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Helper for Theorem 7.4: in a convex set, best approximations are exactly the points satisfying
the standard variational inequality. -/
theorem isBestApproximation_iff_mem_and_inner_sub_right_nonpos (hC_convex : Convex ℝ C)
    {x p : 𝓗} :
    IsBestApproximation x C p ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  -- Rewrite the metric equality to the minimizer statement packaged by mathlib's projection
  -- characterization.
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · intro hp
    rw [dist_eq_norm, Metric.infDist_eq_iInf] at hp
    simp_rw [dist_eq_norm] at hp
    have hinner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hp.2
    refine ⟨hp.1, ?_⟩
    intro y hy
    simpa [real_inner_comm] using hinner y hy
  · intro hp
    refine ⟨hp.1, ?_⟩
    rw [dist_eq_norm, Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    refine (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mpr ?_
    intro y hy
    simpa [real_inner_comm] using hp.2 y hy

/-- Helper for Theorem 7.4: the metric projection onto `C` is characterized by the same
variational inequality. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos {y p : 𝓗} :
    p = P y ↔ p ∈ C ∧ ∀ z ∈ C, ⟪z - p, y - p⟫_ℝ ≤ 0 := by
  -- Reduce the projection statement to the best-approximation characterization proved above.
  constructor
  · intro hp
    exact
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos
        (hC_convex := hC_convex) (C := C) (x := y) (p := p)).mp <|
        by
          simpa [hp] using
            projectionPoint_isBestApproximation C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
  · intro hp
    have hp_best : IsBestApproximation y C p :=
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos
        (hC_convex := hC_convex) (C := C) (x := y) (p := p)).mpr hp
    exact
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex y).unique hp_best
        (projectionPoint_isBestApproximation C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y)

/-- Helper for Theorem 7.4: a support point is exactly a point of `C` admitting a nonzero support
direction with nonpositive translated inner products on all of `C`. -/
theorem mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos {x : 𝓗} :
    x ∈ supportPoints C ↔ x ∈ C ∧ ∃ u : 𝓗, u ≠ 0 ∧ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
  -- Rewrite the support-value equality into pointwise upper bounds and use `x ∈ C` for the
  -- reverse inequality.
  rw [mem_supportPoints_iff]
  constructor
  · rintro ⟨hxC, u, hu_ne, hu_eq⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    intro y hy
    have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
      rw [innerSupremumOn_eq_sSup_image]
      exact le_sSup ⟨y, hy, rfl⟩
    have hyx_le : (⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal) := by
      simpa [hu_eq] using hy_le
    have hyx_le' : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
      exact_mod_cast hyx_le
    simpa [inner_sub_left] using sub_nonpos.mpr hyx_le'
  · rintro ⟨hxC, u, hu_ne, hu_nonpos⟩
    refine ⟨hxC, u, hu_ne, le_antisymm ?_ ?_⟩
    · -- The pointwise support inequalities make `⟪x, u⟫` an upper bound for the image set.
      rw [innerSupremumOn_eq_sSup_image]
      refine (isLUB_sSup _).2 ?_
      rintro _ ⟨y, hy, rfl⟩
      have hyx_le : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
        have := hu_nonpos y hy
        simpa [inner_sub_left] using this
      exact show ((⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal)) by
        exact_mod_cast hyx_le
    · -- Membership of `x` in `C` gives the reverse inequality by definition of the supremum.
      rw [innerSupremumOn_eq_sSup_image]
      exact le_sSup ⟨x, hxC, rfl⟩

/-- Helper for Theorem 7.4: every support point lies on the frontier of the ambient set. -/
theorem supportPoints_subset_frontier :
    supportPoints C ⊆ frontier C := by
  intro x hx
  rcases
      (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
        (C := C)).mp hx with
    ⟨hxC, u, hu_ne, hu_nonpos⟩
  rw [mem_frontier_iff_notMem_interior hxC]
  intro hx_int
  -- An interior point would admit a short outward step staying inside `C`, contradicting the
  -- support inequality in the witness direction.
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx_int) with ⟨ε, hε_pos, hball_subset⟩
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  let t : ℝ := ε / (2 * ‖u‖)
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hy_ball : x + t • u ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(x + t • u) - x‖ = ‖t • u‖ := by
        rw [add_sub_cancel_left]
      _ = |t| * ‖u‖ := norm_smul t u
      _ = t * ‖u‖ := by
        rw [abs_of_pos ht_pos]
      _ = ε / 2 := by
        dsimp [t]
        field_simp [hu_norm_pos.ne']
      _ < ε := by
        linarith
  have hyC : x + t • u ∈ C := hball_subset hy_ball
  have hnonpos : ⟪(x + t • u) - x, u⟫_ℝ ≤ 0 := hu_nonpos (x + t • u) hyC
  have hrewrite : ⟪(x + t • u) - x, u⟫_ℝ = t * ‖u‖ ^ (2 : ℕ) := by
    calc
      ⟪(x + t • u) - x, u⟫_ℝ = ⟪t • u, u⟫_ℝ := by
        congr 1
        abel_nf
      _ = t * ⟪u, u⟫_ℝ := by
        rw [real_inner_smul_left]
      _ = t * ‖u‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hnonpos
  have hpositive : 0 < t * ‖u‖ ^ (2 : ℕ) := by
    refine mul_pos ht_pos ?_
    exact pow_pos hu_norm_pos 2
  linarith

/-- Helper for Theorem 7.4: projection onto `C` does not increase the distance to a point already
in `C`. -/
theorem norm_projectionPoint_sub_le_norm_sub_of_mem (y z : 𝓗) (hz : z ∈ C) :
    ‖P y - z‖ ≤ ‖y - z‖ := by
  have hp :
      P y ∈ C ∧ ∀ w ∈ C, ⟪w - P y, y - P y⟫_ℝ ≤ 0 :=
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
      (y := y) (p := P y)).mp rfl
  have hinner_nonneg : 0 ≤ ⟪P y - z, y - P y⟫_ℝ := by
    have hz_nonpos : ⟪z - P y, y - P y⟫_ℝ ≤ 0 := hp.2 z hz
    have hneg :
        ⟪z - P y, y - P y⟫_ℝ = -⟪P y - z, y - P y⟫_ℝ := by
      rw [show z - P y = -(P y - z) by abel_nf, inner_neg_left]
    linarith
  have hsplit :
      ⟪P y - z, y - z⟫_ℝ = ‖P y - z‖ ^ (2 : ℕ) + ⟪P y - z, y - P y⟫_ℝ := by
    calc
      ⟪P y - z, y - z⟫_ℝ = ⟪P y - z, (y - P y) + (P y - z)⟫_ℝ := by
        congr 1
        abel_nf
      _ = ⟪P y - z, y - P y⟫_ℝ + ⟪P y - z, P y - z⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪P y - z, y - P y⟫_ℝ + ‖P y - z‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
      _ = ‖P y - z‖ ^ (2 : ℕ) + ⟪P y - z, y - P y⟫_ℝ := by
        ring
  have hsq_le_inner : ‖P y - z‖ ^ (2 : ℕ) ≤ ⟪P y - z, y - z⟫_ℝ := by
    rw [hsplit]
    nlinarith
  have hsq_le : ‖P y - z‖ ^ (2 : ℕ) ≤ ‖P y - z‖ * ‖y - z‖ := by
    exact le_trans hsq_le_inner (real_inner_le_norm _ _)
  by_cases hzero : ‖P y - z‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖P y - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    rw [pow_two] at hsq_le
    nlinarith

-- Proof sketch: for `x ∈ supportPoints C`, use Proposition 7.3 to obtain a nonzero normal
-- vector `u ∈ N[C] x \ {0}`. Proposition 6.47 then identifies `x` as the metric projection of
-- `x + u`, and `u ≠ 0` ensures `x + u ∉ C`. Conversely, if `x = P y` with `y ∉ C`, then the
-- residual `y - x` is a nonzero normal vector at `x`, so Proposition 7.3 gives `x ∈ supportPoints
-- C`.
/-- Theorem 7.4 (1): Bishop--Phelps. For a nonempty closed convex subset `C` of a real Hilbert
space, the support points of `C` are exactly the metric projections of points outside `C`,
formalized as `supportPoints C = P '' Cᶜ`. -/
theorem supportPoints_eq_projectionPoint_image_compl :
    supportPoints C = P '' Cᶜ := by
  ext x
  constructor
  · intro hx
    rcases
        (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
          (C := C)).mp hx with
      ⟨hxC, u, hu_ne, hu_nonpos⟩
    -- Move in the support direction to produce an exterior point whose projection is `x`.
    refine ⟨x + u, ?_, ?_⟩
    · intro hxuC
      have hnonpos : ⟪(x + u) - x, u⟫_ℝ ≤ 0 := hu_nonpos (x + u) hxuC
      have hrewrite : ⟪(x + u) - x, u⟫_ℝ = ‖u‖ ^ (2 : ℕ) := by
        calc
          ⟪(x + u) - x, u⟫_ℝ = ⟪u, u⟫_ℝ := by
            congr 1
            abel_nf
          _ = ‖u‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
      rw [hrewrite] at hnonpos
      have hpositive : 0 < ‖u‖ ^ (2 : ℕ) := by
        exact pow_pos (norm_pos_iff.mpr hu_ne) 2
      linarith
    · have hx_proj : x = P (x + u) := by
        refine
          (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
            (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
            (y := x + u) (p := x)).mpr ?_
        refine ⟨hxC, ?_⟩
        intro z hz
        have hz_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := hu_nonpos z hz
        simpa using hz_nonpos
      simpa using hx_proj.symm
  · rintro ⟨y, hy_out, hy_proj⟩
    have hx_proj : x = P y := by
      simpa using hy_proj.symm
    have hproj :
        x ∈ C ∧ ∀ z ∈ C, ⟪z - x, y - x⟫_ℝ ≤ 0 :=
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (y := y) (p := x)).mp hx_proj
    have hyx_ne : y - x ≠ 0 := by
      intro hyx_zero
      have hy_eq : y = x := sub_eq_zero.mp hyx_zero
      exact hy_out (hy_eq.symm ▸ hproj.1)
    -- The projection residual is a nonzero support direction at `x`.
    exact
      (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
        (C := C)).mpr
        ⟨hproj.1, y - x, hyx_ne, hproj.2⟩

-- Proof sketch: the first clause shows that every support point is the projection of some point
-- outside `C`, hence lies on `frontier C`; this gives `closure (supportPoints C) ⊆ frontier C`.
-- For the reverse inclusion, approximate a boundary point by points of `Cᶜ`, project them onto
-- `C`, apply the first clause to land in `supportPoints C`, and use nonexpansiveness of the metric
-- projection to pass to the limit.
/-- Theorem 7.4 (2): Bishop--Phelps. The closure of the support points of a nonempty closed convex
subset `C` of a real Hilbert space is the boundary of `C`, formalized as
`closure (supportPoints C) = frontier C`. -/
theorem closure_supportPoints_eq_frontier (hC_nonempty' : C.Nonempty) (hC_closed' : IsClosed C)
    (hC_convex' : Convex ℝ C) :
    closure (supportPoints C) = frontier C := by
  let P' :=
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty' hC_closed' hC_convex')
  apply Subset.antisymm
  · -- The frontier is closed, so the support-point inclusion upgrades to their closure.
    exact
      closure_minimal
        (supportPoints_subset_frontier (C := C))
        isClosed_frontier
  · intro z hz
    rw [frontier_eq_closure_inter_closure] at hz
    have hzC : z ∈ C := by
      simpa [IsClosed.closure_eq hC_closed'] using hz.1
    -- Approximate the boundary point by exterior points and project them back onto `C`.
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases Metric.mem_closure_iff.1 hz.2 ε hε with ⟨y, hy_out, hy_dist⟩
    let p := P' y
    have hp_support : p ∈ supportPoints C := by
      rw [supportPoints_eq_projectionPoint_image_compl
        (hC_nonempty := hC_nonempty') (hC_closed := hC_closed') (hC_convex := hC_convex')]
      exact ⟨y, hy_out, rfl⟩
    have hp_dist : ‖p - z‖ < ε := by
      have hproj_le :
          ‖P' y - z‖ ≤ ‖y - z‖ :=
        norm_projectionPoint_sub_le_norm_sub_of_mem
          (hC_nonempty := hC_nonempty') (hC_closed := hC_closed') (hC_convex := hC_convex') y z hzC
      have hy_norm_lt : ‖y - z‖ < ε := by
        simpa [dist_eq_norm, norm_sub_rev] using hy_dist
      exact lt_of_le_of_lt hproj_le hy_norm_lt
    exact ⟨p, hp_support, by simpa [p, dist_eq_norm, norm_sub_rev] using hp_dist⟩

end

end Set
