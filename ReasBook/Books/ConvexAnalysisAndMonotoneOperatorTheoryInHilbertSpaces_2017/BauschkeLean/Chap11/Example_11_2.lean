import Mathlib
import BauschkeLean.Chap06.Definition_6_48
import BauschkeLean.Chap06.Proposition_6_49
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap07.Proposition_7_13
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap10.Definition_10_1
import BauschkeLean.Chap10.Proposition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 11.2: the support function is the supremum over the subtype indexing `C`. -/
lemma supportFunction_eq_iSup_subtype
    (C : Set H) :
    σ[C] = fun u : H ↦ ⨆ x : C, ((⟪(x : H), u⟫_ℝ : ℝ) : EReal) := by
  -- Replace the image over `C` by the range of the same functional on the subtype.
  funext u
  rw [supportFunction_eq_sSup_image]
  have himage :
      (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' C =
        Set.range (fun x : C ↦ ((⟪(x : H), u⟫_ℝ : ℝ) : EReal)) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [himage, sSup_range]

/-- Helper for Example 11.2: every continuous linear inner functional belongs to `Γ(H)`. -/
lemma inner_functional_mem_gamma
    (x : H) :
    (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ∈ gamma H := by
  -- Unpack `Γ(H)` into Jensen convexity and lower semicontinuity for the fixed inner functional.
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro u v a ha0 ha1
    -- The Jensen inequality is an equality because the inner product is linear in the second slot.
    have hinner :
        ⟪x, a • u + (1 - a) • v⟫_ℝ =
          a * ⟪x, u⟫_ℝ + (1 - a) * ⟪x, v⟫_ℝ := by
      simp [inner_add_right, inner_smul_right]
    change (((⟪x, a • u + (1 - a) • v⟫_ℝ : ℝ) : EReal)) ≤
      (a : EReal) * ((⟪x, u⟫_ℝ : ℝ) : EReal) +
        (((1 - a : ℝ) : EReal) * ((⟪x, v⟫_ℝ : ℝ) : EReal))
    rw [hinner, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  · -- Continuity of the real inner functional lifts to lower semicontinuity
    -- after coercion to `EReal`.
    simpa using
      (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)).lowerSemicontinuous

/-- Helper for Example 11.2: the support function is the supremum of inner functionals in
`Γ(H)`, hence itself belongs to `Γ(H)`. -/
lemma supportFunction_mem_gamma
    (C : Set H) :
    σ[C] ∈ gamma H := by
  -- Rewrite the support function as a subtype-indexed supremum and apply Proposition 9.3.
  rw [supportFunction_eq_iSup_subtype]
  exact iSup_mem_gamma
    (fun x : C ↦ fun u : H ↦ ((⟪(x : H), u⟫_ℝ : ℝ) : EReal))
    (fun x ↦ inner_functional_mem_gamma (x : H))

/-- Helper for Example 11.2: the support function is positively homogeneous. -/
lemma supportFunction_positivelyHomogeneous
    (C : Set H) :
    PositivelyHomogeneous (σ[C]) := by
  intro a ha u
  -- Evaluate the Chapter 7 scaling identity at the chosen vector `u`.
  simpa [Function.comp, EReal.real_smul_def] using
    congrFun (supportFunction_comp_pos_smul_eq_mul_supportFunction (C := C) ha) u

/-- Helper for Example 11.2: a uniform norm bound on `C` yields the corresponding support-function
bound. -/
lemma supportFunction_le_mul_norm_of_norm_bound
    (C : Set H) {R : ℝ} (_hR : 0 ≤ R) (hC_norm : ∀ x ∈ C, ‖x‖ ≤ R) :
    ∀ u : H, σ[C] u ≤ ((R * ‖u‖ : ℝ) : EReal) := by
  intro u
  -- Bound each inner product term by Cauchy-Schwarz and then take the supremum.
  rw [supportFunction_eq_sSup_image]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hinner_le : ⟪x, u⟫_ℝ ≤ R * ‖u‖ := by
    calc
      ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hC_norm x hx) (norm_nonneg u)
  change (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ ((R * ‖u‖ : ℝ) : EReal)
  exact_mod_cast hinner_le

-- Proof sketch: the support function is positively homogeneous by its supremum definition and
-- convex by the usual support-function inequality.
/-- Example 11.2 (1): for a nonempty subset `C`, the support function `σ[C]` is sublinear. -/
theorem example_11_2_1_supportFunction_sublinear
    (C : Set H) (hC_nonempty : C.Nonempty) :
    Sublinear (σ[C]) := by
  let f : H → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)
  -- Repackage the proper support function into `]-∞,+∞]` and use Proposition 10.3.
  have hph : PositivelyHomogeneous (fun x : H ↦ (f x : EReal)) := by
    simpa [f] using supportFunction_positivelyHomogeneous C
  have hconv : IsConvex (fun x : H ↦ (f x : EReal)) := by
    simpa [f] using (mem_gamma_iff (σ[C])).mp (supportFunction_mem_gamma C) |>.1
  -- The convexity and positive homogeneity of the packaged function are exactly sublinearity.
  simpa [f] using
    (sublinear_iff_isConvex_of_positivelyHomogeneous f hph).2 hconv

-- Proof sketch: the support function is lower semicontinuous, convex on its effective domain, and
-- proper when `C` is nonempty, so its canonical Chapter 9 representative lies in `Γ₀(H)`.
/-- Example 11.2 (2): for a nonempty subset `C`, the canonical `]-∞,+∞]`-valued representative
of the support function belongs to `Γ₀(H)`. -/
theorem example_11_2_2_supportFunction_mem_gammaZero
    (C : Set H) (hC_nonempty : C.Nonempty) :
    properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty) ∈ Γ₀(H) := by
  -- Upgrade the raw `Γ(H)` membership of the support function through its proper repackaging.
  exact properIoi_mem_gammaZero_of_mem_gamma
    (isProper_supportFunction_of_nonempty C hC_nonempty)
    (supportFunction_mem_gamma C)

-- Proof sketch: compose the Chapter 7 owner equalities for convex-hull and closure invariance.
/-- Example 11.2 (3): the support function only depends on the closed convex hull of `C`. -/
theorem example_11_2_3_supportFunction_eq_closure_convexHull
    (C : Set H) :
    σ[C] = σ[closure (convexHull ℝ C)] := by
  rcases supportFunction_eq_convexHull_and_closure_convexHull C with ⟨hconv, hclosure⟩
  exact hconv.trans hclosure

-- Proof sketch: membership in `dom` is finiteness of the support value, which is the definition of
-- the barrier cone.
/-- Example 11.2 (4): the domain of the support function is the barrier cone of the closed convex
hull. -/
theorem example_11_2_4_dom_supportFunction_eq_barrierCone
    (C : Set H) :
    dom (σ[C]) = bar (closure (convexHull ℝ C)) := by
  ext u
  rw [mem_dom_iff, Set.mem_barrierCone_iff,
    example_11_2_3_supportFunction_eq_closure_convexHull C]

-- Proof sketch: boundedness makes the barrier cone of `closure (convexHull ℝ C)` equal to the
-- whole space, while nonemptiness rules out the value `⊥`.
/-- Example 11.2 (5): if `C` is bounded and nonempty, then the support function is real-valued on
`H`. -/
theorem example_11_2_5_supportFunction_realValued_of_bounded
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ∀ u : H, σ[C] u ∈ Set.Ioo (⊥ : EReal) ⊤ := by
  intro u
  refine ⟨bot_lt_supportFunction_of_nonempty C hC_nonempty u, ?_⟩
  have hu : u ∈ bar C := by
    rw [Set.barrierCone_eq_univ_of_bounded hC_bounded]
    simp
  exact Set.mem_barrierCone_iff.mp hu

-- Proof sketch: boundedness gives full finite domain, and the full-domain `Γ₀` continuity theorem
-- gives continuity of the real representative.
/-- Example 11.2 (6): if `C` is bounded and nonempty, then the real-valued support function is
continuous on `H`. -/
theorem example_11_2_6_supportFunction_continuous_of_bounded
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    Continuous (fun u : H ↦ (σ[C] u).toReal) := by
  rcases hC_bounded.subset_ball (0 : H) with ⟨R, hRball⟩
  rcases hC_nonempty with ⟨x₀, hx₀⟩
  have hx₀_ball : x₀ ∈ Metric.ball (0 : H) R := hRball hx₀
  have hR_pos : 0 < R := by
    have hx₀_lt : ‖x₀‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx₀_ball
    exact lt_of_le_of_lt (norm_nonneg x₀) hx₀_lt
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hC_norm : ∀ x ∈ C, ‖x‖ ≤ R := by
    intro x hx
    have hx_ball : x ∈ Metric.ball (0 : H) R := hRball hx
    have hx_lt : ‖x‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx_ball
    exact hx_lt.le
  have hdom : ∀ w : H, w ∈ dom (σ[C]) := by
    intro w
    exact (example_11_2_5_supportFunction_realValued_of_bounded C ⟨x₀, hx₀⟩ hC_bounded w).2
  have hfinite : ∀ w : H, σ[C] w ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    intro w
    exact example_11_2_5_supportFunction_realValued_of_bounded C ⟨x₀, hx₀⟩ hC_bounded w
  have hsubadd :
      Subadditive (σ[C]) :=
    (example_11_2_1_supportFunction_sublinear C ⟨x₀, hx₀⟩).subadditive
  have hbound :
      ∀ w : H, σ[C] w ≤ ((R * ‖w‖ : ℝ) : EReal) :=
    supportFunction_le_mul_norm_of_norm_bound C hR_nonneg hC_norm
  have hdist :
      ∀ u v : H,
        dist ((σ[C] u).toReal) ((σ[C] v).toReal) ≤ R * dist u v := by
    intro u v
    have hu : σ[C] u ∈ Set.Ioo (⊥ : EReal) ⊤ := hfinite u
    have hv : σ[C] v ∈ Set.Ioo (⊥ : EReal) ⊤ := hfinite v
    have huv : σ[C] (u - v) ∈ Set.Ioo (⊥ : EReal) ⊤ := hfinite (u - v)
    have hvu : σ[C] (v - u) ∈ Set.Ioo (⊥ : EReal) ⊤ := hfinite (v - u)
    have hu_bot : σ[C] u ≠ ⊥ := ne_of_gt hu.1
    have hu_top : σ[C] u ≠ ⊤ := ne_of_lt hu.2
    have hv_bot : σ[C] v ≠ ⊥ := ne_of_gt hv.1
    have hv_top : σ[C] v ≠ ⊤ := ne_of_lt hv.2
    have huv_top : σ[C] (u - v) ≠ ⊤ := ne_of_lt huv.2
    have huv_bot : σ[C] (u - v) ≠ ⊥ := ne_of_gt huv.1
    have hvu_top : σ[C] (v - u) ≠ ⊤ := ne_of_lt hvu.2
    have hvu_bot : σ[C] (v - u) ≠ ⊥ := ne_of_gt hvu.1
    have hu_le :
        σ[C] u ≤ σ[C] v + σ[C] (u - v) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hsubadd.map_add_le (hdom v) (hdom (u - v))
    have hv_le :
        σ[C] v ≤ σ[C] u + σ[C] (v - u) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hsubadd.map_add_le (hdom u) (hdom (v - u))
    have hu_real :
        (σ[C] u).toReal ≤ (σ[C] v).toReal + (σ[C] (u - v)).toReal := by
      have hu_sum_top : σ[C] v + σ[C] (u - v) ≠ ⊤ := by
        rw [← EReal.coe_toReal hv_top hv_bot, ← EReal.coe_toReal huv_top huv_bot,
          ← EReal.coe_add]
        exact EReal.coe_ne_top _
      simpa [EReal.toReal_add hv_top hv_bot huv_top huv_bot] using
        EReal.toReal_le_toReal hu_le hu_bot hu_sum_top
    have hv_real :
        (σ[C] v).toReal ≤ (σ[C] u).toReal + (σ[C] (v - u)).toReal := by
      have hv_sum_top : σ[C] u + σ[C] (v - u) ≠ ⊤ := by
        rw [← EReal.coe_toReal hu_top hu_bot, ← EReal.coe_toReal hvu_top hvu_bot,
          ← EReal.coe_add]
        exact EReal.coe_ne_top _
      simpa [EReal.toReal_add hu_top hu_bot hvu_top hvu_bot] using
        EReal.toReal_le_toReal hv_le hv_bot hv_sum_top
    have huv_real :
        (σ[C] (u - v)).toReal ≤ R * ‖u - v‖ := by
      simpa using EReal.toReal_le_toReal (hbound (u - v)) huv_bot (EReal.coe_ne_top _)
    have hvu_real :
        (σ[C] (v - u)).toReal ≤ R * ‖u - v‖ := by
      have hnorm : ‖v - u‖ = ‖u - v‖ := by
        simpa [sub_eq_add_neg, add_comm] using norm_neg (u - v)
      simpa [hnorm] using
        EReal.toReal_le_toReal (hbound (v - u)) hvu_bot (EReal.coe_ne_top _)
    have hupper : (σ[C] u).toReal - (σ[C] v).toReal ≤ R * ‖u - v‖ := by
      linarith
    have hlower : -(R * ‖u - v‖) ≤ (σ[C] u).toReal - (σ[C] v).toReal := by
      linarith
    have habs :
        |(σ[C] u).toReal - (σ[C] v).toReal| ≤ R * ‖u - v‖ :=
      abs_le.mpr ⟨hlower, hupper⟩
    simpa [Real.dist_eq, dist_eq_norm] using habs
  have hLip :
      LipschitzWith ⟨R, hR_nonneg⟩ (fun u : H ↦ (σ[C] u).toReal) :=
    LipschitzWith.of_dist_le_mul hdist
  -- A global Lipschitz estimate gives continuity of the real-valued support function.
  exact hLip.continuous

end ERealFunction
