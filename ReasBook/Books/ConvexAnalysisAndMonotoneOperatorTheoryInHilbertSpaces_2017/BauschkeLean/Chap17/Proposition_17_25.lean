import Mathlib
import BauschkeLean.Chap02.Corollary_2_15
import BauschkeLean.Chap01.Definition_1_7
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap07.Proposition_7_11
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap10.Proposition_10_8
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Corollary_11_30
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap17.Proposition_17_21

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction Filter
open scoped InnerProductSpace Pointwise

universe u

noncomputable section

variable {H : Type u} [NormedAddCommGroup H]

private def chebyshevCenterSqDist (x : H) : H → EReal :=
  fun y ↦ ((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- Helper for Proposition 17 25: for a fixed base point `x`, the squared-distance owner
`r ↦ ‖x - r‖²` is continuous as an `EReal`-valued function. -/
theorem continuous_chebyshevCenterSqDist (x : H) : Continuous (chebyshevCenterSqDist x) := by
  -- Expand the owner as the composition of subtraction, norm, squaring, and the continuous
  -- coercion from `ℝ` to `EReal`.
  have hcont_real : Continuous fun r : H ↦ ‖x - r‖ ^ (2 : ℕ) := by
    simpa using
      ((((continuous_const : Continuous fun _ : H ↦ x).sub continuous_id).norm.pow (2 : ℕ)))
  simpa [chebyshevCenterSqDist] using continuous_coe_real_ereal.comp hcont_real

/-- Helper for Proposition 17 25: for a fixed point `r`, the squared-distance owner
`x ↦ ‖x - r‖²` is continuous as an `EReal`-valued function. -/
theorem continuous_chebyshevCenterSqDist_left (r : H) :
    Continuous fun x : H ↦ chebyshevCenterSqDist x r := by
  -- Expand the owner as the composition of subtraction in the first slot, norm, squaring, and
  -- the continuous coercion from `ℝ` to `EReal`.
  have hcont_real : Continuous fun x : H ↦ ‖x - r‖ ^ (2 : ℕ) := by
    simpa using
      ((((continuous_id : Continuous fun x : H ↦ x).sub continuous_const).norm.pow (2 : ℕ)))
  simpa [chebyshevCenterSqDist] using continuous_coe_real_ereal.comp hcont_real

/-- The Chebyshev-center objective of a nonempty subset `C` is the canonical `]-∞,+∞]`-valued
supremum of the squared distances from `x` to points of `C`. -/
noncomputable def chebyshevCenterObjective (C : Set H) (hC_nonempty : C.Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ by
    refine ⟨sSup (chebyshevCenterSqDist x '' C), ?_⟩
    rcases hC_nonempty with ⟨y, hy⟩
    exact lt_of_lt_of_le (EReal.bot_lt_coe _) <| (isLUB_sSup _).1 ⟨y, hy, rfl⟩

/-- Expanding the Chebyshev-center objective gives the supremum of the squared-distance image. -/
@[simp] theorem chebyshevCenterObjective_eq_sSup_sqDist
    (C : Set H) (hC_nonempty : C.Nonempty) (x : H) :
    (chebyshevCenterObjective C hC_nonempty x : EReal) = sSup (chebyshevCenterSqDist x '' C) :=
  rfl

/-- The active farthest-point map for the Chebyshev-center objective sends `x` to the points of
`C` that attain the supremal squared distance from `x`. -/
def chebyshevCenterActiveSet (C : Set H) : SetValuedOperator H H :=
  fun x ↦ {r | r ∈ C ∧ IsMaxOn (chebyshevCenterSqDist x) C r}

notation "Φ[" C "]" => chebyshevCenterActiveSet C

variable {C : Set H}

/-- Helper for Proposition 17 25: the Chebyshev-center objective is the supremum over the subtype
of points of `C`, rather than over the image set of squared distances. -/
theorem chebyshevCenterObjective_eq_iSup_sqDist_subtype
    (C : Set H) (hC_nonempty : C.Nonempty) (x : H) :
    (chebyshevCenterObjective C hC_nonempty x : EReal) =
      ⨆ r : C, chebyshevCenterSqDist x r := by
  -- Reindex the image supremum by the subtype `C`; this is the canonical owner form for later
  -- compact-attainment and convexity arguments.
  rw [chebyshevCenterObjective_eq_sSup_sqDist, sSup_image']

/-- Helper for Proposition 17 25: boundedness of `C` makes the Chebyshev-center objective finite
at every base point. -/
theorem chebyshevCenterObjective_lt_top_of_bounded
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (x : H) :
    (chebyshevCenterObjective C hC_nonempty x : EReal) < ⊤ := by
  rcases hC_nonempty with ⟨y, hy⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hC_bounded
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg y) (hR y hy)
  have hbound :
      ∀ z ∈ C, chebyshevCenterSqDist x z ≤ (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal) := by
    intro z hz
    have hzR : ‖z‖ ≤ R := hR z hz
    have hnorm : ‖x - z‖ ≤ ‖x‖ + R := by
      calc
        ‖x - z‖ ≤ ‖x‖ + ‖z‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x z
        _ ≤ ‖x‖ + R := by
          linarith
    have hsq :
        (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤ (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal) := by
      exact_mod_cast
        (show ‖x - z‖ ^ (2 : ℕ) ≤ (‖x‖ + R) ^ (2 : ℕ) by
          have hsum_nonneg : 0 ≤ ‖x‖ + R := add_nonneg (norm_nonneg _) hR_nonneg
          nlinarith [hnorm, norm_nonneg (x - z), hsum_nonneg])
    simpa [chebyshevCenterSqDist] using hsq
  have hsSup_le :
      sSup (chebyshevCenterSqDist x '' C) ≤ (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z hz
  rw [chebyshevCenterObjective_eq_sSup_sqDist]
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top _)

/-- A point belongs to the active farthest-point set exactly when it lies in `C` and realizes the
Chebyshev-center objective at `x`. -/
@[simp] theorem mem_chebyshevCenterActiveSet_iff
    (C : Set H) (hC_nonempty : C.Nonempty) (x r : H) :
    r ∈ Φ[C] x ↔
      r ∈ C ∧
        (((‖x - r‖ ^ (2 : ℕ) : ℝ) : EReal) = chebyshevCenterObjective C hC_nonempty x) := by
  constructor
  · rintro ⟨hrC, hrmax⟩
    -- An active point is, by definition, a maximizer of the squared-distance owner on `C`.
    have hr_eq :
        chebyshevCenterSqDist x r = (chebyshevCenterObjective C hC_nonempty x : EReal) := by
      rw [ERealFunction.eq_sSup_image_of_isMaxOn hrC hrmax]
      exact (chebyshevCenterObjective_eq_sSup_sqDist C hC_nonempty x).symm
    exact ⟨hrC, by simpa [chebyshevCenterSqDist] using hr_eq⟩
  · rintro ⟨hrC, hrEq⟩
    refine ⟨hrC, ?_⟩
    -- Conversely, realizing the objective means the squared-distance value is the supremum, hence
    -- `r` is a maximizer on `C`.
    rw [isMaxOn_iff]
    intro y hyC
    have hy_le :
        chebyshevCenterSqDist x y ≤ sSup (chebyshevCenterSqDist x '' C) :=
      (ERealFunction.isLUB_sSup_image (chebyshevCenterSqDist x) C).1 (Set.mem_image_of_mem _ hyC)
    have hr_eq :
        chebyshevCenterSqDist x r = sSup (chebyshevCenterSqDist x '' C) := by
      simpa [chebyshevCenterSqDist, chebyshevCenterObjective_eq_sSup_sqDist] using hrEq
    simpa [hr_eq] using hy_le

/-- Helper for Proposition 17 25: the graph of the active farthest-point map is the carrier-level
set where the squared distance attains the Chebyshev-center objective. -/
theorem graph_chebyshevCenterActiveSet_eq_level_set
    (C : Set H) (hC_nonempty : C.Nonempty) :
    ((Φ[C]).graph) =
      {p : H × H |
        p.2 ∈ C ∧
          (((‖p.1 - p.2‖ ^ (2 : ℕ) : ℝ) : EReal) =
            chebyshevCenterObjective C hC_nonempty p.1)} := by
  ext p
  -- Unfold the graph owner and rewrite the active-point condition with the explicit attainment
  -- criterion from `mem_chebyshevCenterActiveSet_iff`.
  simpa [SetValuedOperator.graph] using
    (mem_chebyshevCenterActiveSet_iff C hC_nonempty p.1 p.2)

/-- Helper for Proposition 17 25: compactness lets the pointwise squared-distance family vary
continuously through its supremum over `C`. -/
theorem continuous_maxValue_sqdist_of_compact
    (C : Set H) (hCcompact : IsCompact C) :
    Continuous fun x : H ↦ sSup (chebyshevCenterSqDist x '' C) := by
  have hcont_pair : Continuous fun p : H × H ↦ chebyshevCenterSqDist p.1 p.2 := by
    -- View the owner on `H × H`; it is continuous because subtraction, norm, squaring, and the
    -- real-to-`EReal` coercion are continuous.
    have hcont_real : Continuous fun p : H × H ↦ ‖p.1 - p.2‖ ^ (2 : ℕ) := by
      simpa using (((continuous_fst.sub continuous_snd).norm.pow (2 : ℕ)))
    simpa [chebyshevCenterSqDist] using continuous_coe_real_ereal.comp hcont_real
  -- The compact-supremum theorem packages the source proof's "continuous family + compact index
  -- set implies continuous maximum-value map" step.
  simpa [Function.uncurry] using
    hCcompact.continuous_sSup (f := chebyshevCenterSqDist) hcont_pair

/-- Helper for Proposition 17 25: the subtype-indexed supremum representation is lower
semicontinuous because each squared-distance owner is continuous in the base point. -/
theorem chebyshevCenterObjective_lowerSemicontinuous
    (C : Set H) (hC_nonempty : C.Nonempty) :
    LowerSemicontinuous (fun x : H ↦ (chebyshevCenterObjective C hC_nonempty x : EReal)) := by
  -- Rewrite the objective into the subtype-indexed `iSup`, then invoke the standard
  -- lower-semicontinuity theorem for pointwise suprema.
  have hiSup_lsc :
      LowerSemicontinuous fun x : H ↦ ⨆ r : C, chebyshevCenterSqDist x r := by
    refine lowerSemicontinuous_iSup ?_
    intro r
    exact (continuous_chebyshevCenterSqDist_left (r : H)).lowerSemicontinuous
  convert hiSup_lsc using 1
  ext x
  exact chebyshevCenterObjective_eq_iSup_sqDist_subtype C hC_nonempty x

-- Proof sketch: compactness makes the squared-distance map attain its supremum on `C`, and the
-- maximum-value function of the continuous family `(x, y) ↦ ‖x - y‖²` varies continuously with
-- `x`.
/-- Proposition 17 25 (1): clause (i). For a nonempty compact set, the finite real representative
of the Chebyshev-center objective is continuous. -/
theorem continuous_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) :
    Continuous fun x ↦ (chebyshevCenterObjective C hC_nonempty x : EReal).toReal := by
  have hcont_obj : Continuous fun x : H ↦ (chebyshevCenterObjective C hC_nonempty x : EReal) := by
    -- Rewrite the objective to the compact supremum owner already handled above.
    simpa [chebyshevCenterObjective_eq_sSup_sqDist] using
      continuous_maxValue_sqdist_of_compact (C := C) hCcompact
  rw [continuous_iff_continuousAt]
  intro x
  have hobj_top :
      (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊤ := by
    exact
      (chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hCcompact.isBounded x).ne
  have hobj_bot :
      (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊥ :=
    ne_of_gt (chebyshevCenterObjective C hC_nonempty x).2
  -- Compose the continuous `EReal` owner with `toReal`, which is continuous on finite `EReal`
  -- values.
  exact (EReal.tendsto_toReal hobj_top hobj_bot).comp hcont_obj.continuousAt

section InnerProduct

variable [InnerProductSpace ℝ H]

/-- Helper for Proposition 17 25: translating the affine-combination norm identity by a base point
`r` gives the textbook squared-distance formula. -/
theorem sqdist_affine_combination_identity
    (x y r : H) (α : ℝ) :
    ‖((α • x + (1 - α) • y) - r)‖ ^ (2 : ℕ) + α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) =
      α * ‖x - r‖ ^ (2 : ℕ) + (1 - α) * ‖y - r‖ ^ (2 : ℕ) := by
  have htranslate :
      α • (x - r) + (1 - α) • (y - r) = (α • x + (1 - α) • y) - r := by
    rw [smul_sub, smul_sub]
    calc
      α • x - α • r + ((1 - α) • y - (1 - α) • r)
          = α • x + (1 - α) • y - (α • r + (1 - α) • r) := by
            abel
      _ = (α • x + (1 - α) • y) - r := by
            rw [← add_smul, show α + (1 - α) = (1 : ℝ) by ring, one_smul]
  -- Route correction: keep the source proof's translated-quadratic identity explicit instead of
  -- hiding the common Jensen gap inside later coercion manipulations.
  simpa [htranslate] using
    norm_sq_affine_combination_add_weighted_norm_sub_sq (x - r) (y - r) α

/-- Helper for Proposition 17 25: boundedness makes the finite real bridge of the objective satisfy
the common Jensen-gap estimate from the translated quadratic identity. -/
theorem chebyshevCenterObjective_toReal_jensen_bound
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (x y : H)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (chebyshevCenterObjective C hC_nonempty (α • x + (1 - α) • y) : EReal).toReal +
        α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) ≤
      α * (chebyshevCenterObjective C hC_nonempty x : EReal).toReal +
        (1 - α) * (chebyshevCenterObjective C hC_nonempty y : EReal).toReal := by
  let z : H := α • x + (1 - α) • y
  let gap : ℝ := α * (1 - α) * ‖x - y‖ ^ (2 : ℕ)
  have hz_top :
      (chebyshevCenterObjective C hC_nonempty z : EReal) < ⊤ :=
    chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded z
  have hx_top :
      (chebyshevCenterObjective C hC_nonempty x : EReal) < ⊤ :=
    chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded x
  have hy_top :
      (chebyshevCenterObjective C hC_nonempty y : EReal) < ⊤ :=
    chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded y
  have hz_bot : (chebyshevCenterObjective C hC_nonempty z : EReal) ≠ ⊥ :=
    ne_of_gt (chebyshevCenterObjective C hC_nonempty z).2
  have hx_bot : (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊥ :=
    ne_of_gt (chebyshevCenterObjective C hC_nonempty x).2
  have hy_bot : (chebyshevCenterObjective C hC_nonempty y : EReal) ≠ ⊥ :=
    ne_of_gt (chebyshevCenterObjective C hC_nonempty y).2
  have hiSup_bound :
      (⨆ r : C, chebyshevCenterSqDist z r + ((gap : ℝ) : EReal)) ≤
        (α : EReal) * (⨆ r : C, chebyshevCenterSqDist x r) +
          ((1 - α : ℝ) : EReal) * (⨆ r : C, chebyshevCenterSqDist y r) := by
    calc
      (⨆ r : C, chebyshevCenterSqDist z r + ((gap : ℝ) : EReal))
          = ⨆ r : C,
              (α : EReal) * chebyshevCenterSqDist x r +
                ((1 - α : ℝ) : EReal) * chebyshevCenterSqDist y r := by
              refine iSup_congr fun r ↦ ?_
              -- Coerce the pointwise real identity into `EReal` before taking the supremum.
              exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) <|
                sqdist_affine_combination_identity x y (r : H) α
      _ ≤ (α : EReal) * (⨆ r : C, chebyshevCenterSqDist x r) +
            ((1 - α : ℝ) : EReal) * (⨆ r : C, chebyshevCenterSqDist y r) :=
          weighted_iSup_le_weighted_iSup hα0 (sub_nonneg.mpr hα1)
  have hE :
      (chebyshevCenterObjective C hC_nonempty z : EReal) + ((gap : ℝ) : EReal) ≤
        (α : EReal) * (chebyshevCenterObjective C hC_nonempty x : EReal) +
          ((1 - α : ℝ) : EReal) * (chebyshevCenterObjective C hC_nonempty y : EReal) := by
    -- Move the finite real Jensen gap through the subtype-indexed supremum, then rewrite the two
    -- remaining suprema back to the objective owner.
    rw [chebyshevCenterObjective_eq_iSup_sqDist_subtype,
      ← ereal_iSup_add_of_real_shift gap (fun r : C ↦ chebyshevCenterSqDist z r),
      chebyshevCenterObjective_eq_iSup_sqDist_subtype,
      chebyshevCenterObjective_eq_iSup_sqDist_subtype]
    exact hiSup_bound
  have hαE_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0
  have h1αE_nonneg : 0 ≤ (1 - α : EReal) := by
    exact_mod_cast sub_nonneg.mpr hα1
  have hmulx_ne_top :
      (α : EReal) * (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hαE_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hx_top.ne⟩
  have hmuly_ne_top :
      ((1 - α : ℝ) : EReal) * (chebyshevCenterObjective C hC_nonempty y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1αE_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hy_top.ne⟩
  have hmulx_ne_bot :
      (α : EReal) * (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊥ := by
    rw [EReal.mul_ne_bot]
    exact ⟨Or.inl (EReal.coe_ne_bot α), Or.inr hx_bot, Or.inl (EReal.coe_ne_top α),
      Or.inl hαE_nonneg⟩
  have hmuly_ne_bot :
      ((1 - α : ℝ) : EReal) * (chebyshevCenterObjective C hC_nonempty y : EReal) ≠ ⊥ := by
    rw [EReal.mul_ne_bot]
    exact ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inr hy_bot,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inl h1αE_nonneg⟩
  have hE_real :
      ((chebyshevCenterObjective C hC_nonempty z : EReal) + ((gap : ℝ) : EReal)).toReal ≤
        ((α : EReal) * (chebyshevCenterObjective C hC_nonempty x : EReal) +
          ((1 - α : ℝ) : EReal) * (chebyshevCenterObjective C hC_nonempty y : EReal)).toReal :=
    EReal.toReal_le_toReal hE
      ((EReal.add_ne_bot_iff).2 ⟨hz_bot, EReal.coe_ne_bot gap⟩)
      (EReal.add_ne_top hmulx_ne_top hmuly_ne_top)
  -- Rewrite the two finite `EReal` sums through `toReal`.
  rw [EReal.toReal_add hz_top.ne hz_bot (EReal.coe_ne_top gap) (EReal.coe_ne_bot gap),
    EReal.toReal_add hmulx_ne_top hmulx_ne_bot hmuly_ne_top hmuly_ne_bot] at hE_real
  simpa [gap, z, EReal.toReal_mul] using hE_real

/-- Helper for Proposition 17 25: boundedness turns the real-valued bridge of the objective into a
strongly convex function on the whole space. -/
theorem chebyshevCenterObjective_strongConvexOn_univ
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    StrongConvexOn (Set.univ : Set H) (2 : ℝ)
      (fun x ↦ (chebyshevCenterObjective C hC_nonempty x : EReal).toReal) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  have ha_le_one : a ≤ 1 := by linarith
  have hjensen :=
    chebyshevCenterObjective_toReal_jensen_bound
      (C := C) hC_nonempty hC_bounded x y ha ha_le_one
  -- Repackage the Jensen-gap inequality into mathlib's `StrongConvexOn` format.
  have hineq :
      (chebyshevCenterObjective C hC_nonempty (a • x + (1 - a) • y) : EReal).toReal ≤
        a * (chebyshevCenterObjective C hC_nonempty x : EReal).toReal +
          (1 - a) * (chebyshevCenterObjective C hC_nonempty y : EReal).toReal -
            a * (1 - a) * ((2 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
    linarith
  simpa [smul_eq_mul] using hineq

-- The next three clauses concern only the objective owner `chebyshevCenterObjective`; unlike the
-- active-set layer below, they do not require compactness or pointwise farthest-point attainment.
-- Proof sketch: write the objective as `x ↦ sup_{y ∈ C} (‖x - y‖²)`. Every function
-- `x ↦ ‖x - y‖²` is strongly convex with constant `2`, and the pointwise supremum of functions
-- with the same strong-convexity modulus preserves that modulus. Boundedness keeps the supremum
-- finite everywhere, so the canonical owner has nonempty effective domain.
/-- Proposition 17.25 (2): clause (i). For a nonempty bounded set, the Chebyshev-center objective
is strongly convex with constant `2`. -/
theorem stronglyConvex_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ERealFunction.StronglyConvex (chebyshevCenterObjective C hC_nonempty) 2 := by
  have hC_nonempty' := hC_nonempty
  have hdom_nonempty : (effectiveDomain (chebyshevCenterObjective C hC_nonempty)).Nonempty := by
    rcases hC_nonempty' with ⟨x, _hxC⟩
    refine ⟨x, ?_⟩
    rw [mem_effectiveDomain_iff]
    exact chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded x
  have hdom_eq :
      effectiveDomain (chebyshevCenterObjective C hC_nonempty) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rw [mem_effectiveDomain_iff]
      exact chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded x
  -- Route correction: first prove strong convexity of the finite real bridge on `Set.univ`, then
  -- transfer it back to the canonical `]-∞,+∞]`-valued owner through the effective-domain bridge.
  exact StrongConvexOn.toStronglyConvex_effectiveDomain
    (by
      simpa [hdom_eq] using
        chebyshevCenterObjective_strongConvexOn_univ
          (C := C) hC_nonempty hC_bounded)
    (by norm_num) hdom_nonempty

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 17 25: if `‖x‖` dominates `2 ‖y‖`, then the squared distance from `x`
to `y` has the textbook quadratic lower bound `‖x‖ (‖x‖ - 2 ‖y‖)`. -/
theorem sqdist_quadratic_lower_bound_of_norm_large
    (x y : H) (hxy : 2 * ‖y‖ ≤ ‖x‖) :
    ‖x‖ * (‖x‖ - 2 * ‖y‖) ≤ ‖x - y‖ ^ (2 : ℕ) := by
  have hnorm_sub_le : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
    have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖(x - y) + y‖ := by
          congr 1
          abel
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le (x - y) y
    linarith
  have hnorm_sub_nonneg : 0 ≤ ‖x‖ - ‖y‖ := by
    linarith [norm_nonneg y, hxy]
  have hsq :
      (‖x‖ - ‖y‖) ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
    nlinarith [hnorm_sub_le, hnorm_sub_nonneg, norm_nonneg (x - y)]
  nlinarith [hsq, sq_nonneg ‖y‖]

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 17 25: once `‖x‖` is positive and dominates `2 ‖y‖`, the normalized
Chebyshev-center objective is bounded below by `‖x‖ - 2 ‖y‖` using the single witness `y ∈ C`. -/
theorem chebyshevCenterObjective_div_norm_lower_bound_of_mem
    (hC_nonempty : C.Nonempty) {y : H} (hy : y ∈ C) {x : H}
    (hx_norm : (1 : ℝ) ≤ ‖x‖) (hxy : 2 * ‖y‖ ≤ ‖x‖) :
    (((‖x‖ - 2 * ‖y‖ : ℝ) : EReal) ≤
      (chebyshevCenterObjective C hC_nonempty x : EReal) / ‖x‖) := by
  have hsq_le :
      (((‖x‖ * (‖x‖ - 2 * ‖y‖) : ℝ) : EReal)) ≤
        chebyshevCenterSqDist x y := by
    -- The single witness `y` gives the quadratic lower bound on the objective numerator.
    have hcast :
        (((‖x‖ * (‖x‖ - 2 * ‖y‖) : ℝ) : EReal)) ≤
          (((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
      exact_mod_cast sqdist_quadratic_lower_bound_of_norm_large x y hxy
    simpa [chebyshevCenterSqDist] using hcast
  have hobj_ge :
      chebyshevCenterSqDist x y ≤ (chebyshevCenterObjective C hC_nonempty x : EReal) := by
    rw [chebyshevCenterObjective_eq_sSup_sqDist]
    exact (isLUB_sSup _).1 ⟨y, hy, rfl⟩
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hx_norm
  have hmul_le :
      ((((‖x‖ - 2 * ‖y‖ : ℝ) : EReal) * ‖x‖)) ≤
        (chebyshevCenterObjective C hC_nonempty x : EReal) := by
    -- Repackage the quadratic lower bound in the form expected by `EReal.le_div_iff_mul_le`.
    calc
      (((‖x‖ - 2 * ‖y‖ : ℝ) : EReal) * ‖x‖) =
          (((‖x‖ * (‖x‖ - 2 * ‖y‖) : ℝ) : EReal)) := by
            rw [← EReal.coe_mul]
            congr 1
            ring
      _ ≤ chebyshevCenterSqDist x y := hsq_le
      _ ≤ (chebyshevCenterObjective C hC_nonempty x : EReal) := hobj_ge
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

-- Proof sketch: the previous clause gives strong convexity with constant `2`, and the objective is
-- lower semicontinuous as a pointwise supremum of continuous squared-distance functions; Corollary
-- 11.17 then turns that strong convexity into supercoercivity.
omit [InnerProductSpace ℝ H] in
/-- Proposition 17.25 (3): clause (i). For a nonempty bounded set, the Chebyshev-center objective
is supercoercive. -/
theorem supercoercive_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ERealFunction.Supercoercive (chebyshevCenterObjective C hC_nonempty).asEReal := by
  let _ := hC_bounded
  rw [ERealFunction.Supercoercive, EReal.tendsto_nhds_top_iff_real]
  rcases hC_nonempty with ⟨y, hy⟩
  intro ξ
  let R : ℝ := max 1 (max (2 * ‖y‖) (ξ + 2 * ‖y‖ + 1))
  have htail :
      ∀ᶠ x in Bornology.cobounded H, R ≤ ‖x‖ := by
    simpa [R] using
      (eventually_cobounded_le_norm R :
        ∀ᶠ x in Bornology.cobounded H, R ≤ ‖x‖)
  filter_upwards [htail] with x hx
  have hR_one : (1 : ℝ) ≤ R := le_max_left _ _
  have hR_y : 2 * ‖y‖ ≤ R := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hR_ξ : ξ + 2 * ‖y‖ + 1 ≤ R := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hx_norm : (1 : ℝ) ≤ ‖x‖ := le_trans hR_one hx
  have hxy : 2 * ‖y‖ ≤ ‖x‖ := le_trans hR_y hx
  have hξ_lt :
      ξ < ‖x‖ - 2 * ‖y‖ := by
    linarith
  have hlower :
      (((‖x‖ - 2 * ‖y‖ : ℝ) : EReal) ≤
        (chebyshevCenterObjective C ⟨y, hy⟩ x : EReal) / ‖x‖) :=
    chebyshevCenterObjective_div_norm_lower_bound_of_mem
      (C := C) ⟨y, hy⟩ hy hx_norm hxy
  exact lt_of_lt_of_le (by exact_mod_cast hξ_lt) hlower

end InnerProduct

-- Proof sketch: for each `x`, compactness of `C` makes the squared-distance function attain its
-- maximum, so `Φ[C] x` is nonempty.
/-- Proposition 17.25 (4): clause (ii). The active farthest-point map is defined at every point of
the ambient space. -/
theorem dom_chebyshevCenterActiveSet_eq_univ
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) :
    (Φ[C]).dom = Set.univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    rw [SetValuedOperator.mem_dom_iff]
    -- Compactness gives a maximizer of the squared-distance owner on `C` for each base point `x`.
    obtain ⟨r, hrC, hrmax⟩ :=
      hCcompact.exists_isMaxOn hC_nonempty (continuous_chebyshevCenterSqDist x).continuousOn
    exact ⟨r, hrC, hrmax⟩

-- Proof sketch: if `(xₙ, rₙ) → (x, r)` with each `rₙ ∈ Φ[C] xₙ`, then compactness makes `C`
-- closed, so `r ∈ C`; continuity of the objective and of the squared norm then passes the
-- equality `‖xₙ - rₙ‖² = chebyshevCenterObjective C xₙ` to the limit.
/-- Proposition 17.25 (5): clause (ii). The graph of the active farthest-point map is closed. -/
theorem isClosed_graph_chebyshevCenterActiveSet
    (hCcompact : IsCompact C) :
    IsClosed ((Φ[C]).graph) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hC_nonempty
  · -- If `C` is empty, then the graph is empty because every value fiber is empty.
    simp [SetValuedOperator.graph, chebyshevCenterActiveSet]
  · have hC_bounded : Bornology.IsBounded C := hCcompact.isBounded
    have hclosed_carrier : IsClosed {p : H × H | p.2 ∈ C} :=
      hCcompact.isClosed.preimage continuous_snd
    have hclosed_level :
        IsClosed
          {p : H × H |
            ‖p.1 - p.2‖ ^ (2 : ℕ) =
              (chebyshevCenterObjective C hC_nonempty p.1 : EReal).toReal} := by
      -- Route correction: rewrite the graph with the real-valued objective so closedness reduces
      -- to equality of two continuous real-valued functions on `H × H`.
      refine isClosed_eq ?_ ?_
      · simpa using
          (((continuous_fst : Continuous fun p : H × H ↦ p.1).sub continuous_snd).norm.pow
            (2 : ℕ))
      · exact (continuous_chebyshevCenterObjective (C := C) hC_nonempty hCcompact).comp
          continuous_fst
    have hgraph :
        ((Φ[C]).graph) =
          {p : H × H | p.2 ∈ C} ∩
            {p : H × H |
              ‖p.1 - p.2‖ ^ (2 : ℕ) =
                (chebyshevCenterObjective C hC_nonempty p.1 : EReal).toReal} := by
      ext p
      constructor
      · intro hp
        rcases (mem_chebyshevCenterActiveSet_iff C hC_nonempty p.1 p.2).1 hp with ⟨hpC, hpEq⟩
        refine ⟨hpC, ?_⟩
        simpa using congrArg EReal.toReal hpEq
      · rintro ⟨hpC, hpEq⟩
        have hobj_top :
            (chebyshevCenterObjective C hC_nonempty p.1 : EReal) < ⊤ :=
          chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hC_bounded p.1
        have hpEqEReal :
            (((‖p.1 - p.2‖ ^ (2 : ℕ) : ℝ) : EReal) =
              chebyshevCenterObjective C hC_nonempty p.1) := by
          rw [← EReal.coe_toReal
              (show (((‖p.1 - p.2‖ ^ (2 : ℕ) : ℝ) : EReal)) ≠ ⊤ by
                exact EReal.coe_ne_top _)
              (show (((‖p.1 - p.2‖ ^ (2 : ℕ) : ℝ) : EReal)) ≠ ⊥ by
                exact EReal.coe_ne_bot _),
            ← EReal.coe_toReal hobj_top.ne
              (ne_of_gt (chebyshevCenterObjective C hC_nonempty p.1).2)]
          exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hpEq
        exact (mem_chebyshevCenterActiveSet_iff C hC_nonempty p.1 p.2).2 ⟨hpC, hpEqEReal⟩
    rw [hgraph]
    exact hclosed_carrier.inter hclosed_level

-- Proof sketch: each value `Φ[C] x` is a closed subset of the compact set `C`, hence compact.
/-- Proposition 17.25 (6): clause (ii). Every active farthest-point value set is compact. -/
theorem isCompact_chebyshevCenterActiveSet_value
    (hCcompact : IsCompact C) (x : H) :
    IsCompact (Φ[C] x) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hC_nonempty
  · -- If `C` is empty, every active-value fiber is empty as well.
    simp [chebyshevCenterActiveSet]
  · -- For nonempty `C`, the active fiber is a closed level set inside the compact carrier `C`.
    have hclosed_level :
        IsClosed {r : H | chebyshevCenterSqDist x r =
          (chebyshevCenterObjective C hC_nonempty x : EReal)} :=
      isClosed_singleton.preimage (continuous_chebyshevCenterSqDist x)
    have hset :
        Φ[C] x =
          C ∩ {r : H | chebyshevCenterSqDist x r =
            (chebyshevCenterObjective C hC_nonempty x : EReal)} := by
      ext r
      -- The active-set owner is exactly membership in `C` together with objective attainment.
      constructor
      · intro hr
        rcases (mem_chebyshevCenterActiveSet_iff C hC_nonempty x r).1 hr with ⟨hrC, hrEq⟩
        exact ⟨hrC, by simpa [chebyshevCenterSqDist] using hrEq⟩
      · rintro ⟨hrC, hrEq⟩
        exact (mem_chebyshevCenterActiveSet_iff C hC_nonempty x r).2
          ⟨hrC, by simpa [chebyshevCenterSqDist] using hrEq⟩
    rw [hset]
    exact hCcompact.inter_right hclosed_level

section InnerProduct

variable [InnerProductSpace ℝ H]

/-- Helper for Proposition 17 25: the support function of the pointwise scaled active
displacement set is the supremum of the corresponding active-point pairings. -/
theorem supportFunction_activeDisplacements_eq_iSup_active_pairing
    (C : Set H) (x z : H) :
    σ[(2 : ℝ) • (({x} : Set H) - Φ[C] x)] z =
      ⨆ r : Φ[C] x, (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal)) := by
  have hset :
      (2 : ℝ) • (({x} : Set H) - Φ[C] x) =
        (fun r : H ↦ (2 : ℝ) • (x - r)) '' Φ[C] x := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_smul_set.mp hy with ⟨u, hu, rfl⟩
      rcases Set.mem_sub.mp hu with ⟨x', hx', r, hr, hxr⟩
      have hx' : x' = x := Set.mem_singleton_iff.mp hx'
      subst x'
      exact ⟨r, hr, by simp [hxr]⟩
    · rintro ⟨r, hr, rfl⟩
      refine Set.mem_smul_set.mpr ?_
      refine ⟨x - r, Set.mem_sub.mpr ?_, rfl⟩
      exact ⟨x, by simp, r, hr, rfl⟩
  have himage :
      (fun y : H ↦ (⟪y, z⟫_ℝ : EReal)) '' ((2 : ℝ) • (({x} : Set H) - Φ[C] x)) =
        Set.range (fun r : Φ[C] x ↦ (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal))) := by
    rw [hset]
    ext t
    constructor
    · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨⟨r, hr⟩, by simp [real_inner_smul_left, mul_comm]⟩
    · rintro ⟨r, rfl⟩
      refine ⟨(2 : ℝ) • (x - (r : H)), ?_, ?_⟩
      · exact ⟨(r : H), r.2, rfl⟩
      · simp [real_inner_smul_left, mul_comm]
  change sSup ((fun y : H ↦ (⟪y, z⟫_ℝ : EReal)) '' ((2 : ℝ) • (({x} : Set H) - Φ[C] x))) =
    ⨆ r : Φ[C] x, (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal))
  rw [himage, sSup_range]

/-- Helper for Proposition 17 25: along a positive step `t`, the squared-distance secant quotient
at `x` in direction `z` has the explicit affine expansion `2⟪x - r, z⟫ + t ‖z‖²`. -/
theorem sqdist_secant_quotient_eq_two_inner_add_t_norm_sq
    (x r z : H) {t : ℝ} (ht : 0 < t) :
    (((chebyshevCenterSqDist (x + t • z) r) - chebyshevCenterSqDist x r) / t) =
      (((2 * ⟪x - r, z⟫_ℝ + t * ‖z‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  have hreal :
      ((‖(x + t • z) - r‖ ^ (2 : ℕ) - ‖x - r‖ ^ (2 : ℕ)) / t : ℝ) =
        2 * ⟪x - r, z⟫_ℝ + t * ‖z‖ ^ (2 : ℕ) := by
    have hexpand :
        ‖(x + t • z) - r‖ ^ (2 : ℕ) =
          ‖x - r‖ ^ (2 : ℕ) + 2 * ⟪x - r, t • z⟫_ℝ + ‖t • z‖ ^ (2 : ℕ) := by
      have hrewrite : (x + t • z) - r = (x - r) + t • z := by
        abel
      rw [hrewrite, norm_add_sq_real]
    calc
      ((‖(x + t • z) - r‖ ^ (2 : ℕ) - ‖x - r‖ ^ (2 : ℕ)) / t : ℝ)
          = ((2 * ⟪x - r, t • z⟫_ℝ + ‖t • z‖ ^ (2 : ℕ)) / t : ℝ) := by
              rw [hexpand]
              ring
      _ = 2 * ⟪x - r, z⟫_ℝ + t * ‖z‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le]
            field_simp [ht.ne']
  -- Rewrite the finite `EReal` secant quotient to the corresponding real quotient.
  rw [chebyshevCenterSqDist, chebyshevCenterSqDist, ← EReal.coe_sub, ← EReal.coe_div]
  exact congrArg (fun s : ℝ ↦ ((s : ℝ) : EReal)) hreal

/-- Helper for Proposition 17 25: a compactness subsequence of active farthest points along a
positive null step sequence converges to an active farthest point at the base point. -/
theorem exists_subseq_tendsto_active_limit_of_vanishing_steps
    (_hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) {x z : H}
    {t : ℕ → ℝ} (_ht_pos : ∀ n, 0 < t n) (ht_zero : Tendsto t atTop (nhds 0))
    {r : ℕ → H} (hr : ∀ n, r n ∈ Φ[C] (x + t n • z)) :
    ∃ rstar : H, rstar ∈ Φ[C] x ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ r (φ n)) atTop (nhds rstar) := by
  have hrC : ∀ n, r n ∈ C := by
    intro n
    exact (hr n).1
  have hseq : IsSeqCompact C := (isCompact_iff_isSeqCompact : IsCompact C ↔ IsSeqCompact C).1
    hCcompact
  obtain ⟨rstar, hrstarC, φ, hφ, hφt⟩ := hseq hrC
  have hbase :
      Tendsto (fun n ↦ x + t (φ n) • z) atTop (nhds x) := by
    have ht_subseq : Tendsto (fun n ↦ t (φ n)) atTop (nhds 0) :=
      ht_zero.comp hφ.tendsto_atTop
    have hcont : Continuous fun s : ℝ ↦ x + s • z := by
      simpa using continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hcont.tendsto 0).comp ht_subseq
  have hpair_tendsto :
      Tendsto (fun n ↦ (x + t (φ n) • z, r (φ n))) atTop (nhds (x, rstar)) :=
    hbase.prodMk_nhds hφt
  have hpair_mem : ∀ n, (x + t (φ n) • z, r (φ n)) ∈ ((Φ[C]).graph) := by
    intro n
    simpa [SetValuedOperator.graph] using hr (φ n)
  have hrstar_active : rstar ∈ Φ[C] x := by
    exact
      (isClosed_graph_chebyshevCenterActiveSet (C := C) hCcompact).mem_of_tendsto hpair_tendsto
        (Filter.Eventually.of_forall hpair_mem)
  exact ⟨rstar, hrstar_active, φ, hφ, hφt⟩

/-- Helper for Proposition 17 25: compactness upgrades the moving-maximizer secant estimate to the
global upper bound by an active pairing at the base point. -/
theorem directionalDerivative_le_iSup_active_pairing_of_compact
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x z : H) :
    (chebyshevCenterObjective C hC_nonempty)′(x; z) ≤
      ⨆ r : Φ[C] x, (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal)) := by
  classical
  let t : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have ht_pos : ∀ n, 0 < t n := by
    intro n
    dsimp [t]
    positivity
  have ht_zero : Tendsto t atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [t, Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hdom :
      ∀ n, ((Φ[C]) (x + t n • z)).Nonempty := by
    intro n
    have hxdom : x + t n • z ∈ (Φ[C]).dom := by
      rw [dom_chebyshevCenterActiveSet_eq_univ (C := C) hC_nonempty hCcompact]
      simp
    simpa [SetValuedOperator.mem_dom_iff] using hxdom
  let r : ℕ → H := fun n ↦ Classical.choose (hdom n)
  have hr : ∀ n, r n ∈ Φ[C] (x + t n • z) := by
    intro n
    exact Classical.choose_spec (hdom n)
  obtain ⟨rstar, hrstar, φ, hφ, hφt⟩ :=
    exists_subseq_tendsto_active_limit_of_vanishing_steps
      (C := C) hC_nonempty hCcompact ht_pos ht_zero hr
  have ht_subseq_zero : Tendsto (fun n ↦ t (φ n)) atTop (nhds 0) :=
    ht_zero.comp hφ.tendsto_atTop
  let d : EReal := (chebyshevCenterObjective C hC_nonempty)′(x; z)
  have hd_le_seq :
      ∀ n,
        d ≤ (((2 * ⟪x - r (φ n), z⟫_ℝ + t (φ n) * ‖z‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    intro n
    have htest :
        d ≤
          (((chebyshevCenterObjective C hC_nonempty (x + t (φ n) • z) : EReal) -
              (chebyshevCenterObjective C hC_nonempty x : EReal)) / t (φ n)) := by
      change (chebyshevCenterObjective C hC_nonempty)′(x; z) ≤
        (((chebyshevCenterObjective C hC_nonempty (x + t (φ n) • z) : EReal) -
            (chebyshevCenterObjective C hC_nonempty x : EReal)) / t (φ n))
      rw [ERealFunction.directionalDerivative]
      exact sInf_le ⟨⟨t (φ n), ht_pos (φ n)⟩, rfl⟩
    rcases
        (mem_chebyshevCenterActiveSet_iff C hC_nonempty (x + t (φ n) • z) (r (φ n))).1
          (hr (φ n)) with
      ⟨hrC, hrEq⟩
    have hobj_ge :
        chebyshevCenterSqDist x (r (φ n)) ≤ (chebyshevCenterObjective C hC_nonempty x : EReal) := by
      rw [chebyshevCenterObjective_eq_sSup_sqDist]
      exact (isLUB_sSup _).1 ⟨r (φ n), hrC, rfl⟩
    have hobj_x_top :
        (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊤ :=
      (chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hCcompact.isBounded x).ne
    have hobj_x_bot :
        (chebyshevCenterObjective C hC_nonempty x : EReal) ≠ ⊥ :=
      ne_of_gt (chebyshevCenterObjective C hC_nonempty x).2
    have hnum_le :
        ((chebyshevCenterObjective C hC_nonempty (x + t (φ n) • z) : EReal) -
            (chebyshevCenterObjective C hC_nonempty x : EReal)) ≤
          chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) -
            chebyshevCenterSqDist x (r (φ n)) := by
      refine (EReal.sub_le_iff_le_add (.inl hobj_x_bot) (.inl hobj_x_top)).2 ?_
      calc
        (chebyshevCenterObjective C hC_nonempty (x + t (φ n) • z) : EReal)
            = chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) := by
                simpa [chebyshevCenterSqDist] using hrEq.symm
        _ = (chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) -
              chebyshevCenterSqDist x (r (φ n))) + chebyshevCenterSqDist x (r (φ n)) := by
              simpa [chebyshevCenterSqDist] using
                (EReal.sub_add_cancel
                  (a := chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)))
                  (b := (‖x - r (φ n)‖ ^ (2 : ℕ) : ℝ))).symm
        _ ≤ (chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) -
              chebyshevCenterSqDist x (r (φ n))) +
            (chebyshevCenterObjective C hC_nonempty x : EReal) := by
              exact add_le_add_right hobj_ge _
    have hquot_le :
        (((chebyshevCenterObjective C hC_nonempty (x + t (φ n) • z) : EReal) -
            (chebyshevCenterObjective C hC_nonempty x : EReal)) / t (φ n)) ≤
          ((chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) -
              chebyshevCenterSqDist x (r (φ n))) / t (φ n)) := by
      exact EReal.div_le_div_right_of_nonneg
        (show (0 : EReal) ≤ (t (φ n) : EReal) by exact_mod_cast (ht_pos (φ n)).le) hnum_le
    have hsec :
        ((chebyshevCenterSqDist (x + t (φ n) • z) (r (φ n)) -
            chebyshevCenterSqDist x (r (φ n))) / t (φ n)) =
          (((2 * ⟪x - r (φ n), z⟫_ℝ + t (φ n) * ‖z‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
      simpa using
        sqdist_secant_quotient_eq_two_inner_add_t_norm_sq
          (x := x) (r := r (φ n)) (z := z) (ht := ht_pos (φ n))
    exact le_trans htest (by simpa [hsec] using hquot_le)
  have hreal_tendsto :
      Tendsto
        (fun n ↦ 2 * ⟪x - r (φ n), z⟫_ℝ + t (φ n) * ‖z‖ ^ (2 : ℕ))
        atTop (nhds (2 * ⟪x - rstar, z⟫_ℝ)) := by
    have hsub :
        Tendsto (fun n ↦ x - r (φ n)) atTop (nhds (x - rstar)) := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hφt
    have hinner :
        Tendsto (fun n ↦ ⟪x - r (φ n), z⟫_ℝ) atTop (nhds ⟪x - rstar, z⟫_ℝ) := by
      simpa using (continuous_id.inner continuous_const).tendsto (x - rstar) |>.comp hsub
    have htail :
        Tendsto (fun n ↦ t (φ n) * ‖z‖ ^ (2 : ℕ)) atTop (nhds (0 * ‖z‖ ^ (2 : ℕ))) := by
      exact ht_subseq_zero.mul tendsto_const_nhds
    have hmain := hinner.const_mul (2 : ℝ)
    simpa using hmain.add htail
  have hseq_tendsto :
      Tendsto
        (fun n ↦ (((2 * ⟪x - r (φ n), z⟫_ℝ + t (φ n) * ‖z‖ ^ (2 : ℕ) : ℝ) : EReal)))
        atTop (nhds (((2 * ⟪x - rstar, z⟫_ℝ : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.tendsto _ |>.comp hreal_tendsto
  have hd_le_star : d ≤ (((2 * ⟪x - rstar, z⟫_ℝ : ℝ) : EReal)) := by
    exact isClosed_Ici.mem_of_tendsto hseq_tendsto (Filter.Eventually.of_forall hd_le_seq)
  exact le_trans hd_le_star
    (le_iSup (fun r : Φ[C] x ↦ (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal))) ⟨rstar, hrstar⟩)

-- Proof sketch: for `r ∈ Φ[C] x`, the pointwise lower estimate comes from comparing the objective
-- at `x + t z` with the single witness `r`. For the reverse inequality, choose maximizers
-- `rₙ ∈ Φ[C] (x + tₙ z)` along a vanishing positive sequence `tₙ → 0`, extract a convergent
-- subsequence from compactness of `C`, and pass to the limit.
/-- Proposition 17.25 (7): clause (iii). The directional derivative of the Chebyshev-center
objective is the support function of the pointwise scaled active displacement set
`2 • ({x} - Φ[C] x)`, equivalently twice the maximal pairing with the active farthest-point
displacements. -/
theorem directionalDerivative_chebyshevCenterObjective_eq_supportFunction_activeDisplacements
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x z : H) :
    (chebyshevCenterObjective C hC_nonempty)′(x; z) =
      σ[(2 : ℝ) • (({x} : Set H) - Φ[C] x)] z := by
  refine le_antisymm ?_ ?_
  · rw [supportFunction_activeDisplacements_eq_iSup_active_pairing]
    exact directionalDerivative_le_iSup_active_pairing_of_compact
      (C := C) hC_nonempty hCcompact x z
  · rw [supportFunction_activeDisplacements_eq_iSup_active_pairing]
    refine iSup_le ?_
    intro r
    rw [ERealFunction.directionalDerivative]
    apply le_sInf
    rintro q ⟨α, rfl⟩
    rcases (mem_chebyshevCenterActiveSet_iff C hC_nonempty x (r : H)).1 r.2 with ⟨hrC, hrEq⟩
    have hsq_le_obj :
        chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) ≤
          (chebyshevCenterObjective C hC_nonempty (x + (α : ℝ) • z) : EReal) := by
      rw [chebyshevCenterObjective_eq_sSup_sqDist]
      exact (isLUB_sSup _).1 ⟨(r : H), hrC, rfl⟩
    have hnum_le :
        chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) - chebyshevCenterSqDist x (r : H) ≤
          (chebyshevCenterObjective C hC_nonempty (x + (α : ℝ) • z) : EReal) -
            (chebyshevCenterObjective C hC_nonempty x : EReal) := by
      have hrEq' :
          chebyshevCenterSqDist x (r : H) =
            (chebyshevCenterObjective C hC_nonempty x : EReal) := by
        simpa [chebyshevCenterSqDist] using hrEq
      rw [← hrEq']
      refine (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 ?_
      have hsec_eq :
          (chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) -
              chebyshevCenterSqDist x (r : H)) +
              (((‖x - (r : H)‖ ^ (2 : ℕ) : ℝ) : EReal)) =
            chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) := by
        simpa [chebyshevCenterSqDist] using
          (EReal.sub_add_cancel
            (a := chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H))
            (b := (‖x - (r : H)‖ ^ (2 : ℕ) : ℝ)))
      rw [hsec_eq]
      exact hsq_le_obj
    have hquot_le :
        ((chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) -
            chebyshevCenterSqDist x (r : H)) / α) ≤
          (((chebyshevCenterObjective C hC_nonempty (x + (α : ℝ) • z) : EReal) -
              (chebyshevCenterObjective C hC_nonempty x : EReal)) / α) := by
      exact EReal.div_le_div_right_of_nonneg
        (show (0 : EReal) ≤ (α : EReal) by exact_mod_cast α.2.le) hnum_le
    have hpair_le_sec :
        (((2 * ⟪x - (r : H), z⟫_ℝ : ℝ) : EReal)) ≤
          ((chebyshevCenterSqDist (x + (α : ℝ) • z) (r : H) -
              chebyshevCenterSqDist x (r : H)) / α) := by
      rw [sqdist_secant_quotient_eq_two_inner_add_t_norm_sq
        (x := x) (r := (r : H)) (z := z) (ht := α.2)]
      have hnonneg : 0 ≤ (α : ℝ) * ‖z‖ ^ (2 : ℕ) := by
        exact mul_nonneg α.2.le (sq_nonneg ‖z‖)
      exact_mod_cast le_add_of_nonneg_right hnonneg
    exact le_trans hpair_le_sec hquot_le

/-- Helper for Proposition 17 25: a subgradient at `x` bounds every positive directional
increment quotient from below by the corresponding inner product. -/
private theorem inner_le_increment_quotient_of_mem_subdifferential_local
    {f : H → Set.Ioi (⊥ : EReal)}
    {x u y : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    {α : ℝ} (hα : 0 < α) :
    (⟪y, u⟫_ℝ : EReal) ≤
      (((f (x + α • y) : EReal) - (f x : EReal)) / α) := by
  have huα :
      (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) ≤
        (f (x + α • y) : EReal) := by
    -- Evaluate the affine minorant inequality at the ray point `x + α • y`.
    simpa using (mem_subdifferential_iff f x u).1 hu (x + α • y)
  by_cases hxy : x + α • y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxy)
    have hxy_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from
        (f (x + α • y)).2)
    have huα_real :
        α * ⟪y, u⟫_ℝ + (f x : EReal).toReal ≤
          (f (x + α • y) : EReal).toReal := by
      -- On the finite branch, rewrite the `EReal` inequality as an ordinary real inequality.
      have hcast :
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
            (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
        calc
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
              = (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) := by
                  rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                  simp [real_inner_smul_left, EReal.coe_mul]
          _ ≤ (f (x + α • y) : EReal) := huα
          _ = (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hxy_top hxy_bot).symm
      exact_mod_cast hcast
    have hquot_real :
        ⟪y, u⟫_ℝ ≤
          ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α := by
      -- Divide the real inequality by the positive scalar `α`.
      refine (le_div_iff₀ hα).2 ?_
      linarith
    have hquot_cast :
        (⟪y, u⟫_ℝ : EReal) ≤
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      exact_mod_cast hquot_real
    have hquot_eq :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) =
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      -- Once both endpoint values are finite, the quotient is the cast of the real quotient.
      rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      simp
    rw [hquot_eq]
    exact hquot_cast
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hxy_top : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxy))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
    -- Outside the effective domain, the positive quotient is `⊤`, so the bound is automatic.
    rw [hxy_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    exact le_top

/-- Helper for Proposition 17 25: every subgradient yields a pointwise lower bound by the
directional derivative. -/
private theorem forall_inner_le_directionalDerivative_of_mem_subdifferential_local
    {f : H → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) := by
  let _ := hconv
  intro y
  rw [directionalDerivative]
  apply le_sInf
  rintro q ⟨α, rfl⟩
  -- Every positive directional difference quotient already dominates the inner product.
  simpa [directionalDifferenceQuotient] using
    inner_le_increment_quotient_of_mem_subdifferential_local
      (f := f) hx hu (α := (α : ℝ)) α.2

/-- Helper for Proposition 17 25: pointwise domination by the directional derivative recovers the
subgradient inequality at the base point. -/
private theorem mem_subdifferential_of_forall_inner_le_directionalDerivative_local
    {f : H → Set.Ioi (⊥ : EReal)} (_hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f)
    (hu : ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro z
  have hdir : (⟪z - x, u⟫_ℝ : EReal) ≤ f′(x; z - x) := hu (z - x)
  -- Evaluate the directional-derivative bound in the source direction `z - x`.
  calc
    (⟪z - x, u⟫_ℝ : EReal) + (f x : EReal) ≤
        f′(x; z - x) + (f x : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdir (f x : EReal)
    _ ≤ (f z : EReal) := directionalDerivative_add_value_le (f := f) hx z

/-- Helper for Proposition 17 25: clause (8) only needs the earlier Chapter 17 bridge from
subgradients to directional derivatives, not a later complete-space owner. -/
theorem mem_subdifferential_iff_inner_le_directionalDerivative_local
    {f : H → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔ ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) := by
  constructor
  · intro hu
    -- Convert subgradients to directional-derivative bounds through the positive quotient family.
    exact forall_inner_le_directionalDerivative_of_mem_subdifferential_local hconv hx hu
  · intro hu
    -- Recover the affine minorant inequality from the directional-derivative domination.
    exact mem_subdifferential_of_forall_inner_le_directionalDerivative_local hconv hx hu

/-- Helper for Proposition 17 25: clause (8) rewrites subgradient membership into the common
support-function inequalities for the active displacement set. -/
theorem mem_subdifferential_iff_forall_inner_le_supportFunction_activeDisplacements
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x u : H) :
    u ∈ (∂ (chebyshevCenterObjective C hC_nonempty)) x ↔
      ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ σ[(2 : ℝ) • (({x} : Set H) - Φ[C] x)] y := by
  have hconv :
      ConvexOn (chebyshevCenterObjective C hC_nonempty)
        (effectiveDomain (chebyshevCenterObjective C hC_nonempty)) := by
    exact (stronglyConvex_chebyshevCenterObjective
      (C := C) hC_nonempty hCcompact.isBounded).uniformlyConvex.convexOn
  have hx : x ∈ effectiveDomain (chebyshevCenterObjective C hC_nonempty) := by
    rw [mem_effectiveDomain_iff]
    exact chebyshevCenterObjective_lt_top_of_bounded C hC_nonempty hCcompact.isBounded x
  rw [mem_subdifferential_iff_inner_le_directionalDerivative_local hconv hx]
  constructor
  · intro hu y
    -- Clause (7) identifies the directional derivative with the support function of the active
    -- displacement set, so the generic subgradient criterion already has the desired shape.
    simpa [directionalDerivative_chebyshevCenterObjective_eq_supportFunction_activeDisplacements
      (C := C) hC_nonempty hCcompact x y] using hu y
  · intro hu y
    -- Rewriting the same clause (7) identity backwards recovers the directional-derivative bound.
    simpa [directionalDerivative_chebyshevCenterObjective_eq_supportFunction_activeDisplacements
      (C := C) hC_nonempty hCcompact x y] using hu y

/-- Helper for Proposition 17 25: the active displacement set is the image of the compact active
farthest-point fiber under the affine scaling map `r ↦ 2 • (x - r)`, hence compact. -/
theorem isCompact_activeDisplacements
    (hCcompact : IsCompact C) (x : H) :
    IsCompact ((2 : ℝ) • (({x} : Set H) - Φ[C] x)) := by
  have himage :
      (2 : ℝ) • (({x} : Set H) - Φ[C] x) =
        (fun r : H ↦ (2 : ℝ) • (x - r)) '' Φ[C] x := by
    -- Rewrite the displacement set as an explicit continuous image of the active fiber.
    ext y
    constructor
    · intro hy
      rcases Set.mem_smul_set.mp hy with ⟨u, hu, rfl⟩
      rcases Set.mem_sub.mp hu with ⟨x', hx', r, hr, hxr⟩
      have hx' : x' = x := Set.mem_singleton_iff.mp hx'
      subst x'
      exact ⟨r, hr, by simpa [hxr]⟩
    · rintro ⟨r, hr, rfl⟩
      refine Set.mem_smul_set.mpr ?_
      refine ⟨x - r, Set.mem_sub.mpr ?_, rfl⟩
      exact ⟨x, by simp, r, hr, rfl⟩
  rw [himage]
  -- Compactness is preserved under the continuous affine scaling map.
  exact (isCompact_chebyshevCenterActiveSet_value (C := C) hCcompact x).image
    ((continuous_const.sub continuous_id).const_smul (2 : ℝ))

/-- Helper for Proposition 17 25: coercing a set into the completion preserves support-function
values on directions coming from the original space. -/
theorem supportFunction_completion_image_coe
    (A : Set H) (y : H) :
    σ[((↑) : H → UniformSpace.Completion H) '' A] (y : UniformSpace.Completion H) = σ[A] y := by
  -- Expand both support functions as supremums of the same image set and rewrite the inner
  -- product through `Completion.inner_coe`.
  change
    sSup ((fun x : UniformSpace.Completion H ↦
      (⟪x, (y : UniformSpace.Completion H)⟫_ℝ : EReal)) '' (((↑) : H → UniformSpace.Completion H) '' A))
      =
    sSup ((fun x : H ↦ (⟪x, y⟫_ℝ : EReal)) '' A)
  congr 1
  ext t
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨a, ha, ?_⟩
    simpa using
      (show ((⟪(a : UniformSpace.Completion H), (y : UniformSpace.Completion H)⟫_ℝ : ℝ) : EReal) =
        ((⟪a, y⟫_ℝ : ℝ) : EReal) by rw [UniformSpace.Completion.inner_coe])
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(a : UniformSpace.Completion H), ⟨a, ha, rfl⟩, ?_⟩
    simpa using
      (show ((⟪(a : UniformSpace.Completion H), (y : UniformSpace.Completion H)⟫_ℝ : ℝ) : EReal) =
        ((⟪a, y⟫_ℝ : ℝ) : EReal) by rw [UniformSpace.Completion.inner_coe]).symm

/-- Helper for Proposition 17 25: closed convex hull membership is unchanged when a point and set
are coerced into the completion. -/
theorem mem_closedConvexHull_completion_image_iff
    (A : Set H) (u : H) :
    ((u : UniformSpace.Completion H) ∈
        closedConvexHull ℝ (((↑) : H → UniformSpace.Completion H) '' A)) ↔
      u ∈ closedConvexHull ℝ A := by
  -- Rewrite the completion hull as the closure of the image of `convexHull`, then pull closure
  -- membership back along the embedding `H ↪ Completion H`.
  rw [closedConvexHull_eq_closure_convexHull, closedConvexHull_eq_closure_convexHull]
  rw [show convexHull ℝ (((↑) : H → UniformSpace.Completion H) '' A) =
      ((↑) : H → UniformSpace.Completion H) '' convexHull ℝ A by
        simpa using
          (LinearMap.image_convexHull
            (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := H)).toLinearMap A).symm]
  have hEmbedding : Topology.IsEmbedding ((↑) : H → UniformSpace.Completion H) :=
    (UniformSpace.Completion.isDenseEmbedding_coe :
      IsDenseEmbedding ((↑) : H → UniformSpace.Completion H)).isEmbedding
  change (u : UniformSpace.Completion H) ∈
      closure (((↑) : H → UniformSpace.Completion H) '' convexHull ℝ A) ↔
        u ∈ closure (convexHull ℝ A)
  rw [hEmbedding.closure_eq_preimage_closure_image (convexHull ℝ A)]
  simp

/-- Helper for Proposition 17 25: support inequalities on `H` extend to the completion by closing
the `EReal`-valued predicate `z ↦ ((⟪u, z⟫ : ℝ) : EReal) ≤ σ[((↑) '' A)] z`. -/
theorem completion_support_inequality_of_dense_coe
    (A : Set H) (hA_nonempty : A.Nonempty) (hAcompact : IsCompact A) (u : H)
    (hineq : ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ σ[A] y) :
    ∀ z : UniformSpace.Completion H,
      (⟪(u : UniformSpace.Completion H), z⟫_ℝ : EReal) ≤
        σ[((↑) : H → UniformSpace.Completion H) '' A] z := by
  let A' : Set (UniformSpace.Completion H) := ((↑) : H → UniformSpace.Completion H) '' A
  have hA'_nonempty : A'.Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    exact ⟨(a : UniformSpace.Completion H), ⟨a, ha, rfl⟩⟩
  have hA'_compact : IsCompact A' := by
    simpa [A'] using hAcompact.image (UniformSpace.Completion.continuous_coe (α := H))
  have hσ'_cont : Continuous fun z : UniformSpace.Completion H ↦ σ[A'] z := by
    have hcont_pair :
        Continuous fun p : UniformSpace.Completion H × UniformSpace.Completion H ↦
          ((⟪p.2, p.1⟫_ℝ : ℝ) : EReal) := by
      -- The support owner is continuous in the direction and source variables jointly.
      have hcont_real :
          Continuous fun p : UniformSpace.Completion H × UniformSpace.Completion H ↦
            (⟪p.2, p.1⟫_ℝ : ℝ) := by
        simpa using continuous_snd.inner continuous_fst
      simpa using continuous_coe_real_ereal.comp hcont_real
    -- Compactness of the index set makes the support-function supremum continuous.
    simpa [A', supportFunctionEReal_eq_sSup_image, Function.uncurry] using
      hA'_compact.continuous_sSup
        (f := fun z a : UniformSpace.Completion H ↦ ((⟪a, z⟫_ℝ : ℝ) : EReal)) hcont_pair
  have hclosed :
      IsClosed {z : UniformSpace.Completion H |
        (⟪(u : UniformSpace.Completion H), z⟫_ℝ : EReal) ≤ σ[A'] z} := by
    -- The dense-extension step works on the closed `EReal` inequality predicate.
    exact isClosed_le
      (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)) hσ'_cont
  intro z
  -- Extend the dense-range inequality from `H` to all of `Completion H`.
  refine UniformSpace.Completion.denseRange_coe.induction_on z hclosed ?_
  intro y
  -- Rewrite the dense-point inequality back to the original support inequality on `H`.
  rw [supportFunction_completion_image_coe (A := A) (y := y)]
  simpa [UniformSpace.Completion.inner_coe, real_inner_comm] using hineq y

/-- Helper for Proposition 17 25: completion-side support inequalities place the coerced point in
the completion closed convex hull, and the embedding then pulls that membership back to `H`. -/
theorem mem_closedConvexHull_of_completion_support_inequalities
    (A : Set H) (u : H)
    (hineq :
      ∀ z : UniformSpace.Completion H,
        (⟪(u : UniformSpace.Completion H), z⟫_ℝ : EReal) ≤
          σ[((↑) : H → UniformSpace.Completion H) '' A] z) :
    u ∈ closedConvexHull ℝ A := by
  let A' : Set (UniformSpace.Completion H) := ((↑) : H → UniformSpace.Completion H) '' A
  have hu_completion :
      (u : UniformSpace.Completion H) ∈ closedConvexHull ℝ A' := by
    rw [closedConvexHull_eq_closure_convexHull,
      closure_convexHull_eq_iInter_supportFunctionHalfspace]
    rw [Set.mem_iInter]
    intro z
    rw [mem_supportFunctionHalfspace_iff]
    exact hineq z
  -- Pull the completion hull membership back along the canonical embedding.
  exact (mem_closedConvexHull_completion_image_iff (A := A) (u := u)).mp (by
    simpa [A'] using hu_completion)

theorem mem_closedConvexHull_iff_forall_inner_le_supportFunction_of_nonempty_of_isCompact
    (A : Set H) (hA_nonempty : A.Nonempty) (hAcompact : IsCompact A) (u : H) :
    u ∈ closedConvexHull ℝ A ↔ ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ σ[A] y := by
  constructor
  · intro hu y
    let A' : Set (UniformSpace.Completion H) := ((↑) : H → UniformSpace.Completion H) '' A
    have hu_completion :
        (u : UniformSpace.Completion H) ∈ closedConvexHull ℝ A' :=
      (mem_closedConvexHull_completion_image_iff (A := A) (u := u)).2 hu
    have hu_half :
        (u : UniformSpace.Completion H) ∈ ⋂ z : UniformSpace.Completion H,
          supportFunctionHalfspace A' z := by
      -- In the completion, Chapter 7 identifies the closed convex hull with the support
      -- halfspace intersection.
      rwa [closedConvexHull_eq_closure_convexHull,
        closure_convexHull_eq_iInter_supportFunctionHalfspace] at hu_completion
    have huy :
        (u : UniformSpace.Completion H) ∈ supportFunctionHalfspace A' (y : UniformSpace.Completion H) :=
      Set.mem_iInter.mp hu_half (y : UniformSpace.Completion H)
    -- Specialize the completion halfspace inequality back to the original direction `y`.
    simpa [A', supportFunction_completion_image_coe, UniformSpace.Completion.inner_coe,
      real_inner_comm] using
      (mem_supportFunctionHalfspace_iff A' (y : UniformSpace.Completion H)
        (u : UniformSpace.Completion H)).mp huy
  · intro hu
    -- Route correction: the reverse implication is completed in the completion, where the
    -- Chapter 7 halfspace characterization is available without reproving a new separation result.
    have hcompletion :
        ∀ z : UniformSpace.Completion H,
          (⟪(u : UniformSpace.Completion H), z⟫_ℝ : EReal) ≤
            σ[((↑) : H → UniformSpace.Completion H) '' A] z :=
      completion_support_inequality_of_dense_coe
        (A := A) hA_nonempty hAcompact u hu
    exact mem_closedConvexHull_of_completion_support_inequalities
      (A := A) u hcompletion

theorem mem_subdifferential_chebyshevCenterObjective_iff_mem_closedConvexHull_activeDisplacements
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x u : H) :
    u ∈ (∂ (chebyshevCenterObjective C hC_nonempty)) x ↔
      u ∈ closedConvexHull ℝ ((2 : ℝ) • (({x} : Set H) - Φ[C] x)) := by
  let A : Set H := (2 : ℝ) • (({x} : Set H) - Φ[C] x)
  have hA_nonempty : A.Nonempty := by
    have hxdom : x ∈ (Φ[C]).dom := by
      rw [dom_chebyshevCenterActiveSet_eq_univ (C := C) hC_nonempty hCcompact]
      simp
    rw [SetValuedOperator.mem_dom_iff] at hxdom
    rcases hxdom with ⟨r, hr⟩
    refine ⟨(2 : ℝ) • (x - r), ?_⟩
    refine Set.mem_smul_set.mpr ?_
    refine ⟨x - r, Set.mem_sub.mpr ?_, rfl⟩
    exact ⟨x, by simp, r, hr, rfl⟩
  have hAcompact : IsCompact A := by
    -- Compactness of the active farthest-point fiber transports to the displacement image.
    simpa [A] using isCompact_activeDisplacements (C := C) hCcompact x
  -- Route correction: clause (7) already reduces the subgradient to support inequalities, so the
  -- only remaining step is the compact-set hull characterization proved just above.
  rw [mem_subdifferential_iff_forall_inner_le_supportFunction_activeDisplacements
    (C := C) hC_nonempty hCcompact x u]
  simpa [A] using
    (mem_closedConvexHull_iff_forall_inner_le_supportFunction_of_nonempty_of_isCompact
      (A := A) hA_nonempty hAcompact u).symm

/-- Helper for Proposition 17 25: negation commutes with closure on subsets of a real normed
space. -/
theorem closure_neg_set (S : Set H) :
    closure (-S) = -closure S := by
  simpa using ((ContinuousLinearEquiv.neg ℝ : H ≃L[ℝ] H).image_closure S).symm

/-- Helper for Proposition 17 25: the closed convex hull of the active displacement set normalizes
to the scaled translate of the closed convex hull of the active farthest-point set. -/
theorem closedConvexHull_activeDisplacements_eq_smul_sub_closedConvexHull_activeSet
    (C : Set H) (x : H) :
    closedConvexHull ℝ ((2 : ℝ) • (({x} : Set H) - Φ[C] x)) =
      (2 : ℝ) • (({x} : Set H) - closedConvexHull ℝ (Φ[C] x)) := by
  let A : Set H := Φ[C] x
  have hsub_vadd : (({x} : Set H) - A) = x +ᵥ (-A) := by
    ext y
    constructor
    · rintro ⟨x', hx', a, ha, hxa⟩
      have hx' : x' = x := Set.mem_singleton_iff.mp hx'
      subst x'
      refine ⟨-a, by simpa using ha, ?_⟩
      simpa [vadd_eq_add, sub_eq_add_neg] using hxa
    · rintro ⟨a, ha, hya⟩
      refine Set.mem_sub.mpr ?_
      refine ⟨x, by simp, -a, ?_, ?_⟩
      · simpa using ha
      · simpa [vadd_eq_add, sub_eq_add_neg] using hya
  have hclosed_sub :
      closedConvexHull ℝ (({x} : Set H) - A) =
        ({x} : Set H) - closedConvexHull ℝ A := by
    calc
      closedConvexHull ℝ (({x} : Set H) - A)
          = closure (convexHull ℝ (({x} : Set H) - A)) := by
              rw [closedConvexHull_eq_closure_convexHull]
      _ = closure (x +ᵥ convexHull ℝ (-A)) := by
            rw [hsub_vadd, convexHull_vadd, convexHull_neg]
      _ = x +ᵥ closure (convexHull ℝ (-A)) := by
            rw [closure_vadd]
      _ = x +ᵥ (-closure (convexHull ℝ A)) := by
            rw [convexHull_neg, closure_neg_set]
      _ = ({x} : Set H) - closure (convexHull ℝ A) := by
            ext y
            constructor
            · rintro ⟨a, ha, hya⟩
              refine Set.mem_sub.mpr ?_
              refine ⟨x, by simp, -a, ?_, ?_⟩
              · simpa using ha
              · simpa [vadd_eq_add, sub_eq_add_neg] using hya
            · rintro ⟨x', hx', a, ha, hxa⟩
              have hx' : x' = x := Set.mem_singleton_iff.mp hx'
              subst x'
              refine ⟨-a, by simpa using ha, ?_⟩
              simpa [vadd_eq_add, sub_eq_add_neg] using hxa
      _ = ({x} : Set H) - closedConvexHull ℝ A := by
            rw [closedConvexHull_eq_closure_convexHull]
  calc
    closedConvexHull ℝ ((2 : ℝ) • (({x} : Set H) - A))
        = closure (convexHull ℝ ((2 : ℝ) • (({x} : Set H) - A))) := by
            rw [closedConvexHull_eq_closure_convexHull]
    _ = closure ((2 : ℝ) • convexHull ℝ (({x} : Set H) - A)) := by
          rw [convexHull_smul]
    _ = (2 : ℝ) • closure (convexHull ℝ (({x} : Set H) - A)) := by
          rw [closure_smul₀]
    _ = (2 : ℝ) • closedConvexHull ℝ (({x} : Set H) - A) := by
          rw [closedConvexHull_eq_closure_convexHull]
    _ = (2 : ℝ) • (({x} : Set H) - closedConvexHull ℝ A) := by
          rw [hclosed_sub]

-- Proof sketch: rewrite the previous clause as a support-function identity for the pointwise
-- scaled displacement set `2 • ({x} - Φ[C] x)`, then apply Proposition 17.24 to identify the
-- subdifferential with the closed convex hull of that active displacement set.
/-- Proposition 17.25 (8): clause (iv). The subdifferential of the Chebyshev-center objective is
the pointwise scaled translate `2 • ({x} - closedConvexHull ℝ (Φ[C] x))` of the closed convex
hull of the active farthest-point set. -/
theorem subdifferential_chebyshevCenterObjective_eq_smul_sub_closedConvexHull_activeSet
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x : H) :
    (∂ (chebyshevCenterObjective C hC_nonempty)) x =
      (2 : ℝ) • (({x} : Set H) - closedConvexHull ℝ (Φ[C] x)) := by
  ext u
  -- Convert clause (7) into the support-halfspace characterization of the closed convex hull of
  -- active displacements, then normalize that hull through the affine set operations.
  rw [mem_subdifferential_chebyshevCenterObjective_iff_mem_closedConvexHull_activeDisplacements
      (C := C) hC_nonempty hCcompact x u,
    closedConvexHull_activeDisplacements_eq_smul_sub_closedConvexHull_activeSet
      (C := C) (x := x)]

/-- Proposition 17.25 (10): clause (v). A point minimizes the Chebyshev-center objective exactly
when it belongs to the closed convex hull of its active farthest-point set. -/
theorem mem_argmin_chebyshevCenterObjective_iff_mem_closedConvexHull_activeSet
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (r : H) :
    r ∈ Argmin (chebyshevCenterObjective C hC_nonempty).asEReal ↔
      r ∈ closedConvexHull ℝ (Φ[C] r) := by
  let S : Set H := closedConvexHull ℝ (Φ[C] r)
  -- Fermat's rule turns minimizers into zeros of the subdifferential, so only the explicit
  -- scaled-translate fiber from clause (8) remains to be simplified.
  rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff,
    subdifferential_chebyshevCenterObjective_eq_smul_sub_closedConvexHull_activeSet
      (C := C) hC_nonempty hCcompact r]
  change (0 : H) ∈ (2 : ℝ) • (({r} : Set H) - S) ↔ r ∈ S
  constructor
  · intro hzero
    have hzero_sub : (0 : H) ∈ ({r} : Set H) - S := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (show (2 : ℝ) ≠ 0 by norm_num)] at hzero
      simpa using hzero
    rcases Set.mem_sub.mp hzero_sub with ⟨x, hx, y, hy, hxy⟩
    have hx' : x = r := Set.mem_singleton_iff.mp hx
    subst x
    have hry : r = y := sub_eq_zero.mp hxy
    subst y
    exact hy
  · intro hrS
    have hzero_sub : (0 : H) ∈ ({r} : Set H) - S := by
      exact Set.mem_sub.mpr ⟨r, Set.mem_singleton r, r, hrS, sub_self r⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (show (2 : ℝ) ≠ 0 by norm_num)]
    simpa using hzero_sub

end InnerProduct

section Complete

variable [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: boundedness makes the objective everywhere finite, and as a supremum of
-- continuous squared-distance functions it is lower semicontinuous; combine this with the strong
-- convexity from clause (2) and Corollary 11.17 to get a unique global minimizer.
/-- Proposition 17.25 (9): clause (v). For a nonempty bounded set, the Chebyshev-center objective
has a unique global minimizer. -/
theorem existsUnique_mem_argmin_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ∃! r : H, r ∈ Argmin (chebyshevCenterObjective C hC_nonempty).asEReal := by
  have hlower :
      LowerSemicontinuous
        (fun x : H ↦ (chebyshevCenterObjective C hC_nonempty x : EReal)) :=
    chebyshevCenterObjective_lowerSemicontinuous (C := C) hC_nonempty
  have hgamma : chebyshevCenterObjective C hC_nonempty ∈ Γ₀(H) := by
    exact ⟨hlower, (stronglyConvex_chebyshevCenterObjective
      (C := C) hC_nonempty hC_bounded).uniformlyConvex.convexOn⟩
  have hcoe : Coercive (chebyshevCenterObjective C hC_nonempty).asEReal :=
    coercive_of_supercoercive
      (supercoercive_chebyshevCenterObjective (C := C) hC_nonempty hC_bounded)
  have hstrict : StrictlyConvex (chebyshevCenterObjective C hC_nonempty) :=
    (stronglyConvex_chebyshevCenterObjective
      (C := C) hC_nonempty hC_bounded).uniformlyConvex.strictlyConvex
  -- The complete-space uniqueness theorem applies once the objective is packaged into `Γ₀(H)`,
  -- coercive, and strictly convex.
  exact existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
    hgamma hcoe hstrict

end Complete
