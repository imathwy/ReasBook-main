import Mathlib
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap10.Example_10_9
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_14
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Function

variable {X : Type*} {Y : Type*}

/-- Helper for Proposition 16 45: the singleton-valued set-valued operator associated with a
function on the whole space. -/
abbrev toSetValuedOperator (T : X → Y) : SetValuedOperator X Y :=
  fun x ↦ ({T x} : Set Y)

/-- Helper for Proposition 16 45: evaluating the singleton-valued operator recovers the
corresponding singleton. -/
@[simp] theorem toSetValuedOperator_apply (T : X → Y) (x : X) :
    T.toSetValuedOperator x = ({T x} : Set Y) :=
  rfl

end Function

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 16 45: the quadratic penalty `y ↦ (1 / 2) ‖x - y‖²` as an
`]-∞,+∞]`-valued function. -/
private noncomputable def quadraticPenalty (x : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2).toEReal

/-- Helper for Proposition 16 45: the bundled proximal objective is the pointwise sum of `f` and
the quadratic penalty. -/
private noncomputable def proximalObjectiveIoi (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    H → Set.Ioi (⊥ : EReal) :=
  f + quadraticPenalty (H := H) x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 45: coercing the bundled proximal objective back to `EReal` gives
the canonical proximal objective from Definition 12.23. -/
@[simp] private theorem proximalObjectiveIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) :
    (proximalObjectiveIoi (H := H) f x y : EReal) = proximalObjective f x y := by
  simp [proximalObjectiveIoi, proximalObjective, quadraticPenalty]

omit [CompleteSpace H] in
/-- Helper for Proposition 16 45: a continuous convex real-valued function on all of `H`
canonically gives a member of `Γ₀(H)` after applying `toEReal`. -/
private theorem real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hreal :
        φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
          (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 16 45: the quadratic penalty belongs to `Γ₀(H)`. -/
private theorem quadraticPenalty_mem_gammaZero (x : H) :
    quadraticPenalty (H := H) x ∈ Γ₀(H) := by
  have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    exact continuous_const.mul
      ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
  have hbase : _root_.ConvexOn ℝ Set.univ (fun z : H ↦ ‖z‖ ^ 2) := by
    exact strongConvexOn_zero.mp ((norm_sq_strongConvexOn_univ (H := H)).mono (by norm_num))
  have hconv : _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    have hsq :
        ‖x - (a • y + b • z)‖ ^ 2 ≤ a * ‖x - y‖ ^ 2 + b * ‖x - z‖ ^ 2 := by
      have hrewrite :
          x - (a • y + b • z) = a • (x - y) + b • (x - z) := by
        calc
          x - (a • y + b • z) = (a + b) • x - (a • y + b • z) := by simp [hab]
          _ = a • x + b • x - (a • y + b • z) := by rw [add_smul]
          _ = a • (x - y) + b • (x - z) := by
            rw [smul_sub, smul_sub]
            abel_nf
      simpa [hrewrite] using
        hbase.2 (by simp : x - y ∈ (Set.univ : Set H)) (by simp : x - z ∈ (Set.univ : Set H))
          ha hb hab
    have htarget :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  simpa [quadraticPenalty, Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (H := H)
      (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) hcont hconv

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 45: the quadratic penalty is supercoercive. -/
private theorem quadraticPenalty_supercoercive (x : H) :
    Supercoercive (quadraticPenalty (H := H) x).asEReal := by
  rw [Supercoercive, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let ξ0 : ℝ := max ξ 0
  have htail :
      ∀ᶠ y in Bornology.cobounded H, max (2 * ‖x‖) (8 * ξ0 + 1) ≤ ‖y‖ := by
    simpa [ξ0] using
      (eventually_cobounded_le_norm (max (2 * ‖x‖) (8 * ξ0 + 1) : ℝ) :
        ∀ᶠ y in Bornology.cobounded H, max (2 * ‖x‖) (8 * ξ0 + 1) ≤ ‖y‖)
  filter_upwards [htail] with y hy
  have hy_x : 2 * ‖x‖ ≤ ‖y‖ := le_trans (le_max_left _ _) hy
  have hy_large : 8 * ξ0 + 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
  have hξ0_nonneg : 0 ≤ ξ0 := le_max_right ξ 0
  have hy_one : 1 ≤ ‖y‖ := by
    linarith
  have hy_pos : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy_one
  have hx_half : ‖x‖ ≤ ‖y‖ / 2 := by
    linarith
  have hdist : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    calc
      ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      _ = ‖x - y‖ := by rw [norm_sub_rev]
  have hhalf : ‖y‖ / 2 ≤ ‖x - y‖ := by
    linarith
  have hξ_lt_tail : ξ < ‖y‖ / 8 := by
    have hξ_le : ξ ≤ ξ0 := le_max_left _ _
    have hξ0_lt : ξ0 < ‖y‖ / 8 := by
      linarith
    exact lt_of_le_of_lt hξ_le hξ0_lt
  have hy_ne : ‖y‖ ≠ 0 := ne_of_gt hy_pos
  have hsq : ‖y‖ ^ 2 / 4 ≤ ‖x - y‖ ^ 2 := by
    nlinarith
  have htail_le_obj : ‖y‖ / 8 ≤ ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := by
    have hden_pos : 0 < 2 * ‖y‖ := by positivity
    have hdiv :
        (‖y‖ ^ 2 / 4) / (2 * ‖y‖) ≤ ‖x - y‖ ^ 2 / (2 * ‖y‖) := by
      exact div_le_div_of_nonneg_right hsq hden_pos.le
    have hleft : ‖y‖ / 8 = (‖y‖ ^ 2 / 4) / (2 * ‖y‖) := by
      field_simp [hy_ne]
      ring
    have hright :
        ‖x - y‖ ^ 2 / (2 * ‖y‖) = ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := by
      have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
      field_simp [hy_ne, htwo_ne]
    calc
      ‖y‖ / 8 = (‖y‖ ^ 2 / 4) / (2 * ‖y‖) := hleft
      _ ≤ ‖x - y‖ ^ 2 / (2 * ‖y‖) := hdiv
      _ = ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := hright
  have hreal : ξ < ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := by
    exact lt_of_lt_of_le hξ_lt_tail htail_le_obj
  rw [Function.asEReal, quadraticPenalty, Function.toEReal_apply, ← EReal.coe_div]
  exact_mod_cast hreal

/-- Helper for Proposition 16 45: every proximal-point set is nonempty for a `Γ₀(H)` function. -/
private theorem proximalPoints_nonempty_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    (proximalPoints f x).Nonempty := by
  have hquad : quadraticPenalty (H := H) x ∈ Γ₀(H) :=
    quadraticPenalty_mem_gammaZero (H := H) x
  rcases hf.2.nonempty with ⟨p, hp⟩
  have hdom :
      (effectiveDomain f ∩ effectiveDomain (quadraticPenalty (H := H) x)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    rw [mem_effectiveDomain_iff]
    change ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) < ⊤)
    exact EReal.coe_lt_top ((1 / 2 : ℝ) * ‖x - p‖ ^ 2)
  have hsum : quadraticPenalty (H := H) x + f ∈ Γ₀(H) := by
    simpa [add_comm] using
      pointwiseAdd_mem_gammaZero f (quadraticPenalty (H := H) x) hf hquad hdom
  have hsuper : Supercoercive (quadraticPenalty (H := H) x + f).asEReal := by
    simpa [add_comm] using
      pointwiseAdd_supercoercive_of_mem_gammaZero f (quadraticPenalty (H := H) x) hf
        (quadraticPenalty_supercoercive (H := H) x)
  have hcoe : Coercive (quadraticPenalty (H := H) x + f).asEReal :=
    coercive_of_supercoercive hsuper
  have hargmin :
      (Argmin ((quadraticPenalty (H := H) x + f).asEReal)).Nonempty := by
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hsum
        isClosed_univ convex_univ Set.univ_nonempty (Or.inl hcoe)
  simpa [proximalPoints, proximalObjectiveIoi, add_comm, proximalObjectiveIoi_apply] using hargmin

/-- Helper for Proposition 16 45: choose one proximal point at each base point. -/
private noncomputable def proximalSelection
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  fun x ↦ Classical.choose (proximalPoints_nonempty_of_mem_gammaZero (H := H) f hf x)

/-- Helper for Proposition 16 45: the selected point is indeed proximal. -/
private theorem proximalSelection_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    IsProxPoint f x (proximalSelection (H := H) f hf x) :=
  Classical.choose_spec (proximalPoints_nonempty_of_mem_gammaZero (H := H) f hf x)

/-- Helper for Proposition 16 45: the residual from a selected proximal point is a subgradient. -/
private theorem sub_mem_subdifferential_of_proximalSelection
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    x - proximalSelection (H := H) f hf x ∈
      (∂ f) (proximalSelection (H := H) f hf x) := by
  -- Convert the selected proximal point into the Chapter 16 subgradient inequality.
  rw [mem_subdifferential_iff]
  exact
    (isProxPoint_iff_forall_inner_add_le
      f hf.2 x (proximalSelection (H := H) f hf x)).1
      (proximalSelection_isProxPoint (H := H) f hf x)

/-- Helper for Proposition 16 45: the selected proximal point realizes the target point inside
`id.toSetValuedOperator + ∂ f`. -/
private theorem selected_proximal_point_mem_id_add_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    x ∈ ((id : H → H).toSetValuedOperator + ∂ f) (proximalSelection (H := H) f hf x) := by
  -- Split `x` as the selected point plus its residual subgradient.
  refine Set.mem_add.2 ?_
  refine ⟨proximalSelection (H := H) f hf x, ?_, x - proximalSelection (H := H) f hf x,
    sub_mem_subdifferential_of_proximalSelection (H := H) f hf x, ?_⟩
  · simp [Function.toSetValuedOperator_apply]
  · abel_nf

-- Proof sketch: choose a proximal minimizer `p` of the regularized objective. Proposition 12.26
-- rewrites proximality as the subgradient inequality `x - p ∈ ∂ f(p)`, and then
-- `x = p + (x - p)` shows `x ∈ (id.toSetValuedOperator + ∂ f) p`.
/-- Proposition 16 45: if `f ∈ Γ₀(H)`, then the range of the set-valued operator
`id.toSetValuedOperator + ∂ f`, i.e. `Id + ∂ f`, is all of `H`. -/
theorem range_id_add_subdifferential_eq_univ_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.range ((id : H → H).toSetValuedOperator + ∂ f) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    -- Produce a witness from the selected proximal point.
    rw [SetValuedOperator.mem_range_iff]
    exact ⟨proximalSelection (H := H) f hf x,
      selected_proximal_point_mem_id_add_subdifferential (H := H) f hf x⟩

end SubdifferentialCalculus

end ERealFunction
