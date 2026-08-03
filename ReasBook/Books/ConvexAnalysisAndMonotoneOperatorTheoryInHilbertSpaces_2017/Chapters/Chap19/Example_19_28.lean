import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_24
import BauschkeLean.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

namespace ERealFunction

open scoped InnerProductSpace Pointwise

universe u v

attribute [local instance] Classical.propDecidable

-- Route correction: on `ℝ × ℝ`, the product ring instances force the sup norm unless we disable
-- them locally. Example 19.28 needs the transported `ℓ²` geometry from `ProdL2`.
attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [-instance] Prod.nonUnitalSeminormedRing Prod.seminormedRing
attribute [-instance] Prod.nonUnitalNormedRing Prod.normedRing
attribute [-instance] Prod.nonUnitalSeminormedCommRing Prod.nonUnitalNormedCommRing
attribute [-instance] Prod.seminormedCommRing Prod.normedCommRing

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

section

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

/- Source/core/bridge triage:
- `source-facing`: Example 19.28 studies one concrete Lorentz-constraint specialization of the
  perturbation theory from Proposition 19.25 and records its primal, dual, Lagrangian, and value
  formulas.
- `core/canonical`: the owner declarations are `inequalityConstraintPerturbation`,
  `perturbationPrimalObjective`, `perturbationDualObjective`, `lagrangian`, and `Prod.snd ▷ ·`.
- `bridge/view`: this file therefore exposes the source perturbation as a direct specialization of
  `inequalityConstraintPerturbation`, then states the displayed formulas as thin companions.
-/

/-- The Lorentz-constraint perturbation `F` from Example 19.28, obtained by specializing
`inequalityConstraintPerturbation` to `f ξ = φ ξ₂`, `R ξ = ‖ξ‖ - ξ₁`, and `K = Iic 0`. -/
abbrev lorentzConstraintPerturbation
    (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    (ℝ × ℝ) × ℝ → Set.Ioi (⊥ : EReal) :=
  inequalityConstraintPerturbation
    (fun ξ : ℝ × ℝ ↦ φ ξ.2)
    (fun ξ ↦ ‖ξ‖ - ξ.1)
    (Iic (0 : ℝ))

/-- The source-facing quantity `γ = inf φ(ℝ)` from Example 19.28. -/
noncomputable def phiRangeInfimum : EReal :=
  sInf (Set.range fun t : ℝ ↦ (φ t : EReal))

local notation "γ" => phiRangeInfimum φ

/-- Helper for Example 19.28: membership in the shifted nonpositive ray rewrites the Lorentz
residual branch as the scalar inequality `y ≤ ξ₁ - ‖ξ‖`. -/
lemma lorentz_residual_add_mem_Iic_zero_iff (ξ : ℝ × ℝ) (y : ℝ) :
    ‖ξ‖ - ξ.1 + y ∈ Set.Iic (0 : ℝ) ↔ y ≤ ξ.1 - ‖ξ‖ := by
  -- Rearranging the translated residual turns the cone membership into the scalar inequality.
  rw [Set.mem_Iic]
  constructor <;> intro h <;> linarith

/-- Helper for Example 19.28: in the local `ProdL2` geometry on `ℝ × ℝ`, the squared norm is the
sum of the squared coordinates. -/
lemma prod_norm_sq_eq (ξ : ℝ × ℝ) :
    ‖ξ‖ ^ 2 = ξ.1 ^ 2 + ξ.2 ^ 2 := by
  -- Transport the product norm to the canonical `WithLp` model and read off the Euclidean formula.
  have hnorm : ‖ξ‖ = ‖WithLp.toLp 2 ξ‖ := by
    simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
      (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := ℝ) (β := ℝ) ξ)
  have hnorm_sq : ‖ξ‖ ^ 2 = ‖WithLp.toLp 2 ξ‖ ^ 2 := by
    simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
  exact hnorm_sq.trans <| by
    simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 ξ))

/-- Helper for Example 19.28: on the horizontal axis, the local `ProdL2` norm is the absolute
value of the first coordinate. -/
lemma prod_l2_norm_eq_abs_fst_of_snd_zero (a : ℝ) :
    ‖((a, 0) : ℝ × ℝ)‖ = |a| := by
  -- Both sides are nonnegative, so it suffices to identify their squares through `prod_norm_sq_eq`.
  have hsq : ‖((a, 0) : ℝ × ℝ)‖ ^ 2 = |a| ^ 2 := by
    calc
      ‖((a, 0) : ℝ × ℝ)‖ ^ 2 = a ^ 2 + (0 : ℝ) ^ 2 := prod_norm_sq_eq ((a, 0) : ℝ × ℝ)
      _ = a ^ 2 := by ring
      _ = |a| ^ 2 := by rw [sq_abs]
  have hnorm_nonneg : 0 ≤ ‖((a, 0) : ℝ × ℝ)‖ := by
    have hnorm : ‖((a, 0) : ℝ × ℝ)‖ = ‖WithLp.toLp 2 ((a, 0) : ℝ × ℝ)‖ := by
      simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
        (WithLp.norm_seminormedAddCommGroupToProd
          (p := 2) (α := ℝ) (β := ℝ) ((a, 0) : ℝ × ℝ))
    rw [hnorm]
    exact norm_nonneg _
  have habs_nonneg : 0 ≤ |a| := abs_nonneg a
  nlinarith

/-- Helper for Example 19.28: the transported `ProdL2` norm vanishes at the origin. -/
lemma prod_l2_norm_zero :
    ‖((0, 0) : ℝ × ℝ)‖ = 0 := by
  have hnorm : ‖((0, 0) : ℝ × ℝ)‖ = ‖WithLp.toLp 2 ((0, 0) : ℝ × ℝ)‖ := by
    simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
      (WithLp.norm_seminormedAddCommGroupToProd
        (p := 2) (α := ℝ) (β := ℝ) ((0, 0) : ℝ × ℝ))
  simpa using hnorm.trans (by simp)

/-- Helper for Example 19.28: the transported `ProdL2` norm is nonnegative. -/
lemma prod_l2_norm_nonneg (ξ : ℝ × ℝ) :
    0 ≤ ‖ξ‖ := by
  have hnorm : ‖ξ‖ = ‖WithLp.toLp 2 ξ‖ := by
    simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
      (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := ℝ) (β := ℝ) ξ)
  rw [hnorm]
  exact norm_nonneg _

/-- Helper for Example 19.28: in the local `ProdL2` geometry, the first coordinate is bounded by
the ambient norm. -/
lemma abs_fst_le_prod_l2_norm (ξ : ℝ × ℝ) :
    |ξ.1| ≤ ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using
    (WithLp.norm_fst_le (p := 2) (x := WithLp.toLp 2 ξ))

/-- Helper for Example 19.28: the first projection is continuous for the transported `ProdL2`
topology on `ℝ × ℝ`. -/
lemma continuous_fst_prodL2 :
    Continuous (fun ξ : ℝ × ℝ ↦ ξ.1) := by
  simpa using
    ((WithLp.continuous_fst (p := 2) (α := ℝ) (β := ℝ)).comp
      (WithLp.prod_continuous_toLp (p := 2) (α := ℝ) (β := ℝ)))

/-- Helper for Example 19.28: the second projection is continuous for the transported `ProdL2`
topology on `ℝ × ℝ`. -/
lemma continuous_snd_prodL2 :
    Continuous (fun ξ : ℝ × ℝ ↦ ξ.2) := by
  simpa using
    ((WithLp.continuous_snd (p := 2) (α := ℝ) (β := ℝ)).comp
      (WithLp.prod_continuous_toLp (p := 2) (α := ℝ) (β := ℝ)))

/-- Helper for Example 19.28: the transported `ProdL2` norm is continuous on `ℝ × ℝ`. -/
lemma continuous_norm_prodL2 :
    Continuous (fun ξ : ℝ × ℝ ↦ ‖ξ‖) := by
  simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
    (continuous_norm.comp
      (WithLp.prod_continuous_toLp (p := 2) (α := ℝ) (β := ℝ)))

/-- Helper for Example 19.28: the triangle inequality for the transported `ProdL2` norm on
`ℝ × ℝ`. -/
lemma prod_l2_norm_add_le (ξ η : ℝ × ℝ) :
    ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := by
  simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
    (norm_add_le (WithLp.toLp 2 ξ) (WithLp.toLp 2 η))

/-- Helper for Example 19.28: the Lorentz feasibility inequality is equivalent to vanishing
second coordinate together with nonnegative first coordinate. -/
lemma lorentz_feasible_coord_iff (ξ : ℝ × ℝ) :
    ‖ξ‖ ≤ ξ.1 ↔ ξ.2 = 0 ∧ 0 ≤ ξ.1 := by
  rcases ξ with ⟨x1, x2⟩
  constructor
  · intro hfeas
    -- The feasible inequality forces the first coordinate to be nonnegative.
    have hnorm_nonneg : 0 ≤ ‖((x1, x2) : ℝ × ℝ)‖ := by
      exact prod_l2_norm_nonneg ((x1, x2) : ℝ × ℝ)
    have hx1_nonneg : 0 ≤ x1 := le_trans hnorm_nonneg hfeas
    -- Squaring the inequality isolates the second coordinate through the Euclidean norm identity.
    have hsq_le : ‖((x1, x2) : ℝ × ℝ)‖ ^ 2 ≤ x1 ^ 2 := by
      have habs_le : |‖((x1, x2) : ℝ × ℝ)‖| ≤ |x1| := by
        simpa [abs_of_nonneg hnorm_nonneg, abs_of_nonneg hx1_nonneg] using hfeas
      exact sq_le_sq.mpr habs_le
    rw [prod_norm_sq_eq] at hsq_le
    have hx2_sq_le : x2 ^ 2 ≤ 0 := by
      nlinarith
    have hx2_zero : x2 = 0 := by
      nlinarith [sq_nonneg x2, hx2_sq_le]
    exact ⟨hx2_zero, hx1_nonneg⟩
  · rintro ⟨hx2_zero, hx1_nonneg⟩
    -- Once the second coordinate vanishes, the norm reduces to the first coordinate.
    have hnorm : ‖((x1, x2) : ℝ × ℝ)‖ = x1 := by
      have hpair : ((x1, x2) : ℝ × ℝ) = (x1, 0) := by
        ext
        · rfl
        · exact hx2_zero
      calc
        ‖((x1, x2) : ℝ × ℝ)‖ = ‖((x1, 0) : ℝ × ℝ)‖ := by rw [hpair]
        _ = |x1| := prod_l2_norm_eq_abs_fst_of_snd_zero x1
        _ = x1 := abs_of_nonneg hx1_nonneg
    exact hnorm.le

/-- Helper for Example 19.28: the nonpositive ray is convex. -/
lemma iic_zero_convex : Convex ℝ (Set.Iic (0 : ℝ)) := by
  -- This is the standard convexity of a lower ray in a linear order.
  simpa using (convex_Iic (0 : ℝ))

/-- Helper for Example 19.28: the nonpositive ray is closed. -/
lemma iic_zero_isClosed : IsClosed (Set.Iic (0 : ℝ)) := by
  simpa using isClosed_Iic

/-- Helper for Example 19.28: the nonpositive ray is a cone. -/
lemma iic_zero_isCone : IsCone (Set.Iic (0 : ℝ)) := by
  -- Positive scaling preserves and characterizes the nonpositive ray.
  rw [isCone_iff]
  ext x
  constructor
  · intro hx
    exact Set.mem_smul.mpr ⟨1, by norm_num, x, hx, by simp⟩
  · rintro ⟨t, ht, y, hy, rfl⟩
    simp only [Set.mem_Iic] at hy ⊢
    exact mul_nonpos_of_nonneg_of_nonpos ht.le hy

/-- Helper for Example 19.28: on `ℝ`, the inner product is ordinary multiplication. -/
lemma real_inner_eq_mul (x y : ℝ) :
    ⟪x, y⟫_ℝ = x * y := by
  -- Reduce the one-dimensional inner product to the standard scalar formula on `ℝ`.
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

/-- Helper for Example 19.28: the Proposition 19.25 dual-branch term simplifies to
`v (ξ₁ - ‖ξ‖) - φ(ξ₂)`. -/
lemma lorentz_dual_branch_term_eq (v : ℝ) (ξ : ℝ × ℝ) :
    -((⟪‖ξ‖ - ξ.1, v⟫_ℝ : ℝ) : EReal) - (φ ξ.2 : EReal) =
      ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal) := by
  have hreal : -(⟪‖ξ‖ - ξ.1, v⟫_ℝ) = v * (ξ.1 - ‖ξ‖) := by
    calc
      -(⟪‖ξ‖ - ξ.1, v⟫_ℝ) = -((‖ξ‖ - ξ.1) * v) := by rw [real_inner_eq_mul]
      _ = v * (ξ.1 - ‖ξ‖) := by ring
  have hcast : -((⟪‖ξ‖ - ξ.1, v⟫_ℝ : ℝ) : EReal) = ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) := by
    simpa using congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  simpa using congrArg (fun t : EReal ↦ t - (φ ξ.2 : EReal)) hcast

/-- Helper for Example 19.28: the polar cone of `(-∞, 0]` is `[0, +∞)`. -/
lemma mem_polarCone_Iic_zero_iff_nonneg {v : ℝ} :
    v ∈ (Set.Iic (0 : ℝ))ᵒ⊖ ↔ 0 ≤ v := by
  constructor
  · intro hv
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hv
    have hneg := hv (-1) (by simp : (-1 : ℝ) ∈ Set.Iic (0 : ℝ))
    simpa [real_inner_eq_mul] using hneg
  · intro hv
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro x hx
    simp only [Set.mem_Iic] at hx
    simpa [real_inner_eq_mul] using mul_nonpos_of_nonpos_of_nonneg hx hv

/-- Helper for Example 19.28: in `EReal`, the infimum of pointwise negatives is the negative of
the corresponding supremum. -/
private theorem iInf_neg_eq_neg_iSup_ereal
    {ι : Sort*} (ψ : ι → EReal) :
    (⨅ i, -ψ i) = -(⨆ i, ψ i) := by
  simpa only [neg_neg] using (OrderIso.map_iSup EReal.negOrderIso ψ).symm

/-- Helper for Example 19.28: the Lorentz residual map is continuous in the local `ProdL2`
geometry on `ℝ × ℝ`. -/
lemma continuous_lorentz_residual_prodL2 :
    Continuous (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) := by
  -- The source residual is the difference between the continuous norm and the first coordinate.
  simpa [sub_eq_add_neg] using (continuous_norm_prodL2.sub continuous_fst_prodL2)

/-- Helper for Example 19.28: every strict Jensen defect of the Lorentz residual belongs to the
nonpositive ray. -/
lemma lorentz_residual_defect_mem_Iic_zero (ξ η : ℝ × ℝ) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (‖α • ξ + (1 - α) • η‖ - (α • ξ + (1 - α) • η).1) -
      α * (‖ξ‖ - ξ.1) - (1 - α) * (‖η‖ - η.1) ∈ Set.Iic (0 : ℝ) := by
  -- Expand the Jensen defect and reduce it to the usual convexity inequality for the norm.
  rw [Set.mem_Iic]
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h1_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  have hnorm_le :
      ‖α • ξ + (1 - α) • η‖ ≤ α * ‖ξ‖ + (1 - α) * ‖η‖ := by
    calc
      ‖α • ξ + (1 - α) • η‖ ≤ ‖α • ξ‖ + ‖(1 - α) • η‖ := by
        exact prod_l2_norm_add_le (α • ξ) ((1 - α) • η)
      _ = |α| * ‖ξ‖ + |1 - α| * ‖η‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = α * ‖ξ‖ + (1 - α) * ‖η‖ := by
            simp [abs_of_nonneg hα_nonneg, abs_of_nonneg h1_nonneg]
  have hfst :
      (α • ξ + (1 - α) • η).1 = α * ξ.1 + (1 - α) * η.1 := by
    simp
  rw [hfst]
  linarith

/-- Helper for Example 19.28: the Lorentz residual map has nonpositive Jensen defect, so it is
convex with respect to `(-∞, 0]`. -/
lemma lorentz_constraintMap_isConvexWithRespectTo_nonpos :
    (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1).IsConvexWithRespectTo ℝ (Set.Iic (0 : ℝ)) := by
  -- The defining defect is exactly the Jensen defect normalized in the previous helper lemma.
  intro ξ η α hα
  simpa using lorentz_residual_defect_mem_Iic_zero (ξ := ξ) (η := η) hα

/-- Helper for Example 19.28: lifting a scalar `Γ₀` integrand through the second projection keeps
the function in `Γ₀(ℝ²)`. -/
lemma phi_snd_mem_gammaZero (hφ : φ ∈ Γ₀(ℝ)) :
    (fun ξ : ℝ × ℝ ↦ φ ξ.2) ∈ Γ₀(ℝ × ℝ) := by
  rw [mem_gammaZero_iff] at hφ ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous second projection.
    simpa using hφ.1.comp continuous_snd_prodL2
  · refine ⟨?_, fun _ hp ↦ hp, ?_⟩
    · -- A domain point for `φ` gives a domain point upstairs by freezing the first coordinate.
      rcases hφ.2.nonempty with ⟨y, hy⟩
      refine ⟨(0, y), ?_⟩
      simpa [mem_effectiveDomain_iff] using hy
    · intro p hp q hq a ha0 ha1
      -- Convexity depends only on the second coordinate, so reuse the scalar convexity owner.
      have hp' : p.2 ∈ effectiveDomain φ := by
        simpa [mem_effectiveDomain_iff] using hp
      have hq' : q.2 ∈ effectiveDomain φ := by
        simpa [mem_effectiveDomain_iff] using hq
      simpa using hφ.2.ineq hp' hq' ha0 ha1

/-- Evaluating the Lorentz-constraint specialization of `inequalityConstraintPerturbation` gives
the branch formula from `(19.67)`. -/
@[simp] theorem lorentzConstraintPerturbation_apply (ξ : ℝ × ℝ) (y : ℝ) :
    (lorentzConstraintPerturbation φ (ξ, y) : EReal) =
      if ξ.1 - ‖ξ‖ ≥ y then (φ ξ.2 : EReal) else ⊤ := by
  -- Consume the canonical feasible/infeasible owners from Proposition 19.25.
  by_cases hξ : ξ.1 - ‖ξ‖ ≥ y
  · have hmem : ‖ξ‖ - ξ.1 + y ∈ Set.Iic (0 : ℝ) := by
      exact (lorentz_residual_add_mem_Iic_zero_iff ξ y).2 hξ
    simpa [lorentzConstraintPerturbation, hξ] using
      (inequalityConstraintPerturbation_apply_of_mem
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (x := ξ) (y := y) hmem)
  · have hmem : ‖ξ‖ - ξ.1 + y ∉ Set.Iic (0 : ℝ) := by
      intro hmem
      exact hξ ((lorentz_residual_add_mem_Iic_zero_iff ξ y).1 hmem)
    simpa [lorentzConstraintPerturbation, hξ] using
      (inequalityConstraintPerturbation_apply_of_not_mem
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (x := ξ) (y := y) hmem)

/-- The Lorentz-type constraint `‖(ξ₁, ξ₂)‖ ≤ ξ₁` is equivalent to membership in
`ℝ₊ × {0}`. -/
theorem lorentz_feasible_iff (ξ : ℝ × ℝ) :
    ‖ξ‖ ≤ ξ.1 ↔ ξ ∈ Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  -- Rewrite the coordinate description into the textbook product-set form.
  rw [lorentz_feasible_coord_iff]
  constructor
  · rintro ⟨hξ2, hξ1⟩
    simp [hξ1, hξ2]
  · intro hξ
    simp only [Set.mem_prod, Set.mem_Ici, Set.mem_singleton_iff] at hξ
    exact ⟨hξ.2, hξ.1⟩

/-- Example 19.28 (1): clause (i). If `φ ∈ Γ₀(ℝ)` and `0 ∈ dom φ`, then the perturbation
function `F` from `(19.67)` belongs to `Γ₀(ℝ² × ℝ)`. -/
theorem lorentzConstraintPerturbation_mem_gammaZero
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    lorentzConstraintPerturbation φ ∈ Γ₀((ℝ × ℝ) × ℝ) := by
  -- Route correction: once the Lorentz residual owners are proved, clause (i) is a direct
  -- specialization of Proposition 19.25.
  have hK_nonempty : (Set.Iic (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  have hfeas :
      (Set.Iic (0 : ℝ) ∩
        (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) '' effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2)).Nonempty := by
    refine ⟨0, by simp, ?_⟩
    refine ⟨(0, 0), ?_, by simpa using prod_l2_norm_zero⟩
    simpa [mem_effectiveDomain_iff] using hφ0
  simpa [lorentzConstraintPerturbation] using
    inequalityConstraintPerturbation_mem_gammaZero
      (f := fun ξ : ℝ × ℝ ↦ φ ξ.2)
      (R := fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1)
      (K := Set.Iic (0 : ℝ))
      (phi_snd_mem_gammaZero (φ := φ) hφ)
      hK_nonempty
      iic_zero_isClosed
      iic_zero_convex
      iic_zero_isCone
      continuous_lorentz_residual_prodL2
      lorentz_constraintMap_isConvexWithRespectTo_nonpos
      hfeas

/-- Example 19.28 (2): clause (ii), first part. The primal objective is
`ξ ↦ φ(ξ₂)` on the feasible set `‖ξ‖ ≤ ξ₁` and `+∞` outside it. -/
theorem perturbationPrimalObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    perturbationPrimalObjective (lorentzConstraintPerturbation φ) =
      fun ξ : ℝ × ℝ ↦ if ‖ξ‖ ≤ ξ.1 then (φ ξ.2 : EReal) else ⊤ := by
  -- Route correction: this is Proposition 19.25 (2) specialized and then rewritten geometrically.
  let _ := hφ
  let _ := hφ0
  simpa [lorentzConstraintPerturbation, Set.mem_Iic, sub_nonpos] using
    perturbationPrimalObjective_inequalityConstraintPerturbation
      (f := fun ξ : ℝ × ℝ ↦ φ ξ.2)
      (R := fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1)
      (K := Set.Iic (0 : ℝ))

/-- Example 19.28 (3): clause (ii), second part. The optimal primal value is `φ(0)`. -/
theorem sInf_perturbationPrimalObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    sInf (range <| perturbationPrimalObjective (lorentzConstraintPerturbation φ)) =
      φ 0 := by
  -- Every feasible point has second coordinate `0`, and the origin attains the matching value.
  refine le_antisymm ?_ ?_
  · refine sInf_le ?_
    refine ⟨(0, 0), ?_⟩
    have horigin :=
      congrFun
        (perturbationPrimalObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        (0, 0)
    have horigin' :
        perturbationPrimalObjective (lorentzConstraintPerturbation φ) (0, 0) = φ 0 := by
      rw [horigin]
      simp [prod_l2_norm_zero]
    exact horigin'
  · refine le_sInf ?_
    rintro z ⟨ξ, rfl⟩
    have hvalue :=
      congrFun
        (perturbationPrimalObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        ξ
    by_cases hfeas : ‖ξ‖ ≤ ξ.1
    · obtain ⟨hξ2, _⟩ := (lorentz_feasible_coord_iff ξ).1 hfeas
      rw [hvalue, if_pos hfeas]
      simp [hξ2]
    · rw [hvalue, if_neg hfeas]
      exact le_top

/-- Example 19.28 (4): clause (ii), third part. Under the standing assumptions
`φ ∈ Γ₀(ℝ)` and `0 ∈ dom φ`, the set of primal solutions is `ℝ₊ × {0}`. -/
theorem argmin_perturbationPrimalObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    Argmin (perturbationPrimalObjective (lorentzConstraintPerturbation φ)) =
      Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  -- The global minimizers are exactly the feasible points, and feasibility is `ℝ₊ × {0}`.
  ext ξ
  constructor
  · intro hξ
    have hvalue :
        perturbationPrimalObjective (lorentzConstraintPerturbation φ) ξ = φ 0 := by
      calc
        perturbationPrimalObjective (lorentzConstraintPerturbation φ) ξ =
            sInf (range <| perturbationPrimalObjective (lorentzConstraintPerturbation φ)) := by
              exact mem_argmin_iff_eq_sInf.mp hξ
        _ = φ 0 :=
          sInf_perturbationPrimalObjective_lorentzConstraintPerturbation
            (φ := φ) hφ hφ0
    have hφ0_lt_top : (φ 0 : EReal) < ⊤ := mem_effectiveDomain_iff.mp hφ0
    have hobj :=
      congrFun
        (perturbationPrimalObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        ξ
    by_cases hfeas : ‖ξ‖ ≤ ξ.1
    · exact (lorentz_feasible_iff ξ).1 hfeas
    · rw [hobj, if_neg hfeas] at hvalue
      exfalso
      exact hφ0_lt_top.ne (by simpa using hvalue.symm)
  · intro hξ
    have hfeas : ‖ξ‖ ≤ ξ.1 := (lorentz_feasible_iff ξ).2 hξ
    obtain ⟨hξ2, _⟩ := (lorentz_feasible_coord_iff ξ).1 hfeas
    rw [mem_argmin_iff_eq_sInf]
    rw [sInf_perturbationPrimalObjective_lorentzConstraintPerturbation
      (φ := φ) hφ hφ0]
    have hobj :=
      congrFun
        (perturbationPrimalObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        ξ
    rw [hobj, if_pos hfeas]
    simp [hξ2]

/-- Example 19.28 (5): clause (iii), first part. The dual objective is
`v ↦ sup_ξ (v (ξ₁ - ‖ξ‖) - φ(ξ₂))` on `ℝ₊` and `+∞` on `(-∞,0)`. -/
theorem perturbationDualObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    perturbationDualObjective (lorentzConstraintPerturbation φ) =
      fun v : ℝ ↦
        if 0 ≤ v then
          ⨆ ξ : ℝ × ℝ, ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal)
        else
          ⊤ := by
  -- Clause (iii) is the direct Proposition 19.25 specialization plus the polar-cone rewrite.
  have hK_nonempty : (Set.Iic (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  have hfeas :
      (Set.Iic (0 : ℝ) ∩
        (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) '' effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2)).Nonempty := by
    refine ⟨0, by simp, ?_⟩
    refine ⟨(0, 0), ?_, by simpa using prod_l2_norm_zero⟩
    simpa [mem_effectiveDomain_iff] using hφ0
  funext v
  by_cases hv : 0 ≤ v
  · have hspecialized :=
        congrFun
          (perturbationDualObjective_inequalityConstraintPerturbation
            (f := fun ξ : ℝ × ℝ ↦ φ ξ.2)
            (R := fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1)
            (K := Set.Iic (0 : ℝ))
            (phi_snd_mem_gammaZero (φ := φ) hφ)
            hK_nonempty
            iic_zero_isClosed
            iic_zero_convex
            iic_zero_isCone
            continuous_lorentz_residual_prodL2
            lorentz_constraintMap_isConvexWithRespectTo_nonpos
            hfeas)
          v
    have hvpolar : v ∈ (Set.Iic (0 : ℝ))ᵒ⊖ :=
      (mem_polarCone_Iic_zero_iff_nonneg).2 hv
    rw [if_pos hvpolar] at hspecialized
    rw [if_pos hv]
    refine hspecialized.trans ?_
    refine iSup_congr fun ξ ↦ ?_
    simpa using lorentz_dual_branch_term_eq (φ := φ) v ξ
  · have hspecialized :=
        congrFun
          (perturbationDualObjective_inequalityConstraintPerturbation
            (f := fun ξ : ℝ × ℝ ↦ φ ξ.2)
            (R := fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1)
            (K := Set.Iic (0 : ℝ))
            (phi_snd_mem_gammaZero (φ := φ) hφ)
            hK_nonempty
            iic_zero_isClosed
            iic_zero_convex
            iic_zero_isCone
            continuous_lorentz_residual_prodL2
            lorentz_constraintMap_isConvexWithRespectTo_nonpos
            hfeas)
          v
    have hvpolar : v ∉ (Set.Iic (0 : ℝ))ᵒ⊖ := by
      intro hvpolar
      exact hv ((mem_polarCone_Iic_zero_iff_nonneg).1 hvpolar)
    rw [if_neg hvpolar] at hspecialized
    rw [if_neg hv]
    exact hspecialized

/-- Helper for Example 19.28: along a horizontal ray with fixed second coordinate, the Lorentz
residual `a - ‖(a, t)‖` can exceed any prescribed negative level. -/
lemma horizontal_residual_can_exceed_any_negative_level
    (t y : ℝ) (hy : y < 0) :
    ∃ a : ℝ, 0 < a ∧ y ≤ a - ‖(a, t)‖ := by
  -- Choose `a` so that `(a - y)^2` dominates `‖(a,t)‖^2`; then compare nonnegative square roots.
  let a : ℝ := t ^ 2 / (-2 * y) + 1
  have ha_pos : 0 < a := by
    have hden_pos : 0 < -2 * y := by nlinarith
    have hfrac_nonneg : 0 ≤ t ^ 2 / (-2 * y) := by
      exact div_nonneg (sq_nonneg t) hden_pos.le
    have : 0 < t ^ 2 / (-2 * y) + 1 := by linarith
    simpa [a] using this
  have hy_ne : y ≠ 0 := ne_of_lt hy
  have hsquares :
      ‖((a, t) : ℝ × ℝ)‖ ^ 2 ≤ (a - y) ^ 2 := by
    rw [prod_norm_sq_eq]
    have haux : t ^ 2 ≤ -2 * a * y + y ^ 2 := by
      have hrewrite : -2 * a * y = t ^ 2 - 2 * y := by
        dsimp [a]
        field_simp [hy_ne]
        ring
      rw [hrewrite]
      nlinarith [hy]
    nlinarith
  have hright_nonneg : 0 ≤ a - y := by linarith
  have hnorm_le : ‖((a, t) : ℝ × ℝ)‖ ≤ a - y := by
    nlinarith [hsquares, norm_nonneg ((a, t) : ℝ × ℝ), hright_nonneg]
  refine ⟨a, ha_pos, ?_⟩
  linarith

/-- Helper for Example 19.28: every term in the nonnegative dual branch is bounded above by
`-γ`. -/
lemma dual_branch_le_neg_phiRangeInfimum {v : ℝ}
    (hv : 0 ≤ v) :
    (⨆ ξ : ℝ × ℝ, ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal)) ≤ -γ := by
  -- The Lorentz residual contributes a nonpositive term, and `γ` is a lower bound for `φ`.
  refine iSup_le fun ξ ↦ ?_
  have hres_nonpos : v * (ξ.1 - ‖ξ‖) ≤ 0 := by
    have hfst_le : ξ.1 ≤ ‖ξ‖ := by
      exact le_trans (le_abs_self ξ.1) (abs_fst_le_prod_l2_norm ξ)
    exact mul_nonpos_of_nonneg_of_nonpos hv (sub_nonpos.mpr hfst_le)
  have hterm_nonpos : (((v * (ξ.1 - ‖ξ‖) : ℝ) : ℝ) : EReal) ≤ 0 := by
    exact_mod_cast hres_nonpos
  have hphi_lower : γ ≤ (φ ξ.2 : EReal) := sInf_le ⟨ξ.2, rfl⟩
  calc
    (((v * (ξ.1 - ‖ξ‖) : ℝ) : ℝ) : EReal) - (φ ξ.2 : EReal) ≤
        (0 : EReal) - (φ ξ.2 : EReal) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            add_le_add_right hterm_nonpos (-(φ ξ.2 : EReal))
    _ = -(φ ξ.2 : EReal) := by simp
    _ ≤ -γ := by simpa using (EReal.neg_le_neg_iff.mpr hphi_lower)

/-- Helper for Example 19.28: every strict threshold below `-γ` is attained in the nonnegative
dual branch. -/
lemma lt_dual_branch_of_lt_neg_phiRangeInfimum {v : ℝ} {c : EReal}
    (hv : 0 ≤ v) (hc : ((c.toReal : ℝ) : EReal) < -γ) :
    (((c.toReal : ℝ) : EReal)) <
      (⨆ ξ : ℝ × ℝ, ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal)) := by
  -- Choose `t` with `φ t` already below the threshold, then use a horizontal ray so the
  -- Lorentz residual contributes only a small negative correction.
  have hγ_lt : γ < -(((c.toReal : ℝ) : EReal)) := by
    simpa using (EReal.neg_lt_neg_iff.mpr hc)
  rcases (sInf_lt_iff).1 hγ_lt with ⟨z, hzmem, hzlt⟩
  rcases hzmem with ⟨t, rfl⟩
  have hc_lt_neg_phi : ((c.toReal : ℝ) : EReal) < -(φ t : EReal) := by
    simpa using (EReal.neg_lt_neg_iff.mpr hzlt)
  by_cases hv_zero : v = 0
  · -- At `v = 0`, the branch reduces to the scalar value `-φ t`.
    refine lt_iSup_iff.mpr ?_
    refine ⟨(0, t), ?_⟩
    simpa [hv_zero] using hc_lt_neg_phi
  · -- For `v > 0`, realize a strictly negative slack with the horizontal-ray lemma.
    have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_zero)
    let p : ℝ := (φ t : EReal).toReal
    have hφt_ne_top : (φ t : EReal) ≠ ⊤ := hzlt.ne_top
    have hφt_ne_bot : (φ t : EReal) ≠ ⊥ := ne_of_gt (φ t).2
    have hp : ((p : ℝ) : EReal) = (φ t : EReal) := by
      simpa [p] using (EReal.coe_toReal hφt_ne_top hφt_ne_bot)
    have hp_lt : p < -c.toReal := by
      have hcast : ((p : ℝ) : EReal) < (((-c.toReal : ℝ) : EReal) : EReal) := by
        simpa [hp] using hzlt
      exact_mod_cast hcast
    let y : ℝ := (c.toReal + p) / (2 * v)
    have hy_neg : y < 0 := by
      have hnum_neg : c.toReal + p < 0 := by
        linarith
      have hden_pos : 0 < 2 * v := by positivity
      exact div_neg_of_neg_of_pos hnum_neg hden_pos
    rcases horizontal_residual_can_exceed_any_negative_level (t := t) (y := y) hy_neg with
      ⟨a, _, hresidual⟩
    have hvy_le :
        v * y ≤ v * (a - ‖((a, t) : ℝ × ℝ)‖) :=
      mul_le_mul_of_nonneg_left hresidual hv
    have hvy_eq : v * y * 2 = c.toReal + p := by
      have hv_ne : v ≠ 0 := hv_zero
      dsimp [y]
      field_simp [hv_ne]
    have hmid : c.toReal < v * y - p := by
      nlinarith [hp_lt, hvy_eq]
    have hreal :
        c.toReal <
          v * (((a, t) : ℝ × ℝ).1 - ‖((a, t) : ℝ × ℝ)‖) - p := by
      nlinarith [hmid, hvy_le]
    have hcast :
        ((c.toReal : ℝ) : EReal) <
          ((((v * (((a, t) : ℝ × ℝ).1 - ‖((a, t) : ℝ × ℝ)‖) - p) : ℝ)) : EReal) := by
      exact_mod_cast hreal
    refine lt_iSup_iff.mpr ?_
    refine ⟨(a, t), ?_⟩
    simpa [hp, p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcast

/-- Helper for Example 19.28: the nonnegative dual branch is exactly the constant value `-γ`. -/
lemma dual_branch_eq_neg_phiRangeInfimum {v : ℝ}
    (hv : 0 ≤ v) :
    (⨆ ξ : ℝ × ℝ, ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal)) = -γ := by
  -- The branch is bounded above by `-γ`, and every strict lower threshold is attained.
  refine le_antisymm (dual_branch_le_neg_phiRangeInfimum (φ := φ) hv) ?_
  refine le_of_forall_lt ?_
  intro c hc
  by_cases hc_bot : c = ⊥
  · -- For the bottom threshold, any finite branch value suffices.
    subst hc_bot
    have hγ_lt_top : γ < (⊤ : EReal) := by
      simpa using (EReal.neg_lt_neg_iff.mpr hc)
    rcases (sInf_lt_iff).1 hγ_lt_top with ⟨z, hzmem, hzlt⟩
    rcases hzmem with ⟨t, rfl⟩
    let p : ℝ := (φ t : EReal).toReal
    have hφt_ne_top : (φ t : EReal) ≠ ⊤ := hzlt.ne_top
    have hφt_ne_bot : (φ t : EReal) ≠ ⊥ := ne_of_gt (φ t).2
    have hp : ((p : ℝ) : EReal) = (φ t : EReal) := by
      simpa [p] using (EReal.coe_toReal hφt_ne_top hφt_ne_bot)
    have hfinite :
        (⊥ : EReal) <
          ((((v * (((0, t) : ℝ × ℝ).1 - ‖((0, t) : ℝ × ℝ)‖) - p) : ℝ)) : EReal) := by
      exact EReal.bot_lt_coe _
    have hbranch :
        (⊥ : EReal) <
          ((v * (((0, t) : ℝ × ℝ).1 - ‖((0, t) : ℝ × ℝ)‖) : ℝ) : EReal) - (φ t : EReal) := by
      simpa [hp, p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfinite
    exact lt_iSup_iff.mpr ⟨(0, t), hbranch⟩
  · -- Every finite threshold below `-γ` is attained by the previous lemma.
    have hc_finite : ((c.toReal : ℝ) : EReal) = c := by
      simpa using (EReal.coe_toReal hc.ne_top hc_bot)
    have hthreshold : ((c.toReal : ℝ) : EReal) < -γ := by
      simpa [hc_finite] using hc
    have hlt :=
      lt_dual_branch_of_lt_neg_phiRangeInfimum (φ := φ) (v := v) (c := c) hv hthreshold
    simpa [hc_finite] using hlt

/-- Example 19.28 (6): clause (iii), second part. The optimal dual value is `-γ`, where
`γ = inf φ(ℝ)`. -/
theorem sInf_perturbationDualObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    sInf (range <| perturbationDualObjective (lorentzConstraintPerturbation φ)) = -γ := by
  -- The nonnegative branch is the constant value `-γ`, while the negative branch is `⊤`.
  refine le_antisymm ?_ ?_
  · refine sInf_le ?_
    refine ⟨(0 : ℝ), ?_⟩
    have hobj :=
      congrFun
        (perturbationDualObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        (0 : ℝ)
    rw [hobj, if_pos (show 0 ≤ (0 : ℝ) by norm_num)]
    simpa using dual_branch_eq_neg_phiRangeInfimum (φ := φ) (v := 0) (by norm_num)
  · refine le_sInf ?_
    rintro z ⟨v, rfl⟩
    have hobj :=
      congrFun
        (perturbationDualObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        v
    by_cases hv : 0 ≤ v
    · rw [hobj, if_pos hv, dual_branch_eq_neg_phiRangeInfimum (φ := φ) hv]
    · rw [hobj, if_neg hv]
      exact le_top

/-- Helper for Example 19.28: when `γ ≠ ⊥`, the negative dual branch is strictly above the
minimum value `-γ`, so the dual minimizers are exactly the nonnegative scalars. -/
lemma dual_argmin_eq_Ici_of_phiRangeInfimum_ne_bot
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγbot : γ ≠ ⊥) :
    Argmin (perturbationDualObjective (lorentzConstraintPerturbation φ)) = Ici (0 : ℝ) := by
  -- Global minimizers are exactly the nonnegative points where the explicit dual formula equals
  -- the computed infimum `-γ`.
  ext v
  constructor
  · intro hv
    have hv_eq :
        perturbationDualObjective (lorentzConstraintPerturbation φ) v = -γ := by
      calc
        perturbationDualObjective (lorentzConstraintPerturbation φ) v =
            sInf (Set.range <| perturbationDualObjective (lorentzConstraintPerturbation φ)) := by
              exact mem_argmin_iff_eq_sInf.mp hv
        _ = -γ :=
          sInf_perturbationDualObjective_lorentzConstraintPerturbation
            (φ := φ) hφ hφ0
    have hobj :=
      congrFun
        (perturbationDualObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        v
    by_cases hv_nonneg : 0 ≤ v
    · exact hv_nonneg
    · rw [hobj, if_neg hv_nonneg] at hv_eq
      have hnegγ_ne_top : (-γ : EReal) ≠ ⊤ := by
        simpa using hγbot
      exfalso
      exact hnegγ_ne_top hv_eq.symm
  · intro hv
    rw [mem_argmin_iff_eq_sInf]
    rw [sInf_perturbationDualObjective_lorentzConstraintPerturbation
      (φ := φ) hφ hφ0]
    have hv_nonneg : 0 ≤ v := hv
    have hobj :=
      congrFun
        (perturbationDualObjective_lorentzConstraintPerturbation
          (φ := φ) hφ hφ0)
        v
    rw [hobj, if_pos hv_nonneg, dual_branch_eq_neg_phiRangeInfimum (φ := φ) hv_nonneg]

/-- Example 19.28 (7): clause (iii), third part. The set of dual solutions of `(19.69)` over the
constraint set `ℝ₊` is `ℝ₊`. -/
theorem argmin_perturbationDualObjective_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    Argmin[Ici (0 : ℝ)] (perturbationDualObjective (lorentzConstraintPerturbation φ)) =
      Ici (0 : ℝ) := by
  -- On the constraint set `ℝ₊`, the dual objective is constant equal to `-γ`.
  ext v
  constructor
  · intro hv
    exact (mem_argminOn_iff.mp hv).1
  · intro hv
    have hv_nonneg : 0 ≤ v := hv
    rw [mem_argminOn_iff, isMinOn_iff]
    constructor
    · exact hv
    · intro w hw
      have hv_obj :=
        congrFun
          (perturbationDualObjective_lorentzConstraintPerturbation
            (φ := φ) hφ hφ0)
          v
      have hw_obj :=
        congrFun
          (perturbationDualObjective_lorentzConstraintPerturbation
            (φ := φ) hφ hφ0)
          w
      have hw_nonneg : 0 ≤ w := hw
      rw [hv_obj, if_pos hv_nonneg, dual_branch_eq_neg_phiRangeInfimum (φ := φ) hv_nonneg]
      rw [hw_obj, if_pos hw_nonneg, dual_branch_eq_neg_phiRangeInfimum (φ := φ) hw_nonneg]

/-- Example 19.28 (8): clause (iv). The Lagrangian has the branch formula displayed in `(19.70)`.
-/
theorem lagrangian_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (ξ : ℝ × ℝ) (v : ℝ) :
    ℒ[lorentzConstraintPerturbation φ] ξ v =
      if _hξ : ξ.2 ∈ effectiveDomain φ then
        if 0 ≤ v then
          (φ ξ.2 : EReal) + ((v * (‖ξ‖ - ξ.1) : ℝ) : EReal)
        else
          ⊥
      else
        ⊤ := by
  -- Clause (iv) is again the Proposition 19.25 specialization with the polar-cone rewrite.
  have hK_nonempty : (Set.Iic (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  have hfeas :
      (Set.Iic (0 : ℝ) ∩
        (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) '' effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2)).Nonempty := by
    refine ⟨0, by simp, ?_⟩
    refine ⟨(0, 0), ?_, by simpa using prod_l2_norm_zero⟩
    simpa [mem_effectiveDomain_iff] using hφ0
  simpa [lorentzConstraintPerturbation, mem_polarCone_Iic_zero_iff_nonneg, real_inner_eq_mul,
    mem_effectiveDomain_iff, mul_comm] using
    lagrangian_inequalityConstraintPerturbation
      (f := fun η : ℝ × ℝ ↦ φ η.2)
      (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
      (K := Set.Iic (0 : ℝ))
      (phi_snd_mem_gammaZero (φ := φ) hφ)
      hK_nonempty
      iic_zero_isClosed
      iic_zero_convex
      iic_zero_isCone
      continuous_lorentz_residual_prodL2
      lorentz_constraintMap_isConvexWithRespectTo_nonpos
      hfeas
      ξ v

/-- Helper for Example 19.28: the feasibility hypothesis from Proposition 19.25 holds for the
Lorentz perturbation because `(0, 0)` is feasible whenever `0 ∈ dom φ`. -/
lemma lorentz_constraint_feasible_inter_nonempty
    (hφ0 : 0 ∈ effectiveDomain φ) :
    (Set.Iic (0 : ℝ) ∩
      (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) '' effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2)).Nonempty := by
  have hzero_mem : (0 : ℝ) ∈ Set.Iic (0 : ℝ) := by
    simp
  have hdom : (0, 0) ∈ effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2) := by
    simpa [mem_effectiveDomain_iff] using hφ0
  have himage :
      (0 : ℝ) ∈
        (fun ξ : ℝ × ℝ ↦ ‖ξ‖ - ξ.1) '' effectiveDomain (fun ξ : ℝ × ℝ ↦ φ ξ.2) := by
    refine ⟨(0, 0), hdom, ?_⟩
    simpa using prod_l2_norm_zero
  exact ⟨0, hzero_mem, himage⟩

/-- Helper for Example 19.28: for nonnegative multipliers, the Lorentz Lagrangian is exactly the
shifted objective `ξ ↦ φ ξ₂ + v (‖ξ‖ - ξ₁)`. -/
lemma lagrangian_lorentzConstraintPerturbation_of_nonneg
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) {v : ℝ}
    (hv : 0 ≤ v) (ξ : ℝ × ℝ) :
    ℒ[lorentzConstraintPerturbation φ] ξ v =
      (φ ξ.2 : EReal) + (((v * (‖ξ‖ - ξ.1) : ℝ)) : EReal) := by
  by_cases hξ : ξ.2 ∈ effectiveDomain φ
  · have hlag :=
      lagrangian_lorentzConstraintPerturbation (φ := φ) hφ hφ0 ξ v
    simpa [hξ, hv] using hlag
  · have hφ_top : (φ ξ.2 : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ))
    have hlag :=
      lagrangian_lorentzConstraintPerturbation (φ := φ) hφ hφ0 ξ v
    calc
      ℒ[lorentzConstraintPerturbation φ] ξ v = ⊤ := by
        simpa [hξ] using hlag
      _ = (φ ξ.2 : EReal) + (((v * (‖ξ‖ - ξ.1) : ℝ)) : EReal) := by
        rw [hφ_top]
        have hne :
            ((((v * (‖ξ‖ - ξ.1) : ℝ)) : ℝ) : EReal) ≠ ⊥ := by
          simpa using (EReal.coe_ne_bot (v * (‖ξ‖ - ξ.1)))
        simpa using (EReal.top_add_of_ne_bot hne).symm

/-- Helper for Example 19.28: every nonnegative shifted objective
`ξ ↦ φ ξ₂ + v (‖ξ‖ - ξ₁)` has infimum `γ`. -/
lemma sInf_lorentz_shiftedObjective_eq_phiRangeInfimum
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) {v : ℝ}
    (hv : 0 ≤ v) :
    sInf (Set.range fun ξ : ℝ × ℝ ↦
      (φ ξ.2 : EReal) + (((v * (‖ξ‖ - ξ.1) : ℝ)) : EReal)) = γ := by
  have hrange :
      Set.range (fun ξ : ℝ × ℝ ↦
        (φ ξ.2 : EReal) + (((v * (‖ξ‖ - ξ.1) : ℝ)) : EReal)) =
        Set.range (fun ξ : ℝ × ℝ ↦ ℒ[lorentzConstraintPerturbation φ] ξ v) := by
    ext z
    constructor
    · rintro ⟨ξ, rfl⟩
      refine ⟨ξ, ?_⟩
      simpa using lagrangian_lorentzConstraintPerturbation_of_nonneg (φ := φ) hφ hφ0 hv ξ
    · rintro ⟨ξ, rfl⟩
      refine ⟨ξ, ?_⟩
      simpa using
        (lagrangian_lorentzConstraintPerturbation_of_nonneg (φ := φ) hφ hφ0 hv ξ).symm
  have hlag :
      sInf (Set.range fun ξ : ℝ × ℝ ↦ ℒ[lorentzConstraintPerturbation φ] ξ v) =
        -perturbationDualObjective (lorentzConstraintPerturbation φ) v := by
    -- Flatten the fixed-`v` Lagrangian fiber to a product infimum, then identify the resulting
    -- supremum with the explicit dual objective owner.
    calc
      sInf (Set.range fun ξ : ℝ × ℝ ↦ ℒ[lorentzConstraintPerturbation φ] ξ v) =
          ⨅ p : (ℝ × ℝ) × ℝ,
            (lorentzConstraintPerturbation φ p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
              rw [sInf_range]
              simp [lagrangian_apply, iInf_prod]
      _ = ⨅ p : (ℝ × ℝ) × ℝ,
            -((((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (lorentzConstraintPerturbation φ p : EReal))) := by
              refine iInf_congr fun p ↦ ?_
              simpa [sub_eq_add_neg, add_comm] using
                (EReal.neg_sub
                  (x := (((⟪p.2, v⟫_ℝ : ℝ) : EReal)))
                  (y := (lorentzConstraintPerturbation φ p : EReal))
                  (.inl (EReal.coe_ne_bot _))
                  (.inl (EReal.coe_ne_top _))).symm
      _ = -(⨆ p : (ℝ × ℝ) × ℝ,
              (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (lorentzConstraintPerturbation φ p : EReal))) := by
              let ψ : (ℝ × ℝ) × ℝ → EReal := fun p ↦
                (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (lorentzConstraintPerturbation φ p : EReal))
              simpa [ψ] using iInf_neg_eq_neg_iSup_ereal ψ
      _ = -perturbationDualObjective (lorentzConstraintPerturbation φ) v := by
            rw [perturbationDualObjective_apply]
  calc
    sInf (Set.range fun ξ : ℝ × ℝ ↦
        (φ ξ.2 : EReal) + (((v * (‖ξ‖ - ξ.1) : ℝ)) : EReal)) =
        sInf (Set.range fun ξ : ℝ × ℝ ↦ ℒ[lorentzConstraintPerturbation φ] ξ v) := by
          rw [hrange]
    _ = -perturbationDualObjective (lorentzConstraintPerturbation φ) v := by
          exact hlag
    _ = -(-γ) := by
          have hdual :=
            congrFun
              (perturbationDualObjective_lorentzConstraintPerturbation
                (φ := φ) hφ hφ0)
              v
          rw [hdual, if_pos hv, dual_branch_eq_neg_phiRangeInfimum (φ := φ) hv]
    _ = γ := by simp

/-- Example 19.28 (9): clause (v), first part. The Lagrangian has a saddle point if and only if
`φ(0) = γ`. -/
theorem exists_saddlePoint_lorentzConstraintPerturbation_iff
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    (∃ ξ : ℝ × ℝ, ∃ v : ℝ,
      IsSaddlePointOn (univ : Set (ℝ × ℝ)) (univ : Set ℝ)
        (ℒ[lorentzConstraintPerturbation φ]) ξ v) ↔
      (φ 0 : EReal) = γ := by
  -- Proposition 19.25 identifies saddle points with the Lorentz optimality system, and the
  -- shifted-objective infimum is already computed above.
  have hzero_mem : (0 : ℝ) ∈ Set.Iic (0 : ℝ) := by
    simp
  have hK_nonempty : (Set.Iic (0 : ℝ)).Nonempty := ⟨0, hzero_mem⟩
  have hfeas := lorentz_constraint_feasible_inter_nonempty (φ := φ) hφ0
  constructor
  · rintro ⟨ξ, v, hsaddle⟩
    have hs :=
      (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (phi_snd_mem_gammaZero (φ := φ) hφ)
        hK_nonempty
        iic_zero_isClosed
        iic_zero_convex
        iic_zero_isCone
        continuous_lorentz_residual_prodL2
        lorentz_constraintMap_isConvexWithRespectTo_nonpos
        hfeas
        ξ v).mp hsaddle
    have hfeasible : ‖ξ‖ ≤ ξ.1 := by
      simpa [Set.mem_setOf_eq, Set.mem_Iic] using hs.1.2
    have hξ2_zero : ξ.2 = 0 := (lorentz_feasible_coord_iff ξ).1 hfeasible |>.1
    have hv : 0 ≤ v := (mem_polarCone_Iic_zero_iff_nonneg).1 hs.2.1
    have hsInf :
        (φ ξ.2 : EReal) =
          sInf (Set.range fun η : ℝ × ℝ ↦
            (φ η.2 : EReal) + (((v * (‖η‖ - η.1) : ℝ)) : EReal)) := by
      simpa [real_inner_eq_mul, mul_comm] using hs.2.2
    calc
      (φ 0 : EReal) = (φ ξ.2 : EReal) := by
            simp [hξ2_zero]
      _ = sInf (Set.range fun η : ℝ × ℝ ↦
            (φ η.2 : EReal) + (((v * (‖η‖ - η.1) : ℝ)) : EReal)) :=
        hsInf
      _ = γ :=
        sInf_lorentz_shiftedObjective_eq_phiRangeInfimum (φ := φ) hφ hφ0 hv
  · intro hγ
    have hξdom : (0, 0) ∈ effectiveDomain (fun η : ℝ × ℝ ↦ φ η.2) := by
      simpa [mem_effectiveDomain_iff] using hφ0
    have hξfeas : (0, 0) ∈ {η : ℝ × ℝ | ‖η‖ - η.1 ∈ Set.Iic (0 : ℝ)} := by
      simp [Set.mem_setOf_eq, prod_l2_norm_zero]
    have hvpolar : (0 : ℝ) ∈ (Set.Iic (0 : ℝ))ᵒ⊖ := by
      exact (mem_polarCone_Iic_zero_iff_nonneg).2 (by norm_num)
    have hsInf :
        (φ 0 : EReal) =
          sInf (Set.range fun η : ℝ × ℝ ↦
            (φ η.2 : EReal) + ((((0 : ℝ) * (‖η‖ - η.1) : ℝ)) : EReal)) := by
      calc
        (φ 0 : EReal) = γ := hγ
        _ = sInf (Set.range fun η : ℝ × ℝ ↦
              (φ η.2 : EReal) + ((((0 : ℝ) * (‖η‖ - η.1) : ℝ)) : EReal)) := by
                symm
                exact sInf_lorentz_shiftedObjective_eq_phiRangeInfimum
                  (φ := φ) hφ hφ0 (by norm_num)
    refine ⟨(0, 0), 0, ?_⟩
    exact
      (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (phi_snd_mem_gammaZero (φ := φ) hφ)
        hK_nonempty
        iic_zero_isClosed
        iic_zero_convex
        iic_zero_isCone
        continuous_lorentz_residual_prodL2
        lorentz_constraintMap_isConvexWithRespectTo_nonpos
        hfeas
        (0, 0) (0 : ℝ)).mpr <|
        ⟨⟨hξdom, hξfeas⟩, hvpolar, by simpa [real_inner_eq_mul, mul_comm] using hsInf⟩

/-- Example 19.28 (10): clause (v), second part. When `φ(0) = γ`, the saddle points are exactly
`(ℝ₊ × {0}) × ℝ₊`. -/
theorem saddlePoints_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγ : (φ 0 : EReal) = γ) :
    {p : (ℝ × ℝ) × ℝ |
        IsSaddlePointOn (univ : Set (ℝ × ℝ)) (univ : Set ℝ)
          (ℒ[lorentzConstraintPerturbation φ]) p.1 p.2} =
      (Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) ×ˢ Ici (0 : ℝ) := by
  -- Proposition 19.25 reduces the saddle-point set to the explicit Lorentz optimality system.
  have hzero_mem : (0 : ℝ) ∈ Set.Iic (0 : ℝ) := by
    simp
  have hK_nonempty : (Set.Iic (0 : ℝ)).Nonempty := ⟨0, hzero_mem⟩
  have hfeas := lorentz_constraint_feasible_inter_nonempty (φ := φ) hφ0
  ext p
  rcases p with ⟨ξ, v⟩
  constructor
  · intro hsaddle
    have hs :=
      (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (phi_snd_mem_gammaZero (φ := φ) hφ)
        hK_nonempty
        iic_zero_isClosed
        iic_zero_convex
        iic_zero_isCone
        continuous_lorentz_residual_prodL2
        lorentz_constraintMap_isConvexWithRespectTo_nonpos
        hfeas
        ξ v).mp hsaddle
    have hfeasible : ‖ξ‖ ≤ ξ.1 := by
      simpa [Set.mem_setOf_eq, Set.mem_Iic] using hs.1.2
    have hcoords : ξ.2 = 0 ∧ 0 ≤ ξ.1 := (lorentz_feasible_coord_iff ξ).1 hfeasible
    have hξset : ξ ∈ Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
      simp [hcoords.1, hcoords.2, Set.mem_prod]
    have hvset : v ∈ Ici (0 : ℝ) := by
      exact (mem_polarCone_Iic_zero_iff_nonneg).1 hs.2.1
    simpa [Set.mem_prod] using And.intro hξset hvset
  · intro hp
    have hp' : ξ ∈ Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) ∧ v ∈ Ici (0 : ℝ) := by
      simpa [Set.mem_prod] using hp
    have hcoords : ξ.2 = 0 ∧ 0 ≤ ξ.1 := by
      simpa [Set.mem_prod] using ⟨hp'.1.2, hp'.1.1⟩
    have hξdom : ξ ∈ effectiveDomain (fun η : ℝ × ℝ ↦ φ η.2) := by
      simpa [mem_effectiveDomain_iff, hcoords.1] using hφ0
    have hfeasible : ‖ξ‖ ≤ ξ.1 := by
      exact (lorentz_feasible_coord_iff ξ).2 hcoords
    have hξfeas : ξ ∈ {η : ℝ × ℝ | ‖η‖ - η.1 ∈ Set.Iic (0 : ℝ)} := by
      simpa [Set.mem_setOf_eq, Set.mem_Iic] using hfeasible
    have hvpolar : v ∈ (Set.Iic (0 : ℝ))ᵒ⊖ := by
      exact (mem_polarCone_Iic_zero_iff_nonneg).2 hp'.2
    have hsInf :
        (φ ξ.2 : EReal) =
          sInf (Set.range fun η : ℝ × ℝ ↦
            (φ η.2 : EReal) + (((v * (‖η‖ - η.1) : ℝ)) : EReal)) := by
      calc
        (φ ξ.2 : EReal) = (φ 0 : EReal) := by
              simp [hcoords.1]
        _ = γ := hγ
        _ = sInf (Set.range fun η : ℝ × ℝ ↦
              (φ η.2 : EReal) + (((v * (‖η‖ - η.1) : ℝ)) : EReal)) := by
                symm
                exact sInf_lorentz_shiftedObjective_eq_phiRangeInfimum
                  (φ := φ) hφ hφ0 hp'.2
    exact
      (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
        (f := fun η : ℝ × ℝ ↦ φ η.2)
        (R := fun η : ℝ × ℝ ↦ ‖η‖ - η.1)
        (K := Set.Iic (0 : ℝ))
        (phi_snd_mem_gammaZero (φ := φ) hφ)
        hK_nonempty
        iic_zero_isClosed
        iic_zero_convex
        iic_zero_isCone
        continuous_lorentz_residual_prodL2
        lorentz_constraintMap_isConvexWithRespectTo_nonpos
        hfeas
        ξ v).mpr <|
        ⟨⟨hξdom, hξfeas⟩, hvpolar, by simpa [real_inner_eq_mul, mul_comm] using hsInf⟩

/-- Helper for Example 19.28: every negative value-function slice equals the infimum `γ`. -/
lemma negative_value_slice_eq_phiRangeInfimum {y : ℝ}
    (hy : y < 0) :
    (Prod.snd ▷ lorentzConstraintPerturbation φ) y = γ := by
  -- Negative slices realize every scalar value `φ t` along a horizontal ray, and no slice value
  -- can drop below the infimum `γ`.
  rw [infimalPostcomposition_snd_apply]
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro z ⟨t, rfl⟩
    rcases horizontal_residual_can_exceed_any_negative_level (t := t) (y := y) hy with
      ⟨a, _, hay⟩
    have hfeas : y ≤ (a : ℝ) - ‖((a, t) : ℝ × ℝ)‖ := hay
    calc
      ⨅ ξ : ℝ × ℝ, (lorentzConstraintPerturbation φ (ξ, y) : EReal) ≤
          (lorentzConstraintPerturbation φ (((a, t) : ℝ × ℝ), y) : EReal) := by
            exact
              iInf_le
                (fun ξ : ℝ × ℝ ↦ (lorentzConstraintPerturbation φ (ξ, y) : EReal))
                (a, t)
        _ = (φ t : EReal) := by
              have hbranch : (a : ℝ) - ‖((a, t) : ℝ × ℝ)‖ ≥ y := by linarith
              simpa [hbranch] using
                (lorentzConstraintPerturbation_apply (φ := φ) ((a, t) : ℝ × ℝ) y)
  · refine le_iInf fun ξ ↦ ?_
    by_cases hfeas : ξ.1 - ‖ξ‖ ≥ y
    · have hvalue := lorentzConstraintPerturbation_apply (φ := φ) ξ y
      rw [if_pos hfeas] at hvalue
      exact le_trans (sInf_le ⟨ξ.2, rfl⟩) (by simp [hvalue])
    · have hvalue := lorentzConstraintPerturbation_apply (φ := φ) ξ y
      rw [if_neg hfeas] at hvalue
      simp [hvalue]

/-- Helper for Example 19.28: every positive value-function slice is infeasible, hence equal to
`+∞`. -/
lemma positive_value_slice_eq_top {y : ℝ}
    (hy : 0 < y) :
    (Prod.snd ▷ lorentzConstraintPerturbation φ) y = ⊤ := by
  -- Every Lorentz residual satisfies `ξ₁ - ‖ξ‖ ≤ 0`, so a positive slice is everywhere infeasible.
  rw [infimalPostcomposition_snd_apply]
  refine le_antisymm le_top ?_
  refine le_iInf fun ξ ↦ ?_
  have hfst_le : ξ.1 ≤ ‖ξ‖ := by
    exact le_trans (le_abs_self ξ.1) (abs_fst_le_prod_l2_norm ξ)
  have hres_nonpos : ξ.1 - ‖ξ‖ ≤ 0 := sub_nonpos.mpr hfst_le
  have hnotfeas : ¬ ξ.1 - ‖ξ‖ ≥ y := by
    linarith
  have hvalue := lorentzConstraintPerturbation_apply (φ := φ) ξ y
  rw [if_neg hnotfeas] at hvalue
  simp [hvalue]

/-- Example 19.28 (11): clause (vi). The value function equals `γ` on `(-∞,0)`, equals `φ(0)` at
`0`, and equals `+∞` on `(0,+∞)`. -/
theorem valueFunction_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    Prod.snd ▷ lorentzConstraintPerturbation φ =
      fun y : ℝ ↦
        if y < 0 then
          γ
        else if y = 0 then
          (φ 0 : EReal)
        else
          ⊤ := by
  -- Assemble the three slice computations from clauses (ii) and (vi).
  funext y
  by_cases hy_neg : y < 0
  · rw [if_pos hy_neg]
    exact negative_value_slice_eq_phiRangeInfimum (φ := φ) hy_neg
  · have hy_nonneg : 0 ≤ y := le_of_not_gt hy_neg
    by_cases hy_zero : y = 0
    · subst hy_zero
      rw [if_neg (show ¬ (0 : ℝ) < 0 by norm_num), if_pos rfl]
      calc
        (Prod.snd ▷ lorentzConstraintPerturbation φ) 0 =
            sInf (Set.range <| perturbationPrimalObjective (lorentzConstraintPerturbation φ)) := by
              rw [infimalPostcomposition_snd_apply, sInf_range]
              refine iInf_congr fun ξ ↦ ?_
              simp [perturbationPrimalObjective]
        _ = (φ 0 : EReal) :=
          sInf_perturbationPrimalObjective_lorentzConstraintPerturbation (φ := φ) hφ hφ0
    · have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy_zero)
      rw [if_neg hy_neg, if_neg hy_zero]
      exact positive_value_slice_eq_top (φ := φ) hy_pos

end

end ERealFunction
