import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Semicontinuity.Basic
import BauschkeLean.Chap01.Text_1_0_54
import BauschkeLean.Chap08.Proposition_8_35
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction

universe u v

namespace ERealFunction

noncomputable section

section ParametricDualityCore

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The Lagrangian associated with `F`, written as the canonical first-projection infimal
postcomposition of the affine defect `(x, y) ↦ F (x, y) - ⟪y, v⟫`. -/
def lagrangian (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (v : K) : EReal :=
  (Prod.fst ▷ fun p : H × K ↦ (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal)) x

notation3:max "ℒ[" F "]" => lagrangian F

/-- Evaluating the Lagrangian gives the canonical fiberwise `iInf` formula
`inf_y (F(x, y) - ⟪y, v⟫)`. -/
@[simp] theorem lagrangian_apply
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (v : K) :
    ℒ[F] x v = ⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
  -- Rewrite the first-projection infimal postcomposition as the canonical `iInf` over the slice.
  simpa [lagrangian] using
    (infimalPostcomposition_fst_apply
      (fun p : H × K ↦ (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal)) x)

end ParametricDualityCore

end

end ERealFunction

-- Semantic recall: `lean_leansearch` confirmed that the direct function-level owners here are
-- `lagrangian`, `ConcaveOn`, and `_root_.ConvexOn ℝ Set.univ`, so the labeled surface uses those
-- predicates rather than set-level `IsConvex` or a negated convexity bridge.

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/-- Helper for Proposition 19.17: in `EReal`, taking the infimum of pointwise negatives is the
same as negating the corresponding supremum. -/
private theorem iInf_neg_eq_neg_iSup_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨅ i, -φ i) = -(⨆ i, φ i) := by
  -- Negation is an order isomorphism, so it transports the `iInf` to an `iSup`.
  have hmap : -(⨅ i, -φ i) = ⨆ i, -(-φ i) := by
    exact OrderIso.map_iInf EReal.negOrderIso (fun i : ι ↦ -φ i)
  have hmap' : -(⨅ i, -φ i) = (⨆ i, φ i) := by
    simpa using hmap
  rw [← hmap']
  simp

/-- Helper for Proposition 19.17: in `EReal`, taking the supremum of pointwise negatives is the
same as negating the corresponding infimum. -/
private theorem iSup_neg_eq_neg_iInf_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨆ i, -φ i) = -(⨅ i, φ i) := by
  -- This is the dual form of `iInf_neg_eq_neg_iSup_ereal`.
  have hdual : (⨅ i, φ i) = -(⨆ i, -φ i) := by
    simpa using (iInf_neg_eq_neg_iSup_ereal (fun i : ι ↦ -φ i))
  have hneg := congrArg Neg.neg hdual
  simpa using hneg.symm

-- Proof sketch: expand the Lagrangian fiber as an infimum of affine defects and then rewrite each
-- defect as the negative of the conjugate summand.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: for fixed `x`, the second-variable Lagrangian fiber is the
negative conjugate of the slice `y ↦ F (x, y)`. -/
private theorem lagrangian_eq_neg_conjugate_second_variable_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    ℒ[F] x = fun v ↦ -((fun y : K ↦ (F (x, y) : EReal))∗ v) := by
  ext v
  -- Normalize the fiber to an infimum of negatives and collapse it to a negated supremum.
  rw [lagrangian_apply, conjugate_apply]
  calc
    (⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)) =
        ⨅ y : K, -((((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          refine iInf_congr fun y ↦ ?_
          simpa [sub_eq_add_neg, add_comm] using
            (EReal.neg_sub
              (x := (((⟪y, v⟫_ℝ : ℝ) : EReal)))
              (y := (F (x, y) : EReal))
              (.inl (EReal.coe_ne_bot _))
              (.inl (EReal.coe_ne_top _))).symm
    _ = -(⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          let φ : K → EReal := fun y : K ↦
            (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))
          simpa [φ] using iInf_neg_eq_neg_iSup_ereal φ

-- Proof sketch: lower semicontinuity is preserved by the continuous slice embedding `y ↦ (x, y)`,
-- and convexity specializes directly from the ambient Jensen inequality.
omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: a nonempty fixed-`x` slice of a `Γ₀(H × K)` perturbation again
lies in `Γ₀(K)`. -/
private theorem second_variable_slice_mem_gammaZero_of_nonempty_effectiveDomain
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H)
    (hx : (effectiveDomain (fun y : K ↦ F (x, y))).Nonempty) :
    (fun y : K ↦ F (x, y)) ∈ Γ₀(K) := by
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · -- The slice is the composition of `F` with the continuous map `y ↦ (x, y)`.
    simpa [Function.comp] using hF.1.comp (Continuous.prodMk_right x)
  · refine ⟨hx, ?_, ?_⟩
    · intro y hy
      simpa [mem_effectiveDomain_iff] using hy
    · intro y₁ hy₁ y₂ hy₂ α hα0 hα1
      -- Specialize convexity of the ambient perturbation to the two slice points.
      simpa [Prod.smul_mk, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using
        hF.2.ineq
          (x := (x, y₁))
          (hx := by simpa [mem_effectiveDomain_iff] using hy₁)
          (y := (x, y₂))
          (hy := by simpa [mem_effectiveDomain_iff] using hy₂)
          (α := α) hα0 hα1

-- Proof sketch: rewrite the fiber as the negative conjugate of the slice, convert the supremum to
-- a negated infimum, and evaluate the slice biconjugate at `0`.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 19.17: if the fixed `x`-slice lies in `Γ₀(K)`, then the supremum of the
corresponding Lagrangian fiber is the primal perturbation objective at `x`. -/
private theorem lagrangianFiberSup_eq_perturbationPrimalObjective_of_slice_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H)
    (hx : (fun y : K ↦ F (x, y)) ∈ Γ₀(K)) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := by
  let fx : K → Set.Ioi (⊥ : EReal) := fun y : K ↦ F (x, y)
  have hsSup :
      sSup (Set.range (ℒ[F] x)) = -sInf (Set.range fun v : K ↦ fx.asEReal∗ v) := by
    -- Rewrite the fiber as a pointwise negative conjugate and turn the `sSup` into an `iSup`.
    rw [lagrangian_eq_neg_conjugate_second_variable_slice, sSup_range, sInf_range]
    simpa using iSup_neg_eq_neg_iInf_ereal (fun v : K ↦ fx.asEReal∗ v)
  -- Evaluate the resulting biconjugate identity at the origin of `K`.
  calc
    sSup (Set.range (ℒ[F] x)) = -sInf (Set.range fun v : K ↦ fx.asEReal∗ v) := hsSup
    _ = -(⨅ v : K, fx.asEReal∗ v) := by
          rw [sInf_range]
    _ = fx.asEReal∗∗ 0 := by
          symm
          exact conjugate_zero_eq_neg_iInf (fx.asEReal∗)
    _ = fx.asEReal 0 := by
          simpa using congrFun (biconjugate_eq_of_mem_gammaZero hx) 0
    _ = perturbationPrimalObjective F x := by
          rw [perturbationPrimalObjective_apply]

-- Proof sketch: either the fixed slice is nonempty, when the slice-local `Γ₀` theorem applies, or
-- it is empty, in which case every fiber value is `⊤`.
omit [CompleteSpace H] in
/-- Helper for Proposition 19.17: if `F ∈ Γ₀(H × K)`, then the fixed-`x` Lagrangian fiber has
supremum equal to the primal perturbation objective at `x`. -/
private theorem lagrangianFiberSup_eq_perturbationPrimalObjective_of_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := by
  by_cases hslice : (effectiveDomain (fun y : K ↦ F (x, y))).Nonempty
  · -- The nonempty branch reduces to the slice-local `Γ₀(K)` statement.
    exact lagrangianFiberSup_eq_perturbationPrimalObjective_of_slice_mem_gammaZero F x
      (second_variable_slice_mem_gammaZero_of_nonempty_effectiveDomain F hF x hslice)
  · have htop_slice : ∀ y : K, (F (x, y) : EReal) = ⊤ := by
      intro y
      by_contra hy
      exact hslice ⟨y, mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy)⟩
    have hlag_top : ∀ v : K, ℒ[F] x v = ⊤ := by
      intro v
      calc
        ℒ[F] x v = ⨅ y : K, (⊤ : EReal) := by
          rw [lagrangian_apply]
          refine iInf_congr fun y ↦ ?_
          rw [htop_slice y]
          exact EReal.top_sub (EReal.coe_ne_top _)
        _ = ⊤ := by
          simp
    have hrange_top :
        Set.range (ℒ[F] x) = ({(⊤ : EReal)} : Set EReal) := by
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        rw [hlag_top v]
        simp
      · intro hz
        have hz' : z = (⊤ : EReal) := by
          simpa using hz
        subst z
        exact ⟨0, hlag_top 0⟩
    -- In the empty-slice branch both sides collapse to `⊤`.
    calc
      sSup (Set.range (ℒ[F] x)) = sSup ({(⊤ : EReal)} : Set EReal) := by
          rw [hrange_top]
      _ = (⊤ : EReal) := by
          simp
      _ = perturbationPrimalObjective F x := by
          rw [perturbationPrimalObjective_apply, htop_slice 0]

-- Proof sketch: subtracting a finite linear form from an `]-∞,+∞]` value keeps the result above
-- `⊥`, so it still lies in the textbook codomain.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: the fixed dual tilt
`(F p : EReal) - (⟪p.2, v⟫_ℝ : EReal)` still belongs to `]-∞,+∞]`. -/
private theorem lagrangianSecondVariableTilt_memIoi
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) (p : H × K) :
    ⊥ < (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
  -- Rewrite subtraction as addition of a finite negated scalar term and exclude `⊥`.
  rw [sub_eq_add_neg, bot_lt_iff_ne_bot]
  refine (EReal.add_ne_bot_iff.2 ?_)
  refine ⟨ne_of_gt (F p).2, ?_⟩
  intro hbot
  have htop : (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) = ⊤ := by
    simpa using congrArg Neg.neg hbot
  exact EReal.coe_ne_top _ htop

-- Proof sketch: flatten the outer infimum over `x` and the inner infimum over `y` into one
-- product-space infimum.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: the infimum of the fixed-`v` Lagrangian fiber over `x` is a
single infimum over pairs `(x, y)`. -/
private theorem lagrangian_sInf_range_eq_iInf_prod_second_variable_tilt
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x : H ↦ ℒ[F] x v) =
      ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
  -- Normalize the marginal infimum to the product-space `iInf`.
  calc
    sInf (Set.range fun x : H ↦ ℒ[F] x v) = ⨅ x : H, ℒ[F] x v := by
          rw [sInf_range]
    _ = ⨅ x : H, ⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
          simp [lagrangian_apply]
    _ = ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
          rw [iInf_prod]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [CompleteSpace K] in
/-- Upper-semicontinuity clause of Proposition 19.17: for every `x ∈ ℋ`,
the fiber `v ↦ ℒ[F] x v` is upper semicontinuous on `𝒦`. -/
theorem lagrangian_upperSemicontinuous_in_second_variable
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    UpperSemicontinuous (lagrangian F x) := by
  let fx : K → EReal := fun y : K ↦ (F (x, y) : EReal)
  have hconj_lsc : LowerSemicontinuous (fx∗) := by
    -- The Fenchel conjugate always lies in `Γ(K)`, hence is lower semicontinuous.
    exact (mem_gamma_iff (fx∗)).mp (conjugate_mem_gamma fx) |>.2
  have hneg_eq : (fun v : K ↦ -(lagrangian F x v)) = fx∗ := by
    -- Negating the fiber-formula removes the outer minus from the conjugate normal form.
    funext v
    have hv := congrFun (lagrangian_eq_neg_conjugate_second_variable_slice F x) v
    simpa [fx] using congrArg Neg.neg hv
  rw [upperSemicontinuous_iff]
  intro v
  rw [upperSemicontinuousAt_iff_lowerSemicontinuousAt_neg]
  -- Pointwise, `-ℒ[F] x` is exactly the conjugate of the fixed slice.
  rw [hneg_eq]
  exact lowerSemicontinuous_iff_forall_lowerSemicontinuousAt.mp hconj_lsc v

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: for fixed `x`, the Fenchel conjugate of the slice
`y ↦ (F (x, y) : EReal)` is convex on all of `K`. -/
private theorem conjugateSecondVariableSlice_convexOn
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    _root_.ConvexOn ℝ Set.univ (fun v : K ↦ ((fun y : K ↦ (F (x, y) : EReal))∗ v)) := by
  let fx : K → EReal := fun y : K ↦ (F (x, y) : EReal)
  have hgamma : fx∗ ∈ gamma K := conjugate_mem_gamma fx
  -- The Chapter 13 `Γ(K)` owner packages exactly the convexity data needed here.
  simpa [fx] using ((mem_gamma_iff (fx∗)).mp hgamma).1.convexOn_univ

/-- Helper for Proposition 19.17: with nonnegative real coefficients, negation distributes across
the corresponding weighted `EReal` sum as soon as both summands are not `⊥`. -/
private theorem ereal_neg_weighted_sum_eq_weighted_neg
    {u w : EReal} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : u ≠ ⊥) (hw : w ≠ ⊥) :
    -((a : EReal) * u + (b : EReal) * w) = (a : EReal) * (-u) + (b : EReal) * (-w) := by
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hbE : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hmul₁_ne_bot : (a : EReal) * u ≠ ⊥ := by
    rw [EReal.mul_ne_bot]
    exact ⟨Or.inl (EReal.coe_ne_bot a), Or.inr hu, Or.inl (EReal.coe_ne_top a), Or.inl haE⟩
  have hmul₂_ne_bot : (b : EReal) * w ≠ ⊥ := by
    rw [EReal.mul_ne_bot]
    exact ⟨Or.inl (EReal.coe_ne_bot b), Or.inr hw, Or.inl (EReal.coe_ne_top b), Or.inl hbE⟩
  -- Push negation through the sum, then through each scalar multiple.
  calc
    -((a : EReal) * u + (b : EReal) * w) = -((a : EReal) * u) - ((b : EReal) * w) := by
      exact EReal.neg_add (Or.inl hmul₁_ne_bot) (Or.inr hmul₂_ne_bot)
    _ = (a : EReal) * (-u) + (b : EReal) * (-w) := by
      simp [sub_eq_add_neg]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [CompleteSpace K] in
/-- Proposition 19.17 (2): for every `x ∈ ℋ`, the fiber `v ↦ ℒ[F] x v` is concave on `𝒦`. -/
theorem lagrangian_concave_in_second_variable
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    ConcaveOn ℝ Set.univ (lagrangian F x) := by
  let fx : K → Set.Ioi (⊥ : EReal) := fun y : K ↦ F (x, y)
  by_cases hslice : (effectiveDomain fx).Nonempty
  · have hconv :
        _root_.ConvexOn ℝ Set.univ
          (fun v : K ↦ ((fun y : K ↦ (F (x, y) : EReal))∗ v)) :=
      conjugateSecondVariableSlice_convexOn F x
    have hconj_ne_bot :
        ∀ v : K, ((fun y : K ↦ (F (x, y) : EReal))∗ v) ≠ ⊥ := by
      obtain ⟨y₀, hy₀⟩ := hslice
      intro v
      have hy₀_top : (F (x, y₀) : EReal) ≠ ⊤ := by
        exact lt_top_iff_ne_top.mp (mem_effectiveDomain_iff.mp hy₀)
      have hy₀_bot : (F (x, y₀) : EReal) ≠ ⊥ := ne_of_gt (F (x, y₀)).2
      have hterm :
          (⊥ : EReal) <
            (((⟪y₀, v⟫_ℝ : ℝ) : EReal) - (F (x, y₀) : EReal)) := by
        rw [← EReal.coe_toReal hy₀_top hy₀_bot, ← EReal.coe_sub]
        exact EReal.bot_lt_coe _
      -- A single finite affine defect lower-bounds the whole supremum defining the conjugate.
      exact ne_of_gt <| lt_of_lt_of_le hterm <| by
        rw [conjugate_apply]
        exact le_iSup (fun y : K ↦ (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) y₀
    constructor
    · exact convex_univ
    · intro v₁ _ v₂ _ a b ha hb hab
      have hineq :=
        hconv.2 (by simp : v₁ ∈ Set.univ) (by simp : v₂ ∈ Set.univ) ha hb hab
      have hlag₁ :
          lagrangian F x v₁ = -((fun y : K ↦ (F (x, y) : EReal))∗ v₁) := by
        simpa using congrFun (lagrangian_eq_neg_conjugate_second_variable_slice F x) v₁
      have hlag₂ :
          lagrangian F x v₂ = -((fun y : K ↦ (F (x, y) : EReal))∗ v₂) := by
        simpa using congrFun (lagrangian_eq_neg_conjugate_second_variable_slice F x) v₂
      have hlag_combo :
          lagrangian F x (a • v₁ + b • v₂) =
            -((fun y : K ↦ (F (x, y) : EReal))∗ (a • v₁ + b • v₂)) := by
        simpa using
          congrFun (lagrangian_eq_neg_conjugate_second_variable_slice F x) (a • v₁ + b • v₂)
      -- Rewrite the weighted left-hand side to a single negated weighted conjugate sum.
      calc
        (a : EReal) • lagrangian F x v₁ + (b : EReal) • lagrangian F x v₂
            = -((a : EReal) * ((fun y : K ↦ (F (x, y) : EReal))∗ v₁) +
                (b : EReal) * ((fun y : K ↦ (F (x, y) : EReal))∗ v₂)) := by
                  rw [hlag₁, hlag₂]
                  simpa [smul_eq_mul] using
                    (ereal_neg_weighted_sum_eq_weighted_neg ha hb
                      (hconj_ne_bot v₁) (hconj_ne_bot v₂)).symm
        _ ≤ -((fun y : K ↦ (F (x, y) : EReal))∗ (a • v₁ + b • v₂)) := by
              exact EReal.neg_le_neg_iff.mpr hineq
        _ = lagrangian F x (a • v₁ + b • v₂) := by
              rw [hlag_combo]
  · have htop_slice : ∀ y : K, (F (x, y) : EReal) = ⊤ := by
      intro y
      by_contra hy
      exact hslice ⟨y, mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy)⟩
    have hlag_top : ∀ v : K, lagrangian F x v = ⊤ := by
      intro v
      calc
        lagrangian F x v = ⨅ y : K, (⊤ : EReal) := by
          rw [lagrangian_apply]
          refine iInf_congr fun y ↦ ?_
          rw [htop_slice y]
          exact EReal.top_sub (EReal.coe_ne_top _)
        _ = ⊤ := by
          simp
    have hconst : lagrangian F x = fun _ : K ↦ (⊤ : EReal) := by
      funext v
      exact hlag_top v
    -- In the empty-slice branch every affine defect is `⊤`, so the fiber is constant.
    constructor
    · exact convex_univ
    · intro v₁ _ v₂ _ a b ha hb hab
      rw [hlag_top v₁, hlag_top v₂, hlag_top (a • v₁ + b • v₂)]
      simp

omit [CompleteSpace H] in
/-- Supremum clause of Proposition 19.17: if `F ∈ Γ₀(H × K)`, then for every `x ∈ ℋ`,
`sSup (Set.range (ℒ[F] x)) = (F (x, 0) : EReal)`. -/
theorem lagrangian_sSup_eq_value_at_zero_of_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) :
    sSup (Set.range (lagrangian F x)) = (F (x, 0) : EReal) := by
  -- First identify the supremum with the primal perturbation objective.
  simpa [perturbationPrimalObjective_apply] using
    lagrangianFiberSup_eq_perturbationPrimalObjective_of_mem_gammaZero F hF x

omit [CompleteSpace H] in
/-- If `F ∈ Γ₀(H × K)`, the supremum of the fixed-`x` Lagrangian fiber is the primal objective
`perturbationPrimalObjective F x`. -/
theorem lagrangian_sSup_eq_perturbationPrimalObjective_of_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) :
    sSup (Set.range (lagrangian F x)) = perturbationPrimalObjective F x := by
  -- This is exactly the fixed-fiber supremum identity proved in the helper API above.
  exact lagrangianFiberSup_eq_perturbationPrimalObjective_of_mem_gammaZero F hF x

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: after converting the finite tilted perturbation to `toEReal`,
the resulting function is convex on `H × K`. -/
private theorem tiltedPerturbation_convexOn
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn F Set.univ) (v : K) :
    ConvexOn
      (Function.toEReal fun p : H × K ↦ (F p : EReal).toReal - ⟪p.2, v⟫_ℝ)
      Set.univ := by
  let g : H × K → ℝ := fun p : H × K ↦ (F p : EReal).toReal - ⟪p.2, v⟫_ℝ
  have heff : effectiveDomain F = Set.univ := by
    ext p
    constructor
    · intro _
      simp
    · intro _
      exact hconv.subset_effectiveDomain (by simp)
  have hconv_eff : ConvexOn F (effectiveDomain F) := by
    simpa [heff] using hconv
  have hFreal : _root_.ConvexOn ℝ Set.univ (fun p : H × K ↦ (F p : EReal).toReal) := by
    -- Convexity of `F` on all of `H × K` upgrades its finite representative to a mathlib
    -- `ConvexOn` statement on `Set.univ`.
    simpa [heff] using hconv_eff.toReal_convexOn_effectiveDomain
  have hgreal : _root_.ConvexOn ℝ Set.univ g := by
    constructor
    · exact convex_univ
    · intro p₁ _ p₂ _ a b ha hb hab
      have hFineq :
          (F (a • p₁ + b • p₂) : EReal).toReal ≤
            a * (F p₁ : EReal).toReal + b * (F p₂ : EReal).toReal := by
        simpa [smul_eq_mul] using
          hFreal.2 (by simp : p₁ ∈ Set.univ) (by simp : p₂ ∈ Set.univ) ha hb hab
      have hpair :
          ⟪(a • p₁ + b • p₂).2, v⟫_ℝ =
            a * ⟪p₁.2, v⟫_ℝ + b * ⟪p₂.2, v⟫_ℝ := by
        -- The dual tilt is linear in the second coordinate of the product variable.
        change ⟪a • p₁.2 + b • p₂.2, v⟫_ℝ =
          a * ⟪p₁.2, v⟫_ℝ + b * ⟪p₂.2, v⟫_ℝ
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      -- Subtract the same affine correction from the Jensen inequality for the finite slice.
      calc
        g (a • p₁ + b • p₂) =
            (F (a • p₁ + b • p₂) : EReal).toReal -
              (a * ⟪p₁.2, v⟫_ℝ + b * ⟪p₂.2, v⟫_ℝ) := by
                change
                  (F (a • p₁ + b • p₂) : EReal).toReal - ⟪(a • p₁ + b • p₂).2, v⟫_ℝ =
                    (F (a • p₁ + b • p₂) : EReal).toReal -
                      (a * ⟪p₁.2, v⟫_ℝ + b * ⟪p₂.2, v⟫_ℝ)
                rw [hpair]
        _ ≤ (a * (F p₁ : EReal).toReal + b * (F p₂ : EReal).toReal) -
              (a * ⟪p₁.2, v⟫_ℝ + b * ⟪p₂.2, v⟫_ℝ) := by
                exact sub_le_sub_right hFineq _
        _ = a * g p₁ + b * g p₂ := by
                simp [g]
                ring
  refine ⟨?_, ?_, ?_⟩
  · -- The real-valued tilt viewed via `toEReal` has full effective domain.
    simp
  · -- Full-domain convexity gives the required effective-domain inclusion immediately.
    simp
  · intro p₁ _ p₂ _ a ha0 ha1
    -- Convert the real Jensen inequality back through `toEReal`.
    have hgineq :
        g (a • p₁ + (1 - a) • p₂) ≤ a * g p₁ + (1 - a) * g p₂ := by
      simpa [smul_eq_mul] using
        hgreal.2 (by simp : p₁ ∈ Set.univ) (by simp : p₂ ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((g (a • p₁ + (1 - a) • p₂) : ℝ) : EReal) ≤
      ((a * g p₁ + (1 - a) * g p₂ : ℝ) : EReal)
    exact_mod_cast hgineq

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19.17: the fixed-`v` Lagrangian fiber is the marginal function of the
finite real tilt `p ↦ (F p : EReal).toReal - ⟪p.2, v⟫`. -/
private theorem lagrangian_eq_marginalFunction_tiltToEReal
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn F Set.univ) (v : K) :
    (fun x : H ↦ lagrangian F x v) =
      marginalFunction
        (Function.toEReal fun p : H × K ↦ (F p : EReal).toReal - ⟪p.2, v⟫_ℝ) := by
  funext x
  -- Compare both owners fiberwise after replacing each finite `F (x, y)` by its `toReal`
  -- representative.
  rw [lagrangian_apply, marginalFunction, sInf_range]
  refine iInf_congr fun y ↦ ?_
  have hfinite : (F (x, y) : EReal) < ⊤ := hconv.subset_effectiveDomain (by simp)
  have htop : (F (x, y) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hfinite
  have hbot : (F (x, y) : EReal) ≠ ⊥ := ne_of_gt (F (x, y)).2
  -- The `toEReal` tilt is literally the original affine defect once the finite value is
  -- rewritten back from `toReal`.
  symm
  calc
    ((Function.toEReal fun p : H × K ↦ (F p : EReal).toReal - ⟪p.2, v⟫_ℝ) (x, y) : EReal) =
        ((((F (x, y) : EReal).toReal - ⟪y, v⟫_ℝ : ℝ) : EReal)) := by
          simp [Function.toEReal_apply]
    _ = (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
          rw [EReal.coe_sub, EReal.coe_toReal htop hbot]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Convexity clause of Proposition 19.17: if `F` is convex, then for every `v ∈ 𝒦`, the fiber
`x ↦ ℒ[F] x v` is convex on `ℋ`. -/
theorem lagrangian_convex_in_first_variable
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn F Set.univ) (v : K) :
    _root_.ConvexOn ℝ Set.univ (fun x : H ↦ lagrangian F x v) := by
  let Gv : H × K → Set.Ioi (⊥ : EReal) :=
    Function.toEReal fun p : H × K ↦ (F p : EReal).toReal - ⟪p.2, v⟫_ℝ
  have hGv : ConvexOn Gv Set.univ := by
    -- The tilted perturbation inherits convexity from `F` after passing to finite real values.
    simpa [Gv] using tiltedPerturbation_convexOn F hconv v
  have hmarg : _root_.ConvexOn ℝ Set.univ (marginalFunction Gv) := by
    constructor
    · exact convex_univ
    · intro x₁ _ x₂ _ a b ha hb hab
      have hb_eq : b = 1 - a := by
        linarith
      subst b
      -- Proposition 8.35 applies directly to the convex tilted perturbation.
      simpa [smul_eq_mul] using
        (marginalFunction_convex Gv hGv (x₁ := x₁) (x₂ := x₂) (α := a) ha (by linarith))
  -- Route correction: rewrite `lagrangian` as the marginal function of the finite tilt before
  -- invoking Proposition 8.35.
  have hlag : (fun x : H ↦ lagrangian F x v) = marginalFunction Gv := by
    simpa [Gv] using lagrangian_eq_marginalFunction_tiltToEReal F hconv v
  exact hlag.symm ▸ hmarg

omit [CompleteSpace H] [CompleteSpace K] in
/-- Infimum clause of Proposition 19.17: for every `v ∈ 𝒦`,
`sInf (Set.range fun x ↦ ℒ[F] x v) = -(((fun p : H × K ↦ (F p : EReal))∗ (0, v)))`. -/
theorem lagrangian_sInf_eq_neg_conjugate_at_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x : H ↦ lagrangian F x v) =
      -(((fun p : H × K ↦ (F p : EReal))∗ (0, v))) := by
  -- Flatten the infimum to a product-space `iInf` and then identify the resulting supremum with
  -- the conjugate at `(0, v)`.
  calc
    sInf (Set.range fun x : H ↦ lagrangian F x v) =
        ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
          exact lagrangian_sInf_range_eq_iInf_prod_second_variable_tilt F v
    _ = ⨅ p : H × K, -((((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))) := by
          refine iInf_congr fun p ↦ ?_
          simpa [sub_eq_add_neg, add_comm] using
            (EReal.neg_sub
              (x := (((⟪p.2, v⟫_ℝ : ℝ) : EReal)))
              (y := (F p : EReal))
              (.inl (EReal.coe_ne_bot _))
              (.inl (EReal.coe_ne_top _))).symm
    _ = -(⨆ p : H × K, (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))) := by
          let ψ : H × K → EReal := fun p : H × K ↦
            (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))
          simpa [ψ] using iInf_neg_eq_neg_iSup_ereal ψ
    _ = -(((fun p : H × K ↦ (F p : EReal))∗ (0, v))) := by
          congr 1
          rw [conjugate_apply]
          congr with p
          congr 1
          change (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) = (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal))
          calc
            (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) =
                (((⟪p.1, (0 : H)⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal)) := by
                  simp
            _ = (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal)) := by
                  rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- The infimum of the fixed-`v` Lagrangian fiber is the negative dual objective
`-perturbationDualObjective F v`. -/
theorem lagrangian_sInf_eq_neg_perturbationDualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x : H ↦ lagrangian F x v) = -perturbationDualObjective F v := by
  -- Expand the conjugate at `(0, v)` and simplify the product pairing.
  calc
    sInf (Set.range fun x : H ↦ lagrangian F x v) =
        -(((fun p : H × K ↦ (F p : EReal))∗ (0, v))) := by
          exact lagrangian_sInf_eq_neg_conjugate_at_zero F v
    _ = -perturbationDualObjective F v := by
          congr 1
          rw [conjugate_apply, perturbationDualObjective_apply]
          congr with p
          congr 1
          change (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal)) = (((⟪p.2, v⟫_ℝ : ℝ) : EReal))
          calc
            (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal)) =
                (((⟪p.1, (0 : H)⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal)) := by
                  rfl
            _ = (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) := by
                  simp

end ParametricDuality
