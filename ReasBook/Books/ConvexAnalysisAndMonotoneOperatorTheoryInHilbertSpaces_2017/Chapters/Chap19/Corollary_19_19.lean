import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_28
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Corollary_13_40
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Set

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 19.19 is the textbook five-way optimality system for a perturbation
  function, adding the Lagrangian saddle-point clause to the older perturbation TFAE.
- `core/canonical`: the owner abstractions here are the perturbation objectives, the packaged
  conjugate `F∗[hF]`, and the whole-space saddle-point owner `lagrangian_isSaddlePointOn_iff`.
- `bridge/view`: because the Chapter 19 proposition owner files are currently unstable, this file
  rebuilds only the minimal earlier API needed to identify the primal and dual Lagrangian extremal
  values and then assembles the source-facing TFAE locally.
-/

-- Proof sketch: unfold the packaged conjugate and collapse the zero first-coordinate pairing term.
omit [CompleteSpace K] in
/-- Helper for Corollary 19 19: the perturbation dual objective is the packaged Fenchel conjugate
of `F` evaluated at the zero-first-coordinate slice. -/
private theorem perturbationDualObjective_eq_conjugate_zero_first
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (v : K) :
    perturbationDualObjective F v = (F∗[hF] (0, v) : EReal) := by
  -- Unpack the conjugate and rewrite the product pairing against `(0, v)`.
  rw [gammaZeroConjugate_apply, conjugate_apply, perturbationDualObjective_apply]
  congr with p
  congr 1
  change (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) = (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal))
  calc
    (((⟪p.2, v⟫_ℝ : ℝ) : EReal)) =
        (((⟪p.1, (0 : H)⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal)) := by
          simp
    _ = (((⟪p, (0, v)⟫_ℝ : ℝ) : EReal)) := by
          rfl

-- Proof sketch: rewrite the attained primal and dual values as the corresponding infima; the
-- strong-duality equality is then exactly the Fenchel--Young zero-gap identity. Conversely, the
-- conjugate supremum formula at `(z, 0)` and `(x, 0)` gives the pointwise lower bounds needed to
-- recover both argmin clauses.
omit [CompleteSpace K] in
/-- Helper for Corollary 19 19: primal attainment, dual attainment, and strong duality are
equivalent to the Fenchel--Young zero-gap identity at `((x, 0), (0, v))`. -/
private theorem fenchel_young_contact_iff_zero_gap
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) ↔
      (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0 := by
  constructor
  · intro hcontact
    -- The conjugate side is never `-∞`, so the contact identity forces both sides to be finite.
    have hconj_ne_bot : (F∗[hF] (0, v) : EReal) ≠ ⊥ := by
      simpa [gammaZeroConjugate_apply] using
        conjugate_ne_bot_of_effectiveDomain_nonempty (f := F) hF.2.nonempty (0, v)
    have hprimal_ne_top : (F (x, 0) : EReal) ≠ ⊤ := by
      intro htop
      have : (F∗[hF] (0, v) : EReal) = ⊥ := by
        exact EReal.neg_eq_top_iff.mp (by simpa [htop] using hcontact.symm)
      exact hconj_ne_bot this
    have hconj_ne_top : (F∗[hF] (0, v) : EReal) ≠ ⊤ := by
      intro htop
      have : (F (x, 0) : EReal) = ⊥ := by
        have hcontact' := hcontact
        rw [htop] at hcontact'
        simpa using hcontact'
      exact (ne_of_gt (F (x, 0)).2) this
    exact
      (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot hprimal_ne_top
        (ne_of_gt (F (x, 0)).2) hconj_ne_top hconj_ne_bot).1 hcontact
  · intro hzero
    -- The zero-gap identity excludes `⊤` on either side because the conjugate is never `-∞`.
    have hconj_ne_bot : (F∗[hF] (0, v) : EReal) ≠ ⊥ := by
      simpa [gammaZeroConjugate_apply] using
        conjugate_ne_bot_of_effectiveDomain_nonempty (f := F) hF.2.nonempty (0, v)
    have hprimal_ne_top : (F (x, 0) : EReal) ≠ ⊤ := by
      intro htop
      have hsum_top : (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = ⊤ := by
        rw [htop, add_comm]
        exact EReal.add_top_of_ne_bot hconj_ne_bot
      exact EReal.zero_ne_top (hzero.symm.trans hsum_top)
    have hconj_ne_top : (F∗[hF] (0, v) : EReal) ≠ ⊤ := by
      intro htop
      have hsum_top :
          (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = ⊤ := by
        rw [htop]
        exact EReal.add_top_of_ne_bot (ne_of_gt (F (x, 0)).2)
      exact EReal.zero_ne_top (hzero.symm.trans hsum_top)
    exact
      (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot hprimal_ne_top
        (ne_of_gt (F (x, 0)).2) hconj_ne_top hconj_ne_bot).2 hzero

omit [CompleteSpace K] in
/-- Helper for Corollary 19 19: primal attainment, dual attainment, and strong duality are
equivalent to the Fenchel--Young zero-gap identity at `((x, 0), (0, v))`. -/
private theorem primal_dual_attainment_strong_duality_iff_fenchelYoung_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (x ∈ Argmin (perturbationPrimalObjective F) ∧
        v ∈ Argmin (perturbationDualObjective F) ∧
        sInf (Set.range (perturbationPrimalObjective F)) =
          -sInf (Set.range (perturbationDualObjective F))) ↔
      ((F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0) := by
  constructor
  · rintro ⟨hx, hv, hstrong⟩
    -- Rewrite the attained values as the primal and dual infima.
    have hx_value :
        (F (x, 0) : EReal) = sInf (Set.range (perturbationPrimalObjective F)) := by
      simpa [perturbationPrimalObjective_apply] using (mem_argmin_iff_eq_sInf.mp hx)
    have hv_value :
        (F∗[hF] (0, v) : EReal) = sInf (Set.range (perturbationDualObjective F)) := by
      calc
        (F∗[hF] (0, v) : EReal) = perturbationDualObjective F v := by
          rw [perturbationDualObjective_eq_conjugate_zero_first F hF v]
        _ = sInf (Set.range (perturbationDualObjective F)) :=
          mem_argmin_iff_eq_sInf.mp hv
    have hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) := by
      calc
        (F (x, 0) : EReal) = sInf (Set.range (perturbationPrimalObjective F)) := hx_value
        _ = -sInf (Set.range (perturbationDualObjective F)) := hstrong
        _ = -((F∗[hF] (0, v) : EReal)) := by
          rw [hv_value]
    exact (fenchel_young_contact_iff_zero_gap F hF x v).1 hcontact
  · intro hzero
    -- Convert the zero-gap identity into the contact equation used in the pointwise bounds.
    have hzero' : (F∗[hF] (0, v) : EReal) + (F (x, 0) : EReal) = 0 := by
      simpa [add_comm] using hzero
    have hdual_contact :
        (F∗[hF] (0, v) : EReal) = -((F (x, 0) : EReal)) := by
      have hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) := by
        exact (fenchel_young_contact_iff_zero_gap F hF x v).2 hzero
      have hneg := congrArg Neg.neg hcontact
      simpa using hneg.symm
    have hx_le : ∀ z : H, (F (x, 0) : EReal) ≤ (F (z, 0) : EReal) := by
      intro z
      -- Evaluating the dual supremum at `(z, 0)` gives the primal lower bound.
      have hz_dual :
          -((F (z, 0) : EReal)) ≤ (F∗[hF] (0, v) : EReal) := by
        calc
          -((F (z, 0) : EReal)) =
              (((⟪((z, 0) : H × K).2, v⟫_ℝ : ℝ) : EReal) - (F (z, 0) : EReal)) := by
                simp
          _ ≤ perturbationDualObjective F v := by
            rw [perturbationDualObjective_apply]
            exact
              le_iSup
                (fun p : H × K ↦ (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))) (z, 0)
          _ = (F∗[hF] (0, v) : EReal) := by
            rw [perturbationDualObjective_eq_conjugate_zero_first F hF v]
      have hz_neg :
          -((F (z, 0) : EReal)) ≤ -((F (x, 0) : EReal)) := by
        rw [hdual_contact] at hz_dual
        exact hz_dual
      exact EReal.neg_le_neg_iff.mp hz_neg
    have hv_le : ∀ w : K, (F∗[hF] (0, v) : EReal) ≤ (F∗[hF] (0, w) : EReal) := by
      intro w
      -- Evaluating the same supremum at `(x, 0)` gives the dual lower bound.
      have hx_dual :
          -((F (x, 0) : EReal)) ≤ (F∗[hF] (0, w) : EReal) := by
        calc
          -((F (x, 0) : EReal)) =
              (((⟪((x, 0) : H × K).2, w⟫_ℝ : ℝ) : EReal) - (F (x, 0) : EReal)) := by
                simp
          _ ≤ perturbationDualObjective F w := by
            rw [perturbationDualObjective_apply]
            exact
              le_iSup
                (fun p : H × K ↦ (((⟪p.2, w⟫_ℝ : ℝ) : EReal) - (F p : EReal))) (x, 0)
          _ = (F∗[hF] (0, w) : EReal) := by
            rw [perturbationDualObjective_eq_conjugate_zero_first F hF w]
      calc
        (F∗[hF] (0, v) : EReal) = -((F (x, 0) : EReal)) := hdual_contact
        _ ≤ (F∗[hF] (0, w) : EReal) := hx_dual
    have hv_owner_le : ∀ w : K, perturbationDualObjective F v ≤ perturbationDualObjective F w := by
      intro w
      rw [perturbationDualObjective_eq_conjugate_zero_first F hF v,
        perturbationDualObjective_eq_conjugate_zero_first F hF w]
      exact hv_le w
    have hx_argmin : x ∈ Argmin (perturbationPrimalObjective F) := by
      -- `x` minimizes the primal objective because its value is below every zero slice.
      rw [mem_argmin_iff_eq_sInf, sInf_range]
      refine le_antisymm ?_ ?_
      · refine le_iInf ?_
        intro z
        simpa [perturbationPrimalObjective_apply] using hx_le z
      · exact iInf_le (fun z : H ↦ perturbationPrimalObjective F z) x
    have hv_argmin : v ∈ Argmin (perturbationDualObjective F) := by
      -- The same lower-bound argument shows that `v` minimizes the dual objective.
      rw [mem_argmin_iff_eq_sInf, sInf_range]
      refine le_antisymm ?_ ?_
      · refine le_iInf ?_
        intro w
        exact hv_owner_le w
      · exact iInf_le (fun w : K ↦ perturbationDualObjective F w) v
    have hstrong :
        sInf (Set.range (perturbationPrimalObjective F)) =
          -sInf (Set.range (perturbationDualObjective F)) := by
      -- Once both minimizers are identified, the zero-gap identity is exactly strong duality.
      calc
        sInf (Set.range (perturbationPrimalObjective F)) = (F (x, 0) : EReal) := by
          exact (mem_argmin_iff_eq_sInf.mp hx_argmin).symm
        _ = -((F∗[hF] (0, v) : EReal)) := by
          exact (fenchel_young_contact_iff_zero_gap F hF x v).2 hzero
        _ = -sInf (Set.range (perturbationDualObjective F)) := by
          rw [← perturbationDualObjective_eq_conjugate_zero_first F hF v,
            mem_argmin_iff_eq_sInf.mp hv_argmin]
    exact ⟨hx_argmin, hv_argmin, hstrong⟩

-- Proof sketch: apply the order isomorphism `x ↦ -x` to the infimum and simplify the double
-- negation.
/-- Helper for Corollary 19 19: in `EReal`, the infimum of pointwise negatives is the negative of
the corresponding supremum. -/
private theorem iInf_neg_eq_neg_iSup_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨅ i, -φ i) = -(⨆ i, φ i) := by
  -- Negation is an order isomorphism, so it transports the infimum to a supremum.
  have hmap : -(⨅ i, -φ i) = ⨆ i, -(-φ i) := by
    exact OrderIso.map_iInf EReal.negOrderIso (fun i : ι ↦ -φ i)
  have hmap' : -(⨅ i, -φ i) = (⨆ i, φ i) := by
    simpa using hmap
  rw [← hmap']
  simp

-- Proof sketch: expand `lagrangian` and rewrite each term as the negative affine defect.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace K] in
/-- Helper for Corollary 19 19: for fixed `x`, the Lagrangian fiber in the second variable is the
negative Fenchel conjugate of the slice `y ↦ F (x, y)`. -/
private theorem lagrangian_eq_neg_conjugate_second_variable_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    ℒ[F] x = fun v ↦ -((fun y : K ↦ (F (x, y) : EReal))∗ v) := by
  ext v
  -- Normalize the Lagrangian fiber to an infimum of negatives, then convert it to a supremum.
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

-- Proof sketch: lower semicontinuity is preserved by the continuous embedding `y ↦ (x, y)`, and
-- convexity of the slice follows by specializing convexity of the ambient perturbation function.
omit [CompleteSpace K] in
/-- Helper for Corollary 19 19: if the fixed second-variable slice has nonempty effective domain,
it inherits `Γ₀(K)` membership from the ambient perturbation function. -/
private theorem second_variable_slice_mem_gammaZero_of_nonempty_effectiveDomain
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H)
    (hx : (effectiveDomain (fun y : K ↦ F (x, y))).Nonempty) :
    (fun y : K ↦ F (x, y)) ∈ Γ₀(K) := by
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · -- Lower semicontinuity passes to the slice through the continuous embedding.
    simpa [Function.comp] using
      hF.1.comp (Continuous.prodMk_right x)
  · refine ⟨hx, ?_, ?_⟩
    · intro y hy
      simpa [mem_effectiveDomain_iff] using hy
    · intro y₁ hy₁ y₂ hy₂ α hα0 hα1
      -- Specialize convexity of `F` to the points `(x, y₁)` and `(x, y₂)`.
      simpa [Prod.smul_mk, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using
        hF.2.ineq
          (x := (x, y₁))
          (hx := by simpa [mem_effectiveDomain_iff] using hy₁)
          (y := (x, y₂))
          (hy := by simpa [mem_effectiveDomain_iff] using hy₂)
          (α := α) hα0 hα1

-- Proof sketch: rewrite the Lagrangian fiber as the negative conjugate of the slice, convert the
-- resulting supremum to a negated infimum, and then evaluate the Fenchel biconjugate at `0`.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Corollary 19 19: if the fixed slice `y ↦ F (x, y)` lies in `Γ₀(K)`, then the
supremum of the corresponding Lagrangian fiber recovers `F (x, 0)`. -/
private theorem lagrangian_sSup_eq_perturbationPrimalObjective_of_slice_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H)
    (hx : (fun y : K ↦ F (x, y)) ∈ Γ₀(K)) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := by
  let fx : K → Set.Ioi (⊥ : EReal) := fun y : K ↦ F (x, y)
  have hsSup :
      sSup (Set.range (ℒ[F] x)) = -sInf (Set.range fun v : K ↦ fx.asEReal∗ v) := by
    -- Rewrite the Lagrangian fiber as the negative conjugate slice and transport the supremum.
    rw [lagrangian_eq_neg_conjugate_second_variable_slice]
    rw [EReal.sSup_eq_neg_sInf_image_neg]
    have himage :
        (-·) '' Set.range (fun v : K ↦ -(fx.asEReal∗ v)) =
          Set.range fun v : K ↦ fx.asEReal∗ v := by
      ext z
      constructor
      · rintro ⟨w, ⟨v, hv⟩, hz⟩
        subst hv hz
        exact ⟨v, by simp⟩
      · rintro ⟨v, rfl⟩
        exact ⟨-(fx.asEReal∗ v), ⟨v, rfl⟩, by simp⟩
    rw [himage]
  -- Evaluate the slice biconjugate at `0`.
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

-- Proof sketch: split into the nonempty-slice branch, where the slice-local theorem applies, and
-- the empty-slice branch, where every slice value and every Lagrangian fiber value is `⊤`.
/-- Helper for Corollary 19 19: if `F ∈ Γ₀(H × K)`, then the fixed-`x` Lagrangian fiber has
supremum `F (x, 0)`. -/
private theorem lagrangian_sSup_eq_perturbationPrimalObjective_of_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := by
  by_cases hslice : (effectiveDomain (fun y : K ↦ F (x, y))).Nonempty
  · -- On a nonempty slice, the slice-local `Γ₀(K)` theorem applies directly.
    exact lagrangian_sSup_eq_perturbationPrimalObjective_of_slice_mem_gammaZero F x
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

-- Proof sketch: flatten the outer `x`-fiber infimum and the inner `y`-fiber infimum into a
-- single infimum over pairs `(x, y)`.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace K] in
/-- Helper for Corollary 19 19: the infimum of the fixed-`v` Lagrangian fiber over `x` is a single
infimum over pairs `(x, y)`. -/
private theorem lagrangian_sInf_range_eq_iInf_prod_second_variable_tilt
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x : H ↦ ℒ[F] x v) =
      ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
  -- Normalize the marginal infimum to the product infimum.
  calc
    sInf (Set.range fun x : H ↦ ℒ[F] x v) = ⨅ x : H, ℒ[F] x v := by
          rw [sInf_range]
    _ = ⨅ x : H, ⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
          simp [lagrangian_apply]
    _ = ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
          rw [iInf_prod]

-- Proof sketch: rewrite the product infimum as an infimum of negatives and then collapse it to a
-- negated supremum matching the dual objective.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace K] in
/-- Helper for Corollary 19 19: the infimum of the fixed-`v` Lagrangian fiber over `x` equals the
negative dual objective value. -/
private theorem lagrangian_sInf_eq_neg_perturbationDualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x ↦ ℒ[F] x v) = -perturbationDualObjective F v := by
  calc
    sInf (Set.range fun x ↦ ℒ[F] x v) =
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
    _ = -perturbationDualObjective F v := by
          rw [perturbationDualObjective_apply]

-- Proof sketch: rewrite the saddle-point condition with `lagrangian_isSaddlePointOn_iff`, then use
-- the two extremal-value identities above to identify the saddle value with `F (x, 0)` and
-- `-F^*(0, v)`.
/-- Companion bridge for Corollary 19 19: the Fenchel--Young zero-gap condition at `((x, 0), (0,
v))` is equivalent to the saddle-point condition for the canonical Lagrangian `ℒ[F]`. -/
theorem fenchelYoung_eq_zero_iff_isSaddlePointOn_lagrangian
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0 ↔
      IsSaddlePointOn univ univ (ℒ[F]) x v := by
  constructor
  · intro hzero
    -- Convert the zero-gap identity into the contact equation used to squeeze the Lagrangian.
    have hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) := by
      exact (fenchel_young_contact_iff_zero_gap F hF x v).2 hzero
    have hsup :
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = (F (x, 0) : EReal) := by
      -- Proposition 19.17's primal-value route is rebuilt locally.
      calc
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = perturbationPrimalObjective F x := by
          exact lagrangian_sSup_eq_perturbationPrimalObjective_of_mem_gammaZero F hF x
        _ = (F (x, 0) : EReal) := by
          rw [perturbationPrimalObjective_apply]
    have hinf :
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -((F∗[hF] (0, v) : EReal)) := by
      -- The dual-value route is the rebuilt local version of Proposition 19.17(iv).
      calc
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -perturbationDualObjective F v := by
          exact lagrangian_sInf_eq_neg_perturbationDualObjective F v
        _ = -((F∗[hF] (0, v) : EReal)) := by
          rw [perturbationDualObjective_eq_conjugate_zero_first F hF v]
    have hlag_lower : (F (x, 0) : EReal) ≤ ℒ[F] x v := by
      -- Evaluating the infimum fiber at `x` gives the lower squeeze bound.
      have hle : -((F∗[hF] (0, v) : EReal)) ≤ ℒ[F] x v := by
        calc
          -((F∗[hF] (0, v) : EReal)) = sInf (Set.range fun z : H ↦ ℒ[F] z v) := by
            symm
            exact hinf
          _ ≤ ℒ[F] x v := by
            exact sInf_le ⟨x, rfl⟩
      simpa [hcontact] using hle
    have hlag_upper : ℒ[F] x v ≤ (F (x, 0) : EReal) := by
      -- Evaluating the supremum fiber at `v` gives the upper squeeze bound.
      calc
        ℒ[F] x v ≤ sSup (Set.range fun w : K ↦ ℒ[F] x w) := by
          exact le_sSup ⟨v, rfl⟩
        _ = (F (x, 0) : EReal) := hsup
    have hlag_eq : ℒ[F] x v = (F (x, 0) : EReal) := by
      exact le_antisymm hlag_upper hlag_lower
    -- The saddle-point owner asks exactly for the two rewritten extremal-value equalities.
    refine (lagrangian_isSaddlePointOn_iff F x v).2 ?_
    constructor
    · calc
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = (F (x, 0) : EReal) := hsup
        _ = ℒ[F] x v := hlag_eq.symm
    · calc
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -((F∗[hF] (0, v) : EReal)) := hinf
        _ = (F (x, 0) : EReal) := by
          symm
          exact hcontact
        _ = ℒ[F] x v := hlag_eq.symm
  · intro hsaddle
    -- Unpack the saddle-point owner and rewrite both extremal values back to `F (x, 0)` and
    -- `-F^*(0, v)`.
    have hs := (lagrangian_isSaddlePointOn_iff F x v).mp hsaddle
    have hsup :
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = (F (x, 0) : EReal) := by
      calc
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = perturbationPrimalObjective F x := by
          exact lagrangian_sSup_eq_perturbationPrimalObjective_of_mem_gammaZero F hF x
        _ = (F (x, 0) : EReal) := by
          rw [perturbationPrimalObjective_apply]
    have hinf :
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -((F∗[hF] (0, v) : EReal)) := by
      calc
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -perturbationDualObjective F v := by
          exact lagrangian_sInf_eq_neg_perturbationDualObjective F v
        _ = -((F∗[hF] (0, v) : EReal)) := by
          rw [perturbationDualObjective_eq_conjugate_zero_first F hF v]
    have hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) := by
      -- Both rewritten extremal values equal the same saddle value `ℒ[F] x v`.
      calc
        (F (x, 0) : EReal) = sSup (Set.range fun w : K ↦ ℒ[F] x w) := hsup.symm
        _ = ℒ[F] x v := hs.1
        _ = sInf (Set.range fun z : H ↦ ℒ[F] z v) := hs.2.symm
        _ = -((F∗[hF] (0, v) : EReal)) := hinf
    exact (fenchel_young_contact_iff_zero_gap F hF x v).1 hcontact

-- Proof sketch: the perturbation attainment/strong-duality clause is equivalent to the zero-gap
-- identity by the first helper, clauses `(ii)`--`(iv)` are the standard Fenchel--Young and inverse
-- subdifferential owners, and the bridge above identifies clause `(ii)` with the saddle-point
-- clause `(v)`.
/-- Corollary 19 19: for `F ∈ Γ₀(ℋ ⊕ 𝒦)` and `(x, v) ∈ ℋ × 𝒦`, the following are equivalent:
(i) `x` is a primal solution, `v` is a dual solution, and strong duality holds;
(ii) `F(x, 0) + F^*(0, v) = 0`; (iii) `(0, v) ∈ ∂ F(x, 0)`; (iv) `(x, 0) ∈ ∂ F^*(0, v)`;
(v) `(x, v)` is a saddle point of `ℒ[F]`, with `F^*` represented by `F∗[hF]`. -/
theorem primal_dual_solution_and_lagrangian_saddlePoint_tfae
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (perturbationPrimalObjective F) ∧
          v ∈ Argmin (perturbationDualObjective F) ∧
          sInf (range (perturbationPrimalObjective F)) =
            -sInf (range (perturbationDualObjective F)),
        (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0,
        (0, v) ∈ (∂ F) (x, 0),
        (x, 0) ∈ (∂ (F∗[hF])) (0, v),
        IsSaddlePointOn univ univ (ℒ[F]) x v] := by
  -- Assemble the source-facing five-way equivalence by splicing the local saddle-point bridge.
  tfae_have 1 ↔ 2 := by
    exact primal_dual_attainment_strong_duality_iff_fenchelYoung_zero F hF x v
  tfae_have 2 ↔ 3 := by
    have hpair : (((⟪((x, 0) : H × K), (0, v)⟫_ℝ : ℝ) : EReal)) = 0 := by
      change (((⟪x, (0 : H)⟫_ℝ + ⟪(0 : K), v⟫_ℝ : ℝ) : EReal)) = 0
      simp
    simpa [gammaZeroConjugate_apply, hpair] using
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := F) hF.2.nonempty (x, 0) (0, v)).symm
  tfae_have 3 ↔ 4 := by
    simpa using
      (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
        (f := F) hF (x := (x, 0)) (u := (0, v)))
  tfae_have 2 ↔ 5 := by
    exact fenchelYoung_eq_zero_iff_isSaddlePointOn_lagrangian F hF x v
  tfae_finish

end ParametricDuality

end

end ERealFunction
