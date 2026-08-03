import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.15 packages primal attainment, dual attainment, strong duality,
  and the two zero-slice subdifferential contact conditions.
- `core/canonical`: the owner abstractions are `Argmin`, the canonical perturbation objectives
  from Definition 19.11, the packaged conjugate `F∗[hF]`, and the subdifferential owner `∂`.
- `bridge/view`: the perturbation-specific work is only the reconstruction of the primal and dual
  argmin clauses from the zero slices. The Fenchel--Young and conjugate-subdifferential clauses are
  supplied by the earlier Chapter 19 canonical bridges specialized to `((x, 0), (0, v))`.
-/

-- Proof sketch: unpack the dual objective as the explicit conjugate supremum and collapse the
-- zero first-coordinate pairing term.
/-- Helper for Proposition 19 15: the perturbation dual objective is the packaged Fenchel
conjugate of `F` evaluated at the zero-first-coordinate slice. -/
private theorem perturbationDualObjective_eq_conjugate_zero_first
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (v : K) :
    perturbationDualObjective F v = (F∗[hF] (0, v) : EReal) := by
  -- Unpack the packaged conjugate and simplify the product inner product against `(0, v)`.
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

-- Proof sketch: in the `ProdL2` inner product, the `H`-slice and the `K`-slice are orthogonal.
/-- Helper for Proposition 19 15: pairing a zero-second-coordinate slice with a
zero-first-coordinate slice gives zero. -/
private lemma zero_slice_pairing_eq_zero (x : H) (v : K) :
    (((⟪((x, 0) : H × K), (0, v)⟫_ℝ : ℝ) : EReal)) = 0 := by
  -- Expand the `ProdL2` inner product into the sum of the two coordinate pairings.
  change (((⟪x, (0 : H)⟫_ℝ + ⟪(0 : K), v⟫_ℝ : ℝ) : EReal)) = 0
  simp

-- Proof sketch: the contact equality and the zero-gap identity are equivalent once one records
-- that `Γ₀` functions never take the forbidden `⊤`/`⊥` values at the two zero slices involved.
/-- Helper for Proposition 19 15: the zero-slice Fenchel--Young contact identity is equivalent to
the zero-gap equality. -/
private lemma fenchel_young_contact_iff_zero_gap
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) ↔
      (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0 := by
  constructor
  · intro hcontact
    -- The conjugate is never `-∞`, so the contact identity forces both sides to be finite.
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
    -- The zero-gap equality excludes `⊤` on either side because the conjugate is never `-∞`.
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

-- Proof sketch: negate the zero-slice contact identity to swap the primal and conjugate terms.
/-- Helper for Proposition 19 15: the zero-slice contact identity can be rewritten from the
conjugate side by negating both sides. -/
private lemma conjugate_zero_slice_contact_of_contact
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K)
    (hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal))) :
    (F∗[hF] (0, v) : EReal) = -((F (x, 0) : EReal)) := by
  -- Negating both sides swaps the two zero-slice values without changing the source route.
  have hneg := congrArg Neg.neg hcontact
  simpa using hneg.symm

-- Proof sketch: evaluating the conjugate supremum at `(z, 0)` gives the pointwise lower bound
-- needed to show that the zero slice `x` minimizes the primal objective.
/-- Helper for Proposition 19 15: a zero-slice Fenchel--Young contact identity forces primal
optimality at the same zero slice. -/
private lemma mem_argmin_perturbationPrimalObjective_of_fenchel_young_contact_zero_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K)
    (hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal))) :
    x ∈ Argmin (perturbationPrimalObjective F) := by
  have hdual_contact :
      (F∗[hF] (0, v) : EReal) = -((F (x, 0) : EReal)) := by
    -- Switch to the conjugate-side contact identity used in the supremum bound.
    exact conjugate_zero_slice_contact_of_contact F hF x v hcontact
  have hx_le : ∀ z : H, (F (x, 0) : EReal) ≤ (F (z, 0) : EReal) := by
    intro z
    -- Evaluating the conjugate supremum at `(z, 0)` yields the primal lower bound.
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
  -- Convert the pointwise lower bound into the `Argmin` characterization by the infimum.
  rw [mem_argmin_iff_eq_sInf, sInf_range]
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro z
    simpa [perturbationPrimalObjective_apply] using hx_le z
  · exact iInf_le (fun z : H ↦ perturbationPrimalObjective F z) x

-- Proof sketch: evaluating the conjugate supremum at `(x, 0)` against arbitrary dual slices
-- gives the pointwise lower bound needed to show that `v` minimizes the dual objective.
/-- Helper for Proposition 19 15: a zero-slice Fenchel--Young contact identity forces dual
optimality at the same zero slice. -/
private lemma mem_argmin_perturbationDualObjective_of_fenchel_young_contact_zero_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K)
    (hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal))) :
    v ∈ Argmin (perturbationDualObjective F) := by
  have hdual_contact :
      (F∗[hF] (0, v) : EReal) = -((F (x, 0) : EReal)) := by
    -- Reuse the conjugate-side form of the zero-slice contact identity.
    exact conjugate_zero_slice_contact_of_contact F hF x v hcontact
  have hv_le : ∀ w : K, (F∗[hF] (0, v) : EReal) ≤ (F∗[hF] (0, w) : EReal) := by
    intro w
    -- Evaluating the same supremum at `(x, 0)` yields the dual lower bound.
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
  -- Convert the pointwise lower bound into the `Argmin` characterization by the infimum.
  rw [mem_argmin_iff_eq_sInf, sInf_range]
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro w
    exact hv_owner_le w
  · exact iInf_le (fun w : K ↦ perturbationDualObjective F w) v

-- Proof sketch: the forward implication rewrites the attained primal and dual values and then
-- converts the strong-duality identity into the zero-gap equality. For the reverse implication,
-- Route correction: instead of replaying subdifferential inequalities, recover the primal and
-- dual argmin clauses directly from the conjugate supremum formula and then rewrite strong
-- duality from the attained values.
/-- Helper for Proposition 19 15: primal attainment, dual attainment, and strong duality are
equivalent to the Fenchel--Young zero-gap identity at `((x, 0), (0, v))`. -/
private lemma primal_dual_attainment_strong_duality_iff_fenchelYoung_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (x ∈ Argmin (perturbationPrimalObjective F) ∧
        v ∈ Argmin (perturbationDualObjective F) ∧
        sInf (Set.range (perturbationPrimalObjective F)) =
          -sInf (Set.range (perturbationDualObjective F))) ↔
      ((F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0) := by
  constructor
  · rintro ⟨hx, hv, hstrong⟩
    -- Rewrite the attained primal and dual values as the corresponding infima.
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
    -- Convert the zero-gap identity into the contact identity used by the owner-level bounds.
    have hcontact : (F (x, 0) : EReal) = -((F∗[hF] (0, v) : EReal)) := by
      exact (fenchel_young_contact_iff_zero_gap F hF x v).2 hzero
    have hx_argmin : x ∈ Argmin (perturbationPrimalObjective F) := by
      -- The conjugate supremum at `(z, 0)` recovers the primal minimizer.
      exact
        mem_argmin_perturbationPrimalObjective_of_fenchel_young_contact_zero_slice
          F hF x v hcontact
    have hv_argmin : v ∈ Argmin (perturbationDualObjective F) := by
      -- The same contact identity recovers the dual minimizer.
      exact
        mem_argmin_perturbationDualObjective_of_fenchel_young_contact_zero_slice
          F hF x v hcontact
    have hstrong :
        sInf (Set.range (perturbationPrimalObjective F)) =
          -sInf (Set.range (perturbationDualObjective F)) := by
      -- Once both minimizers are identified, the zero-gap identity is exactly strong duality.
      calc
        sInf (Set.range (perturbationPrimalObjective F)) = (F (x, 0) : EReal) := by
          exact (mem_argmin_iff_eq_sInf.mp hx_argmin).symm
        _ = -((F∗[hF] (0, v) : EReal)) := hcontact
        _ = -sInf (Set.range (perturbationDualObjective F)) := by
          rw [← perturbationDualObjective_eq_conjugate_zero_first F hF v,
            mem_argmin_iff_eq_sInf.mp hv_argmin]
    exact ⟨hx_argmin, hv_argmin, hstrong⟩

-- Proof sketch: specialize the canonical Fenchel--Young/subgradient bridge to `((x, 0), (0, v))`
-- and simplify the zero pairing on the product space.
/-- Helper for Proposition 19 15: the zero-gap clause is equivalent to the primal
subdifferential contact clause at `((x, 0), (0, v))`. -/
private lemma fenchelYoung_zero_iff_zero_slice_mem_subdifferential
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    ((F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0) ↔
      (0, v) ∈ (∂ F) (x, 0) := by
  -- Specialize the canonical Fenchel--Young criterion to the product-space zero slices.
  simpa [gammaZeroConjugate_apply, zero_slice_pairing_eq_zero (x := x) (v := v)] using
    (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
      (f := F) hF.2.nonempty (x, 0) (0, v)).symm

-- Proof sketch: this is the canonical subgradient/conjugate-subgradient bridge specialized to the
-- same zero slices.
/-- Helper for Proposition 19 15: the primal and conjugate contact clauses are equivalent at the
zero slices. -/
private lemma zero_slice_mem_subdifferential_iff_conjugate_zero_slice_mem_subdifferential
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    (0, v) ∈ (∂ F) (x, 0) ↔ (x, 0) ∈ (∂ (F∗[hF])) (0, v) := by
  -- Specialize the canonical subgradient/conjugate-subgradient equivalence.
  simpa using
    (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
      (f := F) hF (x, 0) (0, v))

-- Proof sketch: clause `(i)` is the perturbation-specific attainment bridge above, while clauses
-- `(ii)`--`(iv)` are handled by the zero-gap/subdifferential bridge and the inverse
-- subdifferential theorem for the packaged conjugate.
/-- Proposition 19 15: for `F ∈ Γ₀(ℋ × 𝒦)` and `(x, v) ∈ ℋ × 𝒦`, the following are equivalent:
(i) `x` is a primal solution, `v` is a dual solution, and strong duality holds;
(ii) `F(x, 0) + F^*(0, v) = 0`; (iii) `(0, v) ∈ ∂ F(x, 0)`; (iv) `(x, 0) ∈ ∂ F^*(0, v)`, with
`F^*` represented by `F∗[hF]`. -/
theorem primal_dual_solution_tfae_for_perturbation_function
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (perturbationPrimalObjective F) ∧
          v ∈ Argmin (perturbationDualObjective F) ∧
          sInf (Set.range (perturbationPrimalObjective F)) =
            -sInf (Set.range (perturbationDualObjective F)),
        (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0,
        (0, v) ∈ (∂ F) (x, 0),
        (x, 0) ∈ (∂ (F∗[hF])) (0, v)] := by
  -- Assemble the perturbation attainment bridge with the canonical Chapter 16 contact theorem.
  tfae_have 1 ↔ 2 := by
    exact primal_dual_attainment_strong_duality_iff_fenchelYoung_zero F hF x v
  tfae_have 2 ↔ 3 := by
    exact fenchelYoung_zero_iff_zero_slice_mem_subdifferential F hF x v
  tfae_have 3 ↔ 4 := by
    exact zero_slice_mem_subdifferential_iff_conjugate_zero_slice_mem_subdifferential F hF x v
  tfae_finish

end ParametricDuality

end

end ERealFunction
