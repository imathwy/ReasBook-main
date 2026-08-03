import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Proposition_8_35
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section PartialInfimumConjugation

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] in
/-- Helper for Proposition 13.33: evaluating the first-projection infimal postcomposition recovers
the infimum over the second coordinate. -/
theorem infimalPostcomposition_fst_apply
    (F : H × K → EReal) (x : H) :
    (Prod.fst ▷ F) x = ⨅ y : K, F (x, y) := by
  -- Rewrite the first-projection fiber as the range of the second-coordinate parametrization.
  change sInf (F '' (Prod.fst ⁻¹' ({x} : Set H))) = _
  rw [show F '' (Prod.fst ⁻¹' ({x} : Set H)) = Set.range (fun y : K ↦ F (x, y)) by
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ha, rfl⟩
      refine ⟨b, ?_⟩
      simp at ha
      simp [ha]
    · rintro ⟨y, rfl⟩
      exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

/-- The source-facing marginal function is the infimal postcomposition of `F` along the first
projection. -/
theorem marginalFunction_eq_infimalPostcomposition_fst
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    marginalFunction F = Prod.fst ▷ F := by
  ext x
  -- Rewrite both owners as the same fiberwise infimum over the second coordinate.
  rw [marginalFunction]
  simpa using (infimalPostcomposition_fst_apply (F := F.asEReal) x).symm

/-- Helper for Proposition 13.33: evaluating the product-space conjugate at a zero second dual
coordinate removes the second pairing term. -/
theorem conjugate_apply_prod_zeroSecond
    (F : H × K → EReal) (u : H) :
    F∗ (u, (0 : K)) =
      ⨆ p : H × K, (((⟪p.1, u⟫_ℝ : ℝ) : EReal) - F p) := by
  -- Expand the conjugate and simplify the product inner product against `(u, 0)`.
  rw [conjugate_apply]
  congr with p
  congr 1
  change (((⟪p.1, u⟫_ℝ + ⟪p.2, (0 : K)⟫_ℝ : ℝ) : EReal)) =
    (((⟪p.1, u⟫_ℝ : ℝ) : EReal))
  simp

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] in
/-- Helper for Proposition 13.33: each second-variable slice is bounded above by subtracting the
fiber infimum from the fixed pairing value. -/
private theorem iSup_second_slice_le_pairing_sub_partialInf
    (F : H × K → EReal) (u x : H) :
    (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) ≤
      (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) := by
  -- The map `t ↦ a - t` is antitone, so it sends the fiber infimum to an upper bound.
  let a : EReal := ((⟪x, u⟫_ℝ : ℝ) : EReal)
  have h_antitone : Antitone (fun t : EReal ↦ a - t) := by
    intro s t hst
    exact EReal.sub_le_sub le_rfl hst
  simpa [a] using (Antitone.le_map_iInf h_antitone (s := fun y : K ↦ F (x, y)))

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] in
/-- Helper for Proposition 13.33: subtracting the fiber infimum is bounded above by the supremum
of the corresponding second-variable slices. -/
private theorem pairing_sub_partialInf_le_iSup_second_slice
    (F : H × K → EReal) (u x : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) ≤
      (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) := by
  -- Rewrite the infimum as an `sInf`, then use a near-minimizer in the fiber.
  let a : EReal := ((⟪x, u⟫_ℝ : ℝ) : EReal)
  let s : Set EReal := Set.range (fun y : K ↦ F (x, y))
  have hs : (⨅ y : K, F (x, y)) = sInf s := by
    simpa [s] using (sInf_range (f := fun y : K ↦ F (x, y))).symm
  rw [hs]
  refine le_of_forall_lt fun c hc ↦ ?_
  have hsInf_ne_top : sInf s ≠ ⊤ := by
    intro hsInf_top
    have : ¬ c < (⊥ : EReal) := by simp
    simp [hsInf_top] at hc
  have hc_ne_top : c ≠ ⊤ := hc.ne_top
  have hc_add : c + sInf s < a := by
    exact
      (EReal.lt_sub_iff_add_lt (b := sInf s) (c := c) (Or.inr hc_ne_top) (Or.inl hsInf_ne_top)).1
        hc
  have hs_lt : sInf s < a - c := by
    exact
      (EReal.lt_sub_iff_add_lt (b := c) (c := sInf s) (Or.inr hsInf_ne_top) (Or.inl hc_ne_top)).2
        (by simpa [add_comm] using hc_add)
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hs_lt
  rcases hzmem with ⟨y, rfl⟩
  have hlt : c < a - F (x, y) := by
    have hz_add : F (x, y) + c < a := by
      exact EReal.add_lt_of_lt_sub hzlt
    exact
      (EReal.lt_sub_iff_add_lt (b := F (x, y)) (c := c) (Or.inr hc_ne_top) (Or.inl hzlt.ne_top)).2
        (by simpa [add_comm] using hz_add)
  exact lt_of_lt_of_le hlt (le_iSup (fun y : K ↦ a - F (x, y)) y)

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] in
/-- Helper for Proposition 13.33: fiberwise, subtracting the second-variable infimum equals the
supremum of the corresponding second-variable slices. -/
theorem pairing_sub_partialInf_eq_iSup_second_slice
    (F : H × K → EReal) (u x : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) =
      (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) := by
  -- Combine the antitone upper bound with the near-minimizer reverse inequality.
  refine le_antisymm
    (pairing_sub_partialInf_le_iSup_second_slice F u x)
    (iSup_second_slice_le_pairing_sub_partialInf F u x)

/-- Helper for Proposition 13.33: the conjugate of the first-projection infimal postcomposition is
the product conjugate evaluated on the zero second dual slice. -/
private theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_core
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.fst ▷ F)∗ = fun u ↦ F.asEReal∗ (u, (0 : K)) := by
  ext u
  -- Expand both conjugates and rewrite the first-projection infimal postcomposition fiberwise.
  rw [conjugate_apply]
  simp_rw [infimalPostcomposition_fst_apply]
  rw [conjugate_apply_prod_zeroSecond]
  -- Replace each fixed-`x` summand by the supremum over the second coordinate, then reindex.
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, (F (x, y) : EReal))) =
        (⨆ x : H, ⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          refine iSup_congr fun x ↦ ?_
          exact pairing_sub_partialInf_eq_iSup_second_slice (F := F.asEReal) u x
    _ = ⨆ p : H × K, (((⟪p.1, u⟫_ℝ : ℝ) : EReal) - (F p : EReal)) := by
          rw [iSup_prod']

/-- Proposition 13.33: if `F` is proper and
`f(x) = inf_{y ∈ K} F (x, y)`, then `f* = F*(·, 0)`. -/
theorem conjugate_marginalFunction_eq_conjugate_zeroSecond_of_isProper
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : IsProper F.asEReal) :
    (marginalFunction F)∗ = fun u ↦ F.asEReal∗ (u, (0 : K)) := by
  -- The canonical bridge itself is order-theoretic, so the properness hypothesis is carried only
  -- for the source-facing statement.
  let _ := hF
  -- Rewrite the source-facing marginal owner by the canonical first-projection infimal
  -- postcomposition and apply the core conjugacy bridge.
  rw [marginalFunction_eq_infimalPostcomposition_fst]
  exact conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_core F

/-- Evaluating the Proposition 13.33 identity at `u` gives the pointwise conjugacy formula. -/
theorem conjugate_marginalFunction_eq_conjugate_zeroSecond_of_isProper_apply
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : IsProper F.asEReal) (u : H) :
    (marginalFunction F)∗ u = F.asEReal∗ (u, (0 : K)) := by
  -- Evaluate the functional identity at the chosen dual variable.
  simpa using
    congrFun (conjugate_marginalFunction_eq_conjugate_zeroSecond_of_isProper F hF) u

/-- Rewriting the marginal function as `Prod.fst ▷ F` yields the canonical bridge used by later
files. -/
theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.fst ▷ F)∗ = fun u ↦ F.asEReal∗ (u, (0 : K)) := by
  -- This is exactly the core bridge proved in the source-proof order above.
  exact conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_core F

/-- Evaluating the `Prod.fst ▷ F` bridge at `u` gives the pointwise conjugacy formula. -/
theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_apply
    (F : H × K → Set.Ioi (⊥ : EReal)) (u : H) :
    (Prod.fst ▷ F)∗ u = F.asEReal∗ (u, (0 : K)) := by
  -- Evaluate the canonical bridge at the chosen dual variable.
  simpa using congrFun (conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond F) u

end PartialInfimumConjugation

end

end ERealFunction
