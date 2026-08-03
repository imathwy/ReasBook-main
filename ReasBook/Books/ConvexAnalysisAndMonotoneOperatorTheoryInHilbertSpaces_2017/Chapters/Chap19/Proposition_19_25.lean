import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.SaddlePoint
import BauschkeLean.Chap07.Corollary_7_19
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap19.Definition_19_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped InnerProductSpace Pointwise translate

universe u v

namespace ERealFunction

variable {H : Type u} {G : Type v}

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/-- Helper for Proposition 19.25: outside the effective domain, an `]-∞,+∞]`-valued function
takes the value `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {X : Type*} (f : X → Set.Ioi (⊥ : EReal)) {x : X}
    (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- The effective domain is exactly the set where the value is strictly below `⊤`.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))

/-- Helper for Proposition 19.25: the infimum of pointwise negatives is the negative of the
corresponding supremum. -/
private theorem iInf_neg_eq_neg_iSup_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨅ i, -φ i) = -(⨆ i, φ i) := by
  -- Negation is an order isomorphism, so it sends the `iInf` to the matching `iSup`.
  have hmap : -(⨅ i, -φ i) = ⨆ i, -(-φ i) := by
    exact OrderIso.map_iInf EReal.negOrderIso (fun i : ι ↦ -φ i)
  have hmap' : -(⨅ i, -φ i) = (⨆ i, φ i) := by
    simpa using hmap
  rw [← hmap']
  simp

/-- Helper for Proposition 19.25: the supremum of pointwise negatives is the negative of the
corresponding infimum. -/
private theorem iSup_neg_eq_neg_iInf_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨆ i, -φ i) = -(⨅ i, φ i) := by
  -- This is the dual form of `iInf_neg_eq_neg_iSup_ereal`.
  have hdual : (⨅ i, φ i) = -(⨆ i, -φ i) := by
    simpa using (iInf_neg_eq_neg_iSup_ereal (fun i : ι ↦ -φ i))
  have hneg := congrArg Neg.neg hdual
  simpa using hneg.symm

/-- Helper for Proposition 19.25: negating `-a - b` for finite real terms yields `b + a`. -/
private theorem ereal_neg_neg_sub_of_real (a b : ℝ) :
    -(-((a : ℝ) : EReal) - ((b : ℝ) : EReal)) = ((b : ℝ) : EReal) + ((a : ℝ) : EReal) := by
  have hna_bot : -((a : ℝ) : EReal) ≠ ⊥ := by
    simp
  have hna_top : -((a : ℝ) : EReal) ≠ ⊤ := by
    simp
  calc
    -(-((a : ℝ) : EReal) - ((b : ℝ) : EReal)) =
        -(-((a : ℝ) : EReal) + -((b : ℝ) : EReal)) := by
          simp [sub_eq_add_neg]
    _ = -(-((a : ℝ) : EReal)) - (-((b : ℝ) : EReal)) := by
          exact EReal.neg_add (Or.inl hna_bot) (Or.inl hna_top)
    _ = ((b : ℝ) : EReal) + ((a : ℝ) : EReal) := by
          simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 19.25: positive scaling preserves membership in a cone. -/
private theorem smul_mem_of_isCone_local
    {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X}
    (hC_cone : IsCone C) {x : X} (hx : x ∈ C) {t : ℝ} (ht : 0 < t) :
    t • x ∈ C := by
  -- Rewrite the cone law as positive-scalar invariance and use the displayed witness.
  rw [isCone_iff] at hC_cone
  exact hC_cone.symm ▸ Set.mem_smul.mpr ⟨t, ht, x, hx, rfl⟩

/-- Helper for Proposition 19.25: a convex cone is closed under addition. -/
private theorem add_mem_of_mem_convex_cone
    {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X}
    (hC_cone : IsCone C) (hC_convex : Convex ℝ C)
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ C := by
  -- Convexity gives the midpoint, and the cone law rescales the midpoint back to the sum.
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C := by
    exact hC_convex hx hy (by positivity) (by positivity) (by norm_num)
  have hsum : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ C := by
    exact smul_mem_of_isCone_local hC_cone hmid (by positivity)
  simpa [smul_add, smul_smul] using hsum

/-- Helper for Proposition 19.25: the first-coordinate lift `p ↦ f p.1` of a `Γ₀(H)` function is
again in `Γ₀(H × G)`. -/
private theorem fstLift_mem_gammaZero
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    (f ∘ Prod.fst : H × G → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H × G) := by
  -- This is the same product-first-coordinate transport used in the composite perturbation file.
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa [Function.comp] using hf.1.comp continuous_fst
  · refine ⟨?_, fun _ hp ↦ hp, ?_⟩
    · rcases hf.2.nonempty with ⟨x, hx⟩
      refine ⟨(x, 0), ?_⟩
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    · intro p hp q hq a ha0 ha1
      have hp' : p.1 ∈ effectiveDomain f := by
        simpa [Function.comp, mem_effectiveDomain_iff] using hp
      have hq' : q.1 ∈ effectiveDomain f := by
        simpa [Function.comp, mem_effectiveDomain_iff] using hq
      simpa using hf.2.ineq hp' hq' ha0 ha1

/-- Helper for Proposition 19.25: the indicator of a nonempty closed convex set belongs to
`Γ₀(H)`. -/
private theorem indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (ι[C] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Proposition 19.25: the pulled-back feasible set
`{p : H × G | R p.1 + p.2 ∈ K}` is nonempty, closed, and convex. -/
private theorem inequalityConstraintFeasibleSet_nonempty_closed_convex
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    {f : H → Set.Ioi (⊥ : EReal)} {R : H → G} {K : Set G}
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    let C : Set (H × G) := {p | R p.1 + p.2 ∈ K}
    C.Nonempty ∧ IsClosed C ∧ Convex ℝ C := by
  let C : Set (H × G) := {p | R p.1 + p.2 ∈ K}
  refine ⟨?_, ?_, ?_⟩
  · rcases hfeas with ⟨z, hzK, hzIm⟩
    rcases hzIm with ⟨x, hx, rfl⟩
    refine ⟨(x, 0), ?_⟩
    simpa [C]
  · -- Closedness comes from the continuous pullback of the closed cone `K`.
    simpa [C] using hK_closed.preimage ((hR_cont.comp continuous_fst).add continuous_snd)
  · -- Convexity combines the Jensen defect of `R` with the convex-cone stability of `K`.
    refine (convex_iff_forall_pos).2 ?_
    intro p hp q hq a b ha hb hab
    have hpK : R p.1 + p.2 ∈ K := hp
    have hqK : R q.1 + q.2 ∈ K := hq
    have hdef :
        R (a • p.1 + (1 - a) • q.1) - a • R p.1 - (1 - a) • R q.1 ∈ K := by
      have ha_mem : a ∈ Set.Ioo (0 : ℝ) 1 := by
        refine ⟨ha, ?_⟩
        have : a < a + b := lt_add_of_pos_right a hb
        simpa [hab] using this
      exact hR_convex.defect_mem ha_mem
    have hsumab : b = 1 - a := by
      linarith
    have hdef' :
        R (a • p.1 + b • q.1) - a • R p.1 - b • R q.1 ∈ K := by
      simpa [hsumab] using hdef
    have hcomb :
        a • (R p.1 + p.2) + b • (R q.1 + q.2) ∈ K := by
      exact (convex_iff_forall_pos.mp hK_convex) hpK hqK ha hb hab
    have hsum :
        (R (a • p.1 + b • q.1) - a • R p.1 - b • R q.1) +
            (a • (R p.1 + p.2) + b • (R q.1 + q.2)) ∈ K := by
      exact add_mem_of_mem_convex_cone hK_cone hK_convex hdef' hcomb
    have htarget :
        R (a • p.1 + b • q.1) + (a • p.2 + b • q.2) ∈ K := by
      simpa [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using hsum
    simpa [C, Prod.smul_mk, Prod.mk_add_mk] using htarget

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.25 introduces the perturbation attached to the inequality
  constraint `R x ∈ K` and studies its primal objective, dual objective, and Lagrangian.
- `core/canonical`: the owner declarations are `perturbationPrimalObjective`,
  `perturbationDualObjective`, `lagrangian`, and `Function.IsConvexWithRespectTo`.
- `bridge/view`: this file should therefore keep `inequalityConstraintPerturbation` as the
  source-facing owner, while phrasing the saddle-point API through the canonical Lagrangian owner
  and deriving companion consequences from that owner theorem rather than duplicating a parallel
  proof route.
-/

section Basic

variable [AddZeroClass G]
variable (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)

/-- The perturbation function attached to the inequality constraint `R x ∈ K`, written through the
canonical indicator formula `f x + ι[K] (R x + y)`. -/
abbrev inequalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    : H × G → Set.Ioi (⊥ : EReal) :=
  (f ∘ Prod.fst) + ((ι[K]) ∘ fun p : H × G ↦ R p.1 + p.2)

/-- Evaluating the inequality-constraint perturbation gives the canonical indicator formula
`f x + ι[K] (R x + y)`. -/
@[simp] theorem inequalityConstraintPerturbation_apply
    (x : H) (y : G) :
    (inequalityConstraintPerturbation f R K (x, y) : EReal) =
      (f x : EReal) + (ι[K] (R x + y) : EReal) := by
  -- Unfold the perturbation and read off the indicator term on the translated constraint fiber.
  simp [inequalityConstraintPerturbation, Function.comp]

-- Proof sketch: unfold `inequalityConstraintPerturbation` and simplify the `if`-branch selected
-- by the hypothesis `R x + y ∈ K`, so the indicator term vanishes.
/-- On the feasible branch `R x + y ∈ K`, the inequality-constraint perturbation equals `f x`. -/
@[simp] theorem inequalityConstraintPerturbation_apply_of_mem
    {x : H} {y : G} (hxy : R x + y ∈ K) :
    (inequalityConstraintPerturbation f R K (x, y) : EReal) = f x := by
  -- On the feasible branch the indicator vanishes, so only the `f x` term remains.
  rw [inequalityConstraintPerturbation_apply]
  simp [indicator_apply, hxy]

-- Proof sketch: unfold `inequalityConstraintPerturbation` and simplify the complementary
-- indicator branch selected by `R x + y ∉ K`.
/-- Off the feasible branch `R x + y ∉ K`, the inequality-constraint perturbation is `+∞`. -/
@[simp] theorem inequalityConstraintPerturbation_apply_of_not_mem
    {x : H} {y : G} (hxy : R x + y ∉ K) :
    (inequalityConstraintPerturbation f R K (x, y) : EReal) = ⊤ := by
  -- Off the feasible branch the indicator contributes `⊤`, so the whole sum is `⊤`.
  rw [inequalityConstraintPerturbation_apply]
  simpa [indicator_apply, hxy] using
    EReal.add_top_of_ne_bot (ne_of_gt (f x).2)

section Primal

-- Proof sketch: evaluate `perturbationPrimalObjective` at `0 ∈ G` and note that
-- `R x + 0 ∈ K` is equivalent to `R x ∈ K`.
/-- Proposition 19.25 (2): under the standing assumptions of Proposition 19.25, the primal
objective of the inequality-constraint perturbation is `f(x)` on the feasible set
`{x | R x ∈ K}` and `+∞` outside it, so the primal problem is to minimize `f` subject to
`R x ∈ K`. -/
theorem perturbationPrimalObjective_inequalityConstraintPerturbation
    :
    perturbationPrimalObjective (inequalityConstraintPerturbation f R K) =
      fun x : H ↦ if R x ∈ K then (f x : EReal) else ⊤ := by
  -- Evaluate the primal objective on the `y = 0` slice and simplify `R x + 0 ∈ K`.
  funext x
  by_cases hxK : R x ∈ K
  · -- On the feasible branch, the translated indicator at `y = 0` vanishes.
    have hxK0 : R x + 0 ∈ K := by
      exact Set.mem_of_eq_of_mem (add_zero (R x)) hxK
    have hvalue :
        perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x =
          (f x : EReal) := by
      simpa [perturbationPrimalObjective] using
        (inequalityConstraintPerturbation_apply_of_mem
          (f := f) (R := R) (K := K) (x := x) (y := 0) hxK0)
    calc
      perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x =
          (f x : EReal) := hvalue
      _ = if R x ∈ K then (f x : EReal) else ⊤ := by
            simp [hxK]
  · -- On the infeasible branch, the translated indicator at `y = 0` is `⊤`.
    have hxK0 : R x + 0 ∉ K := by
      intro hmem
      exact hxK (Set.mem_of_eq_of_mem (add_zero (R x)).symm hmem)
    have hvalue :
        perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x = ⊤ := by
      simpa [perturbationPrimalObjective] using
        (inequalityConstraintPerturbation_apply_of_not_mem
          (f := f) (R := R) (K := K) (x := x) (y := 0) hxK0)
    calc
      perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x = ⊤ := hvalue
      _ = if R x ∈ K then (f x : EReal) else ⊤ := by
            simp [hxK]

end Primal

end Basic

section Regularity

variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup G] [NormedSpace ℝ G]
variable (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)

-- Proof sketch: the perturbation splits as `f(x) + ι_K (R x + y)`. The feasibility hypothesis
-- makes it proper, continuity of `R` and closedness of `K` give lower semicontinuity of the
-- indicator term, and convexity of `K` together with `R.IsConvexWithRespectTo K` yields convexity
-- of its epigraph-style constraint set.
/-- Proposition 19.25 (1): if `f ∈ Γ₀(H)`, if `K` is a nonempty closed convex cone, if `R` is
continuous and convex with respect to `K`, and if `K ∩ R (dom f)` is nonempty, then the
associated inequality-constraint perturbation belongs to `Γ₀(H × G)`. -/
theorem inequalityConstraintPerturbation_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    inequalityConstraintPerturbation f R K ∈ Γ₀(H × G) := by
  let _ := hK_nonempty
  let C : Set (H × G) := {p | R p.1 + p.2 ∈ K}
  rcases
      inequalityConstraintFeasibleSet_nonempty_closed_convex
        hK_closed hK_convex hK_cone hR_cont hR_convex hfeas with
    ⟨hC_nonempty, hC_closed, hC_convex⟩
  have hfst : (f ∘ Prod.fst : H × G → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H × G) :=
    fstLift_mem_gammaZero hf
  have hindicator : (ι[C] : H × G → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H × G) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local hC_nonempty hC_closed hC_convex
  have hdom : (effectiveDomain (f ∘ Prod.fst) ∩ effectiveDomain (ι[C])).Nonempty := by
    rcases hfeas with ⟨z, hzK, hzIm⟩
    rcases hzIm with ⟨x, hx, rfl⟩
    refine ⟨(x, 0), ?_, ?_⟩
    · simpa [Function.comp, mem_effectiveDomain_iff] using hx
    · simpa [C, mem_effectiveDomain_iff]
  have hsum :
      (f ∘ Prod.fst : H × G → Set.Ioi (⊥ : EReal)) + ι[C] ∈ Γ₀(H × G) :=
    pointwiseAdd_mem_gammaZero (f ∘ Prod.fst) (ι[C]) hfst hindicator hdom
  have hEq :
      inequalityConstraintPerturbation f R K =
        (f ∘ Prod.fst : H × G → Set.Ioi (⊥ : EReal)) + ι[C] := by
    ext p
    -- Rewrite the pulled-back indicator as the indicator of the feasible set `C`.
    by_cases hp : R p.1 + p.2 ∈ K
    · simp [inequalityConstraintPerturbation, C, Function.comp, ERealFunction.indicator, hp]
    · simp [inequalityConstraintPerturbation, C, Function.comp, ERealFunction.indicator, hp]
  simpa [hEq] using hsum

end Regularity

section DualFormula

variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)

/-- Helper for Proposition 19.25: for fixed `x`, the Lagrangian fiber is the negative conjugate of
the corresponding `y`-slice. -/
private theorem lagrangian_eq_neg_conjugate_second_variable_slice
    (F : H × G → Set.Ioi (⊥ : EReal)) (x : H) (v : G) :
    ℒ[F] x v = -((fun y : G ↦ (F (x, y) : EReal))∗ v) := by
  let _ := (inferInstance : SeminormedAddCommGroup H)
  let _ := (inferInstance : NormedSpace ℝ H)
  -- Rewrite the Lagrangian fiber as an infimum of negatives and then collapse it to a conjugate.
  rw [lagrangian_apply, conjugate_apply]
  calc
    (⨅ y : G, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)) =
        ⨅ y : G, -((((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          refine iInf_congr fun y ↦ ?_
          have hneg_sub :
              -((((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) =
                -(((⟪y, v⟫_ℝ : ℝ) : EReal)) + (F (x, y) : EReal) :=
            EReal.neg_sub (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
          simpa [sub_eq_add_neg, add_comm] using hneg_sub.symm
    _ = -(⨆ y : G, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          let φ : G → EReal := fun y : G ↦
            (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))
          simpa [φ] using iInf_neg_eq_neg_iSup_ereal φ

/-- Helper for Proposition 19.25: the Fenchel conjugate of the fixed-`x` slice of the
inequality-constraint perturbation is the translated polar-cone indicator, with the off-domain
branch collapsing to `⊥`. -/
private theorem inequalityConstraintSlice_conjugate
    (hK_nonempty : K.Nonempty) (hK_cone : IsCone K)
    (x : H) (v : G) :
    ((fun y : G ↦
        (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v) =
      if _hx : x ∈ effectiveDomain f then
        if _hv : v ∈ Kᵒ⊖ then
          -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
        else
          ⊤
      else
        ⊥ := by
  let _ := (inferInstance : SeminormedAddCommGroup H)
  let _ := (inferInstance : NormedSpace ℝ H)
  -- Route correction: normalize the whole fixed-`x` slice once, including the off-domain branch,
  -- so both the dual objective and the Lagrangian can consume the same conjugate formula.
  by_cases hx : x ∈ effectiveDomain f
  · have hf_ne_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hf_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    let β : ℝ := (f x : EReal).toReal
    have hβ : (f x : EReal) = (β : EReal) := by
      simp [β, EReal.coe_toReal, hf_ne_top, hf_ne_bot]
    have hslice :
        (fun y : G ↦ (inequalityConstraintPerturbation f R K (x, y) : EReal)) =
          (τ (-(R x)) ((ι[K]).asEReal)) + fun _ : G ↦ ((β : ℝ) : EReal) := by
      funext y
      -- Rewrite the fixed slice as a translate of the indicator plus the finite constant `f x`.
      rw [inequalityConstraintPerturbation_apply, hβ]
      simp [Function.asEReal_apply, translate_apply, add_comm]
    have hconj :
        (((τ (-(R x)) ((ι[K]).asEReal)) + fun _ : G ↦ ((β : ℝ) : EReal))∗ v) =
          if hv : v ∈ Kᵒ⊖ then
            -((⟪R x, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal)
          else
            ⊤ := by
      have hbase :=
        congrFun
          (conjugate_translate_add_inner_add_const
            ((ι[K]).asEReal) (-(R x)) (0 : G) β)
          v
      rw [conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
          K hK_nonempty hK_cone] at hbase
      by_cases hv : v ∈ Kᵒ⊖
      · simpa [hv, Function.asEReal_apply, indicator_apply, inner_neg_left, sub_eq_add_neg,
          translate_apply, add_assoc, add_left_comm, add_comm] using hbase
      · simpa [hv, Function.asEReal_apply, indicator_apply, inner_neg_left, sub_eq_add_neg,
          translate_apply, add_assoc, add_left_comm, add_comm] using hbase
    rw [hslice]
    simpa [hx, hβ] using hconj
  · have htop_slice :
      (fun y : G ↦ (inequalityConstraintPerturbation f R K (x, y) : EReal)) =
        fun _ : G ↦ (⊤ : EReal) := by
      funext y
      -- Off the effective domain, every value of the fixed slice is `⊤`.
      have hfx_top : (f x : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain f hx
      rw [inequalityConstraintPerturbation_apply, hfx_top]
      by_cases hy : R x + y ∈ K
      · simp [indicator_apply, hy]
      · simp [indicator_apply, hy]
    rw [conjugate_apply]
    calc
      (⨆ y : G, (((⟪y, v⟫_ℝ : ℝ) : EReal) -
          (inequalityConstraintPerturbation f R K (x, y) : EReal))) =
          ⨆ y : G, (⊥ : EReal) := by
            refine iSup_congr fun y ↦ ?_
            have hy_top :
                (inequalityConstraintPerturbation f R K (x, y) : EReal) = ⊤ := by
              simpa using congrFun htop_slice y
            rw [hy_top]
            simp
      _ = ⊥ := by
            simp
      _ = if hx : x ∈ effectiveDomain f then
            if hv : v ∈ Kᵒ⊖ then
              -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
            else
              ⊤
          else
            ⊥ := by
              simp [hx]

-- Proof sketch: compute `perturbationDualObjective` of the perturbation as `F^*(0, v)`,
-- separate the supremum over `x` from the cone-indicator contribution in `y`, and identify
-- the latter with the
-- indicator of the polar cone `Kᵒ⊖`.
/-- Proposition 19.25 (3): under the standing assumptions of Proposition 19.25, the dual
objective of the inequality-constraint perturbation is the function that equals
`sup_x (-⟪R x, v⟫ - f x)` on `Kᵒ⊖` and `+∞` outside `Kᵒ⊖`. -/
theorem perturbationDualObjective_inequalityConstraintPerturbation
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    perturbationDualObjective (inequalityConstraintPerturbation f R K) =
      fun v : G ↦
        if v ∈ Kᵒ⊖ then
          ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
        else ⊤ := by
  let _ := hK_closed
  let _ := hK_convex
  let _ := hR_cont
  let _ := hR_convex
  let _ := hfeas
  -- Decompose the product supremum into fixed-`x` slice conjugates, then read off the two branches.
  ext v
  calc
    perturbationDualObjective (inequalityConstraintPerturbation f R K) v =
        ⨆ x : H, ((fun y : G ↦ (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v) := by
          rw [perturbationDualObjective_apply]
          calc
            (⨆ p : H × G, (((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
                (inequalityConstraintPerturbation f R K p : EReal))) =
                (⨆ x : H, ⨆ y : G,
                  (((⟪y, v⟫_ℝ : ℝ) : EReal) -
                    (inequalityConstraintPerturbation f R K (x, y) : EReal))) := by
                      simpa using
                        (iSup_prod'
                          (fun x : H ↦ fun y : G ↦
                            (((⟪y, v⟫_ℝ : ℝ) : EReal) -
                              (inequalityConstraintPerturbation f R K (x, y) : EReal)))).symm
            _ = ⨆ x : H, ((fun y : G ↦
                (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v) := by
                  refine iSup_congr fun x ↦ ?_
                  rw [conjugate_apply]
    _ = (fun v : G ↦
        if v ∈ Kᵒ⊖ then
          ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
        else ⊤) v := by
          by_cases hv : v ∈ Kᵒ⊖
          · calc
              (⨆ x : H,
                ((fun y : G ↦
                    (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v)) =
                  ⨆ x : H, if hx : x ∈ effectiveDomain f then
                    -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
                  else
                    ⊥ := by
                      refine iSup_congr fun x ↦ ?_
                      simpa [hv] using
                        inequalityConstraintSlice_conjugate f R K hK_nonempty hK_cone x v
              _ = ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal) := by
                    refine iSup_congr fun x ↦ ?_
                    by_cases hx : x ∈ effectiveDomain f
                    · simp [hx]
                    · have hfx_top : (f x : EReal) = ⊤ := by
                        exact value_eq_top_of_not_mem_effectiveDomain f hx
                      simp [hx, hfx_top]
              _ = (fun v : G ↦
                  if v ∈ Kᵒ⊖ then
                    ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
                  else ⊤) v := by
                    simp [hv]
          · rcases hf.2.nonempty with ⟨x0, hx0⟩
            have htop_x0 :
                ((fun y : G ↦
                    (inequalityConstraintPerturbation f R K (x0, y) : EReal))∗ v) = ⊤ := by
              simpa [hx0, hv] using
                inequalityConstraintSlice_conjugate f R K hK_nonempty hK_cone x0 v
            have htop :
                (⊤ : EReal) ≤
                  ⨆ x : H,
                    ((fun y : G ↦
                        (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v) := by
              calc
                (⊤ : EReal) =
                    ((fun y : G ↦
                        (inequalityConstraintPerturbation f R K (x0, y) : EReal))∗ v) := by
                      symm
                      exact htop_x0
                _ ≤ ⨆ x : H,
                    ((fun y : G ↦ (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v) := by
                      exact le_iSup
                        (fun x : H ↦
                          ((fun y : G ↦ (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v))
                        x0
            have hvalue :
                (⨆ x : H,
                  ((fun y : G ↦
                      (inequalityConstraintPerturbation f R K (x, y) : EReal))∗ v)) =
                  ⊤ :=
              le_antisymm le_top htop
            simpa [hv] using hvalue

-- Proof sketch: unfold `lagrangian` as the infimum over `y`, then split according to whether
-- `x ∈ effectiveDomain f`. For `x` in the effective domain, rewrite the remaining infimum over the
-- feasible fiber as the indicator of the polar cone, giving the three branches of the displayed
-- formula.
/-- Proposition 19.25 (4): under the standing assumptions of Proposition 19.25, the Lagrangian
of the inequality-constraint perturbation is `+∞` off `dom f`, equals `f(x) + ⟪R x, v⟫` when
`x ∈ dom f` and `v ∈ Kᵒ⊖`, and equals `-∞` when `x ∈ dom f` but `v ∉ Kᵒ⊖`. -/
theorem lagrangian_inequalityConstraintPerturbation
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    (x : H) (v : G) :
    ℒ[inequalityConstraintPerturbation f R K] x v =
      if _hx : x ∈ effectiveDomain f then
        if _hv : v ∈ Kᵒ⊖ then
          (f x : EReal) + (⟪R x, v⟫_ℝ : EReal)
        else ⊥
      else ⊤ := by
  let _ := hf
  let _ := hK_closed
  let _ := hK_convex
  let _ := hR_cont
  let _ := hR_convex
  let _ := hfeas
  -- Route correction: consume the fixed-slice conjugate theorem instead of re-normalizing the
  -- translated feasible fiber directly inside the main proof.
  by_cases hx : x ∈ effectiveDomain f
  · by_cases hv : v ∈ Kᵒ⊖
    · have hf_ne_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hf_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
      let β : ℝ := (f x : EReal).toReal
      have hβ : (f x : EReal) = (β : EReal) := by
        simp [β, EReal.coe_toReal, hf_ne_top, hf_ne_bot]
      -- Once `f x` is identified with a finite real constant, the branch is just real arithmetic.
      rw [lagrangian_eq_neg_conjugate_second_variable_slice,
        inequalityConstraintSlice_conjugate f R K hK_nonempty hK_cone x v]
      calc
        -((if hx : x ∈ effectiveDomain f then
            if hv : v ∈ Kᵒ⊖ then
              -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
            else
              ⊤
          else
            ⊥)) =
            -(-((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)) := by
              simp [hx, hv]
        _ = -(-((⟪R x, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal)) := by
              rw [hβ]
        _ = ((β : ℝ) : EReal) + (⟪R x, v⟫_ℝ : EReal) := by
              simpa using ereal_neg_neg_sub_of_real (⟪R x, v⟫_ℝ) β
        _ = (f x : EReal) + (⟪R x, v⟫_ℝ : EReal) := by
              rw [hβ]
        _ = if hx : x ∈ effectiveDomain f then
              if hv : v ∈ Kᵒ⊖ then
                (f x : EReal) + (⟪R x, v⟫_ℝ : EReal)
              else
                ⊥
            else
              ⊤ := by
                simp [hx, hv]
    · rw [lagrangian_eq_neg_conjugate_second_variable_slice,
        inequalityConstraintSlice_conjugate f R K hK_nonempty hK_cone x v]
      simp [hx, hv]
  · rw [lagrangian_eq_neg_conjugate_second_variable_slice,
      inequalityConstraintSlice_conjugate f R K hK_nonempty hK_cone x v]
    simp [hx]

end DualFormula

section SaddlePointCriterion

variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)

/-- Helper for Proposition 19.25: for a finite value `f x`, comparing the shifted objective values
in `EReal` is equivalent to comparing the corresponding real shifts. -/
private theorem ereal_add_real_le_add_real_iff_of_mem_effectiveDomain
    {x : H} (hx : x ∈ effectiveDomain f) {a b : ℝ} :
    ((f x : EReal) + (a : EReal) ≤ (f x : EReal) + (b : EReal)) ↔ a ≤ b := by
  let _ := (inferInstance : SeminormedAddCommGroup H)
  let _ := (inferInstance : NormedSpace ℝ H)
  -- Replace `f x` by its finite real representative and then move the comparison back to `ℝ`.
  have hf_ne_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hf_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  let β : ℝ := (f x : EReal).toReal
  have hβ : (f x : EReal) = (β : EReal) := by
    simp [β, EReal.coe_toReal, hf_ne_top, hf_ne_bot]
  constructor
  · intro hle
    have hle' : (((β + a : ℝ) : EReal)) ≤ (((β + b : ℝ) : EReal)) := by
      simpa [hβ] using hle
    have hle'' : β + a ≤ β + b := by
      exact_mod_cast hle'
    linarith
  · intro hle
    have hle'' : β + a ≤ β + b := by
      linarith
    have hle' : (((β + a : ℝ) : EReal)) ≤ (((β + b : ℝ) : EReal)) := by
      exact_mod_cast hle''
    simpa [hβ] using hle'

/-- Helper for Proposition 19.25: on the polar-feasible branch, the Lagrangian is the shifted
objective `x ↦ f x + ⟪R x, v⟫`. -/
private theorem lagrangian_eq_shiftedObjective_of_mem_polarCone
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {x : H} {v : G} (hv : v ∈ Kᵒ⊖) :
    ℒ[inequalityConstraintPerturbation f R K] x v =
      (f x : EReal) + (⟪R x, v⟫_ℝ : EReal) := by
  let _ := (inferInstance : CompleteSpace G)
  by_cases hx : x ∈ effectiveDomain f
  · simpa [hx, hv] using
      lagrangian_inequalityConstraintPerturbation
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas x v
  · have hfx_top : (f x : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain f hx
    simpa [hx, hv, hfx_top] using
      lagrangian_inequalityConstraintPerturbation
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas x v

/-- Helper for Proposition 19.25: the polar cone `Kᵒ⊖` is itself a cone. -/
private theorem polarCone_isCone_local :
    IsCone (Kᵒ⊖ : Set G) := by
  let _ := (inferInstance : CompleteSpace G)
  rw [isCone_iff]
  refine Set.Subset.antisymm ?_ ?_
  · intro u hu
    exact Set.mem_smul.mpr ⟨1, by simp, u, hu, by simp⟩
  · intro u hu
    rcases Set.mem_smul.mp hu with ⟨t, ht, w, hw, rfl⟩
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hw ⊢
    intro x hx
    simpa [inner_smul_right] using mul_nonpos_of_nonneg_of_nonpos ht.le (hw x hx)

/-- Helper for Proposition 19.25: if `v̄` maximizes the `x`-fiber of the Lagrangian over the polar
cone, then every polar direction has nonpositive pairing with `R x`. -/
private theorem inner_nonpos_of_lagrangian_fiber_maximizer
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {x : H} (hx : x ∈ effectiveDomain f) {vbar : G} (hvbar : vbar ∈ Kᵒ⊖)
    (hsup :
      sSup (Set.range fun w : G ↦ ℒ[inequalityConstraintPerturbation f R K] x w) =
        ℒ[inequalityConstraintPerturbation f R K] x vbar) :
    ∀ w ∈ Kᵒ⊖, ⟪R x, w⟫_ℝ ≤ 0 := by
  let β : ℝ := ⟪R x, vbar⟫_ℝ
  have hpolar_cone : IsCone (Kᵒ⊖ : Set G) := polarCone_isCone_local K
  intro w hw
  by_contra hnonpos
  have hpos : 0 < ⟪R x, w⟫_ℝ := lt_of_not_ge hnonpos
  let t : ℝ := (max β 0 + 1) / ⟪R x, w⟫_ℝ
  have ht : 0 < t := by
    dsimp [t, β]
    positivity
  have htw : t • w ∈ Kᵒ⊖ := smul_mem_of_isCone_local hpolar_cone hw ht
  have hle :
      ℒ[inequalityConstraintPerturbation f R K] x (t • w) ≤
        ℒ[inequalityConstraintPerturbation f R K] x vbar := by
    calc
      ℒ[inequalityConstraintPerturbation f R K] x (t • w) ≤
          sSup (Set.range fun u : G ↦ ℒ[inequalityConstraintPerturbation f R K] x u) := by
            exact le_sSup ⟨t • w, rfl⟩
      _ = ℒ[inequalityConstraintPerturbation f R K] x vbar := hsup
  have hle' :
      (f x : EReal) + ((t * ⟪R x, w⟫_ℝ : ℝ) : EReal) ≤
        (f x : EReal) + ((β : ℝ) : EReal) := by
    calc
      (f x : EReal) + ((t * ⟪R x, w⟫_ℝ : ℝ) : EReal) =
          ℒ[inequalityConstraintPerturbation f R K] x (t • w) := by
            symm
            simpa [inner_smul_right, mul_comm] using
              lagrangian_eq_shiftedObjective_of_mem_polarCone
                f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas htw
      _ ≤ ℒ[inequalityConstraintPerturbation f R K] x vbar := hle
      _ = (f x : EReal) + ((β : ℝ) : EReal) := by
            simpa [β] using
              lagrangian_eq_shiftedObjective_of_mem_polarCone
                f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
  have hle'' : t * ⟪R x, w⟫_ℝ ≤ β :=
    (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hx).1 hle'
  have htw_eq : t * ⟪R x, w⟫_ℝ = max β 0 + 1 := by
    have hw_ne : ⟪R x, w⟫_ℝ ≠ 0 := ne_of_gt hpos
    dsimp [t]
    field_simp [hw_ne]
  have hβ_lt : β < t * ⟪R x, w⟫_ℝ := by
    rw [htw_eq]
    have hβ_le : β ≤ max β 0 := le_max_left β 0
    linarith
  exact not_lt_of_ge hle'' hβ_lt

/-- Helper for Proposition 19.25: a saddle point already forces `x̄ ∈ dom f` and
`v̄ ∈ Kᵒ⊖`. -/
private theorem effectiveDomain_and_polar_of_isSaddlePointOn_inequalityConstraintLagrangian
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    xbar ∈ effectiveDomain f ∧ vbar ∈ Kᵒ⊖ := by
  let F := inequalityConstraintPerturbation f R K
  have hs := (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddle
  have hfeas_mem : (K ∩ R '' effectiveDomain f).Nonempty := hfeas
  have hfeas_data : (K ∩ R '' effectiveDomain f).Nonempty := hfeas
  rcases hfeas_data with ⟨z, hzK, hzIm⟩
  rcases hzIm with ⟨x0, hx0, rfl⟩
  have hxbar : xbar ∈ effectiveDomain f := by
    -- Compare the minimizing `x̄`-fiber against one feasible finite slice
    -- to rule out `ℒ[F] x̄ v̄ = ⊤`.
    by_contra hxbar
    have hx0_ne_top : ℒ[F] x0 vbar ≠ ⊤ := by
      by_cases hv0 : vbar ∈ Kᵒ⊖
      · have hle : ℒ[F] x0 vbar ≤ (f x0 : EReal) := by
          have hinner_nonpos0 : ⟪R x0, vbar⟫_ℝ ≤ 0 := by
            rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hv0
            exact hv0 (R x0) hzK
          calc
            ℒ[F] x0 vbar = (f x0 : EReal) + (⟪R x0, vbar⟫_ℝ : EReal) := by
              simpa [F] using
                  lagrangian_eq_shiftedObjective_of_mem_polarCone
                    f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex
                    hfeas_mem hv0
            _ ≤ (f x0 : EReal) := by
              simpa using
                (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hx0).2 hinner_nonpos0
        intro htop
        exact (ne_of_lt (mem_effectiveDomain_iff.mp hx0)) (top_le_iff.mp (htop ▸ hle))
      · have hbot : ℒ[F] x0 vbar = ⊥ := by
          simpa [F, hx0, hv0] using
            lagrangian_inequalityConstraintPerturbation
              f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas_mem x0
              vbar
        intro htop
        rw [hbot] at htop
        simp at htop
    have htop : ℒ[F] xbar vbar = ⊤ := by
      simpa [F, hxbar] using
        lagrangian_inequalityConstraintPerturbation
          f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas_mem xbar
          vbar
    have hle : sInf (Set.range fun z : H ↦ ℒ[F] z vbar) ≤ ℒ[F] x0 vbar := by
      exact sInf_le ⟨x0, rfl⟩
    rw [hs.2, htop] at hle
    exact hx0_ne_top (top_le_iff.mp hle)
  have hzero_polar : (0 : G) ∈ Kᵒ⊖ := Set.zero_mem_polarCone K
  have hzero_value : ℒ[F] xbar (0 : G) = (f xbar : EReal) := by
    -- The zero multiplier is always polar-feasible,
    -- so the fiber reduces to the unshifted objective.
    simpa [F] using
      lagrangian_eq_shiftedObjective_of_mem_polarCone
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas_mem
        hzero_polar
  have hvbar : vbar ∈ Kᵒ⊖ := by
    -- Compare `v̄` against the zero multiplier to rule out the `⊥` branch of the Lagrangian.
    by_contra hvbar
    have hbot : ℒ[F] xbar vbar = ⊥ := by
      simpa [F, hxbar, hvbar] using
        lagrangian_inequalityConstraintPerturbation
          f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas_mem xbar
          vbar
    have hsSup_bot : sSup (Set.range fun w : G ↦ ℒ[F] xbar w) = ⊥ := by
      rw [hs.1, hbot]
    have hle : ℒ[F] xbar (0 : G) ≤ (⊥ : EReal) := by
      calc
        ℒ[F] xbar (0 : G) ≤ sSup (Set.range fun w : G ↦ ℒ[F] xbar w) := by
          exact le_sSup ⟨0, rfl⟩
        _ = ⊥ := hsSup_bot
    have hzero_ne_bot : ℒ[F] xbar (0 : G) ≠ ⊥ := by
      rw [hzero_value]
      exact ne_of_gt (f xbar).2
    exact hzero_ne_bot (le_bot_iff.mp hle)
  exact ⟨hxbar, hvbar⟩

/-- Helper for Proposition 19.25: on a polar fiber, the Lagrangian range agrees with the shifted
objective range. -/
private theorem lagrangianFiber_range_eq_shiftedObjectiveRange_of_mem_polarCone
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {v : G} (hv : v ∈ Kᵒ⊖) :
    Set.range (fun x : H ↦ ℒ[inequalityConstraintPerturbation f R K] x v) =
      Set.range (fun x : H ↦ (f x : EReal) + (⟪R x, v⟫_ℝ : EReal)) := by
  -- Normalize the fixed `v`-fiber once so both directions can reuse the same transport.
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (lagrangian_eq_shiftedObjective_of_mem_polarCone
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hv).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, lagrangian_eq_shiftedObjective_of_mem_polarCone
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hv⟩

/-- Helper for Proposition 19.25: once `x̄ ∈ dom f` and `v̄ ∈ Kᵒ⊖` are known, the remaining
forward-direction work is primal feasibility plus complementary slackness. -/
private theorem primalFeasible_and_inner_eq_zero_of_isSaddlePointOn_inequalityConstraintLagrangian
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar)
    (hxbar : xbar ∈ effectiveDomain f) (hvbar : vbar ∈ Kᵒ⊖) :
    R xbar ∈ K ∧ ⟪R xbar, vbar⟫_ℝ = 0 := by
  let F := inequalityConstraintPerturbation f R K
  have hs := (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddle
  have hinner_nonpos_all : ∀ w ∈ Kᵒ⊖, ⟪R xbar, w⟫_ℝ ≤ 0 :=
    inner_nonpos_of_lagrangian_fiber_maximizer
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
      hxbar hvbar hs.1
  have hRxbar_bipolar : R xbar ∈ Kᵒ⊖ᵒ⊖ := by
    -- The fiber maximizer inequality exactly says that `R x̄` lies in the double polar cone.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro w hw
    simpa [real_inner_comm] using hinner_nonpos_all w hw
  -- Route correction: close primal feasibility by rewriting the double polar cone back to `K`.
  have hRxbar : R xbar ∈ K := by
    have hKK : Kᵒ⊖ᵒ⊖ = K :=
      Set.polarCone_polarCone_eq_of_nonempty_of_isClosed_of_convex_of_isCone
        K hK_nonempty hK_closed hK_convex hK_cone
    simpa [hKK] using hRxbar_bipolar
  have hzero_polar : (0 : G) ∈ Kᵒ⊖ := Set.zero_mem_polarCone K
  have hzero_value : ℒ[F] xbar (0 : G) = (f xbar : EReal) := by
    -- The zero multiplier gives the unshifted objective value at the saddle point.
    simpa [F] using
      lagrangian_eq_shiftedObjective_of_mem_polarCone
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hzero_polar
  have hinner_nonpos : ⟪R xbar, vbar⟫_ℝ ≤ 0 := hinner_nonpos_all vbar hvbar
  have hzero_le :
      (f xbar : EReal) + (0 : EReal) ≤
        (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
    -- Compare the zero multiplier against the maximizing multiplier `v̄`.
    calc
      (f xbar : EReal) + (0 : EReal) = ℒ[F] xbar (0 : G) := by
        rw [hzero_value]
        simp
      _ ≤ sSup (Set.range fun w : G ↦ ℒ[F] xbar w) := by
        exact le_sSup ⟨0, rfl⟩
      _ = ℒ[F] xbar vbar := hs.1
      _ = (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
        simpa [F] using
          lagrangian_eq_shiftedObjective_of_mem_polarCone
            f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
  have hinner_nonneg : 0 ≤ ⟪R xbar, vbar⟫_ℝ :=
    (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hxbar).1 hzero_le
  have hinner_zero : ⟪R xbar, vbar⟫_ℝ = 0 := by
    linarith
  exact ⟨hRxbar, hinner_zero⟩

/-- Helper for Proposition 19.25: the forward saddle implication yields the displayed optimality
system of clause (19.56). -/
private theorem optimalitySystem_of_isSaddlePointOn_inequalityConstraintLagrangian
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    xbar ∈ effectiveDomain f ∩ {x | R x ∈ K} ∧
      vbar ∈ Kᵒ⊖ ∧
      (f xbar : EReal) =
        sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  let F := inequalityConstraintPerturbation f R K
  have hs := (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddle
  obtain ⟨hxbar, hvbar⟩ :=
    effectiveDomain_and_polar_of_isSaddlePointOn_inequalityConstraintLagrangian
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle
  obtain ⟨hRxbar, hinner_zero⟩ :=
    primalFeasible_and_inner_eq_zero_of_isSaddlePointOn_inequalityConstraintLagrangian
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
      hsaddle hxbar hvbar
  have hrange :
      Set.range (fun x : H ↦ ℒ[F] x vbar) =
        Set.range (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) :=
    lagrangianFiber_range_eq_shiftedObjectiveRange_of_mem_polarCone
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
  have hsInf_eq :
      (f xbar : EReal) =
        sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
    -- Rewrite the minimizing `x`-fiber once
    -- and then use complementary slackness to remove the shift.
    calc
      (f xbar : EReal) = ℒ[F] xbar vbar := by
        calc
          (f xbar : EReal) = (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
            simp [hinner_zero]
          _ = ℒ[F] xbar vbar := by
            symm
            simpa [F] using
              lagrangian_eq_shiftedObjective_of_mem_polarCone
                f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
      _ = sInf (Set.range fun x : H ↦ ℒ[F] x vbar) := hs.2.symm
      _ = sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
            rw [hrange]
  exact ⟨⟨hxbar, hRxbar⟩, hvbar, hsInf_eq⟩

/-- Helper for Proposition 19.25: the displayed optimality system of clause (19.56) assembles
back into a saddle point. -/
private theorem isSaddlePointOn_of_inequalityConstraintOptimalitySystem
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hxbar : xbar ∈ effectiveDomain f) (hRxbar : R xbar ∈ K) (hvbar : vbar ∈ Kᵒ⊖)
    (hsInf_eq :
      (f xbar : EReal) =
        sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal))) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
      (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar := by
  let F := inequalityConstraintPerturbation f R K
  have hinner_nonpos : ⟪R xbar, vbar⟫_ℝ ≤ 0 := by
    -- Dual feasibility bounds the active pairing above by zero on the feasible point `R x̄`.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hvbar
    exact hvbar (R xbar) hRxbar
  have hinner_nonneg : 0 ≤ ⟪R xbar, vbar⟫_ℝ := by
    -- Evaluating the displayed infimum at `x = x̄` gives the reverse inequality.
    have hle :
        (f xbar : EReal) + (0 : EReal) ≤
          (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
      calc
        (f xbar : EReal) + (0 : EReal) = (f xbar : EReal) := by
          simp
        _ = sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := hsInf_eq
        _ ≤ (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
              exact sInf_le ⟨xbar, rfl⟩
    exact
      (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hxbar).1 hle
  have hinner_zero : ⟪R xbar, vbar⟫_ℝ = 0 := by
    linarith
  have hcurrent : ℒ[F] xbar vbar = (f xbar : EReal) := by
    -- Complementary slackness collapses the active Lagrangian branch back to the primal value.
    calc
      ℒ[F] xbar vbar = (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
        simpa [F] using
          lagrangian_eq_shiftedObjective_of_mem_polarCone
            f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
      _ = (f xbar : EReal) := by
        simp [hinner_zero]
  have hsSup_eq :
      sSup (Set.range fun w : G ↦ ℒ[F] xbar w) = (f xbar : EReal) := by
    -- Split the supremum over multipliers into the polar branch and the `⊥` branch.
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro _ ⟨w, rfl⟩
      by_cases hw : w ∈ Kᵒ⊖
      · calc
          ℒ[F] xbar w = (f xbar : EReal) + (⟪R xbar, w⟫_ℝ : EReal) := by
            simpa [F] using
              lagrangian_eq_shiftedObjective_of_mem_polarCone
                f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hw
          _ ≤ (f xbar : EReal) := by
            have hw_nonpos : ⟪R xbar, w⟫_ℝ ≤ 0 := by
              rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hw
              exact hw (R xbar) hRxbar
            simpa using
              (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hxbar).2 hw_nonpos
      · have hbot : ℒ[F] xbar w = ⊥ := by
          simpa [F, hxbar, hw] using
            lagrangian_inequalityConstraintPerturbation
              f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas xbar w
        change ℒ[F] xbar w ≤ (f xbar : EReal)
        rw [hbot]
        exact bot_le
    · calc
        (f xbar : EReal) = ℒ[F] xbar (0 : G) := by
          symm
          simpa [F] using
            lagrangian_eq_shiftedObjective_of_mem_polarCone
              f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
              (Set.zero_mem_polarCone K)
        _ ≤ sSup (Set.range fun w : G ↦ ℒ[F] xbar w) := by
              exact le_sSup ⟨0, rfl⟩
  have hrange :
      Set.range (fun x : H ↦ ℒ[F] x vbar) =
        Set.range (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) :=
    lagrangianFiber_range_eq_shiftedObjectiveRange_of_mem_polarCone
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hvbar
  refine (lagrangian_isSaddlePointOn_iff F xbar vbar).2 ?_
  constructor
  · calc
      sSup (Set.range fun w : G ↦ ℒ[F] xbar w) = (f xbar : EReal) := hsSup_eq
      _ = ℒ[F] xbar vbar := hcurrent.symm
  · calc
      sInf (Set.range fun z : H ↦ ℒ[F] z vbar) =
          sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
            rw [hrange]
      _ = (f xbar : EReal) := hsInf_eq.symm
      _ = ℒ[F] xbar vbar := hcurrent.symm

-- Mathlib recall: `isSaddlePointOn_iff` provides the canonical
-- saddle-point owner used for the source-facing Lagrangian criterion below.
-- Proof sketch: rewrite the saddle condition with the local Fenchel--Young zero-gap bridge, then
-- normalize the primal and dual values by the perturbation-specific
-- zero-gap criterion proved just above.
/-- Proposition 19.25 (5): under the standing assumptions of Proposition 19.25, a pair
`(x̄, v̄)` is a saddle point of the Lagrangian attached to the inequality-constraint perturbation
if and only if it satisfies the corresponding saddle-point optimality system: `x̄ ∈ dom f`,
`R x̄ ∈ K`, `v̄ ∈ Kᵒ⊖`, and `(f x̄ : EReal)` is the infimum of
`x ↦ (f x : EReal) + (⟪R x, v̄⟫_ℝ : EReal)`. -/
theorem isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    (xbar : H) (vbar : G) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
      (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar ↔
        xbar ∈ effectiveDomain f ∩ {x | R x ∈ K} ∧
          vbar ∈ Kᵒ⊖ ∧
          (f xbar : EReal) =
            sInf (Set.range fun x : H ↦
              (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  constructor
  · intro hsaddle
    exact
      optimalitySystem_of_isSaddlePointOn_inequalityConstraintLagrangian
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle
  · rintro ⟨hxbarK, hvbar, hsInf_eq⟩
    exact
      isSaddlePointOn_of_inequalityConstraintOptimalitySystem
        f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
        hxbarK.1 (by simpa [Set.mem_setOf_eq] using hxbarK.2) hvbar hsInf_eq

-- Proof sketch: combine Proposition 19.25 (5) with `mem_argmin_iff_eq_sInf`, then use the
-- complementary-slackness conclusion derived later in this file to convert the displayed
-- infimum equality into the equivalent `Argmin` statement for the shifted objective.
/-- A saddle point of the inequality-constraint Lagrangian makes `x̄` a minimizer of
`x ↦ (f x : EReal) + (⟪R x, v̄⟫_ℝ : EReal)`. -/
theorem mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  -- Proposition 19.25 (5) gives the `sInf` identity for `f x̄`; complementary slackness turns it
  -- into the matching `Argmin` identity for the shifted objective.
  obtain ⟨hxbarK, hvbar, hsInf_eq⟩ :=
    (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas xbar
      vbar).mp hsaddle
  have hxbar : xbar ∈ effectiveDomain f := hxbarK.1
  have hRxbar : R xbar ∈ K := by
    simpa [Set.mem_setOf_eq] using hxbarK.2
  have hinner_nonpos : ⟪R xbar, vbar⟫_ℝ ≤ 0 := by
    -- Dual feasibility bounds the active inner product above by zero.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hvbar
    exact hvbar (R xbar) hRxbar
  have hinner_nonneg : 0 ≤ ⟪R xbar, vbar⟫_ℝ := by
    -- Evaluating the displayed infimum at `x = xbar` gives the reverse inequality.
    have hle :
        (f xbar : EReal) + (0 : EReal) ≤
          (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
      calc
        (f xbar : EReal) + (0 : EReal) = (f xbar : EReal) := by simp
        _ = sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := hsInf_eq
        _ ≤ (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
              exact sInf_le ⟨xbar, rfl⟩
    exact
      (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hxbar).1 hle
  have hinner_zero : ⟪R xbar, vbar⟫_ℝ = 0 := by
    linarith
  rw [mem_argmin_iff_eq_sInf]
  calc
    (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) = (f xbar : EReal) := by
      simp [hinner_zero]
    _ = sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := hsInf_eq

-- Proof sketch: combine the saddle-point criterion above with the Lagrangian branch formula from
-- clause (4). The infimum condition at `x̄` gives `0 ≤ ⟪R x̄, v̄⟫`, while primal feasibility
-- `R x̄ ∈ K` and dual feasibility `v̄ ∈ Kᵒ⊖` give the reverse inequality; hence
-- `⟪R x̄, v̄⟫ = 0`, and the feasible-branch formula for `perturbationPrimalObjective` yields
-- primal optimality of `x̄`.
/-- Helper for Proposition 19.25: on the feasible set, dual feasibility makes the shifted
objective no larger than the original value `f x`. -/
private theorem shiftedObjective_le_of_feasible_and_polar
    {x : H} {v : G} (hxK : R x ∈ K) (hv : v ∈ Kᵒ⊖) :
    (f x : EReal) + (⟪R x, v⟫_ℝ : EReal) ≤ (f x : EReal) := by
  let _ := (inferInstance : CompleteSpace G)
  -- Either `f x = ⊤`, in which case the claim is trivial, or `f x` is finite and the polar
  -- inequality cancels directly.
  by_cases hx : x ∈ effectiveDomain f
  · have hinner_nonpos : ⟪R x, v⟫_ℝ ≤ 0 := by
      rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hv
      exact hv (R x) hxK
    simpa using
      (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hx).2 hinner_nonpos
  · have hfx_top : (f x : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain f hx
    simp [hfx_top]

/-- Helper for Proposition 19.25: a saddle point satisfies complementary slackness. -/
private theorem inner_eq_zero_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    ⟪R xbar, vbar⟫_ℝ = 0 := by
  -- The saddle criterion gives the shifted-objective infimum equality and the primal/dual
  -- feasibility clauses needed to recover complementary slackness.
  obtain ⟨hxbarK, hvbar, hsInf_eq⟩ :=
    (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas xbar
      vbar).mp hsaddle
  have hxbar : xbar ∈ effectiveDomain f := hxbarK.1
  have hRxbar : R xbar ∈ K := by
    simpa [Set.mem_setOf_eq] using hxbarK.2
  have hinner_nonpos : ⟪R xbar, vbar⟫_ℝ ≤ 0 := by
    -- Dual feasibility bounds the active inner product above by zero.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hvbar
    exact hvbar (R xbar) hRxbar
  have hinner_nonneg : 0 ≤ ⟪R xbar, vbar⟫_ℝ := by
    -- Evaluating the displayed infimum at `x = xbar` gives the reverse inequality.
    have hle :
        (f xbar : EReal) + (0 : EReal) ≤
          (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
      calc
        (f xbar : EReal) + (0 : EReal) = (f xbar : EReal) := by simp
        _ = sInf (Set.range fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := hsInf_eq
        _ ≤ (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
              exact sInf_le ⟨xbar, rfl⟩
    exact
      (ereal_add_real_le_add_real_iff_of_mem_effectiveDomain f hxbar).1 hle
  linarith

/-- Under the standing assumptions of Proposition 19.25, a saddle point of the
inequality-constraint Lagrangian satisfies complementary slackness and its first component solves
the primal perturbation problem. This is the `in which case` conclusion attached to Proposition
19.25 (5). -/
theorem
    inner_eq_zero_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    ⟪R xbar, vbar⟫_ℝ = 0 ∧
      xbar ∈
        Argmin (perturbationPrimalObjective (inequalityConstraintPerturbation f R K)) := by
  obtain ⟨hxbarK, hvbar, _⟩ :=
    (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas xbar
      vbar).mp hsaddle
  have hxbar : xbar ∈ effectiveDomain f := hxbarK.1
  have hRxbar : R xbar ∈ K := by
    simpa [Set.mem_setOf_eq] using hxbarK.2
  have hinner_zero :
      ⟪R xbar, vbar⟫_ℝ = 0 :=
    inner_eq_zero_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle
  have hshift_argmin :
      xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) :=
    mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
      f R K hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle
  have hprimal_eq :
      perturbationPrimalObjective (inequalityConstraintPerturbation f R K) =
        fun x : H ↦ if R x ∈ K then (f x : EReal) else ⊤ :=
    perturbationPrimalObjective_inequalityConstraintPerturbation f R K
  -- Convert shifted-objective minimality into primal perturbation minimality using feasibility and
  -- complementary slackness.
  have hprimal_argmin :
      xbar ∈ Argmin (perturbationPrimalObjective (inequalityConstraintPerturbation f R K)) := by
    rw [mem_argmin_iff, isMinOn_univ_iff] at hshift_argmin ⊢
    intro x
    by_cases hxK : R x ∈ K
    · have hshift_le : (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) ≤
          (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal) := hshift_argmin x
      have hx_primal :
          perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x =
            (f x : EReal) := by
        rw [hprimal_eq]
        simp [hxK]
      have hxbar_primal :
          perturbationPrimalObjective (inequalityConstraintPerturbation f R K) xbar =
            (f xbar : EReal) := by
        rw [hprimal_eq]
        simp [hRxbar]
      calc
        perturbationPrimalObjective (inequalityConstraintPerturbation f R K) xbar =
            (f xbar : EReal) + (⟪R xbar, vbar⟫_ℝ : EReal) := by
              rw [hxbar_primal, hinner_zero]
              simp
        _ ≤ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal) := hshift_le
        _ ≤ (f x : EReal) := by
              exact
                shiftedObjective_le_of_feasible_and_polar
                  f R K hxK hvbar
        _ = perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x := by
              exact hx_primal.symm
    · have hx_primal :
          perturbationPrimalObjective (inequalityConstraintPerturbation f R K) x = ⊤ := by
        simpa [hxK] using congrFun hprimal_eq x
      exact hx_primal.symm ▸ le_top
  exact ⟨hinner_zero, hprimal_argmin⟩

end SaddlePointCriterion

end ERealFunction
