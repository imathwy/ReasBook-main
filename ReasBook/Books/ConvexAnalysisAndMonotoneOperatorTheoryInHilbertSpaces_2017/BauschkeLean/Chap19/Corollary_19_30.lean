import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap08.Corollary_8_40
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Definition_19_24
import BauschkeLean.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProductSpace Pointwise

universe u v

namespace ERealFunction

open Set

section LocalConeConstraintOwner

variable {H : Type u} {G : Type v}

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary 19 30: the perturbation attached to the cone constraint `R x ∈ K`. -/
private abbrev coneConstraintPerturbation
    [AddZeroClass G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G) :
    H × G → Set.Ioi (⊥ : EReal) :=
  (f ∘ Prod.fst) + ((ι[K]) ∘ fun p : H × G ↦ R p.1 + p.2)

/-- Helper for Corollary 19 30: evaluating the cone perturbation gives the indicator formula
`f x + ι[K] (R x + y)`. -/
@[simp] private theorem coneConstraintPerturbation_apply
    [AddZeroClass G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (x : H)
    (y : G) :
    (coneConstraintPerturbation f R K (x, y) : EReal) =
      (f x : EReal) + (ι[K] (R x + y) : EReal) := by
  rfl

/-- Helper for Corollary 19 30: on the feasible branch `R x + y ∈ K`, the cone perturbation
reduces to `f x`. -/
@[simp] private theorem coneConstraintPerturbation_apply_of_mem
    [AddZeroClass G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    {x : H} {y : G} (hxy : R x + y ∈ K) :
    (coneConstraintPerturbation f R K (x, y) : EReal) = f x := by
  rw [coneConstraintPerturbation_apply]
  simp [hxy]

/-- Helper for Corollary 19 30: off the feasible branch `R x + y ∉ K`, the cone perturbation
has value `+∞`. -/
@[simp] private theorem coneConstraintPerturbation_apply_of_not_mem
    [AddZeroClass G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    {x : H} {y : G} (hxy : R x + y ∉ K) :
    (coneConstraintPerturbation f R K (x, y) : EReal) = ⊤ := by
  rw [coneConstraintPerturbation_apply]
  rw [show (ι[K] (R x + y) : EReal) = ⊤ by simp [indicator, hxy]]
  exact (EReal.add_top_iff_ne_bot).2 (ne_of_gt (f x).2)

/-- Helper for Corollary 19 30: the primal objective of the cone perturbation. -/
private theorem perturbationPrimalObjective_coneConstraintPerturbation
    [AddZeroClass G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G) :
    perturbationPrimalObjective (coneConstraintPerturbation f R K) =
      fun x : H ↦ if R x ∈ K then (f x : EReal) else ⊤ := by
  funext x
  by_cases hx : R x ∈ K
  · have hx0 : R x + 0 ∈ K := by
      exact Set.mem_of_eq_of_mem (add_zero (R x)) hx
    have hvalue :
        perturbationPrimalObjective (coneConstraintPerturbation f R K) x = (f x : EReal) := by
      simpa [perturbationPrimalObjective] using
        (coneConstraintPerturbation_apply_of_mem (f := f) (R := R) (K := K)
          (x := x) (y := 0) hx0)
    calc
      perturbationPrimalObjective (coneConstraintPerturbation f R K) x = (f x : EReal) := hvalue
      _ = if R x ∈ K then (f x : EReal) else ⊤ := by simp [hx]
  · have hx0 : R x + 0 ∉ K := by
      intro hmem
      exact hx (Set.mem_of_eq_of_mem (add_zero (R x)).symm hmem)
    have hvalue : perturbationPrimalObjective (coneConstraintPerturbation f R K) x = ⊤ := by
      simpa [perturbationPrimalObjective] using
        (coneConstraintPerturbation_apply_of_not_mem (f := f) (R := R) (K := K)
          (x := x) (y := 0) hx0)
    calc
      perturbationPrimalObjective (coneConstraintPerturbation f R K) x = ⊤ := hvalue
      _ = if R x ∈ K then (f x : EReal) else ⊤ := by simp [hx]

/-- Helper for Corollary 19 30: the regularity theorem for cone perturbations. -/
private theorem coneConstraintPerturbation_mem_gammaZero
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (_hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    coneConstraintPerturbation f R K ∈ Γ₀(H × G) := by
  -- Route correction: this local owner is just Proposition 19.25 (1) for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    inequalityConstraintPerturbation_mem_gammaZero
      (f := f) (R := R) (K := K)
      hf hK_nonempty hK_closed hK_convex _hK_cone hR_cont hR_convex hfeas

/-- Helper for Corollary 19 30: the dual objective formula for cone perturbations. -/
private theorem perturbationDualObjective_coneConstraintPerturbation
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    perturbationDualObjective (coneConstraintPerturbation f R K) =
      fun v : G ↦
        if v ∈ Kᵒ⊖ then
          ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
        else
          ⊤ := by
  -- Route correction: this local owner is just Proposition 19.25 (3) for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    perturbationDualObjective_inequalityConstraintPerturbation
      (f := f) (R := R) (K := K)
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas

/-- Helper for Corollary 19 30: the Lagrangian branch formula for cone perturbations. -/
private theorem lagrangian_coneConstraintPerturbation
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    (x : H) (v : G) :
    ℒ[coneConstraintPerturbation f R K] x v =
      if x ∈ effectiveDomain f then
        if v ∈ Kᵒ⊖ then
          (f x : EReal) + (⟪R x, v⟫_ℝ : EReal)
        else
          ⊥
      else
        ⊤ := by
  -- Route correction: this local owner is just Proposition 19.25 (4) for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    lagrangian_inequalityConstraintPerturbation
      (f := f) (R := R) (K := K)
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas x v

/-- Helper for Corollary 19 30: the saddle-point criterion for cone perturbations. -/
private theorem isSaddlePointOn_lagrangian_coneConstraintPerturbation_iff
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    (xbar : H) (vbar : G) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
      (ℒ[coneConstraintPerturbation f R K]) xbar vbar ↔
        xbar ∈ effectiveDomain f ∩ {x | R x ∈ K} ∧
          vbar ∈ Kᵒ⊖ ∧
          (f xbar : EReal) =
            sInf (Set.range fun x : H ↦
              (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  -- Route correction: this local owner is just Proposition 19.25 (5) for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      (f := f) (R := R) (K := K)
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas xbar vbar

/-- Helper for Corollary 19 30: the saddle-point criterion implies the inner-form argmin
condition. -/
private theorem mem_argmin_of_isSaddlePointOn_lagrangian_coneConstraintPerturbation
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[coneConstraintPerturbation f R K]) xbar vbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  -- Route correction: this local owner is just Remark 19.26 for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
      (f := f) (R := R) (K := K)
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle

/-- Helper for Corollary 19 30: under the regularity assumptions, a saddle point has vanishing
pairing and its primal component solves the primal perturbation problem. -/
private theorem
    saddlePoint_inner_eq_zero_and_mem_argmin_primalObjective_coneConstraintPerturbation
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G)
    (K : Set G)
    (_hf : f ∈ Γ₀(H))
    (_hK_nonempty : K.Nonempty) (_hK_closed : IsClosed K) (_hK_convex : Convex ℝ K)
    (_hK_cone : IsCone K)
    (_hR_cont : Continuous R) (_hR_convex : R.IsConvexWithRespectTo ℝ K)
    (_hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[coneConstraintPerturbation f R K]) xbar vbar) :
    ⟪R xbar, vbar⟫_ℝ = 0 ∧
      xbar ∈ Argmin (perturbationPrimalObjective (coneConstraintPerturbation f R K)) := by
  -- Route correction: this local owner is just Proposition 19.25 (6) for the abbreviation
  -- `coneConstraintPerturbation`.
  simpa [coneConstraintPerturbation, inequalityConstraintPerturbation] using
    inner_eq_zero_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
      (f := f) (R := R) (K := K)
      _hf _hK_nonempty _hK_closed _hK_convex _hK_cone _hR_cont _hR_convex _hfeas hsaddle

end LocalConeConstraintOwner

section MixedConstraintCone

variable {m p : ℕ}

/- Source-facing convention: `m` is the total number of constraints and `p` is the size of the
inequality block, so the equality block is indexed by `Fin (m - p)`. -/
local notation "ConstraintSpace" => EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))

attribute [local instance] Classical.propDecidable

/-- The mixed constraint cone `ℝ_-^p × {0}` in the split-coordinate model used in
Corollary 19.30. -/
def mixedConstraintCone : Set ConstraintSpace :=
  {η | (∀ i : Fin p, η (Sum.inl i) ≤ 0) ∧ ∀ j : Fin (m - p), η (Sum.inr j) = 0}

/-- Membership in the mixed cone is exactly blockwise nonpositivity on the inequality coordinates
and vanishing on the equality coordinates. -/
@[simp] theorem mem_mixedConstraintCone_iff {η : ConstraintSpace} :
    η ∈ mixedConstraintCone ↔
      (∀ i : Fin p, η (Sum.inl i) ≤ 0) ∧ ∀ j : Fin (m - p), η (Sum.inr j) = 0 :=
  Iff.rfl

end MixedConstraintCone

section MixedConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m p : ℕ}

/- Source/core/bridge triage:
- `source-facing`: Corollary 19.30 specializes the Chapter 19 perturbation formalism to mixed
  inequality/equality constraints.
- `core/canonical`: the owner abstraction remains `inequalityConstraintPerturbation`.
- `bridge/view`: this file keeps only the mixed constraint map, the mixed cone, and the
  specialized perturbation owner `mixedConstraintPerturbation`.
-/

local notation "EqualitySpace" => EuclideanSpace ℝ (Fin (m - p))
local notation "ConstraintSpace" => EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/-- Helper for Corollary 19 30: the continuous linear map recording the equality-constraint
coordinates `⟪x, u_j⟫`. -/
def mixedEqualityCoordinateMap (u : Fin (m - p) → H) : H →L[ℝ] EqualitySpace :=
  ((EuclideanSpace.equiv (Fin (m - p)) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (u i))

/-- Helper for Corollary 19 30: the `j`th coordinate of the equality map is `⟪x, u_j⟫`. -/
@[simp] theorem mixedEqualityCoordinateMap_apply
    (u : Fin (m - p) → H) (x : H) (j : Fin (m - p)) :
    mixedEqualityCoordinateMap u x j = ⟪x, u j⟫_ℝ := by
  simp [mixedEqualityCoordinateMap, real_inner_comm]

/-- The canonical constraint map whose first block records the inequality functions `g_i` and
whose second block records the affine residuals `equalityCoordinateMap u x - ρ`. -/
def mixedConstraintMap
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : EqualitySpace) :
    H → ConstraintSpace :=
  fun x ↦
    (EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ).symm
      (Sum.elim (fun i ↦ g i x) (mixedEqualityCoordinateMap u x - ρ).ofLp)

@[simp] theorem mixedConstraintMap_apply_inl
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : EqualitySpace)
    (x : H) (i : Fin p) :
    mixedConstraintMap g u ρ x (Sum.inl i) = g i x := by
  simp [mixedConstraintMap]

@[simp] theorem mixedConstraintMap_apply_inr
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : EqualitySpace)
    (x : H) (j : Fin (m - p)) :
    mixedConstraintMap g u ρ x (Sum.inr j) = ⟪x, u j⟫_ℝ - ρ j := by
  simp [mixedConstraintMap, mixedEqualityCoordinateMap_apply]

/-- The shifted constraint vector lies in the mixed cone exactly when the mixed constraints hold
at `(x, η)`. -/
@[simp] theorem mixedConstraintMap_add_mem_mixedConstraintCone_iff
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : EqualitySpace)
    (x : H) (η : ConstraintSpace) :
    mixedConstraintMap g u ρ x + η ∈ mixedConstraintCone ↔
      (∀ i : Fin p, g i x ≤ -η (Sum.inl i)) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = -η (Sum.inr j) + ρ j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi : g i x + η (Sum.inl i) ≤ 0 := by
        simpa [mixedConstraintMap] using h.1 i
      linarith
    · intro j
      have hj : (⟪x, u j⟫_ℝ - ρ j) + η (Sum.inr j) = 0 := by
        simpa [mixedConstraintMap, mixedEqualityCoordinateMap_apply] using h.2 j
      linarith
  · rintro ⟨hineq, heq⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hi : g i x + η (Sum.inl i) ≤ 0 := by
        linarith [hineq i]
      simpa [mixedConstraintMap] using hi
    · intro j
      have hj : (⟪x, u j⟫_ℝ - ρ j) + η (Sum.inr j) = 0 := by
        linarith [heq j]
      simpa [mixedConstraintMap, mixedEqualityCoordinateMap_apply] using hj

/-- The unshifted mixed constraint vector lies in the mixed cone exactly when `x` satisfies all
inequality and equality constraints. -/
@[simp] theorem mixedConstraintMap_mem_mixedConstraintCone_iff
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : EqualitySpace) (x : H) :
    mixedConstraintMap g u ρ x ∈ mixedConstraintCone ↔
      (∀ i : Fin p, g i x ≤ 0) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j) := by
  simpa using (mixedConstraintMap_add_mem_mixedConstraintCone_iff g u ρ x 0)

variable (f : H → Set.Ioi (⊥ : EReal))
variable (g : Fin p → H → ℝ)
variable (u : Fin (m - p) → H)
variable (ρ : EqualitySpace)

/-- The feasibility condition for the mixed perturbation. -/
theorem mixedConstraintFeasible_iff :
    (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty ↔
      ∃ x : H,
        x ∈ effectiveDomain f ∧
          (∀ i : Fin p, g i x ≤ 0) ∧
          ∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j := by
  constructor
  · rintro ⟨η, hηK, x, hx, rfl⟩
    exact ⟨x, hx, (mixedConstraintMap_mem_mixedConstraintCone_iff g u ρ x).1 hηK⟩
  · rintro ⟨x, hx, hineq, heq⟩
    exact ⟨mixedConstraintMap g u ρ x,
      (mixedConstraintMap_mem_mixedConstraintCone_iff g u ρ x).2 ⟨hineq, heq⟩,
      x, hx, rfl⟩

/-- The perturbation function `F` from Corollary 19.30. -/
abbrev mixedConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H)
    (ρ : EqualitySpace) :
    H × ConstraintSpace → Set.Ioi (⊥ : EReal) :=
  coneConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone

/-- Evaluating the mixed-constraint perturbation on a feasible fiber returns `f x`. -/
@[simp] theorem mixedConstraintPerturbation_apply_of_feasible
    {x : H} {η : ConstraintSpace}
    (hfeas :
      (∀ i : Fin p, g i x ≤ -η (Sum.inl i)) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = -η (Sum.inr j) + ρ j)) :
    (mixedConstraintPerturbation f g u ρ (x, η) : EReal) = f x := by
  exact coneConstraintPerturbation_apply_of_mem
    (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
    ((mixedConstraintMap_add_mem_mixedConstraintCone_iff g u ρ x η).2 hfeas)

/-- Helper for Corollary 19 30: the mixed cone contains the origin. -/
lemma mixedConstraintCone_nonempty :
    (mixedConstraintCone : Set ConstraintSpace).Nonempty := by
  refine ⟨0, ?_⟩
  simp [mixedConstraintCone]

/-- Helper for Corollary 19 30: the mixed cone is closed. -/
lemma mixedConstraintCone_isClosed :
    IsClosed (mixedConstraintCone : Set ConstraintSpace) := by
  have hineq :
      IsClosed {η : ConstraintSpace | ∀ i : Fin p, η (Sum.inl i) ≤ 0} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter fun i : Fin p =>
        isClosed_le (EuclideanSpace.proj (Sum.inl i)).continuous continuous_const
  have heq :
      IsClosed {η : ConstraintSpace | ∀ j : Fin (m - p), η (Sum.inr j) = 0} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter fun j : Fin (m - p) =>
        isClosed_eq (EuclideanSpace.proj (Sum.inr j)).continuous continuous_const
  simpa [mixedConstraintCone] using hineq.inter heq

/-- Helper for Corollary 19 30: the mixed cone is convex. -/
lemma mixedConstraintCone_convex :
    Convex ℝ (mixedConstraintCone : Set ConstraintSpace) := by
  refine (convex_iff_forall_pos).2 ?_
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    have h1 : a * η₁ (Sum.inl i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha.le (hη₁.1 i)
    have h2 : b * η₂ (Sum.inl i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb.le (hη₂.1 i)
    simpa [smul_eq_mul] using add_nonpos h1 h2
  · intro j
    simp [hη₁.2 j, hη₂.2 j, smul_eq_mul]

/-- Helper for Corollary 19 30: the mixed cone is a cone. -/
lemma mixedConstraintCone_isCone :
    IsCone (mixedConstraintCone : Set ConstraintSpace) := by
  ext η
  constructor
  · intro hη
    refine ⟨1, by simp, η, hη, ?_⟩
    simp
  · rintro ⟨a, ha, ξ, hξ, rfl⟩
    refine ⟨?_, ?_⟩
    · intro i
      simpa [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos ha.le (hξ.1 i)
    · intro j
      simp [smul_eq_mul, hξ.2 j]

/-- Helper for Corollary 19 30: each inequality coordinate is convex on `univ`. -/
lemma mixedConstraintCoordinate_convexOn_univ
    (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H)) (i : Fin p) :
    _root_.ConvexOn ℝ Set.univ (g i) := by
  have hconv : ERealFunction.ConvexOn (g i).toEReal (effectiveDomain (g i).toEReal) :=
    (mem_gammaZero_iff.mp (hg i)).2
  simpa [Function.effectiveDomain_toEReal] using hconv.toReal_convexOn_effectiveDomain

/-- Helper for Corollary 19 30: each inequality coordinate is continuous. -/
lemma mixedConstraintCoordinate_continuous
    (g : Fin p → H → ℝ)
    (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H)) (i : Fin p) :
    Continuous (g i) := by
  -- The source-faithful starting point is the global convexity inherited from `Γ₀(H)`.
  have hconv : _root_.ConvexOn ℝ Set.univ (g i) :=
    mixedConstraintCoordinate_convexOn_univ (g := g) hg i
  -- Membership in `Γ₀(H)` also packages lower semicontinuity of the bundled real map.
  have hlsc : LowerSemicontinuous (fun x : H ↦ (((g i).toEReal x : EReal))) :=
    (mem_gammaZero_iff.mp (hg i)).1
  -- TODO: close the continuity bridge with a source-faithful theorem matching this header.
  -- `continuous_of_convexOn_univ` needs `[FiniteDimensional ℝ H]`, while the Chapter 8/16
  -- continuity route from `Γ₀(H)` needs `[CompleteSpace H]`; neither assumption is available
  -- here, so the remaining gap is exactly this header-level regularity bridge.
  sorry

/-- Helper for Corollary 19 30: the mixed constraint map is continuous. -/
lemma mixedConstraintMap_continuous_of_mem_gammaZero
    (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H)
    (ρ : EqualitySpace)
    (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H)) :
    Continuous (mixedConstraintMap g u ρ) := by
  have hcoord :
      Continuous
        (fun x : H ↦
          Sum.elim (fun i ↦ g i x) (mixedEqualityCoordinateMap u x - ρ).ofLp) := by
    refine continuous_pi ?_
    intro ij
    cases ij with
    | inl i =>
        simpa using mixedConstraintCoordinate_continuous (g := g) hg i
    | inr j =>
        simpa [mixedEqualityCoordinateMap_apply] using
          ((continuous_id.inner continuous_const).sub continuous_const)
  simpa [mixedConstraintMap] using
    ((EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ).symm.continuous.comp hcoord)

/-- Helper for Corollary 19 30: the mixed constraint map is convex with respect to the mixed
cone. -/
lemma mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
    (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H)
    (ρ : EqualitySpace)
    (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H)) :
    (mixedConstraintMap g u ρ).IsConvexWithRespectTo ℝ mixedConstraintCone := by
  intro x y α hα
  refine ⟨?_, ?_⟩
  · intro i
    have hconv_i : _root_.ConvexOn ℝ Set.univ (g i) :=
      mixedConstraintCoordinate_convexOn_univ (g := g) hg i
    have hineq :
        g i (α • x + (1 - α) • y) ≤ α * g i x + (1 - α) * g i y := by
      exact hconv_i.2 (by simp) (by simp) hα.1.le (sub_nonneg.mpr hα.2.le) (by ring)
    have hdef :
        g i (α • x + (1 - α) • y) - α * g i x - (1 - α) * g i y ≤ 0 := by
      linarith [hineq]
    simpa [mixedConstraintMap_apply_inl, sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hdef
  · intro j
    have hdef :
        mixedConstraintMap g u ρ (α • x + (1 - α) • y) (Sum.inr j) -
            α * mixedConstraintMap g u ρ x (Sum.inr j) -
            (1 - α) * mixedConstraintMap g u ρ y (Sum.inr j) =
          0 := by
      simp [mixedConstraintMap_apply_inr, inner_add_left, inner_smul_left]
      ring
    simpa [sub_eq_add_neg, smul_eq_mul] using hdef

/-- Helper for Corollary 19 30: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul_mixed (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Pairing the mixed constraint vector with a multiplier gives the expected blockwise affine
formula. -/
theorem inner_mixedConstraintMap
    (x : H) (ν : ConstraintSpace) :
    ⟪mixedConstraintMap g u ρ x, ν⟫_ℝ =
      (∑ i : Fin p, ν (Sum.inl i) * g i x) +
        ∑ j : Fin (m - p), ν (Sum.inr j) * (⟪x, u j⟫_ℝ - ρ j) := by
  let νeq : EqualitySpace :=
    (EuclideanSpace.equiv (Fin (m - p)) ℝ).symm (fun j ↦ ν (Sum.inr j))
  have hsplit :
      ⟪mixedConstraintMap g u ρ x, ν⟫_ℝ =
        (∑ i : Fin p, ν (Sum.inl i) * g i x) + ⟪mixedEqualityCoordinateMap u x - ρ, νeq⟫_ℝ := by
    rw [mixedConstraintMap, PiLp.inner_apply, Fintype.sum_sum_type, PiLp.inner_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl ?_
      intro i hi
      simp [real_inner_eq_mul_mixed, mul_comm]
    · refine Finset.sum_congr rfl ?_
      intro j hj
      have hνeq : νeq j = ν (Sum.inr j) := by
        simp [νeq]
      change
        ⟪mixedConstraintMap g u ρ x (Sum.inr j), ν (Sum.inr j)⟫_ℝ =
          ⟪(mixedEqualityCoordinateMap u x - ρ) j, ν (Sum.inr j)⟫_ℝ
      rw [mixedConstraintMap_apply_inr]
      simp [mixedEqualityCoordinateMap_apply]
  have heq :
      ⟪mixedEqualityCoordinateMap u x - ρ, νeq⟫_ℝ =
        ∑ j : Fin (m - p), νeq j * (⟪x, u j⟫_ℝ - ρ j) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hcoord : (mixedEqualityCoordinateMap u x - ρ) j = ⟪x, u j⟫_ℝ - ρ j := by
      change mixedEqualityCoordinateMap u x j - ρ j = ⟪x, u j⟫_ℝ - ρ j
      simp [mixedEqualityCoordinateMap_apply]
    rw [hcoord]
    simp [real_inner_eq_mul_mixed, mul_comm]
  calc
    ⟪mixedConstraintMap g u ρ x, ν⟫_ℝ =
        (∑ i : Fin p, ν (Sum.inl i) * g i x) + ⟪mixedEqualityCoordinateMap u x - ρ, νeq⟫_ℝ := hsplit
    _ =
        (∑ i : Fin p, ν (Sum.inl i) * g i x) +
          ∑ j : Fin (m - p), νeq j * (⟪x, u j⟫_ℝ - ρ j) := by rw [heq]
    _ =
        (∑ i : Fin p, ν (Sum.inl i) * g i x) +
          ∑ j : Fin (m - p), ν (Sum.inr j) * (⟪x, u j⟫_ℝ - ρ j) := by
            simp [νeq]

/-- Helper for Corollary 19 30: the polar cone of `ℝ_-^p × {0}` consists exactly of multipliers
whose inequality coordinates are nonnegative. -/
lemma mem_polarCone_mixedConstraintCone_iff
    {ν : ConstraintSpace} :
    ν ∈ (mixedConstraintCone : Set ConstraintSpace)ᵒ⊖ ↔
      ∀ i : Fin p, 0 ≤ ν (Sum.inl i) := by
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  constructor
  · intro h i
    let η : ConstraintSpace :=
      (EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ).symm (Pi.single (Sum.inl i) (-1 : ℝ))
    have hη : η ∈ mixedConstraintCone := by
      refine ⟨?_, ?_⟩
      · intro k
        by_cases hk : k = i
        · subst hk
          simp [η]
        · simp [η, hk]
      · intro j
        simp [η]
    have htest : ⟪η, ν⟫_ℝ ≤ 0 := h η hη
    have : -ν (Sum.inl i) ≤ 0 := by
      simpa [η, PiLp.inner_apply, Fintype.sum_sum_type, real_inner_eq_mul_mixed] using htest
    linarith
  · intro hν η hη
    rw [PiLp.inner_apply, Fintype.sum_sum_type]
    refine add_nonpos ?_ ?_
    · refine Finset.sum_nonpos fun i _ ↦ ?_
      simpa [real_inner_eq_mul_mixed] using
        mul_nonpos_of_nonpos_of_nonneg (hη.1 i) (hν i)
    · have hsum0 :
          ∑ j : Fin (m - p), ⟪η (Sum.inr j), ν (Sum.inr j)⟫_ℝ = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        simp [real_inner_eq_mul_mixed, hη.2 j]
      simpa [hsum0]

/-- Helper for Corollary 19 30: negating the equality block turns
`⟪x, u_j⟫ - ρ_j` into `ρ_j - ⟪x, u_j⟫`. -/
lemma mixedConstraint_dual_equality_block_neg
    (x : H) (ν : ConstraintSpace) :
    -(∑ j : Fin (m - p), ν (Sum.inr j) * (⟪x, u j⟫_ℝ - ρ j)) =
      ∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  ring

/-- Helper for Corollary 19 30: the negated mixed inner-product term matches the displayed dual
integrand. -/
lemma neg_inner_mixedConstraintMap_dual_rewrite
    (x : H) (ν : ConstraintSpace) :
    -((⟪mixedConstraintMap g u ρ x, ν⟫_ℝ : ℝ) : EReal) =
      -((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal)) +
        ((((∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ)) : ℝ) : EReal)) := by
  have hreal :
      -(⟪mixedConstraintMap g u ρ x, ν⟫_ℝ : ℝ) =
        -((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) +
          ∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ) := by
    rw [inner_mixedConstraintMap]
    rw [neg_add]
    congr 1
    exact mixedConstraint_dual_equality_block_neg (u := u) (ρ := ρ) x ν
  simpa using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal

/-- Helper for Corollary 19 30: the owner dual supremum rewrites to the displayed mixed dual
formula. -/
lemma mixedConstraint_dual_sup_rewrite
    (ν : ConstraintSpace) :
    (⨆ x : H, -((⟪mixedConstraintMap g u ρ x, ν⟫_ℝ : ℝ) : EReal) - (f x : EReal)) =
      ⨆ x : H,
        -((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal)) +
          ((((∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ)) : ℝ) : EReal)) -
          (f x : EReal) := by
  refine iSup_congr fun x ↦ by
    simpa [sub_eq_add_neg, add_assoc] using
      congrArg (fun t : EReal ↦ t - (f x : EReal))
        (neg_inner_mixedConstraintMap_dual_rewrite (g := g) (u := u) (ρ := ρ) x ν)

/-- Corollary 19 30 (1): the perturbation function belongs to `Γ₀(H × ℝ^m)` under the stated
assumptions. -/
theorem mixedConstraintPerturbation_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (hfeas :
      ∃ x : H,
        x ∈ effectiveDomain f ∧
          (∀ i : Fin p, g i x ≤ 0) ∧
          ∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j) :
    mixedConstraintPerturbation f g u ρ ∈
      Γ₀(H × ConstraintSpace) := by
  have hfeas' :
      (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty :=
    (mixedConstraintFeasible_iff (f := f) (g := g) (u := u) (ρ := ρ)).2 hfeas
  simpa [mixedConstraintPerturbation] using
    coneConstraintPerturbation_mem_gammaZero
      (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
      hf mixedConstraintCone_nonempty mixedConstraintCone_isClosed
      mixedConstraintCone_convex mixedConstraintCone_isCone
      (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
      (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
        (g := g) (u := u) (ρ := ρ) hg)
      hfeas'

/-- Corollary 19.30 (2): the primal objective of the mixed perturbation. -/
theorem perturbationPrimalObjective_mixedConstraintPerturbation :
    perturbationPrimalObjective (mixedConstraintPerturbation f g u ρ) =
      fun x : H ↦
        if
          (∀ i : Fin p, g i x ≤ 0) ∧
            (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j) then
          (f x : EReal)
        else
          ⊤ := by
  funext x
  simpa [mixedConstraintPerturbation, mixedConstraintMap_mem_mixedConstraintCone_iff] using
    congrFun
      (perturbationPrimalObjective_coneConstraintPerturbation
        (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)) x

variable (hf : f ∈ Γ₀(H))
variable (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
variable
    (hfeas :
      ∃ x : H,
        x ∈ effectiveDomain f ∧
          (∀ i : Fin p, g i x ≤ 0) ∧
          ∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j)

/-- Corollary 19.30 (3): the dual objective is the explicit supremum formula. -/
theorem perturbationDualObjective_mixedConstraintPerturbation :
    perturbationDualObjective (mixedConstraintPerturbation f g u ρ) =
      fun ν : ConstraintSpace ↦
        if ∀ i : Fin p, 0 ≤ ν (Sum.inl i) then
          ⨆ x : H,
            -((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal)) +
              ((((∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ)) : ℝ) : EReal)) -
              (f x : EReal)
        else
          ⊤ := by
  -- TODO: the source-faithful specialization of Proposition 19.25 (3) needs the standing
  -- corollary assumptions `hf`, `hg`, and `hfeas`, but this local theorem statement omits them.
  -- Re-plan by restoring those assumptions to the theorem type, or by refactoring the file so the
  -- corollary assumptions are section parameters for clauses (3) and onward.
  sorry

/-- Corollary 19.30 (4): the Lagrangian of the mixed perturbation. -/
theorem lagrangian_mixedConstraintPerturbation
    (x : H) (ν : ConstraintSpace) :
    ℒ[mixedConstraintPerturbation f g u ρ] x ν =
      if hx : x ∈ effectiveDomain f then
        if ∀ i : Fin p, 0 ≤ ν (Sum.inl i) then
          (f x : EReal) +
            ((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal) +
              (((∑ j : Fin (m - p), ν (Sum.inr j) * (⟪x, u j⟫_ℝ - ρ j)) : ℝ) : EReal))
        else
          ⊥
      else
        ⊤ := by
  -- TODO: the source-faithful specialization of Proposition 19.25 (4) needs the standing
  -- corollary assumptions `hf`, `hg`, and `hfeas`, but this local theorem statement omits them.
  -- Re-plan by restoring those assumptions to the theorem type, or by refactoring the file so the
  -- corollary assumptions are section parameters for clauses (3) and onward.
  sorry

variable [CompleteSpace H]

/-- Helper for Corollary 19 30: the owner affine objective rewrites to the displayed mixed affine
formula up to an additive constant. -/
lemma mem_argmin_mixed_affine_formula_of_mem_argmin_inner_form
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H)
    (ρ : EqualitySpace)
    {xbar : H} {νbar : ConstraintSpace}
    (hxbar :
      xbar ∈ Argmin
        (fun x : H ↦ (f x : EReal) + (⟪mixedConstraintMap g u ρ x, νbar⟫_ℝ : EReal))) :
    xbar ∈ Argmin
      (fun x : H ↦
        (f x : EReal) +
          (((∑ i : Fin p, νbar (Sum.inl i) * g i x) : ℝ) : EReal) +
            (((∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪x, u j⟫_ℝ) : ℝ) : EReal)) := by
  let c : EReal := (((∑ j : Fin (m - p), νbar (Sum.inr j) * ρ j) : ℝ) : EReal)
  let ψ : H → EReal :=
    fun z ↦ (f z : EReal) + (⟪mixedConstraintMap g u ρ z, νbar⟫_ℝ : EReal)
  let φ : H → EReal :=
    fun z ↦
      (f z : EReal) +
        (((∑ i : Fin p, νbar (Sum.inl i) * g i z) : ℝ) : EReal) +
          (((∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪z, u j⟫_ℝ) : ℝ) : EReal)
  have hshift (z : H) : c + ψ z = φ z := by
    -- Adding the constant equality-block offset converts the owner inner form to the displayed
    -- affine objective.
    have hpair :
        (((∑ j : Fin (m - p), νbar (Sum.inr j) * ρ j) : ℝ) : EReal) +
            ((⟪mixedConstraintMap g u ρ z, νbar⟫_ℝ : ℝ) : EReal) =
          (((∑ i : Fin p, νbar (Sum.inl i) * g i z) : ℝ) : EReal) +
            (((∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪z, u j⟫_ℝ) : ℝ) : EReal) := by
      have hpair_real :
          (∑ j : Fin (m - p), νbar (Sum.inr j) * ρ j) +
              ⟪mixedConstraintMap g u ρ z, νbar⟫_ℝ =
            (∑ i : Fin p, νbar (Sum.inl i) * g i z) +
              ∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪z, u j⟫_ℝ := by
        rw [inner_mixedConstraintMap (g := g) (u := u) (ρ := ρ)]
        ring
      exact_mod_cast hpair_real
    calc
      c + ψ z =
          (((∑ j : Fin (m - p), νbar (Sum.inr j) * ρ j) : ℝ) : EReal) +
            ((f z : EReal) + (⟪mixedConstraintMap g u ρ z, νbar⟫_ℝ : EReal)) := by
              simp [c, ψ]
      _ = (f z : EReal) +
            ((((∑ j : Fin (m - p), νbar (Sum.inr j) * ρ j) : ℝ) : EReal) +
              (⟪mixedConstraintMap g u ρ z, νbar⟫_ℝ : EReal)) := by
              simpa [c, ψ, add_assoc, add_left_comm, add_comm]
      _ = (f z : EReal) +
            ((((∑ i : Fin p, νbar (Sum.inl i) * g i z) : ℝ) : EReal) +
              (((∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪z, u j⟫_ℝ) : ℝ) : EReal)) := by
              rw [hpair]
      _ = φ z := by
            simp [φ]
            ac_rfl
  rw [mem_argmin_iff, isMinOn_univ_iff] at hxbar ⊢
  intro z
  have hle : c + ψ xbar ≤ c + ψ z := by
    simpa [c, ψ, add_assoc, add_left_comm, add_comm] using add_le_add_left (hxbar z) c
  rw [show c + ψ xbar = φ xbar by simpa [ψ] using hshift xbar,
    show c + ψ z = φ z by simpa [ψ] using hshift z] at hle
  simpa [φ] using hle

include hf hg hfeas

/-- Corollary 19.30 (5): every saddle point yields a solution of the primal problem. -/
theorem mem_argmin_perturbationPrimalObjective_of_mixedConstraintPerturbation_isSaddlePoint
    (ρ : EqualitySpace)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (univ : Set H)
        (univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ Argmin (perturbationPrimalObjective (mixedConstraintPerturbation f g u ρ)) := by
  -- Reuse Proposition 19.25 (6) through the mixed owner specialization.
  have hfeas' :
      (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty :=
    (mixedConstraintFeasible_iff (f := f) (g := g) (u := u) (ρ := ρ)).2 hfeas
  have hsaddle' :
      IsSaddlePointOn (univ : Set H) (univ : Set ConstraintSpace)
        (ℒ[coneConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone])
        xbar νbar := by
    simpa [mixedConstraintPerturbation] using hsaddle
  exact
    (saddlePoint_inner_eq_zero_and_mem_argmin_primalObjective_coneConstraintPerturbation
      (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
      hf mixedConstraintCone_nonempty mixedConstraintCone_isClosed
      mixedConstraintCone_convex mixedConstraintCone_isCone
      (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
      (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
        (g := g) (u := u) (ρ := ρ) hg)
      hfeas' hsaddle').2

/-- Corollary 19.30 (6): every saddle point makes its primal component solve the unconstrained
mixed affine minimization problem. -/
theorem mem_argmin_mixedConstraintAffineFormula_of_mixedConstraintPerturbation_isSaddlePoint
    (ρ : EqualitySpace)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (univ : Set H)
        (univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ Argmin
      (fun x : H ↦
        (f x : EReal) +
          (((∑ i : Fin p, νbar (Sum.inl i) * g i x) : ℝ) : EReal) +
            (((∑ j : Fin (m - p), νbar (Sum.inr j) * ⟪x, u j⟫_ℝ) : ℝ) : EReal)) := by
  -- First recover the owner inner-form minimizer, then rewrite it to the mixed affine formula.
  have hfeas' :
      (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty :=
    (mixedConstraintFeasible_iff (f := f) (g := g) (u := u) (ρ := ρ)).2 hfeas
  have hsaddle' :
      IsSaddlePointOn (univ : Set H) (univ : Set ConstraintSpace)
        (ℒ[coneConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone])
        xbar νbar := by
    simpa [mixedConstraintPerturbation] using hsaddle
  exact
    mem_argmin_mixed_affine_formula_of_mem_argmin_inner_form
      (f := f) (g := g) (u := u) (ρ := ρ)
      (mem_argmin_of_isSaddlePointOn_lagrangian_coneConstraintPerturbation
        (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
        hf
        mixedConstraintCone_nonempty mixedConstraintCone_isClosed
        mixedConstraintCone_convex mixedConstraintCone_isCone
        (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
        (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
          (g := g) (u := u) (ρ := ρ) hg)
        hfeas' hsaddle')

/-- Corollary 19.30 (7): at a saddle point, the primal component belongs to `dom f` and
satisfies every inequality constraint. -/
theorem effectiveDomain_and_inequalities_of_mixedConstraintPerturbation_isSaddlePoint
    (ρ : EqualitySpace)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (univ : Set H)
        (univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ effectiveDomain f ∧
      (∀ i : Fin p, g i xbar ≤ 0) := by
  -- Unpack the mixed saddle-point criterion and then rewrite mixed-cone feasibility.
  have hfeas' :
      (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty :=
    (mixedConstraintFeasible_iff (f := f) (g := g) (u := u) (ρ := ρ)).2 hfeas
  have hsaddle' :
      IsSaddlePointOn (univ : Set H) (univ : Set ConstraintSpace)
        (ℒ[coneConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone])
        xbar νbar := by
    simpa [mixedConstraintPerturbation] using hsaddle
  rcases
      (isSaddlePointOn_lagrangian_coneConstraintPerturbation_iff
        (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
        hf
        mixedConstraintCone_nonempty mixedConstraintCone_isClosed
        mixedConstraintCone_convex mixedConstraintCone_isCone
        (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
        (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
          (g := g) (u := u) (ρ := ρ) hg)
        hfeas' xbar νbar).mp hsaddle' with
    ⟨hxbarK, _, _⟩
  exact
    ⟨hxbarK.1,
      (mixedConstraintMap_mem_mixedConstraintCone_iff (g := g) (u := u) (ρ := ρ) xbar).1
        hxbarK.2 |>.1⟩

include hf hg hfeas

/-- Corollary 19.30 (8): at a saddle point, every inequality multiplier is nonnegative and
satisfies complementary slackness. -/
theorem complementarySlackness_of_mixedConstraintPerturbation_isSaddlePoint
    (ρ : EqualitySpace)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (univ : Set H)
        (univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    ∀ i : Fin p, 0 ≤ νbar (Sum.inl i) ∧ νbar (Sum.inl i) * g i xbar = 0 := by
  have hfeas' :
      (mixedConstraintCone ∩ mixedConstraintMap g u ρ '' effectiveDomain f).Nonempty :=
    (mixedConstraintFeasible_iff (f := f) (g := g) (u := u) (ρ := ρ)).2 hfeas
  have hsaddle' :
      IsSaddlePointOn (univ : Set H) (univ : Set ConstraintSpace)
        (ℒ[coneConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone])
        xbar νbar := by
    simpa [mixedConstraintPerturbation] using hsaddle
  rcases
      (isSaddlePointOn_lagrangian_coneConstraintPerturbation_iff
        (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
        hf
        mixedConstraintCone_nonempty mixedConstraintCone_isClosed
        mixedConstraintCone_convex mixedConstraintCone_isCone
        (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
        (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
          (g := g) (u := u) (ρ := ρ) hg)
        hfeas' xbar νbar).mp hsaddle' with
    ⟨hxbarK, hpolar, _⟩
  have hinner0 :
      ⟪mixedConstraintMap g u ρ xbar, νbar⟫_ℝ = 0 :=
    (saddlePoint_inner_eq_zero_and_mem_argmin_primalObjective_coneConstraintPerturbation
      (f := f) (R := mixedConstraintMap g u ρ) (K := mixedConstraintCone)
      hf mixedConstraintCone_nonempty mixedConstraintCone_isClosed
      mixedConstraintCone_convex mixedConstraintCone_isCone
      (mixedConstraintMap_continuous_of_mem_gammaZero (g := g) (u := u) (ρ := ρ) hg)
      (mixedConstraintMap_isConvexWithRespectTo_mixedConstraintCone
        (g := g) (u := u) (ρ := ρ) hg)
      hfeas' hsaddle').1
  rcases
      (mixedConstraintMap_mem_mixedConstraintCone_iff (g := g) (u := u) (ρ := ρ) xbar).1
        hxbarK.2 with
    ⟨hineq, heq⟩
  have hsum_eq_block :
      ∑ j : Fin (m - p), νbar (Sum.inr j) * (⟪xbar, u j⟫_ℝ - ρ j) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [heq j]
  have hsum_ineq_block :
      ∑ i : Fin p, νbar (Sum.inl i) * g i xbar = 0 := by
    calc
      ∑ i : Fin p, νbar (Sum.inl i) * g i xbar
          = (∑ i : Fin p, νbar (Sum.inl i) * g i xbar) +
              ∑ j : Fin (m - p), νbar (Sum.inr j) * (⟪xbar, u j⟫_ℝ - ρ j) := by
                rw [hsum_eq_block, add_zero]
      _ = ⟪mixedConstraintMap g u ρ xbar, νbar⟫_ℝ := by
            symm
            exact inner_mixedConstraintMap (g := g) (u := u) (ρ := ρ) xbar νbar
      _ = 0 := hinner0
  have hnonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin p)), 0 ≤ -(νbar (Sum.inl i) * g i xbar) := by
    intro i hi
    have hνi : 0 ≤ νbar (Sum.inl i) :=
      (mem_polarCone_mixedConstraintCone_iff (m := m) (p := p) (ν := νbar)).1 hpolar i
    have hgi : g i xbar ≤ 0 := hineq i
    nlinarith
  have hsumneg :
      ∑ i : Fin p, -(νbar (Sum.inl i) * g i xbar) = 0 := by
    simpa using congrArg (fun t : ℝ ↦ -t) hsum_ineq_block
  have hzero_each :
      ∀ i : Fin p, -(νbar (Sum.inl i) * g i xbar) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsumneg i (Finset.mem_univ i)
  intro i
  constructor
  · exact (mem_polarCone_mixedConstraintCone_iff (m := m) (p := p) (ν := νbar)).1 hpolar i
  · linarith [hzero_each i]

omit hf hg hfeas

end MixedConstraints

end ERealFunction
