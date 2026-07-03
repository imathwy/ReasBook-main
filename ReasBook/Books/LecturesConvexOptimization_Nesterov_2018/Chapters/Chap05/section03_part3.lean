import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_3_6_1 (from Chap05) -/
open scoped Gradient NewtonDecrement

noncomputable section

universe u

section CentralPath

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The penalty objective `z ↦ t ⟪c, z⟫ + F(z)` used to define a central path for minimizing the
linear functional `⟪c, z⟫` over the barrier domain of `F`. -/
def centralPathPenaltyObjective
    (c : E) (F : E → ℝ) (t : ℝ) : E → ℝ :=
  fun z ↦ t * inner ℝ c z + F z

-- Proof sketch: unfold `centralPathPenaltyObjective`.
/-- Evaluating `centralPathPenaltyObjective c F t` recovers the penalty formula
`t ⟪c, z⟫ + F(z)`. -/
theorem centralPathPenaltyObjective_apply
    (c : E) (F : E → ℝ) (t : ℝ) (z : E) :
    centralPathPenaltyObjective c F t z = t * inner ℝ c z + F z :=
  rfl

/-- A trajectory indexed by `t ≥ 0` is a central path for minimizing `⟪c, z⟫` over `dom` with
barrier `F` when each point minimizes the corresponding penalty objective. -/
def IsCentralPath
    (dom : Set E) (c : E) (F : E → ℝ) (zStar : Set.Ici (0 : ℝ) → dom) : Prop :=
  ∀ t : Set.Ici (0 : ℝ),
    IsMinOn (centralPathPenaltyObjective c F t) dom (zStar t : E)

-- Proof sketch: unfold `IsCentralPath`.
/-- Expanding `IsCentralPath dom c F zStar` states that `zStar t` minimizes the penalty objective
for every nonnegative path parameter `t`. -/
theorem isCentralPath_iff
    (dom : Set E) (c : E) (F : E → ℝ) (zStar : Set.Ici (0 : ℝ) → dom) :
    IsCentralPath dom c F zStar ↔
      ∀ t : Set.Ici (0 : ℝ),
        IsMinOn (centralPathPenaltyObjective c F t) dom (zStar t : E) :=
  Iff.rfl

end CentralPath

section FunctionalConstraint

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 5.3.6.1 lies in the Chapter 5 self-concordant-barrier / path-following domain.

Sampled owner declarations in this domain:
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the owner for the
  analytic-center preprocessing stage;
* `IsCentralPath` in this file, the owner predicate for the continuous path-following stages;
* `IsMinOn` in mathlib and `Definition_5_3_3`, the canonical owner for exact analytic centers;
* `NewtonDecrement.ofPosDefMem` in `Definition_5_0_24`, the canonical owner for
  approximate-centering bounds on a positive-definite Hessian domain.

Best owner abstraction:
* source-facing: the functional-constraint path-following method with its two branch shapes;
* core/canonical: the inherited analytic-center preprocessing owner, used only through the
  stage-compatibility facts that connect it to the auxiliary and final central paths;
* bridge/view: the branch-sign hypotheses, the exact reduced-center time formula, and the
  approximate-centering statement at the start of the final path.

Primitive data:
* the canonical slack parameter `α = ⟪d, z₀⟫ + Δ`;
* in each branch, the source-facing central paths together with the fact that their initial points
  come from a stopped intermediate Newton preprocessing method.

Derived API:
* the starting-point compatibility between adjacent stages;
* existence of an exact reduced analytic center on the auxiliary central path;
* approximate-centering of the reduced endpoint that starts the final central path, read through
  the reduced-barrier Newton decrement.

The branch owners below therefore avoid separate public control fields for step sizes, avoid
primitive witness fields for chosen times or centers, and do not package the internal update
parameter of an unrelated path-following scheme into the public owner surface. Those remain
theorem-shaped bridge facts derived from the owner data.
-/

/-- The canonical slack parameter `α = ⟪d, z₀⟫ + Δ` attached to the source data of
Definition 5.3.6.1. -/
def functionalConstraintAlpha
    (d z0 : E) (Δ : ℝ) : ℝ :=
  inner ℝ d z0 + Δ

@[simp] theorem functionalConstraintAlpha_def
    (d z0 : E) (Δ : ℝ) :
    functionalConstraintAlpha d z0 Δ = inner ℝ d z0 + Δ :=
  rfl

/-- The shifted feasible set `S(α)` appearing in the preprocessing step for the additional
functional constraint `⟪d, z⟫ ≤ 0`; it is the portion of `S` where the logarithmic slack
`α - ⟪d, z⟫` stays positive. -/
def functionalConstraintAuxiliarySet (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ S ∧ inner ℝ d z < α}

-- Proof sketch: unfold `functionalConstraintAuxiliarySet`; membership in the defining set-builder
-- is exactly the conjunction `z ∈ S ∧ ⟪d, z⟫ < α`.
/-- Membership in `functionalConstraintAuxiliarySet S d α` means belonging to `S` and satisfying
the strict slack inequality `⟪d, z⟫ < α`. -/
theorem mem_functionalConstraintAuxiliarySet_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintAuxiliarySet S d α ↔
      z ∈ S ∧ inner ℝ d z < α :=
  Iff.rfl

/-- The auxiliary barrier `F(z) - log (α - ⟪d, z⟫)` on the shifted set `S(α)`. -/
def functionalConstraintAuxiliaryBarrier
    (F : E → ℝ) (d : E) (α : ℝ) : E → ℝ :=
  fun z ↦ F z - Real.log (α - inner ℝ d z)

-- Proof sketch: unfold `functionalConstraintAuxiliaryBarrier`.
/-- Evaluating `functionalConstraintAuxiliaryBarrier F d α` reproduces the textbook formula
`F(z) - log (α - ⟪d, z⟫)`. -/
theorem functionalConstraintAuxiliaryBarrier_apply
    (F : E → ℝ) (d z : E) (α : ℝ) :
    functionalConstraintAuxiliaryBarrier F d α z =
      F z - Real.log (α - inner ℝ d z) :=
  rfl

/-- The reduced feasible set `{z ∈ S(α) | ⟪d, z⟫ ≤ 0}` from Definition 5.3.6.1. -/
def functionalConstraintReducedSet (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ functionalConstraintAuxiliarySet S d α ∧ inner ℝ d z ≤ 0}

-- Proof sketch: unfold `functionalConstraintReducedSet` and then use
-- `mem_functionalConstraintAuxiliarySet_iff`.
/-- Membership in `functionalConstraintReducedSet S d α` means `z ∈ S`, `⟪d, z⟫ < α`, and
`⟪d, z⟫ ≤ 0`. -/
theorem mem_functionalConstraintReducedSet_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintReducedSet S d α ↔
      z ∈ S ∧ inner ℝ d z < α ∧ inner ℝ d z ≤ 0 := by
  constructor
  · rintro ⟨hz, hneg⟩
    exact ⟨hz.1, hz.2, hneg⟩
  · rintro ⟨hzS, hzAlpha, hzNeg⟩
    exact ⟨⟨hzS, hzAlpha⟩, hzNeg⟩

/-- The strict barrier domain inside the reduced feasible set on which the logarithmic term
`-log (-⟪d, z⟫)` is defined. -/
def functionalConstraintReducedBarrierDomain (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ functionalConstraintAuxiliarySet S d α ∧ inner ℝ d z < 0}

-- Proof sketch: unfold `functionalConstraintReducedBarrierDomain` and then use
-- `mem_functionalConstraintAuxiliarySet_iff`.
/-- Membership in `functionalConstraintReducedBarrierDomain S d α` means `z ∈ S`,
`⟪d, z⟫ < α`, and `⟪d, z⟫ < 0`. -/
theorem mem_functionalConstraintReducedBarrierDomain_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintReducedBarrierDomain S d α ↔
      z ∈ S ∧ inner ℝ d z < α ∧ inner ℝ d z < 0 := by
  constructor
  · rintro ⟨hz, hneg⟩
    exact ⟨hz.1, hz.2, hneg⟩
  · rintro ⟨hzS, hzAlpha, hzNeg⟩
    exact ⟨⟨hzS, hzAlpha⟩, hzNeg⟩

/-- Every point of the strict reduced barrier domain belongs to the closed reduced feasible set. -/
theorem functionalConstraintReducedBarrierDomain_subset_reducedSet
    (S : Set E) (d : E) (α : ℝ) :
    functionalConstraintReducedBarrierDomain S d α ⊆
      functionalConstraintReducedSet S d α := by
  intro z hz
  rw [mem_functionalConstraintReducedBarrierDomain_iff] at hz
  rw [mem_functionalConstraintReducedSet_iff]
  exact ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩

/-- For the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` with `Δ > 0`, the source point `z₀`
lies in `S(α)`. -/
theorem z0_mem_functionalConstraintAuxiliarySet_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ) :
    (z0 : E) ∈ functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintAuxiliarySet_iff, functionalConstraintAlpha]
  exact ⟨z0.2, by linarith⟩

/-- If the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive, then `z₀` already lies in
the reduced domain. -/
theorem z0_mem_functionalConstraintReducedSet_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) :
    (z0 : E) ∈
      functionalConstraintReducedSet S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintReducedSet_iff, functionalConstraintAlpha]
  have hα : inner ℝ d (z0 : E) + Δ ≤ 0 := by
    simpa [functionalConstraintAlpha] using alpha_nonpos
  exact ⟨z0.2, by linarith, by linarith⟩

/-- If the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive, then `z₀` lies in the
strict reduced barrier domain as well. -/
theorem z0_mem_functionalConstraintReducedBarrierDomain_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) :
    (z0 : E) ∈
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintReducedBarrierDomain_iff, functionalConstraintAlpha]
  have hα : inner ℝ d (z0 : E) + Δ ≤ 0 := by
    simpa [functionalConstraintAlpha] using alpha_nonpos
  exact ⟨z0.2, by linarith, by linarith⟩

/-- The barrier obtained from `F` by adding the logarithmic slack barriers for
`⟪d, z⟫ < α` and `⟪d, z⟫ < 0`. -/
def functionalConstraintReducedBarrier
    (F : E → ℝ) (d : E) (α : ℝ) : E → ℝ :=
  fun z ↦ functionalConstraintAuxiliaryBarrier F d α z - Real.log (-inner ℝ d z)

-- Proof sketch: unfold `functionalConstraintReducedBarrier` and
-- `functionalConstraintAuxiliaryBarrier`.
/-- Evaluating `functionalConstraintReducedBarrier F d α` gives the textbook barrier
`F(z) - log (α - ⟪d, z⟫) - log (-⟪d, z⟫)`. -/
theorem functionalConstraintReducedBarrier_apply
    (F : E → ℝ) (d z : E) (α : ℝ) :
    functionalConstraintReducedBarrier F d α z =
      F z - Real.log (α - inner ℝ d z) - Real.log (-inner ℝ d z) :=
  rfl

variable [FiniteDimensional ℝ E]

private def functionalConstraintSlackMap (d : E) (α : ℝ) : E →ᴬ[ℝ] ℝ :=
  (-innerSL ℝ d).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α

omit [FiniteDimensional ℝ E] in
@[simp] private theorem functionalConstraintSlackMap_apply (d z : E) (α : ℝ) :
    functionalConstraintSlackMap d α z = α - inner ℝ d z := by
  simp [functionalConstraintSlackMap, innerSL_apply_apply]
  ring

private def functionalConstraintNegInnerMap (d : E) : E →ᴬ[ℝ] ℝ :=
  (-innerSL ℝ d).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in
@[simp] private theorem functionalConstraintNegInnerMap_apply (d z : E) :
    functionalConstraintNegInnerMap d z = -inner ℝ d z := by
  simp [functionalConstraintNegInnerMap, innerSL_apply_apply]

instance functionalConstraintAuxiliaryBarrier_isSelfConcordantBarrierOnWith
    (S : Set E) (d : E) (α : ℝ) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] :
    IsSelfConcordantBarrierOnWith
      (functionalConstraintAuxiliarySet S d α)
      (ν + 1)
      (functionalConstraintAuxiliaryBarrier F d α) := by
  have hdom :
      functionalConstraintAuxiliarySet S d α =
        S ∩ ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext z
    simp [functionalConstraintAuxiliarySet, Set.preimage]
  have hbarrier :
      functionalConstraintAuxiliaryBarrier F d α =
        F + ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := by
    funext z
    simp [functionalConstraintAuxiliaryBarrier, sub_eq_add_neg]
  letI :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := by
    simpa using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap
        (functionalConstraintSlackMap d α))
  have hS : IsSelfConcordantBarrierOnWith S ν F := inferInstance
  have hslack :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := inferInstance
  simpa [hdom, hbarrier] using
    hS.add hslack

instance functionalConstraintReducedBarrier_isSelfConcordantBarrierOnWith
    (S : Set E) (d : E) (α : ℝ) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] :
    IsSelfConcordantBarrierOnWith
      (functionalConstraintReducedBarrierDomain S d α)
      (ν + 2)
      (functionalConstraintReducedBarrier F d α) := by
  have hdom :
      functionalConstraintReducedBarrierDomain S d α =
        functionalConstraintAuxiliarySet S d α ∩
          ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext z
    simp [functionalConstraintReducedBarrierDomain, functionalConstraintAuxiliarySet, Set.preimage]
  have hbarrier :
      functionalConstraintReducedBarrier F d α =
        functionalConstraintAuxiliaryBarrier F d α +
          ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := by
    funext z
    simp [functionalConstraintReducedBarrier, sub_eq_add_neg, functionalConstraintNegInnerMap]
  letI :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := by
    simpa using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap
        (functionalConstraintNegInnerMap d))
  have hnu : ν + 1 + 1 = ν + 2 := by
    ext
    norm_num [add_assoc]
  have haux :
      IsSelfConcordantBarrierOnWith
        (functionalConstraintAuxiliarySet S d α)
        (ν + 1)
        (functionalConstraintAuxiliaryBarrier F d α) := inferInstance
  have hslack :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := inferInstance
  simpa [hdom, hbarrier, hnu] using
    haux.add hslack

section PathFollowingScheme

variable (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
variable [IsSelfConcordantBarrierOnWith S ν F]
variable (z0 : S) (β Δ : ℝ)

/-- The fallback branch for the additional functional constraint `⟪d, z⟫ ≤ 0`, used when the
canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive: first run the Chapter 5
analytic-center scheme on the reduced barrier starting from the canonical source point `z₀`, then
follow the final `c`-central path on the reduced domain. -/
structure NonpositiveFunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) where
  /-- Stage 2 follows the `c`-central path for the reduced problem. -/
  finalCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-2 trajectory is a central path for minimizing `⟪c, z⟫` over the reduced
  feasible set. -/
  finalCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      c
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      finalCentralPath
  /-- The reduced-domain analytic-center preprocessing method from Definition 5.3.5.3, started at
  the canonical source point `z₀`. -/
  preprocessing :
    StoppedIntermediateSelfConcordantNewtonMethod
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      ⟨(z0 : E), z0_mem_functionalConstraintReducedBarrierDomain_alpha d delta_pos alpha_nonpos⟩
      β
  /-- The initial point of the final path is the stopping iterate of the preprocessing stage. -/
  finalCentralPath_zero_eq_preprocessing :
    (finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E) =
      preprocessing.toMethod preprocessing.stopIndex

/-- The positive-`α` branch for the additional functional constraint `⟪d, z⟫ ≤ 0`: first run
the Chapter 5 analytic-center scheme on `S(α)`, then follow the auxiliary `d`-central path to
the reduced set, and finally follow the `c`-central path on that reduced domain. -/
structure PositiveFunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (alpha_pos : 0 < functionalConstraintAlpha d z0 Δ) where
  /-- Stage 2 follows the `d`-central path for the auxiliary barrier on `S(α)`. -/
  auxiliaryCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-2 trajectory is a central path for the penalty objective
  `z ↦ t ⟪d, z⟫ + F(z) - log (α - ⟪d, z⟫)`. -/
  auxiliaryCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ))
      d
      (functionalConstraintAuxiliaryBarrier F d (functionalConstraintAlpha d z0 Δ))
      auxiliaryCentralPath
  /-- The auxiliary analytic-center preprocessing method from Definition 5.3.5.3, started from
  the canonical source point `z₀`. -/
  preprocessing :
    StoppedIntermediateSelfConcordantNewtonMethod
      (functionalConstraintAuxiliaryBarrier F d (functionalConstraintAlpha d z0 Δ))
      ⟨(z0 : E), z0_mem_functionalConstraintAuxiliarySet_alpha d delta_pos⟩
      β
  /-- The initial point of the auxiliary central path is the stopping iterate of the preprocessing
  stage. -/
  auxiliaryCentralPath_zero_eq_preprocessing :
    (auxiliaryCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E) =
      preprocessing.toMethod preprocessing.stopIndex
  /-- The distinguished stage-2 point `z_*`, viewed in the source-facing reduced feasible set
  `{z ∈ S(α) | ⟪d, z⟫ ≤ 0}`. -/
  zStar :
    functionalConstraintReducedSet S d (functionalConstraintAlpha d z0 Δ)
  /-- The distinguished stage-2 point `z_*` lies in the strict reduced barrier domain. -/
  zStar_mem_barrierDomain :
    (zStar : E) ∈
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The distinguished stage-2 time `t_*`. -/
  tStar : Set.Ici (0 : ℝ)
  /-- The distinguished point `z_*` lies on the auxiliary central path at time `t_*`. -/
  zStar_on_auxiliaryPath :
    (auxiliaryCentralPath tStar : E) = zStar
  /-- The distinguished point `z_*` is the exact analytic center of the reduced barrier domain. -/
  zStar_isAnalyticCenter :
    IsMinOn
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      (zStar : E)
  /-- The distinguished time `t_*` satisfies the source formula
  `t_* = -1 / ⟪d, z_*⟫`. -/
  tStar_eq :
    (tStar : ℝ) = -1 / inner ℝ d (zStar : E)
  /-- Stage 3 follows the `c`-central path for the reduced problem. -/
  finalCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-3 trajectory is a central path for minimizing `⟪c, z⟫` over the reduced
  feasible set. -/
  finalCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      c
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      finalCentralPath
  /-- The stage-2 endpoint that starts the final central path lies on the auxiliary central
  path. -/
  finalCentralPath_zero_on_auxiliaryPath :
    ∃ t : Set.Ici (0 : ℝ),
      (auxiliaryCentralPath t : E) = (finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E)
  /-- The reduced barrier on its strict domain carries the canonical positive-definite-Hessian
  owner needed for reduced-domain Newton decrement. -/
  reducedBarrier_hasPositiveDefiniteHessianOn :
    HasPositiveDefiniteHessianOn
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
  /-- The starting point of the final path is `β`-approximately centered for the reduced barrier,
  expressed directly through the reduced-domain Newton decrement. -/
  finalCentralPath_zero_isApproximate :
    let z := finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩
    letI := reducedBarrier_hasPositiveDefiniteHessianOn
    λ[functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ); (z : E) | z.2] ≤
      β

/-- Definition 5.3.6.1: for the problem `min {(c, z) : z ∈ S, ⟪d, z⟫ ≤ 0}`, choose
`α = ⟪d, z₀⟫ + Δ` with `Δ > 0`; if `α ≤ 0`, the method falls back to the two-stage process of
Definition 5.3.5.3, and if `α > 0`, it first finds a `β`-approximate analytic center of `S(α)`,
then follows the `d`-central path to a `β`-approximate analytic center of the reduced set
`{z ∈ S(α) | ⟪d, z⟫ ≤ 0}`, and finally follows the `c`-central path for the reduced problem. -/
inductive FunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ)
    (delta_pos : 0 < Δ) : Type u where
  | fallback
      {alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0}
      (scheme :
        NonpositiveFunctionalConstraintPathFollowingScheme
          S c d F ν z0 β Δ delta_pos alpha_nonpos) :
      FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos
  | positive
      {alpha_pos : 0 < functionalConstraintAlpha d z0 Δ}
      (scheme :
        PositiveFunctionalConstraintPathFollowingScheme
          S c d F ν z0 β Δ delta_pos alpha_pos) :
      FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos

end PathFollowingScheme

namespace FunctionalConstraintPathFollowingScheme

/-- Every functional-constraint path-following scheme is either the fallback branch, determined by
the actual nonpositive-`α` two-stage process, or the positive three-stage branch. -/
theorem eq_fallback_or_eq_positive
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (scheme : FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos) :
    (∃ (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0)
        (fallbackScheme :
          NonpositiveFunctionalConstraintPathFollowingScheme
            S c d F ν z0 β Δ delta_pos alpha_nonpos),
        scheme = fallback fallbackScheme) ∨
      ∃ (alpha_pos : 0 < functionalConstraintAlpha d z0 Δ)
        (positiveScheme :
          PositiveFunctionalConstraintPathFollowingScheme
            S c d F ν z0 β Δ delta_pos alpha_pos),
        scheme = positive positiveScheme := by
  cases scheme with
  | fallback fallbackScheme =>
      exact Or.inl ⟨_, fallbackScheme, rfl⟩
  | positive positiveScheme =>
      exact Or.inr ⟨_, positiveScheme, rfl⟩

end FunctionalConstraintPathFollowingScheme

end FunctionalConstraint

end

/-! ### Proposition_5_3_6_1 (from Chap05) -/
noncomputable section

universe u

section FunctionalConstraintStandardForm

variable {X : Type u} {m : ℕ}

local notation "StdPoint" => ℝ × ℝ × X

/-- The original optimization problem with ambient set `Q`, objective `f₀`, and inequality
constraints `fⱼ(x) ≤ 0`. -/
def functionalConstraintProblem
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) :
    FunctionalConstraintsMinimizationProblem X m where
  basicFeasibleSet := Q
  objective := fun x ↦ f0 x
  constraints := fun j x ↦ fj j x
  senses := fun _ ↦ .le

/-- Evaluating the original functional-constraint owner recovers the original objective. -/
@[simp] theorem functionalConstraintProblem_apply
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (x : Q) :
    functionalConstraintProblem Q f0 fj x = f0 x :=
  rfl

/-- Membership in the original owner feasible set is exactly coordinatewise inequality
constraint satisfaction. -/
@[simp] theorem mem_functionalConstraintProblem_feasibleSet_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {x : Q} :
    x ∈ (functionalConstraintProblem Q f0 fj).feasibleSet ↔
      ∀ j : Fin m, fj j x ≤ 0 :=
  Iff.rfl

/-- The `(ξ, κ, x)` standard-form reformulation of the original functional-constraint problem. -/
def functionalConstraintStandardFormProblem
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    SetConstrainedMinimizationProblem StdPoint where
  feasibleSet := {p | p.1 ≤ xiBar ∧
    p.2.1 ≤ 0 ∧
    p.2.2 ∈ Q ∧
    f0 p.2.2 ≤ p.1 ∧
    ∀ j : Fin m, fj j p.2.2 ≤ p.2.1}
  objective := Prod.fst

/-- Membership in the standard-form feasible set is exactly the conjunction of the bounds
`ξ ≤ ξBar`, `κ ≤ 0`, the ambient constraint `x ∈ Q`, and the lifted inequalities
`f₀(x) ≤ ξ`, `fⱼ(x) ≤ κ`. -/
@[simp] theorem mem_functionalConstraintStandardFormProblem_feasibleSet_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ} {p : StdPoint} :
    p ∈ (functionalConstraintStandardFormProblem Q f0 fj xiBar).feasibleSet ↔
      p.1 ≤ xiBar ∧
        p.2.1 ≤ 0 ∧
        p.2.2 ∈ Q ∧
        f0 p.2.2 ≤ p.1 ∧
        ∀ j : Fin m, fj j p.2.2 ≤ p.2.1 :=
  Iff.rfl

/-- Evaluating the standard-form objective returns the `ξ`-coordinate. -/
@[simp] theorem functionalConstraintStandardFormProblem_apply
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) (p : StdPoint) :
    functionalConstraintStandardFormProblem Q f0 fj xiBar p = p.1 :=
  rfl

-- Proof sketch: every feasible point `x` of the original problem lifts to the feasible triple
-- `(f₀(x), 0, x)` because `f₀(x) ≤ ξBar` on the original feasible set and `fⱼ(x) ≤ 0`.
-- Conversely, every feasible triple `(ξ, κ, x)` projects to an original feasible point `x`, and
-- the lifted inequality `f₀(x) ≤ ξ` compares the original optimal value with the standard-form
-- one. These two comparisons show that the two constrained problems have the same optimal value.
/-- Proposition 5.3.6.1: if `ξBar` bounds the original objective on the original feasible set,
then the original problem and its standard-form reformulation have the same canonical Chapter 1
optimal value. -/
theorem functionalConstraintOptimalValue_eq_standardFormOptimalValue
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ}
    (hUpper :
      ∀ x : Q, x ∈ (functionalConstraintProblem Q f0 fj).feasibleSet → f0 x ≤ xiBar) :
    (functionalConstraintProblem Q f0 fj).toSetConstrainedMinimizationProblem.optimalValue =
      (functionalConstraintStandardFormProblem Q f0 fj xiBar).optimalValue := by
  let originalProblem := functionalConstraintProblem Q f0 fj
  let problem := originalProblem.toSetConstrainedMinimizationProblem
  let standardProblem := functionalConstraintStandardFormProblem Q f0 fj xiBar
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨p, hp, rfl⟩
    rcases (mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mp hp) with
      ⟨_, hkappa, hxQ, hf0, hfj⟩
    let x : Q := ⟨p.2.2, hxQ⟩
    have hx : x ∈ originalProblem.feasibleSet :=
      mem_functionalConstraintProblem_feasibleSet_iff.mpr
        (fun j ↦ le_trans (hfj j) hkappa)
    have hproblem :
        problem.optimalValue ≤ (f0 x : EReal) := by
      simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hx
    exact hproblem.trans <| by
      change (f0 x : EReal) ≤ (p.1 : EReal)
      exact_mod_cast hf0
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hfj : ∀ j : Fin m, fj j x ≤ 0 :=
      mem_functionalConstraintProblem_feasibleSet_iff.mp hx
    have hstandard : (f0 x, 0, (x : X)) ∈ standardProblem.feasibleSet :=
      mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mpr
        ⟨hUpper x hx, le_rfl, x.2, le_rfl, hfj⟩
    simpa [standardProblem] using
      standardProblem.optimalValue_le_of_mem_feasibleSet hstandard

end FunctionalConstraintStandardForm

/-! ### Proposition_5_3_6_2 (from Chap05) -/
noncomputable section

universe u

section FunctionalConstraintStandardFormBarrier

variable {X : Type u} {m : ℕ}

local notation "StdPoint" => ℝ × ℝ × X
local notation "PairPoint" => X × ℝ
local notation "StatePoint" => ℝ × X
local notation "PairPointL2" => WithLp 2 PairPoint
local notation "StatePointL2" => WithLp 2 StatePoint
local notation "StdPointL2" => WithLp 2 (ℝ × StatePointL2)
local notation "ofPairPoint" => (WithLp.ofLp : PairPointL2 → PairPoint)
local notation "ofStatePoint" => (WithLp.ofLp : StatePointL2 → StatePoint)
local notation "ofStdPoint" =>
  (Prod.map id ofStatePoint) ∘ (WithLp.ofLp : StdPointL2 → ℝ × StatePointL2)

/- Proposition 5.3.6.2 lies in the chapter's self-concordant-barrier / standard-form lifting
domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.add` from `Theorem_5_3_2`, the canonical barrier-sum theorem;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barriers over complete real inner-product spaces;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the source-facing strict epigraph owner
  reused by the objective and functional-constraint barrier hypotheses;
* mathlib `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))` together with `WithLp.ofLp`,
  the canonical `L²` pair/triple owners and their bridge back to the raw textbook coordinates;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, the Chapter 5
  strict-epigraph barrier theorem over that owner.

Source/core/bridge triage:
* source-facing: the standard-form barrier on triples `(ξ, κ, x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` pair/triple owners
  `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))`;
* bridge/view: the raw-pair/raw-triple formulas transported to those owners through
  `WithLp.ofLp`.

Primitive data:
* the ambient feasible set `Q`;
* the objective and constraint functions `f₀`, `fⱼ`;
* the barrier data `FQ`, `F₀`, `Fⱼ`;
* the scalar upper bound `xiBar`.

Derived API:
* the source-facing barrier formula itself;
* its evaluation lemma;
* the standard-form barrier theorem, which consumes the canonical `L²` pair-owner barrier data on
  the strict epigraphs and realizes the standard-form owner on the canonical `L²` triple space.

This refinement therefore keeps the source-facing barrier formula and domain on the raw textbook
spaces, reuses the strict-epigraph owner from `Theorem_5_3_5` instead of restating its
set-builder, and presents the numbered theorem entirely on the canonical `WithLp.ofLp` owner
surface rather than mixing raw-pair barrier hypotheses with a separate ad hoc triple transport. -/

/-- The strict domain on which the standard-form logarithmic barrier is defined: the ambient
constraint `x ∈ Q`, the strict epigraph inequalities `f₀(x) < ξ` and `fⱼ(x) < κ`, and the two
strict slack inequalities `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrierDomain
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    Set StdPoint :=
  {p | p.1 < xiBar} ∩
    {p | p.2.1 < 0} ∩
    (fun p : StdPoint ↦ p.2.2) ⁻¹' Q ∩
    (fun p : StdPoint ↦ (p.2.2, p.1)) ⁻¹'
      strictConstrainedEpigraph (Set.univ : Set X) f0 ∩
    {p | ∀ j : Fin m,
      p ∈ (fun q : StdPoint ↦ (q.2.2, q.2.1)) ⁻¹'
        strictConstrainedEpigraph (Set.univ : Set X) (fj j)}

/-- Membership in the standard-form barrier domain means that every logarithmic slack is strictly
positive and that the base point lies in `Q`. -/
@[simp] theorem mem_functionalConstraintStandardFormBarrierDomain_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ} {p : StdPoint} :
    p ∈ functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ↔
      p.1 < xiBar ∧
        p.2.1 < 0 ∧
        p.2.2 ∈ Q ∧
        f0 p.2.2 < p.1 ∧
        ∀ j : Fin m, fj j p.2.2 < p.2.1 := by
  simp [functionalConstraintStandardFormBarrierDomain, and_assoc]

/-- Every point of the strict barrier domain is feasible for the closed standard-form
reformulation. -/
theorem functionalConstraintStandardFormBarrierDomain_subset_feasibleSet
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ⊆
      (functionalConstraintStandardFormProblem Q f0 fj xiBar).feasibleSet := by
  intro p hp
  rcases mem_functionalConstraintStandardFormBarrierDomain_iff.mp hp with
    ⟨hxi, hkappa, hxQ, hf0, hfj⟩
  exact mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mpr
    ⟨le_of_lt hxi, le_of_lt hkappa, hxQ, le_of_lt hf0, fun j ↦ le_of_lt (hfj j)⟩

/-- The explicit barrier obtained by adding the barrier on `Q`, the epigraph barrier for the
objective, the epigraph barriers for the functional constraints, and the two logarithmic slack
terms for `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrier
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ) :
    StdPoint → ℝ :=
  fun p ↦
    FQ p.2.2 +
      F0 (p.2.2, p.1) +
        (∑ j : Fin m, Fj j (p.2.2, p.2.1)) +
          sublevelLogBarrier (fun q : StdPoint ↦ q.1) xiBar p +
            sublevelLogBarrier (fun q : StdPoint ↦ q.2.1) 0 p

/-- Evaluating `functionalConstraintStandardFormBarrier` reproduces the textbook barrier formula
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)`. -/
@[simp]
theorem functionalConstraintStandardFormBarrier_apply
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ)
    (p : StdPoint) :
    functionalConstraintStandardFormBarrier FQ F0 Fj xiBar p =
      FQ p.2.2 +
        F0 (p.2.2, p.1) +
          (∑ j : Fin m, Fj j (p.2.2, p.2.1)) -
            Real.log (xiBar - p.1) - Real.log (-p.2.1) := by
  simp [functionalConstraintStandardFormBarrier, sublevelLogBarrier, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

-- Proof sketch: view each summand as a self-concordant barrier on the reformulated feasible set:
-- `FQ` is pulled back along the coordinate projection `(ξ, κ, x) ↦ x`, `F₀` is pulled back
-- along `(ξ, κ, x) ↦ (x, ξ)`, and each `Fⱼ` is pulled back along `(ξ, κ, x) ↦ (x, κ)` using the
-- canonical owner theorem `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`. The two
-- logarithmic
-- slack terms are the standard one-dimensional barriers pulled back from `x ↦ -log x`. Repeated
-- application of `IsSelfConcordantBarrierOnWith.add` then yields the parameter sum
-- `vQ + v₀ + ∑ⱼ vⱼ + 2`.
/-- Proposition 5.3.6.2: if `F_Q` is a self-concordant barrier for `Q`, if `F₀` is a
self-concordant barrier on the canonical `L²` pair owner over the strict epigraph of `f₀`, and
if each `Fⱼ` is a self-concordant barrier on the canonical `L²` pair owner over the strict
epigraph of `fⱼ`, then
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)` is a self-concordant barrier for
the strict reformulated barrier domain `ξ < ξBar`, `κ < 0`, `x ∈ Q`, `f₀(x) < ξ`, `fⱼ(x) < κ`,
which sits inside the closed feasible set of Proposition `5.3.6.1`, with parameter
`v_Q + v₀ + ∑ⱼ vⱼ + 2`, all viewed on the canonical `L²` owners through `WithLp.ofLp`. -/
theorem functionalConstraintStandardFormBarrier_isSelfConcordantBarrierOnWith
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ}
    {FQ : X → ℝ} {F0 : X × ℝ → ℝ} {Fj : Fin m → X × ℝ → ℝ}
    {xiBar : ℝ} {vQ v0 : NNReal} {vj : Fin m → NNReal}
    (hFQ : IsSelfConcordantBarrierOnWith Q vQ FQ)
    (hF0 : IsSelfConcordantBarrierOnWith
      (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) f0)
      v0 (F0 ∘ ofPairPoint))
    (hFj : ∀ j : Fin m,
      IsSelfConcordantBarrierOnWith
        (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j))
        (vj j) (Fj j ∘ ofPairPoint)) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹'
        functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar)
      (vQ + v0 + (∑ j : Fin m, vj j) + 2)
      (functionalConstraintStandardFormBarrier FQ F0 Fj xiBar ∘ ofStdPoint) := sorry

end FunctionalConstraintStandardFormBarrier

/-! ### Theorem_5_3_6 (from Chap05) -/
open scoped ConstrainedArgmin ConvexAnalysis

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

/- Theorem 5.3.6 lies in the chapter's self-concordant-barrier / partial-minimization domain.

Sampled owner-style declarations in this domain:
- `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  fiberwise infima;
- `extendedRealRealPart` and
  `extendedRealRealPart_partialInfProjection_eq_sInf_image` in `Definition_5_0_18`, the
  canonical real surface of that owner on its finite-value domain;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for chosen constrained minimizers;
- the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) (y x)` and
  `partialMinimizationObjective_isSelfConcordantOnWith` in `Theorem_5_1_11`, the chapter bridge
  and owner theorem for self-concordance of the partial minimization objective;
- mathlib `WithLp 2 (E₁ × E₂)` together with `z ↦ z.ofLp`, the canonical ambient `L²` product
  owner for the barrier data on `E₁ × E₂`;
- `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the Chapter 5 owner for quantitative
  self-concordant barriers.

Best owner abstraction:
- source-facing: the partial-minimization barrier obtained from minimizing `Φ (x, ·)` on the
  feasible fiber above `x`;
- core/canonical: `partialInfProjection Q (Real.toEReal ∘ Φ)` together with its real surface
  `extendedRealRealPart` on `dom`, plus the ambient barrier owner
  `IsSelfConcordantBarrierOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) ν
    (Φ ∘ WithLp.ofLp)`;
- bridge/view: the fiberwise minimizer selection
  `y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)` together with evaluation of the frozen-slice
  Hessian `hessian (Φ ∘ Prod.mk x) (y x)` at the minimizer.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the barrier objective `Φ : E₁ × E₂ → ℝ`;
- the minimizing branch `y : E₁ → E₂`;
- the ambient barrier owner witness
  `hΦ : IsSelfConcordantBarrierOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) ν
    (Φ ∘ WithLp.ofLp)`;
- the pointwise positive-definite frozen-slice `yy` Hessian hypothesis on
  `hessian (Φ ∘ Prod.mk x) (y x)`.

Derived API:
- the natural domain `dom (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- the real-valued partial-minimization objective
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`.

Source/core/bridge triage:
- source-facing: Theorem 5.3.6 and its barrier conclusion for the partial minimization objective;
- core/canonical: `partialInfProjection`, `extendedRealRealPart`, and
  `IsSelfConcordantBarrierOnWith`;
- bridge/view: the canonical fiberwise `argmin` owner and the chosen evaluation point `y x` for
  the frozen slice.

This refinement deletes the local fiber/domain/value-function wrappers and states the theorem
directly on the existing Chapter 3 and Chapter 5 owner surface. It keeps only the source-faithful
extra bridge data not already packaged by the barrier owner: the chosen fiber minimizer and the
positive-definite frozen-slice `yy` Hessian hypothesis needed by the chapter's canonical
partial-minimization self-concordance theorem. -/

-- Proof sketch: first apply the Chapter 5 owner theorem
-- `partialMinimizationObjective_isSelfConcordantOnWith` to the canonical infimal-projection owner
-- surface. The needed interior-attainment hypothesis is derived from `hy_argmin` together with
-- openness of `Q`, supplied by the barrier owner, while the nondegeneracy input is kept as the
-- explicit frozen-slice Hessian hypothesis. Then combine that self-concordance
-- result with the barrier-parameter inequality inherited from the ambient barrier on `Q` to
-- obtain the barrier conclusion for the partial infimal projection with the same parameter `ν`.
section PartialMinimizationBarrier

variable {Q : Set (E₁ × E₂)} {ν : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}

local notation "QZ" => ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q)
local notation "ψ" => partialInfProjection Q (Real.toEReal ∘ Φ)
local notation "D" => dom ψ
local notation "f" => extendedRealRealPart ψ

/-- Theorem 5.3.6: if `Φ` is a `ν`-self-concordant barrier on `Q ⊆ E₁ × E₂`, and if for every
`x ∈ D`, where `D = dom (partialInfProjection Q (Real.toEReal ∘ Φ))`, the explicit barrier
witness `hΦ` on `Q` is given, the fiber problem `min_y Φ(x, y)` over `(Prod.mk x) ⁻¹' Q` is
attained at `y x`, and the frozen-slice `yy` Hessian there is positive definite, then the
canonical real surface of the partial infimal projection is a `ν`-self-concordant barrier on its
natural domain. -/
theorem partialMinimizationObjective_isSelfConcordantBarrierOnWith_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hyy_pos : ∀ ⦃x : E₁⦄, x ∈ D → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    IsSelfConcordantBarrierOnWith D ν f := by
  letI : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp) := hΦ
  sorry

end PartialMinimizationBarrier

end

/-! ### Theorem_5_3_7 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.7 lies in the Chapter 5 self-concordant-barrier / concavity-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, the owner-level
  concavity companion for the exponential transform;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the canonical
  source-facing equivalence between the barrier owner and concavity of `x ↦ exp (-(F x / ν))`;
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`, together with mathlib
  `ConcaveOn.neg`, which give the canonical first-order tangent inequality for the concave
  exponential transform by passing to its negative.

Best owner abstraction:
* source-facing: Theorem 5.3.7's logarithmic lower Taylor bound for a standard
  self-concordant function;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div`, followed by the
  first-order tangent inequality for the concave exponential transform.

Primitive data:
* the domain `dom`;
* the function `F`;
* the standard self-concordance owner `hFsc`;
* the positive barrier parameter hypothesis `hν`.

Derived API:
* the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* concavity of `x ↦ exp (-(F x / ν))` on `dom`;
* the source-facing logarithmic lower Taylor bound together with positivity of its logarithm
  argument.

Source/core/bridge triage:
* source-facing: the numbered equivalence in Theorem 5.3.7;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: the exponential-transform concavity criterion from `Lemma_5_3_1`.

This refinement deletes the previous isolated segment-gradient helper lemmas, which had no
downstream users and duplicated the chapter's canonical concavity route. The file now keeps only
the source-facing theorem and states it directly through the existing owner abstraction. -/

-- Proof sketch: apply
-- `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` from Lemma 5.3.1 to replace the
-- barrier condition by concavity of `x ↦ exp (-(F x / ν))`. Pass to the negative function and use
-- the Chapter 2 owner `ConvexOn.lower_tangent_plane` to obtain the affine support bound at `x`;
-- then rewrite the gradient by the chain rule, simplify the exponential factor, and take
-- logarithms after first recording positivity of the logarithm argument. The converse follows by
-- exponentiating the displayed logarithmic inequality to recover the same tangent inequality for
-- the exponential transform, hence concavity, and then invoking the owner equivalence from
-- Lemma 5.3.1.
/-- Theorem 5.3.7: for a standard self-concordant function `F`, being a
`ν`-self-concordant barrier is equivalent to the logarithmic lower Taylor bound
`F(y) ≥ F(x) - ν log (1 - ν⁻¹ ⟪∇ F(x), y - x⟫)` on the domain, together with the required
positivity of the logarithm argument. -/
theorem isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ∀ {x y : E} (hx : x ∈ dom) (hy : y ∈ dom),
        let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)
        0 < t ∧ F y ≥ F x - (ν : ℝ) * Real.log t := sorry

end

/-! ### Theorem_5_3_8 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.8 lies in the Chapter 5 self-concordant-barrier / local-distance domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise bridge from the barrier parameter inequality to the local
  gradient/local-norm estimate;
* `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` in `Theorem_5_1_5`, the canonical
  Dikin-radius local-norm transport estimate;
* `gradient_difference_inner_ge_hessianLocalNorm_sq_div` in `Theorem_5_1_8`, the canonical
  lower bound for the gradient increment paired with the chord.

Best owner abstraction:
* source-facing: the textbook bound on the local norm of the chord `y - x`;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F` together with `‖y - x‖[F; x]`;
* bridge/view: the owner-level barrier-parameter square estimate at `x`, followed by the standard
  self-concordant local-norm comparison along the segment from `x` to `y`.

Primitive data:
* the barrier owner witness `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* points `x, y ∈ dom`;
* the source-facing nonnegativity hypothesis `0 ≤ ⟪∇ F(x), y - x⟫`.

Derived API:
* the local-distance bound `‖y - x‖[F; x] ≤ ν + 2 √ν`.

This theorem is an owner-level barrier estimate, so its public surface belongs in the barrier
namespace instead of as a parallel top-level theorem with the owner repeated in the binder list.
It uses only the Chapter 5 barrier/local-norm owner layer, so the ambient space assumption stays
at the canonical `[CompleteSpace E]` level rather than introducing a finite-dimensional bridge.
-/

-- Proof sketch: let `r := ‖y - x‖[F; x]`. If `r ≤ Real.sqrt ν`, the claim is immediate.
-- Otherwise choose an intermediate point `z = x + α • (y - x)` on the segment from `x` to `y`
-- with `α = Real.sqrt ν / r`, so the initial subsegment from `x` to `z` has `x`-local norm
-- exactly `√ν`. Since the barrier owner inherits an open convex standard-self-concordant domain,
-- both subsegments stay inside `dom`. Use the chapter's standard self-concordant segment
-- estimates on `x → z` to obtain a lower bound for the gradient increment, and combine that with
-- the barrier-parameter bound at `z` plus local-norm transport on `z → y` to control the
-- remaining pairing. The hypothesis `0 ≤ ⟪∇ F(x), y - x⟫` then lets one rearrange the resulting
-- scalar inequality to obtain `r ≤ ν + 2 * Real.sqrt ν`.
namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {x y : E}

/-- Theorem 5.3.8: if `F` is a `ν`-self-concordant barrier on `dom` and the gradient pairing
`⟪∇ F(x), y - x⟫` is nonnegative, then the local norm of the chord `y - x` at `x` is bounded by
`ν + 2 √ν`. -/
theorem hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy_nonneg : inner ℝ (∇ F x) (y - x) ≥ 0) :
    ‖y - x‖[F; x] ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
  sorry

end

end IsSelfConcordantBarrierOnWith

end

/-! ### Theorem_5_3_9 (from Chap05) -/
open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/- Theorem 5.3.9 lies in the Chapter 5 self-concordant-barrier / analytic-center / Dikin-ellipsoid
domain.

Sampled owner-style declarations in this domain:
* `IsMinOn` in `Definition_5_3_3`, the canonical analytic-center owner;
* `dikinEllipsoid`, `openDikinEllipsoid`, and the notation `W[f; x](r)`, `W⁰[f; x](r)` in
  `Definition_5_0_13`, the chapter owners for the closed and open local-norm balls;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith
    .hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg`
  in `Theorem_5_3_8`, the owner local-distance estimate;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Theorem_5_1_5`, the
  canonical open-Dikin-ball domain-inclusion theorem for standard self-concordant functions.

Best owner abstraction:
* source-facing: the analytic-center local-distance bound and its Dikin-ellipsoid corollaries from
  Theorem 5.3.9;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F` together with the Chapter 5 Dikin-ball
  owners `W[F; xStar : E] (r)` and `W⁰[F; xStar : E](1)`;
* bridge/view: the analytic-center stationarity consequence
  `∇ F (xStar : E) = 0`, obtained from `IsMinOn` via the Chapter 1 local-minimum owner theorem,
  and the standard-self-concordant unit-ball inclusion theorem.

Primitive data:
* the barrier owner witness `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* for clause `(1)`, the analytic-center witness `hcenter : IsMinOn F dom (xStar : E)`;
* for clause `(2)`, only the center point `xStar : dom`.

Derived API:
* the radius-`ν + 2 √ν` Dikin-ellipsoid containment of `dom`;
* the canonical-recall identification of clause `(2)` with the standard self-concordant
  open-Dikin-ball inclusion theorem.

Source/core/bridge triage:
* source-facing: clause `(1)` as an analytic-center containment statement;
* core/canonical: the barrier owner together with the Chapter 5 Dikin-ball owners;
* bridge/view: clause `(1)` is a closed-ball corollary of the owner local-distance bound, while
  clause `(2)` reuses the canonical open-ball owner theorem directly.

This item is therefore best expressed on the barrier and Dikin-ball owner layer. Clause `(1)`
remains a new barrier-specific theorem, while clause `(2)` should be handled by direct recall of
the canonical standard-self-concordant owner theorem rather than by a duplicate specialized
wrapper. The ambient space assumption stays aligned with the upstream owner graph, which lives on
complete real inner-product spaces rather than on a finite-dimensional bridge. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

/-- Theorem 5.3.9 (1): if `xStar` is an analytic center of a `ν`-self-concordant barrier `F`,
then the whole domain `dom` lies in the Dikin ellipsoid centered at `xStar` with radius
`ν + 2 √ν`. Equivalently, every `x ∈ dom` satisfies the local-distance bound `(5.3.17)`. -/
theorem subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E)) :
    dom ⊆ W[F; (xStar : E)]((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hstd : IsStandardSelfConcordantOn dom F := inferInstance
  intro x hx
  rw [mem_dikinEllipsoid_iff]
  have hlocal : IsLocalMin F (xStar : E) :=
    hcenter.isLocalMin (hstd.isOpen_domain.mem_nhds xStar.2)
  have hgrad0 : ∇ F (xStar : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  exact hF.hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
    xStar.2 hx (by simp [hgrad0])

end IsSelfConcordantBarrierOnWith

/- Theorem 5.3.9 (2) is the Chapter 5 owner theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`, specialized to the standard
self-concordant constant `1` inherited from a self-concordant barrier. It introduces no new
barrier-specific API, so this file reuses the canonical owner directly instead of keeping a
duplicate wrapper theorem. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

end

/-! ### Theorem_5_3_10 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: let `x*(t)` be the exact minimizer of the penalty objective. Apply the
-- first-order optimality condition for `x*(t)` and compare it with an optimal solution `xOpt`
-- of the original linear problem on `closure dom`. The barrier inequality against the chord from
-- `x*(t)` to `xOpt`, together with `closure dom` as the closed feasible set, yields the estimate
-- `⟪c, x*(t)⟫ - ⟪c, xOpt⟫ ≤ ν / t`.
/-- For an exact central-path point at parameter `t > 0`, the objective gap to any optimal point
of the original linear problem on `closure dom` is at most `ν / t`. -/
theorem centralPathPoint_objectiveGap_le_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) := sorry

-- Proof sketch: compare the approximate center `x` with an exact penalty minimizer `xPath` at
-- the same parameter `t`. The approximate-centering hypothesis bounds the primal error
-- `t ⟪c, x - xPath⟫` by the Newton-decrement correction
-- `((β + √ν) β) / (1 - β)`, while
-- `centralPathPoint_objectiveGap_le_barrierParameter_div` controls the exact central-path gap
-- `⟪c, xPath⟫ - ⟪c, xOpt⟫` by `ν / t`. Adding the two bounds gives the stated estimate.
/-- Theorem 5.3.10: if `xPath` is an exact central-path point for the penalty objective
`z ↦ t ⟪c, z⟫ + F z` at some `t > 0`, and if another point `x` in `dom` satisfies the
approximate-centering condition
`‖t c + ∇ F(x)‖*ₓ ≤ β` with `β < 1`, then the objective gap from `x` to any optimal point
`xOpt ∈ closure dom` is bounded by
`(ν + ((β + √ν) β) / (1 - β)) / t`. In particular, the exact central-path gap is recovered by
the companion theorem above. -/
theorem centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (ht : 0 < (t : ℝ)) (hβ : β < 1)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := sorry

end

/-! ### Theorem_5_3_11 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The explicit logarithmic iteration bound obtained from the geometric lower estimate on the
path parameters in the proof of Theorem `5.3.11`. -/
abbrev barrierPathFollowingTerminationBound
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) : ℝ :=
  1 +
    ((β + Real.sqrt (ν : ℝ)) / γ) *
      Real.log
        (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) * referenceObjectiveNorm) /
          (γ * (1 - 2 * β)))

-- Proof sketch: unfold `barrierPathFollowingTerminationBound`.
/-- Expanding `barrierPathFollowingTerminationBound ν β γ ε h` gives the logarithmic complexity
expression obtained by solving the geometric lower bound for `tₖ` against the stopping threshold
`(5.3.29)`. -/
theorem barrierPathFollowingTerminationBound_def
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) :
    barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm =
      1 +
        ((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) *
                referenceObjectiveNorm) /
              (γ * (1 - 2 * β))) := sorry

-- Proof sketch: use the geometric lower bound `hgrowth` for the path parameters `tₖ` together
-- with the first-hit conditions `hcontinue` and `hstop` to show that the threshold `(5.3.29)` is
-- reached by the stated natural-ceiling index. For the accuracy claim, apply the objective-gap
-- estimate from Theorem `5.3.10` at the stopping iterate `x_N`, using the residual-centering
-- hypothesis `happrox_stop` and the threshold inequality `hstop`.
/-- Theorem 5.3.11: if a path-following sequence `(tₖ, xₖ)` for a `ν`-self-concordant barrier has
the geometric lower bound coming from the analytic center `x_F^*`, and if `N` is the first index
at which the stopping threshold `(5.3.29)` is reached while `x_N` is still `β`-centered, then
`N` is bounded by a logarithmic complexity estimate of order `O(√ν log (‖c‖*_{x_F^*} / ε))`;
moreover, the stopping iterate satisfies `⟪c, x_N⟫ - c^* ≤ ε`. -/
theorem pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) {β γ ε : ℝ}
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    (t : ℕ → ℝ) (x : ℕ → E)
    (mem_dom : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (hβ_half : β < 1 / 2)
    (hγ : 0 < γ)
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex →
        t k < barrierPathFollowingStoppingThreshold ν β ε)
    (hstop :
      barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xStar : E)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
                  hxStarH
                  ((InnerProductSpace.toDual ℝ E) c)) *
            (1 + γ / (β + Real.sqrt (ν : ℝ))) ^ (k - 1) ≤
          t k)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_dom stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    stopIndex ≤
        ⌈barrierPathFollowingTerminationBound ν β γ ε
          (HessianDualLocalNorm.ofDetNeZero F (xStar : E)
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
            ((InnerProductSpace.toDual ℝ E) c))⌉₊ ∧
      inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤ ε := sorry

end

/-! ### Theorem_5_3_12 (from Chap05) -/
open InnerProductSpace
open HessianDualLocalNorm
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.3.12 lies in the Chapter 5 auxiliary-central-path / analytic-center / local-dual-norm
domain.

Sampled owner declarations:
* `dualLocalNorm` in `Definition_5_0_20`, the chapter owner for the Hessian-metric dual local
  norm of a covector;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical domain-level bridge
  from positive-definite Hessians to that dual norm;
* `IsMinOn` as recalled in `Definition_5_3_3`, the neighboring chapter owner surface for analytic
  centers;
* `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner for the auxiliary central path;
* `dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial` in
  `Lemma_5_3_3`, the chapter bridge that bounds the iterate gradient norm by the analytic-center
  norm `‖∇ F(y₀)‖*_{x_F^*}`;
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the source-facing
  owner for the stopped intermediate Newton preprocessing method.

Best owner abstraction:
* source-facing: the stopping estimate for a
  `StoppedIntermediateSelfConcordantNewtonMethod`, stated with the auxiliary central path based at
  `y₀` and the analytic center `x_F^*` of the barrier;
* core/canonical: the stopped-method owner
  `StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ)` together with the dual local norm
  bridge `HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))`;
* bridge/view: the scalar logarithmic helper obtained by abstracting the dual norm and the
  auxiliary decay profile to scalar data.

Primitive data:
* the stopped intermediate Newton method;
* the auxiliary central path `yStar`;
* the analytic center `xFStar`;
* the discrete auxiliary-path parameters `t`;
* the positive-definite-Hessian owner on `dom`, used to form the dual local norm at `xFStar`;
* the positive complexity parameters `γ` and `β + √ν`;
* the exponential decay estimate for `t`;
* the comparison bound of the iterate decrement by the auxiliary-central-path residual norm.

Derived API:
* the stopping index `method.stopIndex`;
* the ordinary Newton decrement `method.decrement k`;
* the logarithmic stopping bound built from the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}`.

This file therefore keeps the stopped-method owner, the auxiliary central path, and the
analytic-center hypothesis on the public surface, while demoting only the scalar logarithmic
estimate to a private proof helper. -/

section

variable {dom : Set E} {F : E → ℝ} {ν : NNReal} [IsSelfConcordantBarrierOnWith dom ν F]
variable {y0 : dom} {β γ : ℝ}

-- Proof sketch: use the positivity of `γ` and `β + √ν` so that the exponential decay rate and the
-- logarithmic denominator have their textbook sign, then combine the exponential decay estimate
-- for `t_k` with the bound
-- `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` for a scalar reference norm `R`.
-- Since `method` stops when the ordinary Newton decrement drops below `β + γ`, solving the
-- resulting scalar inequality for `k` yields the stated natural-ceiling bound.
/-- Auxiliary scalarized stopping estimate: if an auxiliary path-following scheme satisfies the
generic decrement bound `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` and the geometric decay estimate for
`t_k`, then the stopping index is bounded by the corresponding logarithmic expression in `R`. -/
private theorem stopIndex_le_natCeil_of_referenceDualNorm
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    (t : ℕ → ℝ)
    (referenceDualNorm : ℝ)
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        t k ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + t k * (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm)) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) / γ)⌉₊ := sorry

-- Proof sketch: apply the auxiliary-central-path gradient estimate from `Lemma_5_3_3` at the
-- path points `yStar (t k)` and the analytic center `xFStar`, turning the source-facing
-- decrement comparison into the scalar bound required by
-- `stopIndex_le_natCeil_of_referenceDualNorm`. The logarithmic stopping estimate then follows
-- with the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}` on the theorem surface.
/-- Theorem 5.3.12: let `x_F^*` be an analytic center of a `ν`-self-concordant barrier `F`, and
let `y*(t)` be the auxiliary central path based at `y₀`. If a stopped intermediate Newton method
started at `y₀` has decrement bounded along the iterates by
`β + ‖∇ F(y*(t_k))‖*_{y*(t_k)}` for a nonnegative parameter sequence `t_k` that decays like
`exp (-γ k / (β + √ν))`, then the stopping index is at most
`⌈((β + √ν) / γ) log (((ν + 2 √ν) ‖∇ F(y₀)‖*_{x_F^*}) / γ)⌉₊`, provided `γ > 0` and
`β + √ν > 0`. -/
theorem auxiliaryPathFollowing_stopIndex_le_natCeil_terminationBound
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    [HasPositiveDefiniteHessianOn dom F]
    (yStar : Set.Ici (0 : ℝ) → dom)
    (xFStar : dom)
    (hxFStar : IsMinOn F dom (xFStar : E))
    (hpath : IsCentralPath dom (-∇ F (y0 : E)) F yStar)
    (t : ℕ → Set.Ici (0 : ℝ))
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        (t k : ℝ) ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E)))) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
                ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))) / γ)⌉₊ := by
  let referenceDualNorm := ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))
  refine
    stopIndex_le_natCeil_of_referenceDualNorm
      method
      (fun k ↦ (t k : ℝ))
      referenceDualNorm
      hγ hβsqrt ht ?_
  intro k
  calc
    method.decrement k ≤
        β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E))) :=
      hdecrement k
    _ ≤
        β + (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) * (t k : ℝ) := by
      let hF : IsSelfConcordantBarrierOnWith dom ν F := inferInstance
      gcongr
      simpa [referenceDualNorm] using
        hF.dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial
          y0 yStar xFStar hxFStar hpath (t k)
    _ =
        β +
          (t k : ℝ) *
            (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) := by
      ring

end

end
