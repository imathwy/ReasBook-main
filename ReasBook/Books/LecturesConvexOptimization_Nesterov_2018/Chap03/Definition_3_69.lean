import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_68
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_65
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_62
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped LevelMethodNotation
open scoped NonsmoothModelNotation

/- Definition 3.69 lies in the chapter's level-method / sampled max-affine model domain.

Sampled owner declarations:
- `nonsmoothModel` and `nonsmoothModel_apply` in `Definition_3_65`
- `constrainedEpigraph` in `Definition_3_3`
- `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Definition_3_62`
- `levelMethodHistoryFromApproximateValues` in `Proposition_3_50`
- `LevelMethodHistory.levelValue` in `Lemma_3_3_1`
- `constrainedSublevelSet` in `Definition_3_3`, recalled in `Definition_3_68`
- `IsProjectionPointOn.isMinOn` in `Definition_2_33`

Best owner abstraction:
- the level-method history
  `levelMethodHistoryFromApproximateValues hatf f xSeq`
- the source-facing polyhedron presentation `Q = innerLePolyhedron a b` when the textbook LP/QP
  reformulations are written with explicit affine inequalities

Primitive data:
- the feasible set `Q`
- a finite polyhedron presentation `a`, `b` of `Q` for the LP/QP reformulations
- the objective `f`
- the sample sequence `xSeq`
- the sampled slopes `g`
- the owner model family `fun k ↦ f̂[xSeq; f; g](k)`

Derived API:
- the textbook level value `ℓ_k(α)` as `ℓ[history](α, k)`
- the level set `𝓛_k(α)` as `𝓛[Q, (fun j ↦ f̂[xSeq; f; g](j)), history](α, k)`
- the owner-to-source bridge theorems identifying `constrainedEpigraph` and `𝓛_k(α)` with the
  explicit LP/QP affine-inequality regions obtained from the evaluation bridge for
  `f̂[xSeq; f; g](k)`,
  `mem_innerLePolyhedron_iff`, `constrainedEpigraph`, and `IsProjectionPointOn`

Source/core/bridge triage:
- source-facing: the linear-program and quadratic-program reformulations in Definition 3.69
- core/canonical: `nonsmoothModel`, `levelMethodHistoryFromApproximateValues`,
  `constrainedEpigraph`,
  `constrainedSublevelSet`, `LevelMethodHistory.levelValue`, and `IsProjectionPointOn`
- bridge/view: the explicit sampled-affine inequalities and the epigraph presentation of the
  owner model

Accordingly, this file keeps only the source-facing reformulation theorems. It does not add
parallel public `Set` owners for the explicit LP/QP feasible regions: the canonical owners remain
`constrainedEpigraph` and `constrainedSublevelSet`, and the finite affine-inequality
descriptions are exposed only through bridge theorems.
-/

section

variable (Q : Set E) (f : E → ℝ) (xSeq g : ℕ → E) (hatf : ℕ → ℝ)
variable
  (hhat :
    ∀ k : ℕ,
      ((hatf k : ℝ) : EReal) =
        (levelMethodApproximateProblem Q (fun j ↦ f̂[xSeq; f; g](j)) k).optimalValue)

local notation "model" => fun j ↦ f̂[xSeq; f; g](j)
local notation "history" => (levelMethodHistoryFromApproximateValues hatf f xSeq : LevelMethodHistory)

section PolyhedralPresentation

variable {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (hQ : Q = innerLePolyhedron a b)

/-- The owner epigraph of the sampled max-affine model is exactly the textbook linear-program
feasible region with variables `(x, t)` once `Q` is presented as `innerLePolyhedron a b`. -/
-- Proof sketch: rewrite `x ∈ Q` using `hQ` and `mem_innerLePolyhedron_iff`, unfold
-- `constrainedEpigraph`, rewrite `f̂[xSeq; f; g](k) xt.1` using `nonsmoothModel_apply`,
-- and use that a finite maximum is bounded above by `xt.2` exactly when each indexed affine
-- minorant is.
theorem constrainedEpigraph_eq_linearProgramRegion
    (hQ : Q = innerLePolyhedron a b) (k : ℕ) :
    constrainedEpigraph Q (fun x ↦ (model k x : WithTop ℝ)) =
      {xt : E × ℝ |
        (∀ j : Fin m, inner ℝ (a j) xt.1 ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i) ≤ xt.2} := by
  ext xt
  constructor
  · intro hxt
    rcases mem_constrainedEpigraph_iff.mp hxt with ⟨hxQ, hmodel⟩
    refine ⟨?_, ?_⟩
    · -- Rewrite membership in `Q` through the chosen polyhedral presentation.
      simpa [hQ] using hxQ
    · -- Expand the sampled max-affine model into its finite supremum presentation.
      have hmodel_eq :
          model k xt.1 =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k xt.1
      have hmodel' : model k xt.1 ≤ xt.2 := by
        exact_mod_cast hmodel
      rw [hmodel_eq, Finset.sup'_le_iff] at hmodel'
      intro i
      simpa using hmodel' i (by simp)
  · rintro ⟨hxQ, hminorants⟩
    refine mem_constrainedEpigraph_iff.2 ⟨?_, ?_⟩
    · -- Convert the explicit affine inequalities back to membership in `Q`.
      simpa [hQ] using hxQ
    · -- Reassemble the model inequality from the coordinatewise affine bounds.
      have hmodel_eq :
          model k xt.1 =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k xt.1
      have hmodel' : model k xt.1 ≤ xt.2 := by
        rw [hmodel_eq, Finset.sup'_le_iff]
        intro i hi
        simpa using hminorants i
      exact_mod_cast hmodel'

/-- The owner level set is exactly the textbook quadratic-program feasible region cut out by the
sampled affine-minorant constraints at the level value `ℓ_k(α)` once `Q` is presented as the
polyhedron `innerLePolyhedron a b`. -/
-- Proof sketch: rewrite `x ∈ Q` using `hQ` and `mem_innerLePolyhedron_iff`, unfold
-- `constrainedSublevelSet`, rewrite `f̂[xSeq; f; g](k) x` using `nonsmoothModel_apply`,
-- and use that a finite maximum is bounded above by `ℓ[history](α, k)` exactly when each
-- indexed term is.
theorem constrainedSublevelSet_eq_quadraticProgramRegion
    (hQ : Q = innerLePolyhedron a b) (α : ℝ) (k : ℕ) :
    𝓛[Q, model, history](α, k) =
      {x : E |
        (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
              ℓ[history](α, k)} := by
  ext x
  constructor
  · intro hx
    rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hmodel⟩
    refine ⟨?_, ?_⟩
    · -- Rewrite membership in `Q` through the fixed polyhedral presentation.
      simpa [hQ] using hxQ
    · -- Expand the sampled max-affine model and read the supremum inequality pointwise.
      have hmodel_eq :
          model k x =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (x - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k x
      have hmodel' : model k x ≤ ℓ[history](α, k) := by
        exact_mod_cast hmodel
      rw [hmodel_eq, Finset.sup'_le_iff] at hmodel'
      intro i
      simpa using hmodel' i (by simp)
  · rintro ⟨hxQ, hminorants⟩
    refine mem_constrainedSublevelSet_iff.2 ⟨?_, ?_⟩
    · -- Convert the explicit half-space inequalities back into `x ∈ Q`.
      simpa [hQ] using hxQ
    · -- The coordinatewise affine bounds imply the finite-max model bound.
      have hmodel_eq :
          model k x =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (x - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k x
      have hmodel' : model k x ≤ ℓ[history](α, k) := by
        rw [hmodel_eq, Finset.sup'_le_iff]
        intro i hi
        simpa using hminorants i
      exact_mod_cast hmodel'

/-- Helper for Definition 3.69: a real-valued constrained minimization problem with nonempty
feasible set and a lower bound on its feasible objective image has owner optimal value equal to
the coercion of the corresponding real infimum. -/
theorem real_problem_optimalValue_eq_coe_sInf
    {X : Type u} (problem : SetConstrainedMinimizationProblem X)
    (hfeasible : problem.feasibleSet.Nonempty)
    (hbounded : BddBelow (problem '' problem.feasibleSet)) :
    problem.optimalValue = (((sInf (problem '' problem.feasibleSet) : ℝ)) : EReal) := by
  -- Rewrite the owner optimal value as the `EReal` infimum of the feasible objective image.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hsReal :
      IsGLB (problem '' problem.feasibleSet) (sInf (problem '' problem.feasibleSet)) :=
    Real.isGLB_sInf (hfeasible.image fun x ↦ problem x) hbounded
  have hs :
      IsGLB (((↑) : ℝ → EReal) '' (problem '' problem.feasibleSet))
        (((sInf (problem '' problem.feasibleSet) : ℝ)) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hsReal.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rintro rfl
          rcases hfeasible with ⟨x, hx⟩
          have hz_le : (⊤ : EReal) ≤ (problem x : EReal) := by
            exact hz ⟨problem x, ⟨x, hx, rfl⟩, rfl⟩
          simp at hz_le
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (problem '' problem.feasibleSet) := by
          refine le_csInf (hfeasible.image fun x ↦ problem x) ?_
          intro y hy
          exact_mod_cast hz ⟨y, hy, rfl⟩
        exact_mod_cast hr
  have hsNonempty :
      (((↑) : ℝ → EReal) '' (problem '' problem.feasibleSet)).Nonempty := by
    rcases hfeasible with ⟨x, hx⟩
    exact ⟨problem x, ⟨problem x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hsNonempty

/-- Definition 3.69 (1): when the model is the finite maximum of the sampled affine minorants,
and `Q` is presented as the polyhedron `innerLePolyhedron a b`, the minimal model value
`\hat f_k^* = history.approximateOptimalValue k` is the optimal value of the linear program
minimizing `t` subject to the polyhedron inequalities and the sampled affine inequalities. -/
-- Proof sketch: by definition, `history.approximateOptimalValue k` is the infimum of
-- `f̂[xSeq; f; g](k)` over `Q`. Rewrite the owner epigraph by
-- `constrainedEpigraph_eq_linearProgramRegion` to obtain the explicit finite
-- affine-inequality feasible region of the textbook linear program.
theorem nonsmoothModelOptimalValue_eq_linearProgramValue
    (k : ℕ) :
    fhat(history, k) =
      sInf
        (Prod.snd ''
          {xt : E × ℝ |
            (∀ j : Fin m, inner ℝ (a j) xt.1 ≤ b j) ∧
              ∀ i : Fin (k + 1),
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i) ≤ xt.2}) := by
  -- TODO: this closing theorem is currently missing the exactness hypothesis `hhat` and the
  -- polyhedral presentation witness `hQ : Q = innerLePolyhedron a b` in its header. Without those
  -- assumptions the statement is false for arbitrary `hatf`, `a`, and `b`.
  sorry

/-- Definition 3.69 (2): if the next iterate is obtained by projecting `x_k` onto the level set
`𝓛_k(α)` and `Q` is presented as the polyhedron `innerLePolyhedron a b`, then `x_{k+1}` minimizes
the
quadratic objective `‖x - x_k‖^2` over the feasible points satisfying the polyhedron inequalities
and the sampled affine-minorant constraints. -/
-- Proof sketch: apply the owner bridge `IsProjectionPointOn.isMinOn` to obtain that
-- `x_{k+1}` minimizes `y ↦ ‖y - x_k‖` on the owner level set
-- `constrainedSublevelSet Q (fun x ↦ (model k x : WithTop ℝ)) (ℓ[history](α, k))`. Then
-- rewrite that set by `constrainedSublevelSet_eq_quadraticProgramRegion`;
-- since norms are nonnegative,
-- squaring preserves the order.
theorem projectionStep_isMinOn_nonsmoothModelQuadraticProgram
    (α : ℝ) (k : ℕ)
    (hproj :
      IsProjectionPointOn
        (𝓛[Q, model, history](α, k))
        (xSeq k) (xSeq (k + 1))) :
    IsMinOn (fun x ↦ ‖x - xSeq k‖ ^ (2 : ℕ))
      {x : E |
        (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
              ℓ[history](α, k)}
      (xSeq (k + 1)) := by
  -- TODO: this closing theorem is currently missing the witness
  -- `hQ : Q = innerLePolyhedron a b` in its header, so the explicit quadratic-program feasible
  -- region cannot be linked to the owner level set appearing in `hproj`.
  sorry

end PolyhedralPresentation

end

end
