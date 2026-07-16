import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Lemma_3_1_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_1_5_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_23
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_27
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_6
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Text_6_1_1_Conjugate_Closedness_and_Domain_Nonemptiness

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 5.1.6 lies in the chapter's Fenchel-duality / self-concordance domain.

Primary domain:
- Fenchel conjugates of `WithTop ℝ`-valued functions whose finite real part is self-concordant on
  its effective domain, with the closedness of its constrained epigraph supplied separately from
  the self-concordance owner.

Sampled owner declarations before refinement:
- `fenchelDual` / notation `f⋆` in `Chap05/Definition_5_0_27`, the source-facing Fenchel-dual
  owner;
- `IsSelfConcordantOn` in `Chap05/Definition_5_1_1`, the chapter owner for self-concordance on a
  domain;
- `HasPositiveDefiniteHessianOn` in `Chap05/Definition_5_0_23`, the chapter owner for positive
  definiteness of the Hessian on a domain;
- `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line` in `Chap05/Theorem_5_1_6`,
  the canonical bridge from self-concordance plus closed constrained epigraph to positive
  definiteness of the Hessian;
- `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y`.

Best owner abstraction:
- source-facing: the self-concordant standing assumptions on the primal owner
  `f : E → WithTop ℝ` and the resulting properties of `f⋆`;
- core/canonical: `dom f`, `withTopRealPart f`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, and
  `effectiveEpigraph (f⋆)`;
- bridge/view: the gradient image `∇ (withTopRealPart f) '' dom f`.

Primitive data:
- the primal owner `f : E → WithTop ℝ`;
- closedness of the constrained epigraph of the finite real part `withTopRealPart f` on `dom f`;
- self-concordance of `withTopRealPart f` on `dom f`;
- the no-affine-line standing assumption used in the source discussion.

Derived API in this file:
- the singleton-subdifferential and gradient-recovery lemmas on `dom f`;
- existence of Fenchel-support maximizers on `dom f` for points of `dom (f⋆)`;
- the source-facing identity `dom (f⋆) = {∇ f(x) | x ∈ dom f}`;
- the source-level openness consequence for `dom (f⋆)`.
- the positive-definite Hessian owner `HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)`,
  derived internally from `hself`, the closed constrained epigraph hypothesis, and the
  no-affine-line hypothesis via
  `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line`.

Closedness of `effectiveEpigraph (f⋆)` and convexity of `extendedRealRealPart (f⋆)` already
live as unconditional canonical owners in
`Chap06/Text_6_1_1_Conjugate_Closedness_and_Domain_Nonemptiness`;
they are reused directly rather than re-exported here under stronger self-concordant hypotheses.

This refinement deletes the local `IsLegendreFunction` wrapper introduced in the previous round.
The source item is not defining a new owner-level Legendre class; it is proving properties of the
canonical Fenchel dual under the chapter's standing self-concordant assumptions. The public API
therefore stays on the existing chapter owners `constrainedEpigraph`, `IsSelfConcordantOn`,
`HasPositiveDefiniteHessianOn`, `f⋆`, `dom`, and `effectiveEpigraph`, with the gradient-image
formula exposed as the bridge statement rather than as a replacement owner. -/

omit [CompleteSpace E] in
/-- A Fenchel-support maximizer yields the corresponding subgradient on the effective domain. -/
theorem subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn
    {f : E → WithTop ℝ} {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    s ∈ ∂ f(x) := by
  refine mem_subdifferential_iff.2 ⟨hx, ?_⟩
  intro y hy
  have hsupport : inner ℝ s y - withTopRealPart f y ≤ inner ℝ s x - withTopRealPart f x :=
    hmax hy
  have hsupport' :
      withTopRealPart f x + inner ℝ s (y - x) ≤ withTopRealPart f y := by
    have hsupport'' :
        withTopRealPart f x + (inner ℝ s y - inner ℝ s x) ≤ withTopRealPart f y := by
      linarith
    simpa [inner_sub_right] using hsupport''
  rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx]
  exact_mod_cast hsupport'

section SelfConcordantPrimal

variable {f : E → WithTop ℝ}
variable (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))

include hself

/-- For a self-concordant primal function, the subdifferential at a finite point is
the singleton consisting of the primal gradient. -/
theorem subdifferential_eq_singleton_gradient_of_selfConcordant
    {x : E} (hx : x ∈ dom f) :
    ∂ f(x) = {∇ (withTopRealPart f) x} := by
  rcases hself with ⟨Mf, hMf⟩
  have hxin : x ∈ interior (dom f) := by
    rwa [hMf.isOpen_domain.interior_eq]
  have hfd : DifferentiableAt ℝ (withTopRealPart f) x := by
    exact
      (hMf.contDiffOn.contDiffAt (hMf.isOpen_domain.mem_nhds hx)).differentiableAt
        (by norm_num)
  exact subdifferential_eq_singleton_gradient hMf.convexOn hxin hfd

/-- At a Fenchel-support maximizer of a self-concordant function, the primal
gradient recovers the dual slope. -/
theorem gradient_eq_of_fenchelSupport_isMaxOn
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    ∇ (withTopRealPart f) x = s := by
  have hsub : s ∈ ∂ f(x) :=
    subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn hx hmax
  have hs_mem : s ∈ ({∇ (withTopRealPart f) x} : Set E) := by
    simpa [subdifferential_eq_singleton_gradient_of_selfConcordant hself hx] using hsub
  have hs : s = ∇ (withTopRealPart f) x := by
    simpa using hs_mem
  exact hs.symm

/-- Every gradient vector of the primal finite real part lies in the effective domain of the
Fenchel dual. -/
theorem image_gradient_subset_dom_fenchelDual_of_selfConcordant
    : ∇ (withTopRealPart f) '' dom f ⊆ dom (f⋆) := by
  rintro s ⟨x, hx, rfl⟩
  have hsingleton : ∂ f(x) = {∇ (withTopRealPart f) x} :=
    subdifferential_eq_singleton_gradient_of_selfConcordant hself hx
  have hgrad_mem : ∇ (withTopRealPart f) x ∈ ∂ f(x) := by
    simp [hsingleton]
  exact subdifferential_subset_dom_fenchelDual hgrad_mem

end SelfConcordantPrimal

section StandingAssumptions

variable {f : E → WithTop ℝ}
variable
  (hclosed :
    IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
variable (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
variable
  (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)

include hclosed hself hnoAffineLine

/-- Under the standing assumptions of Section 5.1.5, every finite dual point admits a
Fenchel-support maximizer on the primal effective domain. -/
theorem exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
    {s : E} (hs : s ∈ dom (f⋆)) :
    ∃ x, x ∈ dom f ∧
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x := by
  letI : HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) :=
    IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line hself
      hclosed hnoAffineLine
  sorry

/-- Under the standing self-concordant hypotheses, every finite dual point belongs to the
gradient image of the primal effective domain. -/
theorem dom_fenchelDual_subset_image_gradient_of_selfConcordant
    : dom (f⋆) ⊆ ∇ (withTopRealPart f) '' dom f := by
  intro s hs
  obtain ⟨x, hx, hmax⟩ :=
    exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
      hclosed hself hnoAffineLine hs
  have hgrad :
      ∇ (withTopRealPart f) x = s :=
    gradient_eq_of_fenchelSupport_isMaxOn hself hx hmax
  refine ⟨x, hx, ?_⟩
  simpa using hgrad

/-- Lemma 5.1.6: under the standing self-concordant assumptions of Section 5.1.5, the effective
domain of the Fenchel dual is exactly the gradient image of the primal effective domain. -/
theorem dom_fenchelDual_eq_image_gradient_of_selfConcordant
    : dom (f⋆) = ∇ (withTopRealPart f) '' dom f := by
  refine Set.Subset.antisymm
    (dom_fenchelDual_subset_image_gradient_of_selfConcordant hclosed hself hnoAffineLine)
    (image_gradient_subset_dom_fenchelDual_of_selfConcordant hself)

/-- Under the standing self-concordant assumptions, the effective domain of the Fenchel dual is
open. -/
theorem isOpen_dom_fenchelDual_of_selfConcordant
    : IsOpen (dom (f⋆)) := by
  letI : HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) :=
    IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line hself
      hclosed hnoAffineLine
  sorry

end StandingAssumptions

end
