import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_6_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4

noncomputable section

open Bornology
open Filter
open Function
open scoped Gradient PolarCone RealInnerProductSpace Rockafellar

universe u v
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

section

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type u} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]
variable {f : E → WithTopBot 𝕜}

/- Theorem 6.27.1: the summary theorem on minima of a closed proper convex function is split into
atomic clause-level declarations below. Clauses `(1)` and `(2)` are the `y = 0` specialization of
the chapter conjugate formula, so their public surface belongs to the weaker pairing-valued
`WithTopBot` layer rather than to the later closed/proper/convex Euclidean specialization. -/

-- Proof sketch: this is the origin specialization of the Fenchel conjugate infimum formula
-- `convexConjugate_eq_neg_iInf_sub_pairing`.
/-- Theorem 6.27.1 (1), clause (a): the infimum of `f` is the negative of the value of its
Fenchel conjugate at the dual-side origin. -/
theorem infimum_eq_neg_convexConjugate_zero
    :
    (⨅ x : E, f x) = -(f⋆ (0 : Y)) := sorry

-- Proof sketch: combine the infimum formula from clause `(a)` with the defining description
-- `0 ∈ dom(f⋆) ↔ f⋆ 0 < ⊤`, then rewrite a real lower bound on `f` as finiteness of `f⋆ 0`.
/-- Theorem 6.27.1 (2), clause (a): `f` is bounded below exactly when the dual-side origin
belongs to the effective domain of its conjugate. -/
theorem boundedBelow_iff_zero_mem_effectiveDomain_convexConjugate
    :
    (∃ a : 𝕜, ∀ x : E, (a : WithTopBot 𝕜) ≤ f x) ↔
      (0 : Y) ∈ dom(f⋆) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type u} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [HasLinearPairing E Y ℝ] [HasPairing Y E ℝ]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: apply the Fenchel-Young subgradient equivalence at the dual base point `0`; the
-- zero-subgradient criterion for a minimum is exactly `argmin(f)`-membership.
/-- Theorem 6.27.1 (3), clause (b): `argmin(f)` is the pairing-level subdifferential
of `f⋆` at the origin. -/
theorem minimumSet_eq_subdifferentialAt_convexConjugate_zero
    :
    argmin(f) = (∂[E]f⋆((0 : Y))) := sorry

-- Proof sketch: rewrite attainment of the infimum as nonemptiness of `argmin(f)`, then use the
-- set identity from the previous clause.
/-- Theorem 6.27.1 (4), clause (b): the infimum of `f` is attained exactly when `f⋆` is
subdifferentiable at the origin. -/
theorem minimumSet_nonempty_iff_subdifferentialAt_convexConjugate_zero_nonempty
    :
    (argmin(f)).Nonempty ↔
      (∂[E]f⋆((0 : Y))).Nonempty := sorry

-- Proof sketch: this is the singleton refinement of the set identity in clause `(3)`, kept on the
-- pairing-level subdifferential owner without any inner-product bridge.
/-- Clause `(e)`, pairing-primary form: `argmin(f)` is a singleton exactly when the
subdifferential of `f⋆` at the origin is that singleton. -/
theorem minimumSet_eq_singleton_iff_subdifferentialAt_convexConjugate_zero_eq_singleton
    (x : E) :
    argmin(f) = {x} ↔
      (∂[E]f⋆((0 : Y))) = {x} := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E Y ℝ] [HasPairing Y E ℝ]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: specialize the Chapter 13 relative-interior criterion for `dom(f⋆)` to `x⋆ = 0`
-- and translate the positivity condition into existence of a minimizer.
/-- Theorem 6.27.1 (5), clause (b): if the origin lies in the relative interior of `dom(f⋆)`,
then `argmin(f)` is nonempty. -/
theorem zero_mem_riDom_convexConjugate_imp_minimumSet_nonempty
    (h0 : (0 : Y) ∈ riDom(f⋆)) :
    (argmin(f)).Nonempty := sorry

-- Proof sketch: combine the relative-interior characterization at the origin with the recession
-- direction owner from Definition 6.27.4 and identify the zero-value directions with the
-- constancy directions of `f`.
/-- Theorem 6.27.1 (6), clause (b): the origin lies in `ri(dom(f⋆))` exactly when every recession
direction of `f` lies in the function lineality space `lineal f`. -/
theorem zero_mem_riDom_convexConjugate_iff_recessionDirections_are_constancyDirections
    :
    (0 : Y) ∈ riDom(f⋆) ↔
      ∀ y : E, f.RecedesInDirection ℝ y → y ∈ lineal f := sorry

-- Proof sketch: finite but unattained infimum is equivalent to finite conjugate value at `0`
-- together with failure of subdifferential nonemptiness there; Theorem 23.2 translates that
-- failure into a direction where the directional derivative drops to `⊥ = -∞`.
/-- Theorem 6.27.1 (7), clause (c): the infimum of `f` is finite and unattained exactly when
`f⋆ 0` is finite and the directional derivative of `f⋆` at `0` is `-∞` in some direction. -/
theorem
    finiteInfimum_unattained_iff_convexConjugate_zero_finite_and_exists_bot_directionalDerivative
    :
    (⊥ < (⨅ x : E, f x) ∧ (⨅ x : E, f x) < ⊤ ∧ argmin(f) = ∅) ↔
      (f⋆ (0 : Y) < ⊤ ∧
        ∃ y : Y, directionalDerivativeAt (f⋆) (0 : Y) y = ⊥) :=
  sorry

-- Proof sketch: bounded attainment implies the ambient-interior criterion in clause `(d')`,
-- and ambient interior always lies in intrinsic interior.
/-- Theorem 6.27.1 (8), clause (d), intrinsic-primary form: if `argmin(f)` is
nonempty and bounded, then the origin belongs to `riDom(f⋆)`. -/
theorem minimumSet_nonempty_bounded_imp_zero_mem_riDom_convexConjugate
    (hmin : (argmin(f)).Nonempty ∧ IsBounded (argmin(f))) :
    (0 : Y) ∈ riDom(f⋆) := sorry

-- Proof sketch: combine the `argmin(f)`/subdifferential identification with the Chapter 14
-- interior-domain boundedness criterion and the Section 27 minimum-set existence theorem.
/-- Clause `(d')`, ambient strengthening used downstream: `argmin(f)` is nonempty and
bounded exactly when the origin lies in the ambient interior of `dom(f⋆)`. -/
theorem minimumSet_nonempty_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate
    :
    (argmin(f)).Nonempty ∧ IsBounded (argmin(f)) ↔
      (0 : Y) ∈ interior dom(f⋆) := sorry

-- Proof sketch: use the ambient interior-domain characterization of bounded sublevel sets
-- together with the source-facing recession-direction owner from Definition 6.27.4.
/-- Clause `(d')`, ambient no-recession reformulation: `0 ∈ int(dom(f⋆))` exactly when `f`
has no direction of recession. -/
theorem zero_mem_interior_effectiveDomain_convexConjugate_iff_no_recessionDirections
    :
    (0 : Y) ∈ interior dom(f⋆) ↔
      ¬ ∃ y : E, f.RecedesInDirection ℝ y := sorry

-- Proof sketch: first move from the no-recession condition to ambient interior via the previous
-- theorem, then pass to relative interior through `interior_subset_intrinsicInterior`.
/-- Clause `(d')`, intrinsic-primary consequence: if `f` has no recession direction, then the
dual-side origin belongs to `riDom(f⋆)`. -/
theorem no_recessionDirections_imp_zero_mem_riDom_convexConjugate
    (hno : ¬ ∃ y : E, f.RecedesInDirection ℝ y) :
    (0 : Y) ∈ riDom(f⋆) := by
  have h0int : (0 : Y) ∈ interior dom(f⋆) :=
    (zero_mem_interior_effectiveDomain_convexConjugate_iff_no_recessionDirections
      (f := f)).2 hno
  exact interior_subset_intrinsicInterior (𝕜 := ℝ) h0int

-- Proof sketch: Theorem 8.7 identifies the recession cone of each nonempty real sublevel set
-- with the common owner `recessionCone (f0⁺)`, so any two nonempty real sublevel sets
-- have the same recession cone.
/-- Theorem 6.27.1 (11), clause (f): any two nonempty real sublevel sets of `f` have the same
recession cone, namely the recession cone of `f`. -/
theorem recessionCone_sublevelSet_eq_recessionCone_sublevelSet
    {α β : ℝ}
    (hα_nonempty : {x : E | f x ≤ (α : WithTopBot ℝ)}.Nonempty)
    (hβ_nonempty : {x : E | f x ≤ (β : WithTopBot ℝ)}.Nonempty) :
    0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} =
      0⁺[ℝ] {x : E | f x ≤ (β : WithTopBot ℝ)} := sorry

-- Proof sketch: combine the common-cone identification from Theorem 8.7 with the Chapter 14 owner
-- theorem for the polar of the generated cone of `dom(f⋆)`, then use biconjugacy to rewrite the
-- resulting recession cone of `(f⋆)⋆` back to the recession cone of `f`.
/-- Theorem 6.27.1 (12), clause (f): every nonempty real sublevel set of `f` has recession cone
equal to the recession cone of `f`, and this common cone is the polar of the convex cone
generated by `dom(f⋆)`. -/
theorem
    recessionCone_sublevelSet_eq_recessionCone_and_polarCone_cone_dom_convexConjugate
    [HasLinearPairing Y E ℝ]
    (α : ℝ)
    (hα_nonempty : {x : E | f x ≤ (α : WithTopBot ℝ)}.Nonempty) :
    0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} = recessionCone (f₀⁺) ∧
      0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} =
        ((cone[ℝ] dom(f⋆))ᵒ[ℝ] : Set E) := sorry

-- Proof sketch: shift the zero-sublevel support-function theorem from Chapter 13 by the level
-- parameter `α`, so that the `α`-sublevel set of `f` becomes the zero sublevel set of
-- `x ↦ f x - α`.
/-- Theorem 6.27.1 (13), clause (g): for each real `α`, the support function of the `α`-sublevel
set of `f` is the closure `cl(·)` of the positively homogeneous convex function generated by
`f⋆ + α`. -/
theorem supportFunction_sublevelSet_eq_closure_sublinearHull_convexConjugate_add
    (α : ℝ) :
    (δᵛ[WithTopBot ℝ](· | {x : E | f x ≤ (α : WithTopBot ℝ)})) =
      cl(sublinearHull fun xStar : Y ↦ f⋆ xStar + (α : WithTopBot ℝ)) :=
  sorry

-- Proof sketch: after normalizing by the infimum value, `argmin(f)` is the zero sublevel set
-- of the translated function, and the first part of clause `(h)` reduces its support function to
-- the closure of the directional-derivative profile of `f⋆` at the origin.
/-- Theorem 6.27.1 (14), clause (g): if `f` is bounded below, the support function of `argmin(f)`
is the closure `cl(·)` of the directional-derivative function of `f⋆` at the origin. -/
theorem supportFunction_minimumSet_eq_closure_directionalDerivativeAt_convexConjugate_zero
    (hboundedBelow : ∃ a : ℝ, ∀ x : E, (a : WithTopBot ℝ) ≤ f x) :
    (δᵛ[WithTopBot ℝ](· | argmin(f))) =
      cl(directionalDerivativeAt (f⋆) (0 : Y)) :=
  sorry

-- Proof sketch: rewrite the approaching level `α ↓ inf f` as the positive parameter
-- `ε ↓ 0` in the translated sublevel family `{x | f x ≤ inf f + ε}`, then apply the support
-- function formula from clause `(h)` and pass to the limit.
/-- Theorem 6.27.1 (15), clause (h): if the infimum of `f` is finite, then the support functions
of the sublevel sets `{x | f x ≤ inf f + ε}` converge as `ε ↓ 0` to the directional derivative of
`f⋆` at the origin. -/
theorem tendsto_supportFunction_sublevelSet_to_directionalDerivativeAt_convexConjugate_zero
    (hfiniteInf : (⊥ : WithTopBot ℝ) < (⨅ x : E, f x) ∧ (⨅ x : E, f x) < ⊤)
    (y : Y) :
    Tendsto
      (fun ε : ℝ ↦ δᵛ[WithTopBot ℝ](y | {x : E | f x ≤ (⨅ z : E, f z) + ε}))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (directionalDerivativeAt (f⋆) (0 : Y) y)) := sorry

-- Proof sketch: specialize the Chapter 13 closure criterion for `dom(f⋆)` to `x⋆ = 0`, where the
-- translated recession function is just the recession function of `f` itself.
/-- Theorem 6.27.1 (16), clause (i): the origin lies in the closure of `dom(f⋆)` exactly when the
recession function of `f` is nonnegative in every direction. -/
theorem zero_mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction
    :
    (0 : Y) ∈ closure (dom(f⋆)) ↔
      ∀ y : E, 0 ≤ recessionFunction f y := sorry

-- Proof sketch: negate the closure criterion from the previous clause and use the directional
-- recession owner to rewrite strict negativity of the recession function as a uniform affine
-- descent estimate along one nonzero ray direction.
/-- Theorem 6.27.1 (17), clause (i): the origin fails to belong to `cl(dom(f⋆))` exactly when
there is a nonzero direction along which `f` decreases at a uniform positive linear rate on every
forward ray from `dom(f)`. -/
theorem zero_not_mem_closure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction
    :
    (0 : Y) ∉ closure (dom(f⋆)) ↔
      ∃ y : E, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ dom(f),
          f (x + t • y) ≤ f x - (t * ε : WithTopBot ℝ) := sorry

-- Proof sketch: in finite-dimensional real normed spaces, intrinsic closure equals ambient
-- closure, so clause `(i)` is unchanged when rewritten on `intrinsicClosure`.
/-- Clause `(i)`, intrinsic-topology form: the origin belongs to `intrinsicClosure ℝ (dom(f⋆))`
exactly when the recession function of `f` is nonnegative in every direction. -/
theorem zero_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction
    [FiniteDimensional ℝ Y]
    :
    (0 : Y) ∈ intrinsicClosure ℝ (dom(f⋆)) ↔
      ∀ y : E, 0 ≤ recessionFunction f y := by
  simpa [intrinsicClosure_eq_closure (𝕜 := ℝ) (s := dom(f⋆))] using
    zero_mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction

-- Proof sketch: same intrinsic-closure rewrite as above, applied to the strict-descent
-- negation formulation.
/-- Clause `(i)`, intrinsic-topology negation form: the origin fails to belong to
`intrinsicClosure ℝ (dom(f⋆))` exactly when `f` has a strict uniform linear descent direction. -/
theorem
zero_not_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction
    [FiniteDimensional ℝ Y]
    :
    (0 : Y) ∉ intrinsicClosure ℝ (dom(f⋆)) ↔
      ∃ y : E, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ dom(f),
          f (x + t • y) ≤ f x - (t * ε : WithTopBot ℝ) := by
  simpa [intrinsicClosure_eq_closure (𝕜 := ℝ) (s := dom(f⋆))] using
    zero_not_mem_closure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: identify `argmin(f)` with `∂f⋆(0)`, then use the singleton-subdifferential
-- criterion supplied by differentiability of the real branch of `f⋆` at the origin.
/-- Theorem 6.27.1 (10), clause (e): `argmin(f)` is the singleton `{x}` exactly when
the real branch of `f⋆` is differentiable at the origin and `x` is its gradient there. -/
theorem minimumSet_eq_singleton_iff_differentiableAt_convexConjugate_zero
    (x : E) :
    argmin(f) = {x} ↔
      DifferentiableAt ℝ (f⋆).realBranch (0 : E) ∧
        x = ∇ (f⋆).realBranch (0 : E) := sorry

end
