import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

variable {ι : Type*} [Finite ι]
variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.8.3.1 says that if finitely many closed proper convex functions on
  a finite-dimensional Hausdorff topological vector space over `𝕜` have the same recession
  function,
  then their convex hull is again closed and proper, has that same recession function, and the
  finite-convex-combination infimum formula from Theorem 5.6 is attained at every point.
- `core/canonical`: the existing owner objects are `Function.convexHull`, used here through the
  source-facing specialization `conv(⨅ i, f i)` for the convex hull of a family of functions,
  `LowerSemicontinuous` for closedness, `f.IsProper` for properness, and
  `Function.recessionFunction` for recession functions.
- `bridge/view`: Rockafellar's list `f₁, ..., f_m` is represented by a family
  `f : ι → E → WithTopBot 𝕜`, and the attainment clause uses the canonical finite-simplex owners
  packaged in `Function.convexCombinationValues`, whose point and value coordinates are both
  expressed through the canonical `StdSimplex.sum` interface from Theorem 5.6.

Domain-style sampling used here:
- `Function.convexHull_iInf_eq_verticalInfimum_convexHull_iUnion_epigraph`;
- `Function.convexHull_iInf_eq_sInf_convexCombination_values`;
- `Function.convexCombinationValues`;
- `StdSimplex.sum`;
- `Function.recessionFunction`;
- `recessionCone_convexHull_iUnion_eq_common_recessionCone`.

Primitive data vs derived API:
- primitive inputs for the owner-side epigraph consequences: the family `f`, the intrinsic common-
  recession-function owner hypothesis `∃ g, ∀ i, (f i)₀⁺ = g` (with pairwise equality used as a
  bridge form), and the convexity and lower-semicontinuity hypotheses on each `f i`;
- extra primitive input for the owner bridge from epigraph recession cones back to recession
  functions, and hence for the closedness, properness, recession-function, and attainment clauses:
  properness of each `f i`;
- extra primitive input for the nontrivial properness and attainment clauses: `Nonempty ι`, which
  rules out the empty-family degeneracy;
- derived conclusions: lower semicontinuity, properness, preservation of the common recession
  function, and attainment for the already-canonical finite-convex-combination formula
  `Function.convexHull_iInf_eq_sInf_convexCombination_values`, expressed on the canonical owner
  `Function.convexCombinationValues`.

Ambient minimization check:
- unlike the family convex-hull owner from Theorem 5.6, the closedness and common-recession
  consequences here are obtained by passing to scalar epigraphs and invoking Corollary 9.8.1;
- since that owner theorem already lives on the intrinsic chapter ambient of finite-dimensional
  Hausdorff topological vector spaces over `𝕜`, this file should reuse the same ambient layer
  rather than falling back to the coordinate model `R^n = EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`; the item is stated directly for the textbook convex hull
`conv {f_i | i ∈ ι}` as the canonical owner `conv(⨅ i, f i)`, without introducing any extra
package or wrapper around the family. The primitive public common-recession assumption is the
intrinsic existence form `∃ g, ∀ i, (f i)₀⁺ = g`; pairwise equalities are retained as thin bridges,
and the explicit-value form is kept where the conclusion itself names the common function `g`.
-/

variable {f : ι → E → WithTopBot 𝕜}

private theorem lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    LowerSemicontinuous (conv(⨅ i, f i)) := sorry

/-- Corollary 9.8.3.1 (1), source-facing common-recession form: if a finite family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a common
recession function, then its convex hull is closed, expressed here by lower semicontinuity. -/
-- Proof sketch: apply Corollary 9.8.1 to the scalar epigraphs of the functions `f i`. Closedness
-- and convexity of those epigraphs come from `hf_closed` and `hf_convex`, while the common
-- recession-function hypothesis identifies those recession cones pairwise. Properness is used to
-- identify each epigraph recession cone with the epigraph of `(f i)₀⁺`. Reading the resulting
-- closed convex hull back as an epigraph gives lower semicontinuity of `conv(⨅ i, f i)`.
theorem lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    LowerSemicontinuous (conv(⨅ i, f i)) := by
  rcases h_common_recession with ⟨_, hg⟩
  exact lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (1), intrinsic bridge form: if a finite family of closed proper convex
functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise equal
recession functions, then its convex hull is closed. -/
theorem lowerSemicontinuous_convexHull_iInf_of_pairwise_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    LowerSemicontinuous (conv(⨅ i, f i)) := by
  exact lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

section

variable [Nonempty ι]

private theorem isProper_convexHull_iInf_of_common_recessionFunction_core
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    (conv(⨅ i, f i)).IsProper := sorry

/-- Corollary 9.8.3.1 (2), source-facing common-recession form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function, then its convex hull is proper. -/
-- Proof sketch: the epigraph of `conv(⨅ i, f i)` is the closed convex hull of the
-- union of the epigraphs of the `f i`. Part (1) gives lower semicontinuity, while
-- the owner theorem `Function.isGreatest_conv_iInf_minorant` supplies convexity of
-- `conv(⨅ i, f i)`. Properness then amounts to excluding the degenerate values `⊥` and `⊤`,
-- which follows from the properness of each `f i` together with the common recession-function
-- hypothesis.
theorem isProper_convexHull_iInf_of_common_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    (conv(⨅ i, f i)).IsProper := by
  rcases h_common_recession with ⟨_, hg⟩
  exact isProper_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (2), intrinsic bridge form: if a finite nonempty family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise
equal recession functions, then its convex hull is proper. -/
theorem isProper_convexHull_iInf_of_pairwise_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    (conv(⨅ i, f i)).IsProper := by
  exact isProper_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

end

private theorem recessionFunction_convexHull_iInf_eq_common_core (i : ι)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ := sorry

section

variable [Nonempty ι]

/-- Corollary 9.8.3.1 (3), source-facing common-value form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function `g`, then the recession function of its convex hull agrees with `g`. -/
-- Proof sketch: pass to scalar epigraphs and apply Corollary 9.8.1 to identify the recession
-- cone of the convex hull of their union with the common recession cone of the family epigraphs.
-- Properness identifies those epigraph recession cones with the epigraphs of the recession
-- functions. The convex hull epigraph is exactly the epigraph of `conv(⨅ i, f i)`, so comparing
-- those epigraph recession cones gives the stated equality of recession functions.
theorem recessionFunction_convexHull_iInf_eq_common_recessionFunction
    (g : E → WithTopBot 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ j, (f j)₀⁺ = g) :
    (conv(⨅ i, f i))₀⁺ = g := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  calc
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ :=
      recessionFunction_convexHull_iInf_eq_common_core i
        hf_convex hf_closed hf_proper
        (by
          intro j k
          simp [h_common_recession j, h_common_recession k])
    _ = g := h_common_recession i

end

/-- Corollary 9.8.3.1 (3), intrinsic bridge form: if a finite family of closed proper convex
functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise equal
recession functions, then the recession function of its convex hull agrees with `(f i)₀⁺` for any
chosen index `i`. -/
theorem recessionFunction_convexHull_iInf_eq_recessionFunction_of_pairwise (i : ι)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ := by
  exact recessionFunction_convexHull_iInf_eq_common_core i
    hf_convex hf_closed hf_proper
    (by
      intro j k
      by_cases hjk : j = k
      · simp [hjk]
      · exact h_pairwise_recession hjk)

section

variable [Nonempty ι]

private theorem exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := sorry

/-- Corollary 9.8.3.1 (4), source-facing common-recession form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function, then for each `x` the infimum in
`Function.convexHull_iInf_eq_sInf_convexCombination_values` is attained, equivalently by
membership of `conv(⨅ i, f i) x` in the canonical owner
`Function.convexCombinationValues (⨅ i, f i) x`. -/
-- Proof sketch: `Function.convexHull_iInf_eq_sInf_convexCombination_values` identifies
-- `conv(⨅ i, f i) x` with the infimum over finite convex combinations of function
-- values. Since part (1) gives closedness and part (3) identifies the common recession function
-- of the resulting epigraph, the closed convex hull of the union of the epigraphs contains the
-- point `(x, conv(⨅ i, f i) x)` itself. Unwinding the proof of Theorem 5.6, that
-- point comes from one finite convex combination, which exactly says that
-- `conv(⨅ i, f i) x` belongs to `Function.convexCombinationValues (⨅ i, f i) x`.
theorem exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := by
  rcases h_common_recession with ⟨_, hg⟩
  exact exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    x hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (4), intrinsic bridge form: if a finite nonempty family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise
equal recession functions, then for each `x` the infimum in
`Function.convexHull_iInf_eq_sInf_convexCombination_values` is attained. -/
theorem exists_finite_convex_combination_eq_convexHull_iInf_of_pairwise_recessionFunction
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := by
  exact exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    x hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

end

end

end
