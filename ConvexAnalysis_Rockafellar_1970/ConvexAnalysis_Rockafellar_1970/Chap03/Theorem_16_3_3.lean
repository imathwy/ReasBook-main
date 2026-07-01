import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_16_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.3 removes the closure from Theorem 16.3.2 under a relative-
  interior hypothesis, then records the pointwise infimum formula and the attainment-or-vacuity
  alternative.
- `core/canonical`: the owner layer is pairing-based and scalar-parameterized:
  `convexConjugate`, `Function.linearImage`, and `riDom[𝕜](g)`.
- `bridge/view`: the Euclidean/adjoint statement is a specialization via `Astar := A.adjoint`.

Domain-style sampling used here:
- `convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_adjoint_of_convex`
  and its pairing-level owner from Theorem 16.3.2;
- `Function.linearImage_eq_sInf_image` from Theorem 5.7;
- `convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula`
  from Text 16.0.5;
- the relative-interior owner `riDom[𝕜](·)`.

Primitive data vs derived API:
- primitive inputs: linear maps `A : E → F`, `Astar : F → E`, compatibility
  `⟪Astar y, x⟫ = ⟪y, A x⟫`, a convex `g : F → WithBotTop 𝕜`, and
  `∃ x, A x ∈ riDom[𝕜](g)`;
- derived API: closure-free dual identity, pointwise infimum formula, and attainment-or-vacuity.

Layer target: `source-facing`, expressed directly through the established owner declarations.
-/

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (g : F → WithBotTop 𝕜)

-- Proof sketch: combine Theorem 9.5 (`cl(g ∘ A) = cl(g) ∘ A`) with Theorem 16.3.2 on the
-- pairing owner layer, then remove the remaining closure on the linear image under the same
-- relative-interior hypothesis.
/-- Pairing-layer closure-free form of Theorem 16.3.3. -/
theorem convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    :
    (g ∘ A)⋆ = Astar ◁ g⋆ := by
  have hcl_comp : cl(g ∘ A) = cl(g) ∘ A := by
    exact hg.lowerSemicontinuousHull_comp_linearMap_eq (A := A) (by
      simpa [Set.Nonempty] using hri)
  have hdual :
      ((g ∘ A)⋆ : E → WithBotTop 𝕜) =
        cl(Astar ◁ (g⋆ : F → WithBotTop 𝕜)) := by
    sorry
  -- The remaining step is exactly the closure-removal claim for the linear-image side.
  sorry

-- Proof sketch: apply the owner-level pointwise theorem from Text 16.0.5 to the closure-free
-- equality established just above, then expand the right-hand side by
-- `Function.linearImage_eq_sInf_image`.
/-- Evaluating the closure-free dual formula at `xStar` gives the infimum of `g⋆` on the dual
fiber `Astar yStar = xStar`. -/
theorem convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : F | Astar yStar = xStar}) := by
  have hdual : (g ∘ A)⋆ = Astar ◁ g⋆ :=
    convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
      A Astar g hAstar hg hri
  simpa [Function.linearImage_eq_sInf_image] using
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
      A Astar g hdual xStar

-- Proof sketch: under the same relative-interior hypothesis, the source theorem states that the
-- infimum over the dual fiber is attained whenever the fiber is nonempty. If the fiber is empty,
-- the displayed infimum is vacuous and equals `⊤`.
/-- Under the same hypothesis, the infimum over the dual fiber is either vacuous (`⊤`) or attained
at some `yStar` with `Astar yStar = xStar`. -/
theorem convexConjugate_comp_linearMap_apply_eq_top_or_exists_eq_and_eq_conjugate_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar = ⊤ ∨
      ∃ yStar : F, Astar yStar = xStar ∧
        (g ∘ A)⋆ xStar = g⋆ yStar := sorry

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (A : E →ₗ[ℝ] F) (g : F → WithBotTop ℝ)

/-- Theorem 16.3.3, adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    :
    (g ∘ A)⋆ = A.adjoint ◁ g⋆ := by
  simpa using
    (convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri)

/-- Pointwise infimum formula in the adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : F | A.adjoint yStar = xStar}) := by
  simpa using
    (convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri xStar)

/-- Attainment-or-vacuity formula in the adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar = ⊤ ∨
      ∃ yStar : F, A.adjoint yStar = xStar ∧
        (g ∘ A)⋆ xStar = g⋆ yStar := by
  simpa using
    (convexConjugate_comp_linearMap_apply_eq_top_or_exists_eq_and_eq_conjugate_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri xStar)

end
