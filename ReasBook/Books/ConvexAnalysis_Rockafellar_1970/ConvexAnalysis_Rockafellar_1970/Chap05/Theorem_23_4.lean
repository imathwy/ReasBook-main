import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_3

-- Declarations for this item were appended by the statement pipeline.

noncomputable section

open Bornology
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

/-!
Theorem 23.4 at the canonical owner layer.

- codomain generalized from `WithBotTop ℝ` to `WithBotTop 𝕜`;
- subdifferential-facing clauses exposed at the pairing level `Y`;
- real inner-product vector-subdifferential theorems kept below as bridge views.
-/

-- Proof sketch: if `x ∉ dom(f)`, then `f x = ⊤`. A subgradient inequality at `x` would force
-- every finite point of `f` to have value `⊤`, contradicting properness.
/-- Theorem 23.4 (1), intrinsic owner form: for a proper function, the dual-valued
subdifferential is empty at every point outside the effective domain. -/
theorem subdifferentialAt_eq_empty_of_not_mem_dom
    (hf_proper : f.IsProper) (hx : x ∉ dom(f)) :
    (∂[Y]f(x)) = ∅ := sorry

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: combine convexity/properness with Theorem 23.3's emptiness consequence on
-- `riDom(f)` to rule out empty subdifferential at `x`.
/-- Theorem 23.4 (2), intrinsic owner form: for a proper convex function, every point of
`ri[𝕜] (dom f)` has a nonempty dual-valued subdifferential. -/
theorem subdifferentialAt_nonempty_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    (∂[Y]f(x)).Nonempty := sorry

-- Proof sketch: clause (2) supplies nonemptiness of `∂ f at x`; Lemma 23.0.1 then gives the
-- support-function formula for the directional derivative, yielding closed/proper/convexity.
/-- Theorem 23.4 (3), intrinsic owner form: for a proper convex function and `x ∈ ri (dom f)`,
the directional-derivative function is closed proper convex. -/
theorem isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    IsClosedProperConvex[𝕜] (Function.directionalDerivativeAt f x) := sorry

-- Proof sketch: apply the canonical owner theorem
-- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` to `∂ f at x`.
/-- Theorem 23.4 (4), intrinsic owner form: for a proper convex function and `x ∈ ri (dom f)`,
the directional derivative at `x` equals the support function of `∂ f at x`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    Function.directionalDerivativeAt f x =
      (δᵛ(· | ∂[Y]f(x)) : E → WithBotTop 𝕜) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

-- Proof sketch: combine clause (4) with the bounded-support-function characterization and the
-- interior criterion on finite-dimensional spaces.
/-- Theorem 23.4 (5), intrinsic owner form: for a proper convex function on a finite-dimensional
real normed space, `∂[StrongDual ℝ E]f(x)` is nonempty and bounded iff
`x ∈ interior (dom f)`. -/
theorem subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    ((∂[StrongDual ℝ E]f(x)).Nonempty ∧ IsBounded (∂[StrongDual ℝ E]f(x))) ↔
      x ∈ interior (dom(f)) := sorry

-- Proof sketch: from clause (5), interior points give bounded nonempty subdifferential; combine
-- with clause (4) to show finiteness of the support value in every direction.
/-- Theorem 23.4 (6), intrinsic owner form: if `x ∈ interior (dom f)`, then all directional
derivatives at `x` are finite-valued. -/
theorem directionalDerivativeAt_finite_everywhere_of_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ interior (dom(f))) :
    ∀ y : E, ∃ r : ℝ, Function.directionalDerivativeAt f x y = (r : WithBotTop ℝ) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

namespace Function

/-! Euclidean bridge view of clause (1) through `Function.subdifferentialAt`. -/

-- Proof sketch: this is the Fréchet-Riesz preimage bridge of the intrinsic emptiness theorem.
/-- Theorem 23.4 (1), Euclidean bridge form: outside `dom(f)`, the vector-valued
subdifferential is empty. -/
theorem subdifferentialAt_eq_empty_of_not_mem_dom
    (hf_proper : f.IsProper) (hx : x ∉ dom(f)) :
    (∂ᵥf(x)) = ∅ := by
  have hroot : (∂[StrongDual ℝ E]f(x) : Set (StrongDual ℝ E)) = ∅ :=
    _root_.subdifferentialAt_eq_empty_of_not_mem_dom (f := f) (x := x) hf_proper hx
  simp [Function.subdifferentialAt, hroot]

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

namespace Function

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-! Euclidean bridge view of clauses (2)–(6). -/

-- Proof sketch: Euclidean bridge form of the intrinsic nonemptiness clause.
/-- Theorem 23.4 (2), Euclidean bridge form: for a proper convex function, every point of
`ri (dom f)` has a nonempty vector-valued subdifferential. -/
theorem subdifferentialAt_nonempty_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    (∂ᵥf(x)).Nonempty := sorry

-- Proof sketch: Euclidean bridge form of clause (3).
/-- Theorem 23.4 (3), Euclidean bridge form: for a proper convex function and `x ∈ ri (dom f)`,
the directional-derivative function is closed proper convex. -/
theorem isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    IsClosedProperConvex[ℝ] (directionalDerivativeAt f x) := sorry

-- Proof sketch: Euclidean bridge form of clause (4).
/-- Theorem 23.4 (4), Euclidean bridge form: for a proper convex function and `x ∈ ri (dom f)`,
the directional derivative at `x` equals the support function of `∂ᵥf(x)`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    directionalDerivativeAt f x =
      (δᵛ(· | ∂ᵥf(x)) : E → WithBotTop ℝ) := sorry

-- Proof sketch: Euclidean bridge form of clause (5).
/-- Theorem 23.4 (5), Euclidean bridge form: for a proper convex function on a finite-dimensional
real inner-product space, `∂ᵥf(x)` is nonempty and bounded iff `x ∈ interior (dom f)`. -/
theorem subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    ((∂ᵥf(x)).Nonempty ∧ IsBounded (∂ᵥf(x))) ↔ x ∈ interior (dom(f)) := sorry

-- Proof sketch: Euclidean bridge form of clause (6).
/-- Theorem 23.4 (6), Euclidean bridge form: if `x ∈ interior (dom f)`, then every directional
derivative at `x` is finite-valued. -/
theorem directionalDerivativeAt_finite_everywhere_of_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ interior (dom(f))) :
    ∀ y : E, ∃ r : ℝ, directionalDerivativeAt f x y = (r : WithBotTop ℝ) := sorry

end Function

end
