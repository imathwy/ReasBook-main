import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.7 starts from convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization
  sets `K₁, K₂ ⊆ R × E`, then forms the set `K` of pairs `(λ, x)` whose second coordinate
  decomposes fiberwise as `x = x₁ + x₂` with `(λ, x₁) ∈ K₁` and `(λ, x₂) ∈ K₂`.
- `core/canonical`: the chapter owners are `homogenizationSet` and `+ᶠ`, with
  convexity expressed by the canonical predicate `Convex R`.
- `bridge/view`: `K₁` and `K₂` are exactly `homogenizationSet C₁` and `homogenizationSet C₂`,
  while `K` is exactly their fiberwise sum `+ᶠ` from Theorem 3.6.
- Primitive data vs derived API: the sets `C₁`, `C₂` are primitive, and the displayed convexity
  conclusion for their fiberwise homogenized sum is the direct theorem.
- Domain-style sampling: this item reuses the source-facing set constructor
  `homogenizationSet`, the owner theorem `Convex.homogenizationSet`, and the fiberwise-sum
  convexity theorem `Convex.fiberwiseSum`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `No`.
  2. Scalar/ambient structure too strong in this source-facing theorem? `No`; no additional
     strengthening is introduced beyond the upstream owner theorem `Convex.homogenizationSet`.
  3. Owner tied to concrete model? `No`; theorem is over generic module `E`.
  4. Better intrinsic/relative topology surface? `N/A` (non-topological statement).
  5. Owner name too concrete/heavy? `No`; uses short owner `Convex` and chapter notation `K[...]`.
  6. Needed notation used on theorem surface? `Yes`; both `K[R | C]` and `+ᶠ` are used directly.
- Layer target: `bridge/view`.
-/

/-- Text 3.6.7: for convex sets `C₁` and `C₂` in `R^n`, the set of pairs `(λ, x)` admitting a
decomposition `x = x₁ + x₂` with `(λ, x₁)` in the homogenization set of `C₁` and `(λ, x₂)` in the
homogenization set of `C₂` is convex. This formulation over `R` specializes to `R^n`
without changing the mathematics. -/
-- Proof sketch: the owner theorem `Convex.homogenizationSet` gives convexity of
-- `homogenizationSet C₁` and `homogenizationSet C₂`. Theorem 3.6 then applies directly to their
-- fiberwise sum set.
theorem Convex.homogenizationSet_fiberwiseSum {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] +ᶠ K[R | C₂]) := by
  exact (hC₁.homogenizationSet).fiberwiseSum hC₂.homogenizationSet

end
