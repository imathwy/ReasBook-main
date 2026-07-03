

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_8_8 (from Chap02) -/
noncomputable section

open scoped Rockafellar

section

variable {𝕜 : Type*}
variable {E : Type*} [Add E] [SMul 𝕜 E]
variable {α : Type*} [Add α] [SMul 𝕜 α]

namespace Function

/-- Global affine translation law for `f` along direction `y` with slope `v`. -/
def HasTranslationSlope (𝕜 : Type*) [SMul 𝕜 E] [SMul 𝕜 α]
    (f : E → WithBotTop α) (y : E) (v : α) : Prop :=
  ∀ x : E, ∀ t : 𝕜, f (x + t • y) = f x + ((t • v : α) : WithBotTop α)

/-- Unfolding bridge for `HasTranslationSlope`. -/
@[simp] theorem hasTranslationSlope_iff
    {f : E → WithBotTop α} {y : E} {v : α} :
    f.HasTranslationSlope 𝕜 y v ↔
      (∀ x : E, ∀ t : 𝕜, f (x + t • y) = f x + ((t • v : α) : WithBotTop α)) :=
  Iff.rfl

end Function

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type*} [AddCommGroup E] [SMul 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.8 gives three equivalent ways to say that a proper convex function is
  affine in the direction `y` with slope `v`, and then adds the closed-case criterion coming from
  the existence of one affine line.
  `Function.IsProper`, `Function.recessionFunction`, the function-facing owner
  `Function.HasTranslationSlope`, and the imported owner `Set.lineal` for subsets of `E × α`.
- `bridge/view`: the source condition `(y, v) ∈ lin (epi f)` is rendered directly as membership in
  the chapter epigraph owner `lin[𝕜](epi f)`, while the recession-function clause is written as the
  oddness relation `-(((f)₀⁺) (-y)) = ((f)₀⁺) y` together with the value constraint
  `((f)₀⁺) y = v`.

Domain-style sampling used here:
- the chapter owners `Function.IsConvex` and `Function.IsProper`;
- `ConvexERealFunction.recessionFunction` from Corollary 8.5.1;
- `Function.HasTranslationSlope` introduced in this file;
- `Set.lineal` from Definition 8.4.2;
- the coordinate-free owner layer already used in Theorem 8.5 for the same recession-function API;
- `List.TFAE` as the canonical owner for a three-way equivalence statement.

Primitive data vs derived API:
- primitive input: only the function `f : E → WithBotTop α` and the direction/slope data `y`, `v`;
- owner hypotheses: `f.IsConvex 𝕜` and `f.IsProper`;
- derived views: epigraph lineality membership and the recession-function equalities.

Layer target: the two labeled declarations remain `source-facing`, but now reuse the upstream
chapter owners directly on the coordinate-free scalar-action layer instead of redeclaring local
copies on a concrete `R^n` model.
-/

variable (f : E → WithBotTop α)

/-- Theorem 8.8 (1): for a proper convex function, the global affine-translation formula along the
direction `y` with slope `v`, membership of `(y, v)` in the lineality space of the epigraph,
and the recession-function identity `-(((f)₀⁺) (-y)) = ((f)₀⁺) y = v` are equivalent. -/
-- Proof sketch: Theorem 8.5 identifies `((f)₀⁺) y` with the supremum of the
-- translation differences `f (x + y) - f x`, so the global affine-translation identity forces the
-- recession values at `y` and `-y` to be `v` and `-v`. The pair `(y, v)` belongs to the lineality
-- space of the epigraph exactly when both `(y, v)` and `(-y, -v)` lie in the recession cone of the
-- epigraph, which is the same oddness condition on `((f)₀⁺)`. Finally, if the
-- epigraph is invariant under translation by `(y, v)`, then every translate of `f` by `λ • y`
-- differs from `f` by the affine height shift `λ v`.
theorem translation_formula_epigraph_lineality_recession_value_tfae
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (y : E) (v : α) :
    List.TFAE
      [ f.HasTranslationSlope 𝕜 y v,
        ((y, v) ∈ lin[𝕜](epi f)),
        (-(((f)₀⁺) (-y)) = ((f)₀⁺) y ∧
          ((f)₀⁺) y = (v : WithBotTop α)) ] := sorry

end

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [SMul 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [IsOrderedAddMonoid α] [SMul 𝕜 α]
variable [TopologicalSpace α] [OrderTopology α]
variable [TopologicalSpace (WithBotTop α)] [OrderTopology (WithBotTop α)]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithBotTop α)

/-- Theorem 8.8 (2): if a closed proper convex function admits one affine line parallel to `y`,
then there is a slope `v = ((f)₀⁺)(y)` such that the global translation formula of part (1) holds,
and hence all three equivalent conditions of part (1) are satisfied. This is stated on the same
ordered scalar topological vector-space owner layer as the closed-case recession formulas in
Theorem 8.5. -/
-- Proof sketch: for a closed convex function, Theorem 8.5 identifies `((f)₀⁺) y` with
-- the positive difference-quotient limit based at any finite point. Along one affine line those
-- quotients are constant, so their common real value is `((f)₀⁺) y`. Applying part (1)
-- with that slope gives the global affine translation law.
theorem exists_global_translation_slope_of_affine_line
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) (y : E)
    (h_affine : ∃ x : E, ∃ a b : α, ∀ t : 𝕜,
      f (x + t • y) = ((t • a + b : α) : WithBotTop α)) :
    ∃ v : α,
      ((f)₀⁺) y = (v : WithBotTop α) ∧
        f.HasTranslationSlope 𝕜 y v := sorry

end
