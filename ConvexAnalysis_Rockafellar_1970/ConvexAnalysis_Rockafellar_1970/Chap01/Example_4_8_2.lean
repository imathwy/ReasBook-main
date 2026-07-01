import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item gives the absolute-value function as an example of a positively
  homogeneous convex function that is not linear; positive homogeneity uses the ordered-ring
  layer, nonlinearity uses the strict-ordered-ring layer, and convexity uses the same
  ordered-ring layer.
- `core/canonical`: the primitive owner abstractions are the canonical function `abs`,
  `Function.PositivelyHomogeneous` on the finite codomain surface `(abs : 𝕜 → 𝕜)`,
  the finite-valued convexity owner `ConvexOn 𝕜 Set.univ (abs : 𝕜 → 𝕜)`, and mathlib's
  predicate `IsLinearMap`.
- `bridge/view`: the identity `abs_mul` proves positive homogeneity; the convexity owner
  statement uses `Function.isConvex_coe_of_convexOn_univ` together with the triangle inequality
  bridge `abs_sub`; failure of
  `map_neg` shows nonlinearity.
- Primitive data vs derived API: no local wrapper function belongs here. The primitive object is
  the canonical function `abs`; positive homogeneity, convexity on `Set.univ`, and nonlinearity
  are source-facing theorem facts. The chapter owner statements on `WithTopBot` are then explicit
  bridge consequences.

Domain-style sampling used here:
- `abs : 𝕜 → 𝕜` on the ordered-ring layer;
- `Function.PositivelyHomogeneous` from Definition 4.8;
- `ConvexOn`, `Function.isConvex_coe_of_convexOn_univ`, `abs_sub`, `abs_mul`;
- `IsLinearMap.map_neg`.
- Layer target: `source-facing` at the primitive owner layer, with chapter-codomain statements
  provided as direct bridge consequences.
-/

namespace Function

/-- Helper for Example 4.8.2: the canonical codomain lift sends a finite-valued function to the
same function viewed in `WithTopBot`. -/
abbrev toWithTopBot {E α : Type*} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Helper for Example 4.8.2: the chapter owner `Function.IsConvex` is convexity of the epigraph
of a `WithTopBot`-valued map. -/
abbrev IsConvex (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E α : Type*} [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [LE α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Example 4.8.2: convexity on `Set.univ` for a finite-valued map yields convexity of
its canonical `WithTopBot` lift. -/
theorem isConvex_coe_of_convexOn_univ {𝕜 E β : Type*}
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f.toWithTopBot.IsConvex 𝕜 := by
  simpa [Function.toWithTopBot, Function.IsConvex, epi_univ_eq_setOf_le] using hf.convex_epigraph

end Function

/-- Helper for Example 4.8.2: scalar multiplication on `WithTopBot 𝕜` is multiplication by the
coerced scalar. -/
local instance instSMulWithTopBot {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Example 4.8.2 (primitive owner surface): absolute value is positively homogeneous. -/
theorem abs_positivelyHomogeneous_coe {𝕜 : Type*}
    [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    (abs : 𝕜 → 𝕜).PositivelyHomogeneous 𝕜 := by
  intro c x
  simp [smul_eq_mul, abs_of_pos c.2, abs_mul]

/-- Example 4.8.2 (chapter bridge surface): absolute value is positively homogeneous after the
canonical codomain lift to `WithTopBot`. -/
theorem abs_positivelyHomogeneous {𝕜 : Type*}
    [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ((abs : 𝕜 → 𝕜).toWithTopBot).PositivelyHomogeneous 𝕜 := by
  -- Map the finite-valued homogeneity equality through the canonical coercion into `WithTopBot`.
  intro c x
  change (((abs ((c : 𝕜) * x) : 𝕜) : WithTopBot 𝕜) =
    ((c : 𝕜) : WithTopBot 𝕜) * ((abs x : 𝕜) : WithTopBot 𝕜))
  simp [abs_mul, abs_of_pos c.2]

/-- Example 4.8.2 (primitive owner surface): absolute value is convex on `Set.univ`. -/
theorem abs_convexOn_univ {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ConvexOn 𝕜 (Set.univ : Set 𝕜) (abs : 𝕜 → 𝕜) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have htri : |a * x + b * y| ≤ |a * x| + |b * y| := by
    simpa [sub_eq_add_neg, abs_neg, add_assoc, add_comm, add_left_comm] using
      (abs_sub (a * x) (-(b * y)))
  calc
    |a • x + b • y| = |a * x + b * y| := by simp [smul_eq_mul]
    _ ≤ |a * x| + |b * y| := htri
    _ = a * |x| + b * |y| := by
      simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a • |x| + b • |y| := by simp [smul_eq_mul]

/-- Example 4.8.2 (chapter bridge surface): absolute value is convex after the canonical codomain
lift to `WithTopBot`. -/
theorem abs_isConvex {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ((abs : 𝕜 → 𝕜).toWithTopBot).IsConvex 𝕜 := by
  exact Function.isConvex_coe_of_convexOn_univ abs_convexOn_univ

/-- Example 4.8.2: absolute value is not linear on any strictly ordered ring. -/
theorem abs_not_isLinearMap {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    ¬ IsLinearMap 𝕜 (abs : 𝕜 → 𝕜) := by
  intro h
  have hneg := h.map_neg (1 : 𝕜)
  have hone : (1 : 𝕜) = -1 := by
    simpa using hneg
  have h01 : (0 : 𝕜) < -1 := by
    exact hone ▸ (zero_lt_one : (0 : 𝕜) < 1)
  exact (not_lt_of_gt (neg_one_lt_zero : (-1 : 𝕜) < 0)) h01
