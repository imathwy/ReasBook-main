import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section

variable {ι : Type*} {𝕜 E : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E]

namespace Set

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.3.1 specializes the finite-convex-combination description of a
  convex hull to a finitely indexed family `b : ι → E`.
- `core/canonical`: the owner abstractions are `conv[𝕜] (range b)` for the hull itself and
  the simplex membership theorem `Set.mem_conv_iff_exists_stdSimplex`; the simplex-side point
  map is the owner-level convex-combination map
  `fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination`.
- `bridge/view`: the set-level bridge theorem is the image equality
  `conv[𝕜] (range b) = Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination)`.
- Primitive data vs derived API: the indexed family `b` is the primitive data; nonnegativity and
  total mass `1` are fields of `StdSimplex`, and the owner-level API should expose simplex
  witnesses directly; the range equality is a bridge view of that owner statement.
- Domain-style sampling: this item reuses `StdSimplex`, `StdSimplex.map_map`, and
  `Set.mem_conv_iff_exists_stdSimplex`.
- Layer target: `core/canonical` first (membership via simplex owner), then the range-equality
  bridge.
-/

/-- Helper for Corollary 2.3.1: simplex witnesses on `range b` are equivalent to simplex
witnesses on the original index type `ι`. -/
private theorem exists_stdSimplex_range_iff_exists_stdSimplex
    (b : ι → E) {x : E} :
    (∃ w : StdSimplex 𝕜 (range b), (w.map Subtype.val).convexCombination = x) ↔
      ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x := by
  constructor
  · rintro ⟨w, hx⟩
    -- Choose a preimage in `ι` for each point of `range b`, then reindex the simplex along it.
    choose c hc using (fun y : range b ↦ y.2)
    refine ⟨w.map c, ?_⟩
    simpa [StdSimplex.map_map, hc] using hx
  · rintro ⟨w, hw⟩
    -- Push the simplex forward along the canonical map from `ι` into `range b`.
    refine ⟨w.map (fun i ↦ ⟨b i, Set.mem_range_self i⟩), ?_⟩
    simpa [StdSimplex.map_map] using hw

/-- Helper for Corollary 2.3.1: owner-level membership form on the canonical set surface.
A point belongs to `conv[𝕜] (range b)` exactly when it belongs to the range of the simplex-map
convex-combination operator induced by `b`. -/
theorem mem_conv_range_iff_mem_range_convexCombination (b : ι → E) {x : E} :
    x ∈ (conv[𝕜] (range b)) ↔
      x ∈ Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
  -- Specialize Theorem 2.3 to `range b`, then replace subtype witnesses by indexed witnesses.
  calc
    x ∈ (conv[𝕜] (range b))
        ↔ ∃ w : StdSimplex 𝕜 (range b), (w.map Subtype.val).convexCombination = x := by
          simpa using
            (Set.mem_conv_iff_exists_stdSimplex (𝕜 := 𝕜) (s := range b) (x := x))
    _ ↔ ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x :=
      exists_stdSimplex_range_iff_exists_stdSimplex (b := b) (x := x)
    _ ↔ x ∈ Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
      simp [Set.mem_range]

/-- Helper for Corollary 2.3.1: existential simplex-witness form of
`Set.mem_conv_range_iff_mem_range_convexCombination`. -/
theorem mem_conv_range_iff_exists_stdSimplex (b : ι → E) {x : E} :
    x ∈ (conv[𝕜] (range b)) ↔
      ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x := by
  -- This is just the `Set.range` presentation rewritten as an existential witness.
  simpa [Set.mem_range] using
    (mem_conv_range_iff_mem_range_convexCombination (𝕜 := 𝕜) (b := b) (x := x))

/-- Corollary 2.3.1 as the set-image bridge view of
`Set.mem_conv_range_iff_mem_range_convexCombination`. -/
theorem conv_range_eq_range_convexCombination (b : ι → E) :
    (conv[𝕜] (range b)) =
      Set.range
        (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
  -- Extensionality reduces the set equality to the membership theorem above.
  ext x
  simpa using
    (mem_conv_range_iff_mem_range_convexCombination (𝕜 := 𝕜) (b := b) (x := x))

end Set

end
