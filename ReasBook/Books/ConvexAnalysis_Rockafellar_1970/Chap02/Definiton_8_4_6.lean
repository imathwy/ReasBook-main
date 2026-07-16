import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.6 defines the rank of a set by subtracting the dimension of its
  lineality space from the dimension of the set itself.
- `core/canonical`: the owner abstractions are the set-dimension owner `Set.affineDim` and the
  immediately upstream invariant `Set.lineality`.
- `bridge/view`: rank is only the numerical composite
  `Set.affineDim 𝕜 C - Set.lineality 𝕜 C`, so it should
  reuse those owners directly rather than introducing a surrogate structure or an entrywise
  package of dimension data.
- `primitive data`: the primitive owner data are `Set.affineDim 𝕜 C` and `Set.lineality 𝕜 C`.
- `derived API`: the single integer invariant `Set.rank 𝕜 C`.

Domain-style sampling used here:
- `Set.affineDim` from Definition 2.4.10;
- `Set.lineality` from Definition 8.4.4;
- the parallel function-side invariant `Function.rank` from Definition 8.9.2.

Primitive data vs derived API:
- primitive owner data: the ambient affine dimension and the lineality;
- derived API: their difference, exposed as `Set.rank`.

Layer target: `bridge/view`, keeping the canonical set-side owners as the public core.
-/

namespace Set

section

variable (𝕜 : Type*) [DivisionRing 𝕜] [LE 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {P : Type*} [AddTorsor E P] [HAdd P E P]

/-- Definition 8.4.6: the rank of a set is its affine dimension minus its lineality. -/
abbrev rank (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] : ℤ :=
  dim[𝕜](C) - Set.lineality (E := E) 𝕜 C

scoped[Rockafellar] notation (name := setRankNotation_8_4_6)
    "rank[" 𝕜 "](" C ")" => Set.rank 𝕜 C

/-- Owner-level expansion of `Set.rank`: affine dimension minus lineality. -/
theorem rank_eq_affineDim_sub_lineality (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    Set.rank 𝕜 C = dim[𝕜](C) - Set.lineality (E := E) 𝕜 C :=
  rfl

/-- The rank of a set is its affine dimension minus its lineality. -/
@[simp] theorem rank_eq (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    rank[𝕜](C) = dim[𝕜](C) - Set.lineality (E := E) 𝕜 C :=
  rfl

end

end Set

end
