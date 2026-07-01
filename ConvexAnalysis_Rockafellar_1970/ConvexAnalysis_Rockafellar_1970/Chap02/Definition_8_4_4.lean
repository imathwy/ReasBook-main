import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.4 names the lineality of a set as the dimension of its
  lineality space.
- `core/canonical`: the owner abstractions already present upstream are `Set.lineal` (written as
  `lin[𝕜](C)`) from
  Definition 8.4.2 and the affine-dimension owner `Set.affineDim` from Definition 2.4.10.
- `bridge/view`: lineality is only the numerical composite of those two owners, so it should be a
  thin abbreviation rather than a new wrapper structure or a second set-side lineality package.
- `primitive data`: the primitive owner remains the scalar-parameterized set
  `Set.lineal 𝕜 C`.
- `derived API`: the scalar invariant `Set.lineality 𝕜 C`.

Domain-style sampling used here:
- `Set.lineal` / `lin[𝕜](C)` from Definition 8.4.2;
- `Set.affineDim` from Definition 2.4.10;
- the parallel function-side invariant `ConvexERealFunction.lineality` from Definition 8.9.2,
  which is likewise a thin affine-dimension composite.

Primitive data vs derived API:
- primitive owner data: the set `Set.lineal 𝕜 C`;
- derived API: its affine dimension, exposed as `Set.lineality 𝕜 C`.

Layer target: `bridge/view`, reusing the existing owner abstractions directly.
-/

namespace Set

open scoped Rockafellar

variable (𝕜 : Type*) [DivisionRing 𝕜] [LE 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {P : Type*} [HAdd P E P]

/-- Definition 8.4.4: the lineality of a set is the affine dimension of its lineality space. -/
abbrev lineality (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] : ℤ :=
  dim[𝕜](Set.lineal (E := E) 𝕜 C)

scoped[Rockafellar] notation (name := setLinealityNotation_8_4_4)
    "lineality[" 𝕜 "](" C ")" => Set.lineality 𝕜 C
scoped[Rockafellar] notation (name := setLinealityNotationAmbient_8_4_4)
    "lineality[" 𝕜 "," ambient "](" C ")" => Set.lineality (E := ambient) 𝕜 C

/-- The lineality of a set is the affine dimension of its lineality space. -/
theorem lineality_eq (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    Set.lineality (E := E) 𝕜 C = dim[𝕜](Set.lineal (E := E) 𝕜 C) :=
  rfl

/-- Owner-level expansion: lineality is the affine dimension of the affine span of `lin[𝕜](C)`. -/
theorem lineality_eq_affineSpan_affineDim (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    Set.lineality (E := E) 𝕜 C = (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).affineDim :=
  rfl

end Set
