import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 5.19.9:
- primary domain: topological Krull dimension under specialization/generalization-lifting maps
- owner declarations inspected: `topologicalKrullDim`, `SpecializingMap`, `GeneralizingMap`, and
  the quasi-sober generic-point API `IsIrreducible.genericPoint`
- best owner abstraction: the canonical dimension owner `topologicalKrullDim` together with the
  map-lifting predicates `SpecializingMap f` and `GeneralizingMap f`; the only target-space
  irreducible-closed data needed in the proof is supplied canonically by `[QuasiSober Y]`
- primitive data: a surjective map carrying one of the two canonical lifting predicates, with
  quasi-sobriety on the target to choose generic points of irreducible closed subsets
- derived API: the disjunctive source-facing dimension inequality

Layer triage:
- `source-facing`: the dimension inequality for a surjective map along which specializations or
  generalizations lift
- `core/canonical`: `topologicalKrullDim`, `SpecializingMap`, `GeneralizingMap`, `QuasiSober`
- `bridge/view`: none

The file already uses the correct owner predicates, so the refinement here is only to keep the
public statement on that canonical layer, with only the quasi-sober generic-point hypothesis that
the proof actually uses, and keep the two directional cases as internal branches of one proof
rather than as separate local declarations.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [QuasiSober Y] {f : X → Y}

/-- Lemma 5.19.9: if `f : X → Y` is surjective, `Y` is sober, and either specializations or
generalizations lift along `f`, then the topological Krull dimension of `X` is at least that of
`Y`. For this dimension comparison, the source sober hypothesis is used only through the canonical
generic-point owner `[QuasiSober Y]`. -/
theorem topologicalKrullDim_le_of_surjective_specializing_or_generalizing
    (hSurj : Function.Surjective f) (hLift : SpecializingMap f ∨ GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rcases hLift with hSpec | hGen
  · -- Use quasi-sobriety of `Y` to identify
    -- irreducible closed subsets with generic points. A specialization chain in `Y` can then be
    -- lifted pointwise along the surjective specializing map, producing a chain of irreducible
    -- closed subsets in `X` of the same length.
    sorry
  · -- Represent irreducible closed subsets of the quasi-sober target `Y` by their generic points
    -- and
    -- lift a specialization chain in the opposite direction along the surjective generalizing map.
    -- This again yields a chain in `X` of the same length.
    sorry

end
