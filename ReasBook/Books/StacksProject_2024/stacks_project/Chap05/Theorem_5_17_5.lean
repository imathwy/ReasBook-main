import StacksProject_2024.Chap05.Definition_5_17_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for characterizations of proper maps:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_universally_closed`,
  and the chapter bridge `isProperMap_iff_isUniversallyClosedMap`;
- source-facing: `IsQuasiProperMap`;
- core/canonical: `IsProperMap`;
- bridge/view: `IsUniversallyClosedMap`. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- The source-facing condition that a map is both quasi-proper and closed. -/
def IsQuasiProperClosedMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

/-- The source-facing condition that a map is closed and has compact fibers. -/
def IsClosedMapWithCompactFibers (f : X → Y) : Prop :=
  IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y})

/-- Bourbaki properness is equivalent to being both quasi-proper and closed. -/
-- Proof sketch: use `isProperMap_iff_isClosedMap_and_compact_fibers`; compact fibers come from
-- quasi-properness on singletons, and quasi-properness follows from properness by compact
-- preimages.
theorem isQuasiProperClosedMap_iff_isProperMap (hf : Continuous f) :
    IsQuasiProperClosedMap f ↔ IsProperMap f := sorry

/-- Theorem 5.17.5: for a continuous map of topological spaces, the Stacks conditions
"quasi-proper and closed", "Bourbaki-proper", "universally closed", and "closed with
quasi-compact fibers" are equivalent. Here Bourbaki-proper is expressed by mathlib's
`IsProperMap`, Stacks universal closedness by the chapter's bridge predicate
`IsUniversallyClosedMap`, and quasi-compactness by `IsCompact`. -/
-- Proof sketch: combine the equivalence between quasi-proper closed maps and `IsProperMap`,
-- the chapter bridge `isProperMap_iff_isUniversallyClosedMap`, and the standard compact-fiber
-- characterization of proper maps.
theorem proper_map_characterization_tfae (hf : Continuous f) :
    List.TFAE
      [ IsQuasiProperClosedMap f,
        IsProperMap f,
        IsUniversallyClosedMap f,
        IsClosedMapWithCompactFibers f ] := sorry

end
