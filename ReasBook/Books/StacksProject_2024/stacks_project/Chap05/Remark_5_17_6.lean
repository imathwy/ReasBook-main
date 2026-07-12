import StacksProject_2024.Chap05.Theorem_5_17_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for proper-map characterizations:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_isUniversallyClosedMap`,
  `proper_map_characterization_tfae`;
- `source-facing`: the three-clause equivalence from Remark 5.17.6;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: `IsUniversallyClosedMap`.

Primitive data belongs to the owner layer: continuity, closedness, and compact fibers. The target
remark only extracts the clauses `(1)`, `(2)`, and `(4)` from the chapter's four-way
characterization, so the file should keep only that source-facing projection and reuse the chapter
owner theorem directly rather than rebuilding any of its component equivalences locally. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- A map is quasi-proper, moreover closed. -/
def IsClosedQuasiProperMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

/-- A map is closed, with quasi-compact fibers. -/
def IsClosedMapWithCompactFibers (f : X → Y) : Prop :=
  IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y})

-- Proof sketch: specialize Theorem `5.17.5` to clauses `(1)`, `(2)`, `(4)`, then rewrite the
-- first plus third clauses using the two semantic helper predicates above.
/-- Remark 5.17.6: for a continuous map, the quasi-proper closed condition, Bourbaki properness,
together with the closed compact-fiber condition from Theorem 5.17.5, are equivalent. -/
theorem proper_map_characterization_124_tfae (hf : Continuous f) :
    List.TFAE
      [ IsClosedQuasiProperMap f,
        IsProperMap f,
        IsClosedMapWithCompactFibers f ] := sorry

end
