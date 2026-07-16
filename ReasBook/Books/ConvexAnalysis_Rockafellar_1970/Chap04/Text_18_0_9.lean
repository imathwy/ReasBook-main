import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_5

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.9 characterizes exposed directions of `C` as rays `r` for which some
  affine half-line `affineHalfLine x r` is exposed in `C`.
- `core/canonical`: the owner is `Set.exposedDirections`, built from `IsExposed` on
  `affineHalfLine`.
- `bridge/view`: `Defn_18_5` already packages the source phrasing by quantifying over exposed
  affine half-lines, via `Set.mem_exposedDirections_iff`.

Domain-style sampling used here:
- `IsExposed`;
- `affineHalfLine`;
- `Set.exposedDirections`;
- `Set.mem_exposedDirections_iff`.

Primitive data vs derived API:
- primitive owner data (`Set.exposedDirections`) is defined upstream in `Defn_18_5`;
- this item records the source-facing membership characterization bridge
  `Set.mem_exposedDirections_iff`.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain appears in this item;
- scalar/ambient minimization: the bridge theorem already lives over the weakest owner layer used
  by `Set.exposedDirections`, with no `ℝ` specialization;
- owner correctness: `Set.exposedDirections` is the intrinsic direction owner for exposed
  half-line faces;
- topology phrasing: this item is not an ambient-vs-relative topology theorem;
- notation surface: owner-level theorem surface is primary; no extra notation owner is needed.
-/

/- Text 18.0.9: exposed directions are exactly rays carried by exposed affine half-line faces.
This is the canonical bridge theorem `Set.mem_exposedDirections_iff` on the owner
`Set.exposedDirections`. -/
recall Set.mem_exposedDirections_iff
