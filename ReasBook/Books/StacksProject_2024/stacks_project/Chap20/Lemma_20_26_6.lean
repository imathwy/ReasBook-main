import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_59_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.26.6:
- primary domain: K-flat objects in distinguished triangles of the homotopy category of cochain
  complexes of `𝒪_X`-modules;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 distinguished-triangle two-out-of-three theorems for the
  owner predicate `CochainComplex.IsKFlat`;
- primitive vs derived:
  primitive data are only a distinguished triangle in `K(𝒪_X)` and K-flatness
  hypotheses on two vertices;
  the ringed-space formulation is derived API by specializing the ambient category to `X.Modules`,
  so this file should expose only that specialized theorem surface instead of parallel local
  declarations.

Source/core/bridge triage:
- `source-facing`: the ringed-space two-out-of-three property for K-flat complexes in a
  distinguished triangle;
- `core/canonical`: `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file records the direct specialization of those owner theorems to
  `K(𝒪_X)`.

This file is therefore recall-only after refinement: Definition `20.26.2` already identifies the
ringed-space notion with the owner predicate `CochainComplex.IsKFlat`, so Lemma `20.26.6` adds no
second local theorem family beyond the three Chapter 15 distinguished-triangle owners.
-/

/- Lemma 20.26.6 (1): if `T` is a distinguished triangle in `K(𝒪_X)` and the first two
terms are K-flat, then the third term is K-flat. This file directly recalls the canonical owner
theorem `CochainComplex.isKFlat_obj₃_of_distinguished_triangle` on the ringed-space surface. -/
recall CochainComplex.isKFlat_obj₃_of_distinguished_triangle

/- Lemma 20.26.6 (2): if `T` is a distinguished triangle in `K(𝒪_X)` and the first and
third terms are K-flat, then the second term is K-flat. This file directly recalls the canonical
owner theorem `CochainComplex.isKFlat_obj₂_of_distinguished_triangle` on the ringed-space
surface. -/
recall CochainComplex.isKFlat_obj₂_of_distinguished_triangle

/- Lemma 20.26.6 (3): if `T` is a distinguished triangle in `K(𝒪_X)` and the second and
third terms are K-flat, then the first term is K-flat. This file directly recalls the canonical
owner theorem `CochainComplex.isKFlat_obj₁_of_distinguished_triangle` on the ringed-space surface.
-/
recall CochainComplex.isKFlat_obj₁_of_distinguished_triangle

end AlgebraicGeometry.RingedSpace
